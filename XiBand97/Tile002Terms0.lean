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
namespace Reinmann.XiBand97.Tile002Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9561/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9561/640))
  have he : value ((69/80), (9561/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-347455105/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-370109903641463/1125899906842624), (992937241389393/2251799813685248)), (54714757/2251799813685248), by norm_num⟩
  | 1 => ⟨((30582027/134217728), (-656367921/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-678331065/8589934592), (227479787/2147483648)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((156727755/8589934592), (-52558991/2147483648)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-217270803/68719476736), (582897863/137438953472)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((240961031/549755813888), (-646454417/1099511627776)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-222695279/4398046511104), (298725371/4398046511104)), (83/17592186044416), by norm_num⟩
  | 7 => ⟨((705648479/140737488355328), (-946562965/140737488355328)), (17/35184372088832), by norm_num⟩
  | 8 => ⟨((-244559127/562949953421312), (328053725/562949953421312)), (49/1125899906842624), by norm_num⟩
  | 9 => ⟨((602721669/18014398509481984), (-202124013/4503599627370496)), (31/9007199254740992), by norm_num⟩
  | 10 => ⟨((-668439721/288230376151711744), (448325407/144115188075855872)), (71/288230376151711744), by norm_num⟩
  | 11 => ⟨((673930339/4611686018427387904), (-113001997/576460752303423488)), (37/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-311421943/36893488147419103232), (835488167/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 13 => ⟨((531350749/1180591620717411303424), (-712758483/1180591620717411303424)), (61/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-210459585/9444732965739290427392), (564624609/18889465931478580854784)), (99/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((622419063/604462909807314587353088), (-417459153/302231454903657293676544)), (75/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-862856037/19342813113834066795298816), (289360635/4835703278458516698824704)), (53/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2880597436035/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781042203050265/633825300114114700748351602688), (3417345910815/633825300114114700748351602688)), (23135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118268677034359/2475880078570760549798248448), (240268339959/2475880078570760549798248448)), (1627/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892232955836805/2475880078570760549798248448), (2042155429609/1237940039285380274899124224)), (27665/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773898348830203/154742504910672534362390528), (2042014232467/77371252455336267181195264)), (3459/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552090948074413/9671406556917033397649408), (3828476545307/9671406556917033397649408)), (12975/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630504053122969/302231454903657293676544), (1674808363957/302231454903657293676544)), (11357/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236424612666101/9444732965739290427392), (2721281992375/37778931862957161709568)), (36923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300241603321825/4722366482869645213696), (2040714979763/2361183241434822606848)), (27705/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203145143269547/73786976294838206464), (5611164589863/590295810358705651712)), (19057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828112271063031/73786976294838206464), (7012752574557/73786976294838206464)), (5959/9223372036854775808), by norm_num⟩
  | 7 => ⟨((57120913764805/288230376151711744), (7887691069907/9223372036854775808)), (6709/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199888934809693/144115188075855872), (3942809879711/576460752303423488)), (53723/1152921504606846976), by norm_num⟩
  | 5 => ⟨((4683822776285/562949953421312), (6897584537925/144115188075855872)), (47065/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498340118464481/36028797018963968), (10341704993331/36028797018963968)), (70713/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497611452011993/9007199254740992), (12918941390855/9007199254740992)), (44297/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122290921818193/2251799813685248), (12906628313875/2251799813685248)), (44449/1125899906842624), by norm_num⟩
  | 1 => ⟨((560217564672581/562949953421312), (19329060966113/1125899906842624)), (67053/562949953421312), by norm_num⟩
  | 0 => ⟨((278691442994567/281474976710656), (19267002482197/562949953421312)), (67815/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278691442994567/281474976710656), (19267002482197/562949953421312)), (258693696142101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1102422914587915/1125899906842624), (38152938401079/562949953421312)), (138931/281474976710656), by norm_num⟩
  | 2 => ⟨((268565990729545/281474976710656), (149429530268501/1125899906842624)), (72725/70368744177664), by norm_num⟩
  | 3 => ⟨((1005163843278119/1125899906842624), (285152806901653/1125899906842624)), (2529337/1125899906842624), by norm_num⟩
  | 4 => ⟨((825155258387997/1125899906842624), (509148796557939/1125899906842624)), (724675/140737488355328), by norm_num⟩
  | 5 => ⟨((374499279062381/1125899906842624), (746295126642067/1125899906842624)), (13740999/1125899906842624), by norm_num⟩
  | 6 => ⟨((-370109903641463/1125899906842624), (992937241389393/2251799813685248)), (54714757/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-347455105/33554432)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-34418957/2097152)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-665294849906905/2251799813685248), (565248913484009/2251799813685248)), (77990785/2251799813685248), by norm_num⟩
  | 1 => ⟨((697041605/2147483648), (-148055411/536870912)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-765778473/4294967296), (81327747/536870912)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((1121724855/17179869184), (-953041731/17179869184)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((-616170355/34359738368), (523511679/34359738368)), (79/34359738368), by norm_num⟩
  | 5 => ⟨((1083091719/274877906944), (-460109091/137438953472)), (71/137438953472), by norm_num⟩
  | 6 => ⟨((-24789539/34359738368), (84246917/137438953472)), (107/1099511627776), by norm_num⟩
  | 7 => ⟨((995989657/8796093022208), (-846214385/8796093022208)), (137/8796093022208), by norm_num⟩
  | 8 => ⟨((-1094206477/70368744177664), (464830761/35184372088832)), (153/70368744177664), by norm_num⟩
  | 9 => ⟨((1068541051/562949953421312), (-226963905/140737488355328)), (19/70368744177664), by norm_num⟩
  | 10 => ⟨((-117391233/562949953421312), (797905073/4503599627370496)), (17/562949953421312), by norm_num⟩
  | 11 => ⟨((46897255/2251799813685248), (-637518777/36028797018963968)), (111/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1099133881/576460752303423488), (466923975/288230376151711744)), (83/288230376151711744), by norm_num⟩
  | 13 => ⟨((743090455/4611686018427387904), (-39459109/288230376151711744)), (57/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-932992349/73786976294838206464), (396345253/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 15 => ⟨((17083281/18446744073709551616), (-928916833/1180591620717411303424)), (87/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-300286439/4722366482869645213696), (127564931/2361183241434822606848)), (97/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (3174879184239/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445125149884659/158456325028528675187087900672), (1882146657627/316912650057057350374175801344)), (23143/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945844748680003/19807040628566084398385987584), (1058613229073/9903520314283042199192993792)), (52083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472896372554551/618970019642690137449562112), (1124667240721/618970019642690137449562112)), (6919/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886625415221469/77371252455336267181195264), (4498176914797/154742504910672534362390528)), (6921/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387870960901407/2417851639229258349412352), (527064745835/1208925819614629174706176)), (51923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260476833951673/604462909807314587353088), (3688930228867/604462909807314587353088)), (45449/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59079171227291/2361183241434822606848), (5993530797443/75557863725914323419136)), (36943/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299593945480339/4722366482869645213696), (1123572415597/1180591620717411303424)), (27721/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624270468646867/590295810358705651712), (6178252926465/590295810358705651712)), (76275/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826998702883177/73786976294838206464), (3860361208867/36893488147419103232)), (47705/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913308086543613/4611686018427387904), (542683293063/576460752303423488)), (53713/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199732254218821/144115188075855872), (1084916368307/144115188075855872)), (26885/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197961444338543/144115188075855872), (948795034993/18014398509481984)), (94225/144115188075855872), by norm_num⟩
  | 4 => ⟨((748346750000647/18014398509481984), (11377425993903/36028797018963968)), (17699/4503599627370496), by norm_num⟩
  | 3 => ⟨((1495551723558491/9007199254740992), (14207569171421/9007199254740992)), (44359/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120229035603573/2251799813685248), (14186223142011/2251799813685248)), (178107/2251799813685248), by norm_num⟩
  | 1 => ⟨((279334248518601/281474976710656), (21225878934353/1125899906842624)), (134419/562949953421312), by norm_num⟩
  | 0 => ⟨((1108548807574655/1125899906842624), (42237394222859/1125899906842624)), (136101/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108548807574655/1125899906842624), (42237394222859/1125899906842624)), (519184113622569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((272470148955251/281474976710656), (41586479149923/562949953421312)), (1112875/1125899906842624), by norm_num⟩
  | 2 => ⟨((262217352754401/281474976710656), (40256062193947/281474976710656)), (2318967/1125899906842624), by norm_num⟩
  | 3 => ⟨((954079688741601/1125899906842624), (300014962158835/1125899906842624)), (4983931/1125899906842624), by norm_num⟩
  | 4 => ⟨((728536408933869/1125899906842624), (127115287946433/281474976710656)), (11102801/1125899906842624), by norm_num⟩
  | 5 => ⟨((483582163232271/2251799813685248), (1316040473413537/2251799813685248)), (12198365/562949953421312), by norm_num⟩
  | 6 => ⟨((-665294849906905/2251799813685248), (565248913484009/2251799813685248)), (77990785/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-34418957/2097152)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-347455105/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-194510630821695/2251799813685248), (-652803867376123/2251799813685248)), (58014017/2251799813685248), by norm_num⟩
  | 1 => ⟨((257157317/2147483648), (863054581/2147483648)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-178247869/2147483648), (-1196447699/4294967296)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((329472021/8589934592), (552876233/4294967296)), (103/8589934592), by norm_num⟩
  | 4 => ⟨((-456745205/34359738368), (-1532898409/34359738368)), (145/34359738368), by norm_num⟩
  | 5 => ⟨((253273321/68719476736), (106252421/8589934592)), (41/34359738368), by norm_num⟩
  | 6 => ⟨((-234074251/274877906944), (-1571169409/549755813888)), (77/274877906944), by norm_num⟩
  | 7 => ⟨((370852359/2199023255552), (1244630453/2199023255552)), (31/549755813888), by norm_num⟩
  | 8 => ⟨((-257055267/8796093022208), (-862712089/8796093022208)), (11/1099511627776), by norm_num⟩
  | 9 => ⟨((316759349/70368744177664), (531543513/35184372088832)), (55/35184372088832), by norm_num⟩
  | 10 => ⟨((-21956085/35184372088832), (-147375155/70368744177664)), (31/140737488355328), by norm_num⟩
  | 11 => ⟨((354182945/4503599627370496), (297171413/1125899906842624)), (127/4503599627370496), by norm_num⟩
  | 12 => ⟨((-163667273/18014398509481984), (-1098578811/36028797018963968)), (119/36028797018963968), by norm_num⟩
  | 13 => ⟨((279250483/288230376151711744), (468601111/144115188075855872)), (103/288230376151711744), by norm_num⟩
  | 14 => ⟨((-442426709/4611686018427387904), (-742421803/2305843009213693952)), (83/2305843009213693952), by norm_num⟩
  | 15 => ⟨((327111281/36893488147419103232), (1097829503/36893488147419103232)), (31/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-113368131/147573952589676412928), (-760957425/295147905179352825856)), (87/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-302919438977/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890060308216561/316912650057057350374175801344), (-1436037691559/316912650057057350374175801344)), (23121/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945631124578527/19807040628566084398385987584), (-807683253491/9903520314283042199192993792)), (52031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118195738903353/154742504910672534362390528), (-858058515805/618970019642690137449562112)), (55293/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886398740765853/77371252455336267181195264), (-428970227865/19342813113834066795298816)), (55305/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551059167720907/9671406556917033397649408), (-201048435749/604462909807314587353088)), (51861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260105581202325/604462909807314587353088), (-2814176384059/604462909807314587353088)), (45391/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944965414187803/37778931862957161709568), (-142877998425/2361183241434822606848)), (73783/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81196407039131/295147905179352825856), (-53566389311/73786976294838206464)), (27679/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811825325293589/295147905179352825856), (-589063111451/73786976294838206464)), (76151/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913112641496537/36893488147419103232), (-5888625207553/73786976294838206464)), (95239/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825747934858595/9223372036854775808), (-6621945472221/9223372036854775808)), (26803/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596992118265135/1152921504606846976), (-827312308655/144115188075855872)), (107299/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598603189867269/72057594037927936), (-723413596511/18014398509481984)), (2937/4503599627370496), by norm_num⟩
  | 4 => ⟨((1495566121879709/36028797018963968), (-8673209611529/36028797018963968)), (70585/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494151624521307/9007199254740992), (-5413973046013/4503599627370496)), (176803/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118842603430267/2251799813685248), (-2701900704049/562949953421312)), (88657/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115291447829783/1125899906842624), (-4040141459707/281474976710656)), (267251/1125899906842624), by norm_num⟩
  | 0 => ⟨((276148432691457/281474976710656), (-16058949186425/562949953421312)), (134909/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276148432691457/281474976710656), (-16058949186425/562949953421312)), (514636994481944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1082774537276593/1125899906842624), (-63020218711117/1125899906842624)), (1089637/1125899906842624), by norm_num⟩
  | 2 => ⟨((259443389129675/281474976710656), (-121212707700379/1125899906842624)), (2217783/1125899906842624), by norm_num⟩
  | 3 => ⟨((943495445416977/1125899906842624), (-223450312058809/1125899906842624)), (2282957/562949953421312), by norm_num⟩
  | 4 => ⟨((746295126642061/1125899906842624), (-46812409882799/140737488355328)), (18929477/2251799813685248), by norm_num⟩
  | 5 => ⟨((740219807282895/2251799813685248), (-496468620694707/1125899906842624)), (2355455/140737488355328), by norm_num⟩
  | 6 => ⟨((-194510630821695/2251799813685248), (-652803867376123/2251799813685248)), (58014017/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-347455105/16777216)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-403382885/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((260250730051987/2251799813685248), (996020931620191/4503599627370496)), (74323505/4503599627370496), by norm_num⟩
  | 1 => ⟨((-399453537/2147483648), (-764386105/2147483648)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((642895667/4294967296), (1230231977/4294967296)), (97/4294967296), by norm_num⟩
  | 3 => ⟨((-86225055/1073741824), (-659993995/4294967296)), (53/4294967296), by norm_num⟩
  | 4 => ⟨((277547745/8589934592), (531109679/8589934592)), (87/17179869184), by norm_num⟩
  | 5 => ⟨((-714713381/68719476736), (-1367660885/68719476736)), (57/34359738368), by norm_num⟩
  | 6 => ⟨((383428937/137438953472), (22928805/4294967296)), (63/137438953472), by norm_num⟩
  | 7 => ⟨((-705262935/1099511627776), (-674788353/549755813888)), (59/549755813888), by norm_num⟩
  | 8 => ⟨((567538453/4398046511104), (543014979/2199023255552)), (97/4398046511104), by norm_num⟩
  | 9 => ⟨((-405963513/17592186044416), (-388421731/8796093022208)), (71/17592186044416), by norm_num⟩
  | 10 => ⟨((522698455/140737488355328), (31257033/4398046511104)), (93/140737488355328), by norm_num⟩
  | 11 => ⟨((-305909349/562949953421312), (-73172733/70368744177664)), (111/1125899906842624), by norm_num⟩
  | 12 => ⟨((656456139/9007199254740992), (314045255/2251799813685248)), (121/9007199254740992), by norm_num⟩
  | 13 => ⟨((-162542369/18014398509481984), (-622075495/36028797018963968)), (61/36028797018963968), by norm_num⟩
  | 14 => ⟨((37371693/36028797018963968), (1144219299/576460752303423488)), (57/288230376151711744), by norm_num⟩
  | 15 => ⟨((-128314495/1152921504606846976), (-982159957/4611686018427387904)), (25/1152921504606846976), by norm_num⟩
  | 16 => ⟨((206514213/18446744073709551616), (49397671/2305843009213693952)), (41/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (709433346025/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222478304176417/79228162514264337593543950336), (1681057349357/633825300114114700748351602688)), (5773/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890931503149581/39614081257132168796771975168), (1890955306829/39614081257132168796771975168)), (51961/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472695166303811/618970019642690137449562112), (62776727405/77371252455336267181195264)), (55215/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110777913571703/9671406556917033397649408), (502133750501/38685626227668133590597632)), (27611/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48460329481897/302231454903657293676544), (470665332447/2417851639229258349412352)), (25889/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314954586472673/151115727451828646838272), (1646988493707/604462909807314587353088)), (45313/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889464653795433/75557863725914323419136), (2675718621331/75557863725914323419136)), (73647/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298793391410099/4722366482869645213696), (1003115566345/2361183241434822606848)), (3453/295147905179352825856), by norm_num⟩
  | 9 => ⟨((25362053699593/9223372036854775808), (689415396531/147573952589676412928)), (75985/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825627506753901/73786976294838206464), (3445718101727/73786976294838206464)), (47505/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825077141766127/9223372036854775808), (1937282567985/4611686018427387904)), (106927/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399080863697467/288230376151711744), (3872231574283/1152921504606846976)), (106977/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196623692465177/144115188075855872), (423197360139/18014398509481984)), (46831/72057594037927936), by norm_num⟩
  | 4 => ⟨((747348435575681/18014398509481984), (5073124603725/36028797018963968)), (140607/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493073412098343/9007199254740992), (6332237737631/9007199254740992)), (87979/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235553777729279/4503599627370496), (12637005361717/4503599627370496)), (176257/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227448041027811/2251799813685248), (9443475725101/1125899906842624)), (16571/70368744177664), by norm_num⟩
  | 0 => ⟨((1101582854183841/1125899906842624), (37500387960461/2251799813685248)), (1066559/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101582854183841/1125899906842624), (37500387960461/2251799813685248)), (4068599709517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2154957483315771/2251799813685248), (36690459028753/1125899906842624)), (530643/562949953421312), by norm_num⟩
  | 2 => ⟨((2059888702172187/2251799813685248), (8778131471743/140737488355328)), (4200915/2251799813685248), by norm_num⟩
  | 3 => ⟨((1875573134024757/2251799813685248), (128480151636449/1125899906842624)), (8209821/2251799813685248), by norm_num⟩
  | 4 => ⟨((383220786616939/562949953421312), (428055672089923/2251799813685248)), (7774989/1125899906842624), by norm_num⟩
  | 5 => ⟨((962118865606835/2251799813685248), (582786552791045/2251799813685248)), (27082831/2251799813685248), by norm_num⟩
  | 6 => ⟨((260250730051987/2251799813685248), (996020931620191/4503599627370496)), (74323505/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-403382885/16777216)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-898158417/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-122199621566235/9007199254740992), (-958348489262283/4503599627370496)), (155991635/9007199254740992), by norm_num⟩
  | 1 => ⟨((52202303/2147483648), (1637582761/4294967296)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((-93533971/4294967296), (-733538605/2147483648)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((111726919/8589934592), (1752432989/8589934592)), (149/8589934592), by norm_num⟩
  | 4 => ⟨((-100093883/17179869184), (-1569969201/17179869184)), (17/2147483648), by norm_num⟩
  | 5 => ⟨((71737665/34359738368), (1125202873/34359738368)), (99/34359738368), by norm_num⟩
  | 6 => ⟨((-42845547/68719476736), (-1344061935/137438953472)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((43867951/274877906944), (688067343/274877906944)), (125/549755813888), by norm_num⟩
  | 8 => ⟨((-78600817/2199023255552), (-616425589/1099511627776)), (57/1099511627776), by norm_num⟩
  | 9 => ⟨((125185563/17592186044416), (981765677/8796093022208)), (23/2199023255552), by norm_num⟩
  | 10 => ⟨((-89720967/70368744177664), (-1407270359/70368744177664)), (133/70368744177664), by norm_num⟩
  | 11 => ⟨((58457597/281474976710656), (1833810903/562949953421312)), (175/562949953421312), by norm_num⟩
  | 12 => ⟨((-69827969/2251799813685248), (-547624675/1125899906842624)), (53/1125899906842624), by norm_num⟩
  | 13 => ⟨((9624225/2251799813685248), (603822583/9007199254740992)), (59/9007199254740992), by norm_num⟩
  | 14 => ⟨((-78831069/144115188075855872), (-154557833/18014398509481984)), (61/72057594037927936), by norm_num⟩
  | 15 => ⟨((9416421/144115188075855872), (590784983/576460752303423488)), (59/576460752303423488), by norm_num⟩
  | 16 => ⟨((-33743923/4611686018427387904), (-264636147/2305843009213693952)), (107/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-532268440903/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779581885171621/633825300114114700748351602688), (-2521848815543/633825300114114700748351602688)), (46225/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890656312975623/39614081257132168796771975168), (-1418343699163/19807040628566084398385987584)), (52011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945244089991109/1237940039285380274899124224), (-3013504554225/2475880078570760549798248448)), (55271/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772154024363445/154742504910672534362390528), (-3012969339883/154742504910672534362390528)), (55281/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550456123486781/9671406556917033397649408), (-2824090175667/9671406556917033397649408)), (51837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259578114332185/604462909807314587353088), (-2470510418549/604462909807314587353088)), (5671/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944537031860297/37778931862957161709568), (-4013513723021/75557863725914323419136)), (73743/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298500261961501/4722366482869645213696), (-3009203001101/4722366482869645213696)), (27663/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405692020102813/147573952589676412928), (-517017441651/73786976294838206464)), (76103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912561428410149/36893488147419103232), (-5167903191323/73786976294838206464)), (23793/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824508786616019/9223372036854775808), (-726346154495/1152921504606846976)), (107129/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595754321073405/1152921504606846976), (-5806868538819/1152921504606846976)), (107205/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196124826502277/144115188075855872), (-5076623915937/144115188075855872)), (46945/72057594037927936), by norm_num⟩
  | 4 => ⟨((746973414547503/18014398509481984), (-237692791737/1125899906842624)), (70503/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492132819889481/9007199254740992), (-9492382768383/9007199254740992)), (44139/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116831758776215/2251799813685248), (-4734707252195/1125899906842624)), (88503/1125899906842624), by norm_num⟩
  | 1 => ⟨((556147528019309/562949953421312), (-7073394464403/562949953421312)), (66659/281474976710656), by norm_num⟩
  | 0 => ⟨((549340149332885/562949953421312), (-28064773739977/1125899906842624)), (537789/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549340149332885/562949953421312), (-28064773739977/1125899906842624)), (2051502232078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071419190835625/1125899906842624), (-54772566916883/1125899906842624)), (1076387/1125899906842624), by norm_num⟩
  | 2 => ⟨((2033820309329217/2251799813685248), (-208488797163671/2251799813685248)), (4306665/2251799813685248), by norm_num⟩
  | 3 => ⟨((454409562433393/562949953421312), (-94153296257081/562949953421312)), (2144257/562949953421312), by norm_num⟩
  | 4 => ⟨((702098671591621/1125899906842624), (-607999455636471/2251799813685248)), (16715657/2251799813685248), by norm_num⟩
  | 5 => ⟨((355739180457311/1125899906842624), (-758283409628993/2251799813685248)), (29874053/2251799813685248), by norm_num⟩
  | 6 => ⟨((-122199621566235/9007199254740992), (-958348489262283/4503599627370496)), (155991635/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-898158417/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-975429799/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-73539352059743/562949953421312), (37538142170021/281474976710656)), (75986819/4503599627370496), by norm_num⟩
  | 1 => ⟨((545886885/2147483648), (-557295623/2147483648)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-531123415/2147483648), (1084447209/4294967296)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((86126537/536870912), (-703412277/4294967296)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((-335189005/4294967296), (10693571/134217728)), (93/8589934592), by norm_num⟩
  | 5 => ⟨((1043596299/34359738368), (-1065406891/34359738368)), (147/34359738368), by norm_num⟩
  | 6 => ⟨((-676914877/68719476736), (691062027/68719476736)), (97/68719476736), by norm_num⟩
  | 7 => ⟨((188173647/68719476736), (-768425493/274877906944)), (55/137438953472), by norm_num⟩
  | 8 => ⟨((-732338019/1099511627776), (747643483/1099511627776)), (27/274877906944), by norm_num⟩
  | 9 => ⟨((633361771/4398046511104), (-646598685/4398046511104)), (95/4398046511104), by norm_num⟩
  | 10 => ⟨((-985972079/35184372088832), (1006578355/35184372088832)), (75/17592186044416), by norm_num⟩
  | 11 => ⟨((348838741/70368744177664), (-712258559/140737488355328)), (107/140737488355328), by norm_num⟩
  | 12 => ⟨((-452539231/562949953421312), (461997053/562949953421312)), (35/281474976710656), by norm_num⟩
  | 13 => ⟨((33869257/281474976710656), (-553233695/4503599627370496)), (85/4503599627370496), by norm_num⟩
  | 14 => ⟨((-602573997/36028797018963968), (76895933/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 15 => ⟨((312681295/144115188075855872), (-319216163/144115188075855872)), (101/288230376151711744), by norm_num⟩
  | 16 => ⟨((-608449705/2305843009213693952), (621165971/2305843009213693952)), (25/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (3055735708265/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889686583444417/316912650057057350374175801344), (3618669383289/633825300114114700748351602688)), (23139/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236302666451033/4951760157141521099596496896), (4070385597663/39614081257132168796771975168)), (52075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890238287595217/2475880078570760549798248448), (4324042390369/2475880078570760549798248448)), (55343/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885951939689357/77371252455336267181195264), (4323207313585/154742504910672534362390528)), (55357/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775110672171177/4835703278458516698824704), (4052119668487/9671406556917033397649408)), (25957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629686207271899/302231454903657293676544), (3544717612993/604462909807314587353088)), (355/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1888739299386427/75557863725914323419136), (5758503008059/75557863725914323419136)), (36935/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298248749696311/4722366482869645213696), (1079355556503/1180591620717411303424)), (13857/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811210769190595/295147905179352825856), (2967045750465/295147905179352825856)), (2383/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1824688611567155/73786976294838206464), (7414068924183/73786976294838206464)), (95383/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824018794680399/9223372036854775808), (8335953581191/9223372036854775808)), (107393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595262499728139/1152921504606846976), (8329862692725/1152921504606846976)), (53751/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195692429029777/144115188075855872), (7281779755615/144115188075855872)), (23547/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493294136012075/36028797018963968), (2727243704555/9007199254740992)), (70763/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491309808092113/9007199254740992), (53172909183/35184372088832)), (88669/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115998076919815/2251799813685248), (13576358493445/2251799813685248)), (177985/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111018026183403/1125899906842624), (10137428953537/562949953421312)), (67149/281474976710656), by norm_num⟩
  | 0 => ⟨((548010608382503/562949953421312), (40191514600301/1125899906842624)), (543689/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548010608382503/562949953421312), (40191514600301/1125899906842624)), (2074008945945357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065500709665537/1125899906842624), (78249855903057/1125899906842624)), (1097339/1125899906842624), by norm_num⟩
  | 2 => ⟨((250725822847667/281474976710656), (18513030441077/140737488355328)), (2229475/1125899906842624), by norm_num⟩
  | 3 => ⟨((109232639037399/140737488355328), (263849801214231/1125899906842624)), (2279193/562949953421312), by norm_num⟩
  | 4 => ⟨((1232821002595571/2251799813685248), (819142374442765/2251799813685248)), (4606205/562949953421312), by norm_num⟩
  | 5 => ⟨((188483316694969/1125899906842624), (896932238107203/2251799813685248)), (8394853/562949953421312), by norm_num⟩
  | 6 => ⟨((-73539352059743/562949953421312), (37538142170021/281474976710656)), (75986819/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-975429799/33554432)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1042365315/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1407183512650973/9007199254740992), (257644131552647/4503599627370496)), (125698259/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1395299841/4294967296), (-510936651/4294967296)), (1/33554432), by norm_num⟩
  | 2 => ⟨((725361113/2147483648), (531231449/4294967296)), (17/536870912), by norm_num⟩
  | 3 => ⟨((-1005564021/4294967296), (-368221581/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((1045505799/8589934592), (191423813/4294967296)), (51/4294967296), by norm_num⟩
  | 5 => ⟨((-217406819/4294967296), (-318443703/17179869184)), (87/17179869184), by norm_num⟩
  | 6 => ⟨((1205559389/68719476736), (220728355/34359738368)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-179063591/34359738368), (-524561955/274877906944)), (149/274877906944), by norm_num⟩
  | 8 => ⟨((1489409079/1099511627776), (68174745/137438953472)), (157/1099511627776), by norm_num⟩
  | 9 => ⟨((-43015821/137438953472), (-63006843/549755813888)), (37/1099511627776), by norm_num⟩
  | 10 => ⟨((572472865/8796093022208), (209630475/8796093022208)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((-865762805/70368744177664), (-317028595/70368744177664)), (97/70368744177664), by norm_num⟩
  | 12 => ⟨((1200202095/562949953421312), (219747477/281474976710656)), (137/562949953421312), by norm_num⟩
  | 13 => ⟨((-383961553/1125899906842624), (-562402501/4503599627370496)), (89/2251799813685248), by norm_num⟩
  | 14 => ⟨((228121601/4503599627370496), (334138035/18014398509481984)), (27/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1011979805/144115188075855872), (-370570939/144115188075855872)), (61/72057594037927936), by norm_num⟩
  | 16 => ⟨((1052176423/1152921504606846976), (192645151/576460752303423488)), (129/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (457241924219/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779202366939509/633825300114114700748351602688), (270686541163/316912650057057350374175801344)), (46127/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890229606287529/39614081257132168796771975168), (304474382751/19807040628566084398385987584)), (103789/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118127195051797/154742504910672534362390528), (161722424203/618970019642690137449562112)), (13785/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110731332583027/9671406556917033397649408), (161689143949/38685626227668133590597632)), (27571/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387508023152313/2417851639229258349412352), (303096443517/4835703278458516698824704)), (25849/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259207465354333/604462909807314587353088), (530277416475/604462909807314587353088)), (90477/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888472467578849/75557863725914323419136), (861435843921/75557863725914323419136)), (147033/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649024842184499/2361183241434822606848), (161461284083/1180591620717411303424)), (110283/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622149542223927/590295810358705651712), (887660645721/590295810358705651712)), (151651/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824351191852113/73786976294838206464), (138626435253/9223372036854775808)), (189583/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823642734695215/9223372036854775808), (1246862457397/9223372036854775808)), (213307/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797445427550299/576460752303423488), (622946931395/576460752303423488)), (53335/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195372198828941/144115188075855872), (1089068464265/144115188075855872)), (186709/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492823687354883/36028797018963968), (203928483837/4503599627370496)), (140069/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490739019085383/9007199254740992), (1017742262139/4503599627370496)), (350303/9007199254740992), by norm_num⟩
  | 2 => ⟨((278863275287439/562949953421312), (2029795297855/2251799813685248)), (700997/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110264765547307/1125899906842624), (378813645073/140737488355328)), (1052483/2251799813685248), by norm_num⟩
  | 0 => ⟨((2189539064287637/2251799813685248), (12009036487083/2251799813685248)), (1054471/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189539064287637/2251799813685248), (12009036487083/2251799813685248)), (4022487644675826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66529241797345/70368744177664), (11676994710241/1125899906842624)), (2061879/1125899906842624), by norm_num⟩
  | 2 => ⟨((1006266617952635/1125899906842624), (44159469583971/2251799813685248)), (985381/281474976710656), by norm_num⟩
  | 3 => ⟨((449456024272865/562949953421312), (78934547980305/2251799813685248)), (14400045/2251799813685248), by norm_num⟩
  | 4 => ⟨((1432605510317705/2251799813685248), (126041783634191/2251799813685248)), (12001693/1125899906842624), by norm_num⟩
  | 5 => ⟨((1808750497796797/4503599627370496), (20047092182353/281474976710656)), (66458507/4503599627370496), by norm_num⟩
  | 6 => ⟨((1407183512650973/9007199254740992), (257644131552647/4503599627370496)), (125698259/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1042365315/33554432)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile002Terms0
