/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile004Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2599/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2599/160))
  have he : value ((15/16), (2599/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-69118709/33554432), (-1197596827/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-243033023658481/4503599627370496), (1040153899045261/9007199254740992)), (203230455/9007199254740992), by norm_num⟩
  | 1 => ⟨((31828769/268435456), (-1089788299/4294967296)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-139869907/1073741824), (598627409/2147483648)), (15/268435456), by norm_num⟩
  | 3 => ⟨((409767463/4294967296), (-876879237/4294967296)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((-225087785/4294967296), (481675153/4294967296)), (99/4294967296), by norm_num⟩
  | 5 => ⟨((395654731/17179869184), (-211669697/4294967296)), (11/1073741824), by norm_num⟩
  | 6 => ⟨((-579561533/68719476736), (620114481/34359738368)), (65/17179869184), by norm_num⟩
  | 7 => ⟨((363836241/137438953472), (-97323627/17179869184)), (165/137438953472), by norm_num⟩
  | 8 => ⟨((-199857483/274877906944), (855367461/549755813888)), (183/549755813888), by norm_num⟩
  | 9 => ⟨((195169677/1099511627776), (-417652091/1099511627776)), (181/2199023255552), by norm_num⟩
  | 10 => ⟨((-343065289/8796093022208), (734140351/8796093022208)), (161/8796093022208), by norm_num⟩
  | 11 => ⟨((548211989/70368744177664), (-293285677/17592186044416)), (65/17592186044416), by norm_num⟩
  | 12 => ⟨((-50189369/35184372088832), (429609665/140737488355328)), (3/4398046511104), by norm_num⟩
  | 13 => ⟨((542903705/2251799813685248), (-72611455/140737488355328)), (131/1125899906842624), by norm_num⟩
  | 14 => ⟨((-340823247/9007199254740992), (1458685015/18014398509481984)), (83/4503599627370496), by norm_num⟩
  | 15 => ⟨((399394781/72057594037927936), (-213670571/18014398509481984)), (197/72057594037927936), by norm_num⟩
  | 16 => ⟨((-438780015/576460752303423488), (234741115/144115188075855872)), (219/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (653893174917/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222348331348009/79228162514264337593543950336), (3095469508395/633825300114114700748351602688)), (92505/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889761722903531/39614081257132168796771975168), (435220900061/4951760157141521099596496896)), (104087/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889537725834127/2475880078570760549798248448), (3698599348939/2475880078570760549798248448)), (13827/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442800906028969/38685626227668133590597632), (3697723932981/154742504910672534362390528)), (110641/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774782590304435/4835703278458516698824704), (3465686259019/9671406556917033397649408)), (103753/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629399298381871/302231454903657293676544), (1515772887401/302231454903657293676544)), (22703/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887807455592965/75557863725914323419136), (2462259586999/37778931862957161709568)), (147619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297550400499381/4722366482869645213696), (1845932495039/2361183241434822606848)), (110759/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810731087529989/295147905179352825856), (5073838128529/590295810358705651712)), (76183/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823490707033243/73786976294838206464), (3169292444573/36893488147419103232)), (190565/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822672938047189/9223372036854775808), (3562902751555/4611686018427387904)), (214535/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593918874043227/1152921504606846976), (3559715613423/576460752303423488)), (107361/576460752303423488), by norm_num⟩
  | 5 => ⟨((149314908036663/18014398509481984), (3111168274709/72057594037927936)), (188093/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491539399181361/36028797018963968), (2329796622861/9007199254740992)), (282559/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489125143318183/9007199254740992), (726497235197/562949953421312)), (353937/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227653046168961/4503599627370496), (23172948377941/4503599627370496)), (355045/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107793390548369/1125899906842624), (34572430776253/2251799813685248)), (1070691/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089702231604809/1125899906842624), (68399390153319/2251799813685248)), (1081839/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1089702231604809/1125899906842624), (68399390153319/2251799813685248)), (4126888279441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2107258961851891/2251799813685248), (132400700342003/2251799813685248)), (4319677/2251799813685248), by norm_num⟩
  | 2 => ⟨((982105593928319/1125899906842624), (61951013730333/562949953421312)), (4296389/1125899906842624), by norm_num⟩
  | 3 => ⟨((1686081825653987/2251799813685248), (432311517315683/2251799813685248)), (4220481/562949953421312), by norm_num⟩
  | 4 => ⟨((1179491471069169/2251799813685248), (323702217193965/1125899906842624)), (31763531/2251799813685248), by norm_num⟩
  | 5 => ⟨((863369490264671/4503599627370496), (1356440308862479/4503599627370496)), (103079617/4503599627370496), by norm_num⟩
  | 6 => ⟨((-243033023658481/4503599627370496), (1040153899045261/9007199254740992)), (203230455/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1197596827/33554432)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-9054133/4194304), (-313755889/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((497375126157801/4503599627370496), (4748382003303/140737488355328)), (83963133/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1092194129/4294967296), (-333665577/4294967296)), (47/2147483648), by norm_num⟩
  | 2 => ⟨((78589685/268435456), (96036673/1073741824)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((-482558499/2147483648), (-147421741/2147483648)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((555566003/4294967296), (339451103/8589934592)), (101/8589934592), by norm_num⟩
  | 5 => ⟨((-1023390397/17179869184), (-78161505/4294967296)), (95/17179869184), by norm_num⟩
  | 6 => ⟨((1570962315/68719476736), (479929377/68719476736)), (37/17179869184), by norm_num⟩
  | 7 => ⟨((-516753487/68719476736), (-315736637/137438953472)), (99/137438953472), by norm_num⟩
  | 8 => ⟨((297467219/137438953472), (363505237/549755813888)), (29/137438953472), by norm_num⟩
  | 9 => ⟨((-1217677483/2199023255552), (-372000773/2199023255552)), (121/2199023255552), by norm_num⟩
  | 10 => ⟨((140190301/1099511627776), (171312687/4398046511104)), (57/4398046511104), by norm_num⟩
  | 11 => ⟨((-939054829/35184372088832), (-286881483/35184372088832)), (49/17592186044416), by norm_num⟩
  | 12 => ⟨((720751217/140737488355328), (440379351/281474976710656)), (153/281474976710656), by norm_num⟩
  | 13 => ⟨((-510643387/562949953421312), (-312003363/1125899906842624)), (111/1125899906842624), by norm_num⟩
  | 14 => ⟨((671885629/4503599627370496), (410522453/9007199254740992)), (37/2251799813685248), by norm_num⟩
  | 15 => ⟨((-825106045/36028797018963968), (-126035051/18014398509481984)), (93/36028797018963968), by norm_num⟩
  | 16 => ⟨((118742305/36028797018963968), (145103215/144115188075855872)), (109/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (386218131839/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444659851719693/158456325028528675187087900672), (228502837209/316912650057057350374175801344)), (92245/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944798194159713/19807040628566084398385987584), (32127170505/2475880078570760549798248448)), (103779/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944681232828133/1237940039285380274899124224), (273020834669/1237940039285380274899124224)), (110269/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771028822383993/154742504910672534362390528), (545906464759/154742504910672534362390528)), (110273/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549401790790967/9671406556917033397649408), (511643702953/9671406556917033397649408)), (12923/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258656117149003/604462909807314587353088), (447544685335/604462909807314587353088)), (45233/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887576837660897/75557863725914323419136), (363495530555/37778931862957161709568)), (147013/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297378233861911/4722366482869645213696), (68125998423/590295810358705651712)), (110267/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101326671215033/36893488147419103232), (374501908661/295147905179352825856)), (151627/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227899793809467/9223372036854775808), (233920473123/18446744073709551616)), (189551/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822346697900205/9223372036854775808), (131481877391/1152921504606846976)), (213267/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796797977270521/576460752303423488), (1050872029337/1152921504606846976)), (213295/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597120218895243/72057594037927936), (229602098783/36028797018963968)), (186665/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491128596418785/36028797018963968), (343851602585/9007199254740992)), (280061/36028797018963968), by norm_num⟩
  | 3 => ⟨((744312305815637/4503599627370496), (1715404110677/9007199254740992)), (87547/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226690726601633/4503599627370496), (3419274131025/4503599627370496)), (700711/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214239562763337/2251799813685248), (5100172398637/2251799813685248)), (1051917/2251799813685248), by norm_num⟩
  | 0 => ⟨((272136436674367/281474976710656), (5042983170611/1125899906842624)), (526819/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272136436674367/281474976710656), (5042983170611/1125899906842624)), (2009655000926780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((131551037948917/140737488355328), (19502685265975/2251799813685248)), (4093603/2251799813685248), by norm_num⟩
  | 2 => ⟨((983629310255949/1125899906842624), (36459347392253/2251799813685248)), (7723707/2251799813685248), by norm_num⟩
  | 3 => ⟨((1718082208042529/2251799813685248), (63704566471443/2251799813685248)), (6872783/1125899906842624), by norm_num⟩
  | 4 => ⟨((1309063169775627/2251799813685248), (48605422897929/1125899906842624)), (5438243/562949953421312), by norm_num⟩
  | 5 => ⟨((756815247770011/2251799813685248), (226050534618053/4503599627370496)), (54339893/4503599627370496), by norm_num⟩
  | 6 => ⟨((497375126157801/4503599627370496), (4748382003303/140737488355328)), (83963133/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-313755889/8388608)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-75431263/33554432), (-653486175/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((74602140218599/2251799813685248), (-903208151748621/9007199254740992)), (68516991/4503599627370496), by norm_num⟩
  | 1 => ⟨((-170601005/2147483648), (1032733229/4294967296)), (159/4294967296), by norm_num⟩
  | 2 => ⟨((409083343/4294967296), (-154774133/536870912)), (193/4294967296), by norm_num⟩
  | 3 => ⟨((-326979671/4294967296), (989685765/4294967296)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((24501969/536870912), (-1186581409/8589934592)), (189/8589934592), by norm_num⟩
  | 5 => ⟨((-94005049/4294967296), (1138119181/17179869184)), (183/17179869184), by norm_num⟩
  | 6 => ⟨((150276175/17179869184), (-227424217/8589934592)), (37/8589934592), by norm_num⟩
  | 7 => ⟨((-411824605/137438953472), (1246490183/137438953472)), (205/137438953472), by norm_num⟩
  | 8 => ⟨((493756137/549755813888), (-1494476459/549755813888)), (31/68719476736), by norm_num⟩
  | 9 => ⟨((-65776417/274877906944), (796355119/1099511627776)), (267/2199023255552), by norm_num⟩
  | 10 => ⟨((252359935/4398046511104), (-381915235/2199023255552)), (129/4398046511104), by norm_num⟩
  | 11 => ⟨((-220048253/17592186044416), (666031081/17592186044416)), (57/8796093022208), by norm_num⟩
  | 12 => ⟨((87942111/35184372088832), (-1064715187/140737488355328)), (23/17592186044416), by norm_num⟩
  | 13 => ⟨((-129769829/281474976710656), (1571123393/1125899906842624)), (137/562949953421312), by norm_num⟩
  | 14 => ⟨((177813977/2251799813685248), (-1076396959/4503599627370496)), (95/2251799813685248), by norm_num⟩
  | 15 => ⟨((-454804581/36028797018963968), (1376579829/36028797018963968)), (245/36028797018963968), by norm_num⟩
  | 16 => ⟨((272643439/144115188075855872), (-412611783/72057594037927936)), (149/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (-203809791267/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778499810296085/633825300114114700748351602688), (-482258528179/158456325028528675187087900672)), (46195/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889439266695865/39614081257132168796771975168), (-2169737083401/39614081257132168796771975168)), (103951/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118074713924293/154742504910672534362390528), (-2304816920837/2475880078570760549798248448)), (55231/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885430832929851/77371252455336267181195264), (-288027788641/19342813113834066795298816)), (55239/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549244960888171/9671406556917033397649408), (-2159576834795/9671406556917033397649408)), (51795/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258518770434223/604462909807314587353088), (-1888998369731/604462909807314587353088)), (90659/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943676711727545/37778931862957161709568), (-3068439015313/75557863725914323419136)), (147351/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297210475874017/4722366482869645213696), (-575073577145/1180591620717411303424)), (55271/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810497875991579/295147905179352825856), (-1580611874269/295147905179352825856)), (152039/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822909136592451/73786976294838206464), (-1974504911747/36893488147419103232)), (190117/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911010337070693/4611686018427387904), (-4439173719957/9223372036854775808)), (213975/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99579319374381/72057594037927936), (-4434849521567/1152921504606846976)), (214091/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596976764001161/72057594037927936), (-968908428357/36028797018963968)), (187461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490696396574711/36028797018963968), (-725468010601/4503599627370496)), (281455/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488081164772493/9007199254740992), (-7237722410899/9007199254740992)), (44035/1125899906842624), by norm_num⟩
  | 2 => ⟨((2225594299472535/4503599627370496), (-901542886309/281474976710656)), (705945/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106285644953851/1125899906842624), (-21510532449919/2251799813685248)), (1062393/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173661621202637/2251799813685248), (-42517470106305/2251799813685248)), (2138747/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2173661621202637/2251799813685248), (-42517470106305/2251799813685248)), (8158672341353606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2097432053915787/2251799813685248), (-20521049970569/562949953421312)), (2104915/1125899906842624), by norm_num⟩
  | 2 => ⟨((1950654484571805/2251799813685248), (-9557134636635/140737488355328)), (8149387/2251799813685248), by norm_num⟩
  | 3 => ⟨((1679398921985265/2251799813685248), (-264928239894979/2251799813685248)), (15225861/2251799813685248), by norm_num⟩
  | 4 => ⟨((76333211054031/140737488355328), (-197584260278863/1125899906842624)), (6573421/562949953421312), by norm_num⟩
  | 5 => ⟨((593077663634897/2251799813685248), (-214331536210765/1125899906842624)), (75501807/4503599627370496), by norm_num⟩
  | 6 => ⟨((74602140218599/2251799813685248), (-903208151748621/9007199254740992)), (68516991/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-653486175/16777216)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-19542101/8388608), (-338599471/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-97381395842047/1125899906842624), (-201062578413885/4503599627370496)), (19715095/1125899906842624), by norm_num⟩
  | 1 => ⟨((923094475/4294967296), (476476419/4294967296)), (189/4294967296), by norm_num⟩
  | 2 => ⟨((-1146901799/4294967296), (-591999711/4294967296)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((474990651/2147483648), (490354673/4294967296)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-1180307427/8589934592), (-304621397/4294967296)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((1173181509/17179869184), (151391147/4294967296)), (249/17179869184), by norm_num⟩
  | 6 => ⟨((-242937211/8589934592), (-250795245/17179869184)), (13/2147483648), by norm_num⟩
  | 7 => ⟨((689915761/68719476736), (712231739/137438953472)), (149/68719476736), by norm_num⟩
  | 8 => ⟨((-857188131/274877906944), (-221228673/137438953472)), (187/274877906944), by norm_num⟩
  | 9 => ⟨((946681105/1099511627776), (7635175/17179869184)), (209/1099511627776), by norm_num⟩
  | 10 => ⟨((-940965669/4398046511104), (-242850523/2199023255552)), (105/2199023255552), by norm_num⟩
  | 11 => ⟨((425129427/8796093022208), (3428755/137438953472)), (3/274877906944), by norm_num⟩
  | 12 => ⟨((-1408542587/140737488355328), (-363525807/70368744177664)), (321/140737488355328), by norm_num⟩
  | 13 => ⟨((538476437/281474976710656), (277946983/281474976710656)), (247/562949953421312), by norm_num⟩
  | 14 => ⟨((-95575977/281474976710656), (-394669889/2251799813685248)), (177/2251799813685248), by norm_num⟩
  | 15 => ⟨((506661079/9007199254740992), (261524755/9007199254740992)), (59/4503599627370496), by norm_num⟩
  | 16 => ⟨((-314751371/36028797018963968), (-649864603/144115188075855872)), (37/18014398509481984), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (-3471577983481/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444591765392155/158456325028528675187087900672), (-2053351587859/316912650057057350374175801344)), (92605/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889289560875299/39614081257132168796771975168), (-4619084230137/39614081257132168796771975168)), (52103/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944517939327453/1237940039285380274899124224), (-2453304253917/1237940039285380274899124224)), (110749/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885350790165491/77371252455336267181195264), (-4905294149791/154742504910672534362390528)), (110783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549094305904521/9671406556917033397649408), (-4597317043591/9671406556917033397649408)), (103895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258386373008591/604462909807314587353088), (-4021256509833/604462909807314587353088)), (90945/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943568600914569/37778931862957161709568), (-6531925186823/75557863725914323419136)), (147851/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324261842338001/1180591620717411303424), (-2448327502953/2361183241434822606848)), (27737/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202596244306847/73786976294838206464), (-6729182466499/590295810358705651712)), (76325/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455656150991925/18446744073709551616), (-8405903056879/73786976294838206464)), (47739/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113856089847719/576460752303423488), (-9448978892893/9223372036854775808)), (13439/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592941959907863/1152921504606846976), (-9439406760367/1152921504606846976)), (26909/144115188075855872), by norm_num⟩
  | 5 => ⟨((149207860033591/18014398509481984), (-8248719729955/144115188075855872)), (188643/144115188075855872), by norm_num⟩
  | 4 => ⟨((372562917577653/9007199254740992), (-3087893974029/9007199254740992)), (283523/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487509999523631/9007199254740992), (-15401880443471/9007199254740992)), (355385/9007199254740992), by norm_num⟩
  | 2 => ⟨((139025403069285/281474976710656), (-15345580481471/2251799813685248)), (356859/2251799813685248), by norm_num⟩
  | 1 => ⟨((552669148862107/562949953421312), (-5719478955401/281474976710656)), (269491/562949953421312), by norm_num⟩
  | 0 => ⟨((542356455066535/562949953421312), (-45195785084389/1125899906842624)), (1092797/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((542356455066535/562949953421312), (-45195785084389/1125899906842624)), (4168689732078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521609172929853/562949953421312), (-1360701872417/17592186044416)), (2193377/1125899906842624), by norm_num⟩
  | 2 => ⟨((59992052096927/70368744177664), (-161379507125169/1125899906842624)), (4403911/1125899906842624), by norm_num⟩
  | 3 => ⟨((1590394502793197/2251799813685248), (-275164433072335/1125899906842624)), (8771465/1125899906842624), by norm_num⟩
  | 4 => ⟨((988761434329685/2251799813685248), (-194342320779505/562949953421312)), (33355151/2251799813685248), by norm_num⟩
  | 5 => ⟨((82899503191463/1125899906842624), (-341341518330479/1125899906842624)), (26161099/1125899906842624), by norm_num⟩
  | 6 => ⟨((-97381395842047/1125899906842624), (-201062578413885/4503599627370496)), (19715095/1125899906842624), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-338599471/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40343165/16777216), (-1398025147/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-276336650448975/4503599627370496), (298354329455449/4503599627370496)), (74311955/4503599627370496), by norm_num⟩
  | 1 => ⟨((675954355/4294967296), (-182453095/1073741824)), (23/536870912), by norm_num⟩
  | 2 => ⟨((-108361793/536870912), (467982949/2147483648)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((370590015/2147483648), (-800235043/4294967296)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-950544621/8589934592), (256570295/2147483648)), (265/8589934592), by norm_num⟩
  | 5 => ⟨((487619763/8589934592), (-1052943701/17179869184)), (137/8589934592), by norm_num⟩
  | 6 => ⟨((-208453333/8589934592), (450124545/17179869184)), (59/8589934592), by norm_num⟩
  | 7 => ⟨((76381749/8589934592), (-329870475/34359738368)), (175/68719476736), by norm_num⟩
  | 8 => ⟨((-97957659/34359738368), (846101063/274877906944)), (113/137438953472), by norm_num⟩
  | 9 => ⟨((223339053/274877906944), (-120567021/137438953472)), (65/274877906944), by norm_num⟩
  | 10 => ⟨((-916565377/4398046511104), (494797285/2199023255552)), (269/4398046511104), by norm_num⟩
  | 11 => ⟨((427444323/8796093022208), (-923003621/17592186044416)), (253/17592186044416), by norm_num⟩
  | 12 => ⟨((-730915361/70368744177664), (789152515/70368744177664)), (109/35184372088832), by norm_num⟩
  | 13 => ⟨((576849503/281474976710656), (-311405575/140737488355328)), (87/140737488355328), by norm_num⟩
  | 14 => ⟨((-105684983/281474976710656), (912845177/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | 15 => ⟨((578296809/9007199254740992), (-624373773/9007199254740992)), (89/4503599627370496), by norm_num⟩
  | 16 => ⟨((-370825507/36028797018963968), (400371777/36028797018963968)), (115/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (3019324864761/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778253638450841/633825300114114700748351602688), (3571267828857/633825300114114700748351602688)), (11569/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889162110575023/39614081257132168796771975168), (502103063581/4951760157141521099596496896)), (6509/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944450328868181/1237940039285380274899124224), (4266827884129/2475880078570760549798248448)), (110679/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770566578667339/154742504910672534362390528), (4265648987721/154742504910672534362390528)), (27677/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548967974663941/9671406556917033397649408), (3997793668429/9671406556917033397649408)), (25955/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258276065835655/604462909807314587353088), (3496817561851/604462909807314587353088)), (45437/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943479194291481/37778931862957161709568), (5679981993185/75557863725914323419136)), (147729/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296913640506139/4722366482869645213696), (2128967016047/2361183241434822606848)), (433/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1620586695938087/590295810358705651712), (5851325474347/590295810358705651712)), (38125/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822396457701933/73786976294838206464), (7309158619507/73786976294838206464)), (95375/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227680255713163/1152921504606846976), (513495935125/576460752303423488)), (107383/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592688156260963/1152921504606846976), (2051838865883/288230376151711744)), (107491/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193442585171621/144115188075855872), (7171792491805/144115188075855872)), (188353/144115188075855872), by norm_num⟩
  | 4 => ⟨((186240598094037/4503599627370496), (10738422649223/36028797018963968)), (35377/4503599627370496), by norm_num⟩
  | 3 => ⟨((371776899256755/2251799813685248), (13389359872707/9007199254740992)), (354623/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223620175786055/4503599627370496), (26677903245271/4503599627370496)), (5561/35184372088832), by norm_num⟩
  | 1 => ⟨((2209543229305707/2251799813685248), (39765474256175/2251799813685248)), (268535/562949953421312), by norm_num⟩
  | 0 => ⟨((1083670777890769/1125899906842624), (78529388113695/2251799813685248)), (2174093/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1083670777890769/1125899906842624), (78529388113695/2251799813685248)), (8293506630904387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083312435727803/2251799813685248), (151167972547579/2251799813685248)), (4336739/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917283642486985/2251799813685248), (17482133357179/140737488355328)), (537923/140737488355328), by norm_num⟩
  | 3 => ⟨((798857995120873/1125899906842624), (238161194385323/1125899906842624)), (4198653/562949953421312), by norm_num⟩
  | 4 => ⟨((1032868620600697/2251799813685248), (84491069368587/281474976710656)), (30937627/2251799813685248), by norm_num⟩
  | 5 => ⟨((270866962649021/2251799813685248), (1240155345837625/4503599627370496)), (93909113/4503599627370496), by norm_num⟩
  | 6 => ⟨((-276336650448975/4503599627370496), (298354329455449/4503599627370496)), (74311955/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1398025147/33554432)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83017565/33554432), (-719208841/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((334588057755871/9007199254740992), (680985967633659/9007199254740992)), (103287945/9007199254740992), by norm_num⟩
  | 1 => ⟨((-105261453/1073741824), (-214238287/1073741824)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((277791009/2147483648), (1130774243/4294967296)), (11/268435456), by norm_num⟩
  | 3 => ⟨((-488737599/4294967296), (-497363009/2147483648)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((644903271/8589934592), (656284747/4294967296)), (209/8589934592), by norm_num⟩
  | 5 => ⟨((-340387341/8589934592), (-1385578457/17179869184)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((598867805/34359738368), (1218873661/34359738368)), (199/34359738368), by norm_num⟩
  | 7 => ⟨((-225778067/34359738368), (-919050705/68719476736)), (19/8589934592), by norm_num⟩
  | 8 => ⟨((297920631/137438953472), (1212713749/274877906944)), (203/274877906944), by norm_num⟩
  | 9 => ⟨((-698870777/1099511627776), (-1422409381/1099511627776)), (241/1099511627776), by norm_num⟩
  | 10 => ⟨((368872009/2199023255552), (187690995/549755813888)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((-353990683/8796093022208), (-720476067/8796093022208)), (125/8796093022208), by norm_num⟩
  | 12 => ⟨((311400569/35184372088832), (1267585097/70368744177664)), (223/70368744177664), by norm_num⟩
  | 13 => ⟨((-252862755/140737488355328), (-1029301459/281474976710656)), (183/281474976710656), by norm_num⟩
  | 14 => ⟨((190662659/562949953421312), (48506885/70368744177664)), (35/281474976710656), by norm_num⟩
  | 15 => ⟨((-536714333/9007199254740992), (-546186455/4503599627370496)), (199/9007199254740992), by norm_num⟩
  | 16 => ⟨((177052487/18014398509481984), (180177171/9007199254740992)), (67/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (1451252227219/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889075927881617/316912650057057350374175801344), (1716349194241/633825300114114700748351602688)), (46185/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889047922225975/39614081257132168796771975168), (1930478239857/39614081257132168796771975168)), (103927/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888779750036737/2475880078570760549798248448), (1025307771833/1237940039285380274899124224)), (110435/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221305767516735/19342813113834066795298816), (64063547053/4835703278458516698824704)), (110449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548855561676651/9671406556917033397649408), (960644107225/4835703278458516698824704)), (103561/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258178202214409/604462909807314587353088), (1680509236029/604462909807314587353088)), (90631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943400146313287/37778931862957161709568), (2729669370787/75557863725914323419136)), (147303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296795883574725/4722366482869645213696), (1023119589407/2361183241434822606848)), (55251/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202553262877403/73786976294838206464), (2811933967627/590295810358705651712)), (37995/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822197698098385/73786976294838206464), (439056476631/9223372036854775808)), (47509/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227652645164387/1152921504606846976), (3948120799861/9223372036854775808)), (106937/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796235332696123/576460752303423488), (985972648803/288230376151711744)), (106989/576460752303423488), by norm_num⟩
  | 5 => ⟨((596628044598119/72057594037927936), (3446151001587/144115188075855872)), (46837/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489652634953901/36028797018963968), (5159734224295/36028797018963968)), (35157/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486780648134479/9007199254740992), (6433088332399/9007199254740992)), (351981/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223005787851243/4503599627370496), (3204141560065/1125899906842624)), (44075/281474976710656), by norm_num⟩
  | 1 => ⟨((2208719706086203/2251799813685248), (9550634979759/1125899906842624)), (530453/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166082466888717/2251799813685248), (18855446918481/1125899906842624)), (1067151/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2166082466888717/2251799813685248), (18855446918481/1125899906842624)), (4070858006003951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082996504992319/2251799813685248), (2267211583777/70368744177664)), (2088801/1125899906842624), by norm_num⟩
  | 2 => ⟨((1924509807286791/2251799813685248), (134224188885969/2251799813685248)), (499879/140737488355328), by norm_num⟩
  | 3 => ⟨((818394655479825/1125899906842624), (57357622626189/562949953421312)), (7312323/1125899906842624), by norm_num⟩
  | 4 => ⟨((1166374063332093/2251799813685248), (83384271591139/562949953421312)), (1515055/140737488355328), by norm_num⟩
  | 5 => ⟨((138687002730149/562949953421312), (86381792095963/562949953421312)), (64586855/4503599627370496), by norm_num⟩
  | 6 => ⟨((334588057755871/9007199254740992), (680985967633659/9007199254740992)), (103287945/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-719208841/16777216)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-85187893/33554432), (-1476022233/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((711204966289149/9007199254740992), (-4689247841207/9007199254740992)), (88820593/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1836756469/8589934592), (6055221/4294967296)), (117/8589934592), by norm_num⟩
  | 2 => ⟨((1243507181/4294967296), (-8198921/4294967296)), (81/4294967296), by norm_num⟩
  | 3 => ⟨((-561246645/2147483648), (3700515/2147483648)), (75/4294967296), by norm_num⟩
  | 4 => ⟨((759942045/4294967296), (-2505295/2147483648)), (13/1073741824), by norm_num⟩
  | 5 => ⟨((-823184483/8589934592), (10855143/17179869184)), (115/17179869184), by norm_num⟩
  | 6 => ⟨((92884371/2147483648), (-9798757/34359738368)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((-71867297/4294967296), (7581579/68719476736)), (21/17179869184), by norm_num⟩
  | 8 => ⟨((1556961985/274877906944), (-641603/17179869184)), (29/68719476736), by norm_num⟩
  | 9 => ⟨((-1873924985/1099511627776), (12355507/1099511627776)), (71/549755813888), by norm_num⟩
  | 10 => ⟨((2029873173/4398046511104), (-13383733/4398046511104)), (39/1099511627776), by norm_num⟩
  | 11 => ⟨((-1998908529/17592186044416), (13179571/17592186044416)), (39/4398046511104), by norm_num⟩
  | 12 => ⟨((451095387/17592186044416), (-2974245/17592186044416)), (143/70368744177664), by norm_num⟩
  | 13 => ⟨((-93968381/17592186044416), (4956557/140737488355328)), (61/140737488355328), by norm_num⟩
  | 14 => ⟨((1163296425/1125899906842624), (-1917515/281474976710656)), (3/35184372088832), by norm_num⟩
  | 15 => ⟨((-420035349/2251799813685248), (11077817/9007199254740992)), (141/9007199254740992), by norm_num⟩
  | 16 => ⟨((1137476811/36028797018963968), (-7499821/36028797018963968)), (97/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-4294247543/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778053795521305/633825300114114700748351602688), (-5078125553/316912650057057350374175801344)), (46101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888937715955023/39614081257132168796771975168), (-11423279197/39614081257132168796771975168)), (103727/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888662802108809/2475880078570760549798248448), (-1516761585/309485009821345068724781056)), (55105/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((13830698098157/1208925819614629174706176), (-12130560261/154742504910672534362390528)), (55105/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548746251591825/9671406556917033397649408), (-11368648505/9671406556917033397649408)), (103323/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629041365134197/302231454903657293676544), (-2485954335/151115727451828646838272)), (90407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886645477389661/75557863725914323419136), (-16151675217/75557863725914323419136)), (4591/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296680057704425/4722366482869645213696), (-12107610425/4722366482869645213696)), (13773/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810133652973563/295147905179352825856), (-8318991811/295147905179352825856)), (9469/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821999896078991/73786976294838206464), (-20782519855/73786976294838206464)), (47345/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910499793613533/4611686018427387904), (-5839945947/2305843009213693952)), (106527/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592250280526263/1152921504606846976), (-1458382669/72057594037927936)), (213055/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596532293607035/72057594037927936), (-10194263361/72057594037927936)), (186425/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489368043798921/36028797018963968), (-30525223849/36028797018963968)), (279641/36028797018963968), by norm_num⟩
  | 3 => ⟨((185803693751951/1125899906842624), (-19028001199/4503599627370496)), (349559/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222317444868149/4503599627370496), (-37905637331/2251799813685248)), (699143/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207721583414715/2251799813685248), (-112968060595/2251799813685248)), (1048787/2251799813685248), by norm_num⟩
  | 0 => ⟨((541055587055675/562949953421312), (-55739622987/562949953421312)), (2097919/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((541055587055675/562949953421312), (-55739622987/562949953421312)), (8002925881392668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1040025470818959/1125899906842624), (-214287144029/1125899906842624)), (4033069/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921401587227253/2251799813685248), (-791772293451/2251799813685248)), (7452455/2251799813685248), by norm_num⟩
  | 3 => ⟨((1639481187474719/2251799813685248), (-675598484427/1125899906842624)), (6361605/1125899906842624), by norm_num⟩
  | 4 => ⟨((596832969346265/1125899906842624), (-61485872255/70368744177664)), (18542195/2251799813685248), by norm_num⟩
  | 5 => ⟨((632753628138053/2251799813685248), (-4171942658877/4503599627370496)), (39381245/4503599627370496), by norm_num⟩
  | 6 => ⟨((711204966289149/9007199254740992), (-4689247841207/9007199254740992)), (88820593/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-1476022233/33554432)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile004Terms1
