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
namespace Reinmann.XiBand97.Tile021Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28251/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28251/1280))
  have he : value ((69/80), (28251/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1627227201/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-134172097538221/4503599627370496), (1326942006831797/9007199254740992)), (57195255/2251799813685248), by norm_num⟩
  | 1 => ⟨((140574565/2147483648), (-1390261455/4294967296)), (121/2147483648), by norm_num⟩
  | 2 => ⟨((-308873889/4294967296), (1527358319/4294967296)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((226221767/4294967296), (-559324873/2147483648)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-248530013/8589934592), (614481179/4294967296)), (55/2147483648), by norm_num⟩
  | 5 => ⟨((218430501/17179869184), (-1080122519/17179869184)), (195/17179869184), by norm_num⟩
  | 6 => ⟨((-319960577/68719476736), (395545291/17179869184)), (9/2147483648), by norm_num⟩
  | 7 => ⟨((200864355/137438953472), (-124157405/17179869184)), (183/137438953472), by norm_num⟩
  | 8 => ⟨((-220672049/549755813888), (1091206807/549755813888)), (203/549755813888), by norm_num⟩
  | 9 => ⟨((107748011/1099511627776), (-266402935/549755813888)), (25/274877906944), by norm_num⟩
  | 10 => ⟨((-94698631/4398046511104), (468277661/4398046511104)), (89/4398046511104), by norm_num⟩
  | 11 => ⟨((302653323/70368744177664), (-1496598089/70368744177664)), (287/70368744177664), by norm_num⟩
  | 12 => ⟨((-221665773/281474976710656), (1096120701/281474976710656)), (213/281474976710656), by norm_num⟩
  | 13 => ⟨((37465345/281474976710656), (-741053337/1125899906842624)), (291/2251799813685248), by norm_num⟩
  | 14 => ⟨((-94079745/4503599627370496), (116304329/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 15 => ⟨((220495283/72057594037927936), (-1090332715/72057594037927936)), (109/36028797018963968), by norm_num⟩
  | 16 => ⟨((-60559707/144115188075855872), (149731615/72057594037927936)), (121/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1153028075247/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222380234028641/79228162514264337593543950336), (2729906090235/633825300114114700748351602688)), (92469/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890048860174737/39614081257132168796771975168), (1535313839887/19807040628566084398385987584)), (26011/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889842831638301/2475880078570760549798248448), (815477625481/618970019642690137449562112)), (110567/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771508755103279/154742504910672534362390528), (3261200306279/154742504910672534362390528)), (55295/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774925633803979/4835703278458516698824704), (1528310430019/4835703278458516698824704)), (51851/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629524474760097/302231454903657293676544), (2673789000591/604462909807314587353088)), (90763/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888214328617205/75557863725914323419136), (4343493275753/75557863725914323419136)), (147535/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648927799348919/2361183241434822606848), (3256383210035/4722366482869645213696)), (110691/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621881892894127/590295810358705651712), (4475517898001/590295810358705651712)), (152263/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456003864833297/18446744073709551616), (5591385069689/73786976294838206464)), (23803/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455815857005889/2305843009213693952), (3143084135363/4611686018427387904)), (214359/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594509542450731/1152921504606846976), (6280996329993/1152921504606846976)), (214523/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149379537293851/18014398509481984), (5490057445503/144115188075855872)), (187893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492315344841787/36028797018963968), (8223467704887/36028797018963968)), (141105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490095757306843/9007199254740992), (10259025316437/9007199254740992)), (353413/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114798142811075/2251799813685248), (10228607322327/2251799813685248)), (354389/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218506549507483/2251799813685248), (1908378356869/140737488355328)), (1068061/2251799813685248), by norm_num⟩
  | 0 => ⟨((273157865488005/281474976710656), (60462963608737/2251799813685248)), (1077877/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((273157865488005/281474976710656), (60462963608737/2251799813685248)), (4111774448875045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264883574886481/281474976710656), (7334548115719/140737488355328)), (4299879/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988045308405469/2251799813685248), (220870938968409/2251799813685248)), (2135257/562949953421312), by norm_num⟩
  | 3 => ⟨((216690009080101/281474976710656), (390000417719755/2251799813685248)), (2094593/281474976710656), by norm_num⟩
  | 4 => ⟨((633491374119501/1125899906842624), (600473939420971/2251799813685248)), (31604311/2251799813685248), by norm_num⟩
  | 5 => ⟨((552747328979703/2251799813685248), (84464671036675/281474976710656)), (52420009/2251799813685248), by norm_num⟩
  | 6 => ⟨((-134172097538221/4503599627370496), (1326942006831797/9007199254740992)), (57195255/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1627227201/33554432)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1705255409/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((262647859531727/2251799813685248), (-81437793938063/1125899906842624)), (60530869/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1153505413/4294967296), (715322305/4294967296)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((166002773/536870912), (-411772619/2147483648)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-1019294695/4294967296), (316047165/2147483648)), (31/1073741824), by norm_num⟩
  | 4 => ⟨((1173506385/8589934592), (-727725491/8589934592)), (145/8589934592), by norm_num⟩
  | 5 => ⟨((-270209831/4294967296), (670259947/17179869184)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((829574839/34359738368), (-514443521/34359738368)), (107/34359738368), by norm_num⟩
  | 7 => ⟨((-1091523805/137438953472), (84610713/17179869184)), (9/8589934592), by norm_num⟩
  | 8 => ⟨((1256663221/549755813888), (-389646733/274877906944)), (21/68719476736), by norm_num⟩
  | 9 => ⟨((-1286032889/2199023255552), (199376613/549755813888)), (175/2199023255552), by norm_num⟩
  | 10 => ⟨((18507501/137438953472), (-734530587/8796093022208)), (41/2199023255552), by norm_num⟩
  | 11 => ⟨((-991769505/35184372088832), (153756289/8796093022208)), (35/8796093022208), by norm_num⟩
  | 12 => ⟨((380605613/70368744177664), (-118012313/35184372088832)), (109/140737488355328), by norm_num⟩
  | 13 => ⟨((-1078617613/1125899906842624), (334441099/562949953421312)), (157/1125899906842624), by norm_num⟩
  | 14 => ⟨((709602525/4503599627370496), (-220022597/2251799813685248)), (105/4503599627370496), by norm_num⟩
  | 15 => ⟨((-871424105/36028797018963968), (540395469/36028797018963968)), (131/36028797018963968), by norm_num⟩
  | 16 => ⟨((1003264077/288230376151711744), (-155538319/72057594037927936)), (153/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-723065391921/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889452674002041/316912650057057350374175801344), (-427917739391/316912650057057350374175801344)), (92285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889895502009809/39614081257132168796771975168), (-481323784121/19807040628566084398385987584)), (51913/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472420046528569/618970019642690137449562112), (-511302927871/1237940039285380274899124224)), (110321/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771346444070563/154742504910672534362390528), (-63898303275/9671406556917033397649408)), (110329/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699456217385/9671406556917033397649408), (-958227056307/9671406556917033397649408)), (6465/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((78682279346081/37778931862957161709568), (-209550315963/151115727451828646838272)), (45259/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235999964221889/9444732965739290427392), (-1361613334263/75557863725914323419136)), (147105/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297695219090759/4722366482869645213696), (-1020804421097/4722366482869645213696)), (110341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810831157520777/295147905179352825856), (-701473670023/295147905179352825856)), (151739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823742401656529/73786976294838206464), (-876348320049/36893488147419103232)), (23713/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911479090397643/4611686018427387904), (-492606697713/2305843009213693952)), (106729/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594206719842311/1152921504606846976), (-246091503149/144115188075855872)), (106755/576460752303423488), by norm_num⟩
  | 5 => ⟨((597387025590175/72057594037927936), (-1720735828353/144115188075855872)), (365/281474976710656), by norm_num⟩
  | 4 => ⟨((1491927406613347/36028797018963968), (-2577299144223/36028797018963968)), (70109/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489620312923375/9007199254740992), (-3214976644613/9007199254740992)), (350751/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228673718212199/4503599627370496), (-50078550059/35184372088832)), (87765/562949953421312), by norm_num⟩
  | 1 => ⟨((2217193104360299/2251799813685248), (-9565484505557/2251799813685248)), (263683/562949953421312), by norm_num⟩
  | 0 => ⟨((545728820324919/562949953421312), (-4733369665455/562949953421312)), (2115709/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545728820324919/562949953421312), (-4733369665455/562949953421312)), (8070789345748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2115978791613585/2251799813685248), (-36708573868659/2251799813685248)), (4137555/2251799813685248), by norm_num⟩
  | 2 => ⟨((1987751619819907/2251799813685248), (-17247217826469/562949953421312)), (1977721/562949953421312), by norm_num⟩
  | 3 => ⟨((438138085560325/562949953421312), (-121798340913239/2251799813685248)), (3612807/562949953421312), by norm_num⟩
  | 4 => ⟨((1357405244404863/2251799813685248), (-189588760378535/2251799813685248)), (6014449/562949953421312), by norm_num⟩
  | 5 => ⟨((802293831137371/2251799813685248), (-114285815308275/1125899906842624)), (66111147/4503599627370496), by norm_num⟩
  | 6 => ⟨((262647859531727/2251799813685248), (-81437793938063/1125899906842624)), (60530869/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1705255409/33554432)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1775840509/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1008441824084515/9007199254740992), (-528733324936401/9007199254740992)), (102072117/4503599627370496), by norm_num⟩
  | 1 => ⟨((288264499/1073741824), (604556627/4294967296)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((-1382456159/4294967296), (-724831739/4294967296)), (285/4294967296), by norm_num⟩
  | 3 => ⟨((552497515/2147483648), (579356867/4294967296)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((-1324831179/8589934592), (-347309273/4294967296)), (279/8589934592), by norm_num⟩
  | 5 => ⟨((1270722569/17179869184), (666249011/17179869184)), (135/8589934592), by norm_num⟩
  | 6 => ⟨((-1015686547/34359738368), (-532531785/34359738368)), (109/17179869184), by norm_num⟩
  | 7 => ⟨((1391719983/137438953472), (729688829/137438953472)), (151/68719476736), by norm_num⟩
  | 8 => ⟨((-208574923/68719476736), (-109357337/68719476736)), (183/274877906944), by norm_num⟩
  | 9 => ⟨((889139239/1099511627776), (233091059/549755813888)), (197/1099511627776), by norm_num⟩
  | 10 => ⟨((-852825111/4398046511104), (-447142359/4398046511104)), (191/4398046511104), by norm_num⟩
  | 11 => ⟨((743631019/17592186044416), (389891109/17592186044416)), (21/2199023255552), by norm_num⟩
  | 12 => ⟨((-1188766203/140737488355328), (-311639349/70368744177664)), (271/140737488355328), by norm_num⟩
  | 13 => ⟨((109636033/70368744177664), (229931853/281474976710656)), (101/281474976710656), by norm_num⟩
  | 14 => ⟨((-600904515/2251799813685248), (-630117147/4503599627370496)), (279/4503599627370496), by norm_num⟩
  | 15 => ⟨((768483251/18014398509481984), (201460657/9007199254740992)), (45/4503599627370496), by norm_num⟩
  | 16 => ⟨((-921371177/144115188075855872), (-483081557/144115188075855872)), (109/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1731619568797/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889385006542973/316912650057057350374175801344), (-1024651746851/158456325028528675187087900672)), (23151/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944871395086341/19807040628566084398385987584), (-4610077553621/39614081257132168796771975168)), (104205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944758664599087/1237940039285380274899124224), (-2448585786165/1237940039285380274899124224)), (110747/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771182912027949/154742504910672534362390528), (-4896006343775/154742504910672534362390528)), (55391/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387386357018651/2417851639229258349412352), (-4588768070711/9671406556917033397649408)), (51947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629390489293565/302231454903657293676544), (-2006967193009/302231454903657293676544)), (90943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887778198991915/75557863725914323419136), (-6520323161851/75557863725914323419136)), (147849/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324381977470723/1180591620717411303424), (-4888212609969/4722366482869645213696)), (55473/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621430360658861/590295810358705651712), (-6717994777783/590295810358705651712)), (152647/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823449606015961/73786976294838206464), (-4196274267231/36893488147419103232)), (23869/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822624869249273/9223372036854775808), (-4717410047491/4611686018427387904)), (107509/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796934260832771/576460752303423488), (-9426327265773/1152921504606846976)), (107633/576460752303423488), by norm_num⟩
  | 5 => ⟨((597236321292417/72057594037927936), (-8238486645471/144115188075855872)), (47159/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491464353971199/36028797018963968), (-12338642365101/36028797018963968)), (35439/4503599627370496), by norm_num⟩
  | 3 => ⟨((372255605344133/2251799813685248), (-15389926300671/9007199254740992)), (44421/1125899906842624), by norm_num⟩
  | 2 => ⟨((69606905706703/140737488355328), (-3834978686733/562949953421312)), (89209/562949953421312), by norm_num⟩
  | 1 => ⟨((34612071544341/35184372088832), (-22885030824133/1125899906842624)), (269467/562949953421312), by norm_num⟩
  | 0 => ⟨((34036160581937/35184372088832), (-45271826632325/1125899906842624)), (1092639/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((34036160581937/35184372088832), (-45271826632325/1125899906842624)), (4168087009910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131474135392451/140737488355328), (-43794419784019/562949953421312)), (2201833/1125899906842624), by norm_num⟩
  | 2 => ⟨((975750045138787/1125899906842624), (-163647470006877/1125899906842624)), (4456399/1125899906842624), by norm_num⟩
  | 3 => ⟨((821838291774573/1125899906842624), (-141823465190479/562949953421312)), (18039295/2251799813685248), by norm_num⟩
  | 4 => ⟨((1056865877857419/2251799813685248), (-828179866841295/2251799813685248)), (17712209/1125899906842624), by norm_num⟩
  | 5 => ⟨((382879143446207/4503599627370496), (-388700201800181/1125899906842624)), (118619159/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1008441824084515/9007199254740992), (-528733324936401/9007199254740992)), (102072117/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1775840509/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1840279657/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-140353087892633/9007199254740992), (261738803840549/2251799813685248)), (176404461/9007199254740992), by norm_num⟩
  | 1 => ⟨((41575947/1073741824), (-9691663/33554432)), (211/4294967296), by norm_num⟩
  | 2 => ⟨((-103312347/2147483648), (1541304181/4294967296)), (33/536870912), by norm_num⟩
  | 3 => ⟨((42786923/1073741824), (-1276665669/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-212643019/8589934592), (1586197505/8589934592)), (277/8589934592), by norm_num⟩
  | 5 => ⟨((211359221/17179869184), (-1576621091/17179869184)), (139/8589934592), by norm_num⟩
  | 6 => ⟨((-175069311/34359738368), (163239843/4294967296)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((248589083/137438953472), (-927167477/68719476736)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((-77215083/137438953472), (575981157/137438953472)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((42638283/274877906944), (-159028823/137438953472)), (29/137438953472), by norm_num⟩
  | 10 => ⟨((-169523445/4398046511104), (1264549695/4398046511104)), (29/549755813888), by norm_num⟩
  | 11 => ⟨((153181795/17592186044416), (-571325081/8796093022208)), (211/17592186044416), by norm_num⟩
  | 12 => ⟨((-253761641/140737488355328), (473229831/35184372088832)), (353/140737488355328), by norm_num⟩
  | 13 => ⟨((97011383/281474976710656), (-723650433/281474976710656)), (17/35184372088832), by norm_num⟩
  | 14 => ⟨((-137750989/2251799813685248), (1027545013/2251799813685248)), (195/2251799813685248), by norm_num⟩
  | 15 => ⟨((182559119/18014398509481984), (-1361788499/18014398509481984)), (261/18014398509481984), by norm_num⟩
  | 16 => ⟨((-3544081/2251799813685248), (211494831/18014398509481984)), (327/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1109864297901/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889329813034667/316912650057057350374175801344), (2626635923665/633825300114114700748351602688)), (92459/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472404732125275/9903520314283042199192993792), (1477203851047/19807040628566084398385987584)), (104033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236173268153805/309485009821345068724781056), (1569185703503/1237940039285380274899124224)), (55277/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885526099587765/77371252455336267181195264), (1568799495695/77371252455336267181195264)), (6911/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549423385035403/9671406556917033397649408), (2940678575773/9671406556917033397649408)), (12961/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((78667168178149/37778931862957161709568), (2572273514617/604462909807314587353088)), (45375/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117975401128613/4722366482869645213696), (2089203510777/37778931862957161709568)), (147511/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324349973256067/1180591620717411303424), (3132460515083/4722366482869645213696)), (110671/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621255666753843/590295810358705651712), (4304948941207/590295810358705651712)), (152235/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455808307549953/18446744073709551616), (1344477861011/18446744073709551616)), (190385/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455596045261153/2305843009213693952), (6045650327107/9223372036854775808)), (107155/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593631245980375/1152921504606846976), (6040029330703/1152921504606846976)), (214469/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597134428795917/72057594037927936), (2639353813613/72057594037927936)), (187839/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491166319332813/36028797018963968), (1976359829519/9007199254740992)), (282115/36028797018963968), by norm_num⟩
  | 3 => ⟨((744331604498581/4503599627370496), (77029232825/70368744177664)), (353271/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226742374608389/4503599627370496), (19653436930123/4503599627370496)), (708423/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214253593960711/2251799813685248), (7328869248065/562949953421312)), (1067353/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176868337623719/2251799813685248), (57974866067821/2251799813685248)), (1076825/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176868337623719/2251799813685248), (57974866067821/2251799813685248)), (4107761387351607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2102937679217241/2251799813685248), (112091358702507/2251799813685248)), (2137433/1125899906842624), by norm_num⟩
  | 2 => ⟨((1958336786056867/2251799813685248), (26170303893975/281474976710656)), (1051265/281474976710656), by norm_num⟩
  | 3 => ⟨((1683653367854697/2251799813685248), (364155062142817/2251799813685248)), (4048009/562949953421312), by norm_num⟩
  | 4 => ⟨((599982231409385/1125899906842624), (272275933709527/1125899906842624)), (7362597/562949953421312), by norm_num⟩
  | 5 => ⟨((1015523643593461/4503599627370496), (580373872573559/2251799813685248)), (22815831/1125899906842624), by norm_num⟩
  | 6 => ⟨((-140353087892633/9007199254740992), (261738803840549/2251799813685248)), (176404461/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1840279657/33554432)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1899557927/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1967854271407931/18014398509481984), (-30822379370983/4503599627370496)), (129371817/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1203405035/4294967296), (37697717/2147483648)), (81/4294967296), by norm_num⟩
  | 2 => ⟨((771668243/2147483648), (-96692735/4294967296)), (53/2147483648), by norm_num⟩
  | 3 => ⟨((-1319526643/4294967296), (1291729/67108864)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((423064877/2147483648), (-106023023/8589934592)), (15/1073741824), by norm_num⟩
  | 5 => ⟨((-1736223975/17179869184), (54388737/8589934592)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((742221095/17179869184), (-11625363/4294967296)), (109/34359738368), by norm_num⟩
  | 7 => ⟨((-1087862583/68719476736), (68156497/68719476736)), (41/34359738368), by norm_num⟩
  | 8 => ⟨((1395156217/274877906944), (-43704491/137438953472)), (107/274877906944), by norm_num⟩
  | 9 => ⟨((-795223343/549755813888), (6227767/68719476736)), (31/274877906944), by norm_num⟩
  | 10 => ⟨((815883041/2199023255552), (-102233005/4398046511104)), (65/2199023255552), by norm_num⟩
  | 11 => ⟨((-760981339/8796093022208), (95353629/17592186044416)), (123/17592186044416), by norm_num⟩
  | 12 => ⟨((650626199/35184372088832), (-81525743/70368744177664)), (107/70368744177664), by norm_num⟩
  | 13 => ⟨((-1026968155/281474976710656), (64341355/281474976710656)), (87/281474976710656), by norm_num⟩
  | 14 => ⟨((1505212177/2251799813685248), (-94304181/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 15 => ⟨((-514772401/4503599627370496), (32251393/4503599627370496)), (45/4503599627370496), by norm_num⟩
  | 16 => ⟨((1320365139/72057594037927936), (-41361595/36028797018963968)), (59/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-20376092955/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444639226939653/158456325028528675187087900672), (-48217137193/316912650057057350374175801344)), (46105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118093975030203/2475880078570760549798248448), (-108467689175/39614081257132168796771975168)), (103737/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472315977107393/618970019642690137449562112), (-28805230419/618970019642690137449562112)), (110221/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770930298719755/154742504910672534362390528), (-115191685845/154742504910672534362390528)), (55111/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387327365125221/2417851639229258349412352), (-107961152911/9671406556917033397649408)), (51667/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258575363773473/604462909807314587353088), (-94434968045/604462909807314587353088)), (90419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471861420048231/18889465931478580854784), (-76699323381/37778931862957161709568)), (146931/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297279924146525/4722366482869645213696), (-114998105887/4722366482869645213696)), (13775/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810545829195727/295147905179352825856), (-158039763931/590295810358705651712)), (18941/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227878705157699/9223372036854775808), (-197425839633/73786976294838206464)), (189413/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822157095227705/9223372036854775808), (-221933888325/9223372036854775808)), (106547/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398351648893813/288230376151711744), (-110860680909/576460752303423488)), (213101/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74629688904625/9007199254740992), (-193767374081/144115188075855872)), (186471/144115188075855872), by norm_num⟩
  | 4 => ⟨((23295015937875/562949953421312), (-290174112267/36028797018963968)), (34965/4503599627370496), by norm_num⟩
  | 3 => ⟨((372079023864487/2251799813685248), (-361884521341/9007199254740992)), (349677/9007199254740992), by norm_num⟩
  | 2 => ⟨((69564892139261/140737488355328), (-360637919951/2251799813685248)), (174859/1125899906842624), by norm_num⟩
  | 1 => ⟨((553331350120345/562949953421312), (-537851119777/1125899906842624)), (1049365/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175291405883047/2251799813685248), (-2126686894393/2251799813685248)), (1049811/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175291405883047/2251799813685248), (-2126686894393/2251799813685248)), (4004711155418014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2101380481938751/2251799813685248), (-4108858785991/2251799813685248)), (4060535/2251799813685248), by norm_num⟩
  | 2 => ⟨((980500802139653/1125899906842624), (-3834388653667/1125899906842624)), (7593405/2251799813685248), by norm_num⟩
  | 3 => ⟨((853865529801961/1125899906842624), (-13356857488971/2251799813685248)), (13277301/2251799813685248), by norm_num⟩
  | 4 => ⟨((80939892740771/140737488355328), (-10129639523901/1125899906842624)), (20296123/2251799813685248), by norm_num⟩
  | 5 => ⟨((1489220940569839/4503599627370496), (-23302730385445/2251799813685248)), (47420631/4503599627370496), by norm_num⟩
  | 6 => ⟨((1967854271407931/18014398509481984), (-30822379370983/4503599627370496)), (129371817/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1899557927/33554432)), (1/16777216), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-244305129/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-117518999996195/9007199254740992), (-1834633483320851/18014398509481984)), (154541079/9007199254740992), by norm_num⟩
  | 1 => ⟨((36971495/1073741824), (1154351935/4294967296)), (197/4294967296), by norm_num⟩
  | 2 => ⟨((-97569895/2147483648), (-1523200467/4294967296)), (131/2147483648), by norm_num⟩
  | 3 => ⟨((85830849/2147483648), (1339937785/4294967296)), (233/4294967296), by norm_num⟩
  | 4 => ⟨((-226512531/8589934592), (-442021579/2147483648)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((119555911/8589934592), (466608115/4294967296)), (329/17179869184), by norm_num⟩
  | 6 => ⟨((-210343269/34359738368), (-205234261/4294967296)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((79301135/34359738368), (309499989/17179869184)), (111/34359738368), by norm_num⟩
  | 8 => ⟨((-104640121/137438953472), (-1633576429/274877906944)), (37/34359738368), by norm_num⟩
  | 9 => ⟨((122733901/549755813888), (958022633/549755813888)), (11/34359738368), by norm_num⟩
  | 10 => ⟨((-8097545/137438953472), (-252827665/549755813888)), (47/549755813888), by norm_num⟩
  | 11 => ⟨((124333879/8796093022208), (970511567/8796093022208)), (91/4398046511104), by norm_num⟩
  | 12 => ⟨((-109374745/35184372088832), (-853745221/35184372088832)), (323/70368744177664), by norm_num⟩
  | 13 => ⟨((177628445/281474976710656), (693256179/140737488355328)), (265/281474976710656), by norm_num⟩
  | 14 => ⟨((-133934757/1125899906842624), (-1045453029/1125899906842624)), (101/562949953421312), by norm_num⟩
  | 15 => ⟨((188512801/9007199254740992), (1471472255/9007199254740992)), (143/4503599627370496), by norm_num⟩
  | 16 => ⟨((-62187011/18014398509481984), (-485412455/18014398509481984)), (191/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-2212113287895/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778454737276043/633825300114114700748351602688), (-2617050186831/633825300114114700748351602688)), (46229/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889388475755887/39614081257132168796771975168), (-1471796759985/19807040628566084398385987584)), (3251/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((472285336598269/618970019642690137449562112), (-390855189693/309485009821345068724781056)), (110553/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442701866172185/38685626227668133590597632), (-3126024344465/154742504910672534362390528)), (55287/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774597007407853/4835703278458516698824704), (-366222477913/1208925819614629174706176)), (51843/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258474060257681/604462909807314587353088), (-2562689623291/604462909807314587353088)), (90749/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943640260737117/37778931862957161709568), (-520343031065/9444732965739290427392)), (147509/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162144447834267/590295810358705651712), (-1560317842583/2361183241434822606848)), (55335/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405229980529055/147573952589676412928), (-4288563607453/590295810358705651712)), (19029/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227851727807327/9223372036854775808), (-334827547037/4611686018427387904)), (95191/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910956361324731/4611686018427387904), (-188191760017/288230376151711744)), (107153/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796580128259989/576460752303423488), (-3008095809799/576460752303423488)), (3351/18014398509481984), by norm_num⟩
  | 5 => ⟨((1193857269080041/144115188075855872), (-2628743173239/72057594037927936)), (187835/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490549990382149/36028797018963968), (-1968220759157/9007199254740992)), (70527/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487894640376313/9007199254740992), (-4908891887433/4503599627370496)), (88315/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112605379301547/2251799813685248), (-19565752626987/4503599627370496)), (177099/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211969950337581/2251799813685248), (-29174598912841/2251799813685248)), (533651/1125899906842624), by norm_num⟩
  | 0 => ⟨((2172356035083647/2251799813685248), (-57656115702623/2251799813685248)), (2153509/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172356035083647/2251799813685248), (-57656115702623/2251799813685248)), (8214984902388762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094238789268145/2251799813685248), (-27811000370653/562949953421312)), (2132673/1125899906842624), by norm_num⟩
  | 2 => ⟨((485551696472957/562949953421312), (-51730065337605/562949953421312)), (4177613/1125899906842624), by norm_num⟩
  | 3 => ⟨((1656164629707275/2251799813685248), (-178471431292813/1125899906842624)), (7974263/1125899906842624), by norm_num⟩
  | 4 => ⟨((580751685306827/1125899906842624), (-262526064816261/1125899906842624)), (3564493/281474976710656), by norm_num⟩
  | 5 => ⟨((238344975115375/1125899906842624), (-541655447886359/2251799813685248)), (42715807/2251799813685248), by norm_num⟩
  | 6 => ⟨((-117518999996195/9007199254740992), (-1834633483320851/18014398509481984)), (154541079/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-244305129/4194304)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-2005535981/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1737287499259841/18014398509481984), (138177822023849/18014398509481984)), (288929887/18014398509481984), by norm_num⟩
  | 1 => ⟨((280419693/1073741824), (-89214439/4294967296)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((-379695303/1073741824), (60399295/2147483648)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((1370978589/4294967296), (-54521441/2147483648)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((-928169711/4294967296), (147646799/8589934592)), (319/8589934592), by norm_num⟩
  | 5 => ⟨((1005412069/8589934592), (-79966989/8589934592)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((-907568785/17179869184), (144369747/34359738368)), (79/8589934592), by norm_num⟩
  | 7 => ⟨((1404423903/68719476736), (-55851503/34359738368)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((-14856447/2147483648), (75624337/137438953472)), (335/274877906944), by norm_num⟩
  | 9 => ⟨((1144377011/549755813888), (-45509889/274877906944)), (51/137438953472), by norm_num⟩
  | 10 => ⟨((-619806079/1099511627776), (98594451/2199023255552)), (223/2199023255552), by norm_num⟩
  | 11 => ⟨((19073477/137438953472), (-97090445/8796093022208)), (111/4398046511104), by norm_num⟩
  | 12 => ⟨((-1101907909/35184372088832), (87641933/35184372088832)), (101/17592186044416), by norm_num⟩
  | 13 => ⟨((918160595/140737488355328), (-73027309/140737488355328)), (339/281474976710656), by norm_num⟩
  | 14 => ⟨((-355203569/281474976710656), (113006639/1125899906842624)), (33/140737488355328), by norm_num⟩
  | 15 => ⟨((1026036369/4503599627370496), (-40803687/2251799813685248)), (193/4503599627370496), by norm_num⟩
  | 16 => ⟨((-694639499/18014398509481984), (110498433/36028797018963968)), (33/4503599627370496), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (498610953087/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778354778910971/633825300114114700748351602688), (2359303571989/316912650057057350374175801344)), (92665/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472318896036859/9903520314283042199192993792), (5307322317611/39614081257132168796771975168)), (52139/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944510409378961/1237940039285380274899124224), (5637682870079/2475880078570760549798248448)), (55415/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770686284805287/154742504910672534362390528), (2818083735129/77371252455336267181195264)), (110869/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774539858088385/4835703278458516698824704), (5282297141721/9671406556917033397649408)), (103981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258373357030143/604462909807314587353088), (4620400418595/604462909807314587353088)), (5689/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943557791306857/37778931862957161709568), (7505133315035/75557863725914323419136)), (18499/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297030745658165/4722366482869645213696), (2813105195175/2361183241434822606848)), (55531/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101296652038175/36893488147419103232), (7731751066841/590295810358705651712)), (152821/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822594206697335/73786976294838206464), (1207282309003/9223372036854775808)), (23899/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910830937441255/4611686018427387904), (10856702236537/9223372036854775808)), (215319/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592904693522911/1152921504606846976), (5422829433513/576460752303423488)), (53901/288230376151711744), by norm_num⟩
  | 5 => ⟨((298407090075953/36028797018963968), (4738767172425/72057594037927936)), (188975/144115188075855872), by norm_num⟩
  | 4 => ⟨((745098039283397/18014398509481984), (14191483791751/36028797018963968)), (142053/18014398509481984), by norm_num⟩
  | 3 => ⟨((743716933037571/4503599627370496), (17695961170073/9007199254740992)), (356259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112117179116885/2251799813685248), (17630945953185/2251799813685248)), (357953/2251799813685248), by norm_num⟩
  | 1 => ⟨((552592318516379/562949953421312), (26284144931661/1125899906842624)), (67647/140737488355328), by norm_num⟩
  | 0 => ⟨((67769271257465/70368744177664), (51920786580173/1125899906842624)), (68713/70368744177664), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((67769271257465/70368744177664), (51920786580173/1125899906842624)), (262119293481326081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1041858873283871/1125899906842624), (100005589435247/1125899906842624)), (2218989/1125899906842624), by norm_num⟩
  | 2 => ⟨((477604086911241/562949953421312), (185081657965995/1125899906842624)), (4500907/1125899906842624), by norm_num⟩
  | 3 => ⟨((1559938729694891/2251799813685248), (628089624803377/2251799813685248)), (9116865/1125899906842624), by norm_num⟩
  | 4 => ⟨((452729468051519/1125899906842624), (435110317309615/1125899906842624)), (35434695/2251799813685248), by norm_num⟩
  | 5 => ⟨((55575039727307/4503599627370496), (1399678684061525/4503599627370496)), (55884777/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1737287499259841/18014398509481984), (138177822023849/18014398509481984)), (288929887/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-2005535981/33554432)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile021Terms1
