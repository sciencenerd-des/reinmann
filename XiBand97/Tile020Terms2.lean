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
namespace Reinmann.XiBand97.Tile020Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27893/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27893/1280))
  have he : value ((69/80), (27893/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-2027312047/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-615085765460995/9007199254740992), (548622482902419/9007199254740992)), (150706575/9007199254740992), by norm_num⟩
  | 1 => ⟨((203297121/1073741824), (-725319151/4294967296)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((-563659305/2147483648), (1005505849/4294967296)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((520931811/2147483648), (-464642363/2147483648)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-22567651/134217728), (40258193/268435456)), (23/536870912), by norm_num⟩
  | 5 => ⟨((200226607/2147483648), (-178591059/2147483648)), (103/4294967296), by norm_num⟩
  | 6 => ⟨((-370097355/8589934592), (660212741/17179869184)), (3/268435456), by norm_num⟩
  | 7 => ⟨((146589679/8589934592), (-522999543/34359738368)), (77/17179869184), by norm_num⟩
  | 8 => ⟨((-406432891/68719476736), (725031317/137438953472)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((1001663333/549755813888), (-446714145/274877906944)), (67/137438953472), by norm_num⟩
  | 10 => ⟨((-138860023/274877906944), (30963865/68719476736)), (75/549755813888), by norm_num⟩
  | 11 => ⟨((280001261/2199023255552), (-499491275/4398046511104)), (305/8796093022208), by norm_num⟩
  | 12 => ⟨((-1035104451/35184372088832), (923255917/35184372088832)), (71/8796093022208), by norm_num⟩
  | 13 => ⟨((441525989/70368744177664), (-787633521/140737488355328)), (61/35184372088832), by norm_num⟩
  | 14 => ⟨((-349762851/281474976710656), (311969117/281474976710656)), (195/562949953421312), by norm_num⟩
  | 15 => ⟨((1034398439/4503599627370496), (-922626193/4503599627370496)), (291/4503599627370496), by norm_num⟩
  | 16 => ⟨((-358495181/9007199254740992), (19984867/562949953421312)), (51/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (785880545401/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778273529243047/633825300114114700748351602688), (1859125195499/316912650057057350374175801344)), (92567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472296112706631/9903520314283042199192993792), (2091074012309/19807040628566084398385987584)), (104161/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888924346144681/2475880078570760549798248448), (4442446831123/2475880078570760549798248448)), (55349/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885295106497523/77371252455336267181195264), (4441225967721/154742504910672534362390528)), (110729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548990074422735/9671406556917033397649408), (4162352492931/9671406556917033397649408)), (103841/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629147672871507/302231454903657293676544), (1820380967069/302231454903657293676544)), (45447/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943494805465415/37778931862957161709568), (369612997773/4722366482869645213696)), (147763/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648468481645995/2361183241434822606848), (4433230320601/4722366482869645213696)), (27719/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405154653056415/147573952589676412928), (3046119459127/295147905179352825856)), (152541/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227804515567263/9223372036854775808), (1902530490443/18446744073709551616)), (95403/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910743178574629/4611686018427387904), (8554273282045/9223372036854775808)), (214837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592732076230081/1152921504606846976), (4272693451735/576460752303423488)), (107531/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193480575708733/144115188075855872), (7467224652699/144115188075855872)), (188433/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489980894116591/36028797018963968), (2795219980941/9007199254740992)), (283155/36028797018963968), by norm_num⟩
  | 3 => ⟨((743588102710087/4503599627370496), (13941221679363/9007199254740992)), (22177/562949953421312), by norm_num⟩
  | 2 => ⟨((1111876414717949/2251799813685248), (27777995170171/4503599627370496)), (178083/1125899906842624), by norm_num⟩
  | 1 => ⟨((276216359757149/281474976710656), (41406524993933/2251799813685248)), (537595/1125899906842624), by norm_num⟩
  | 0 => ⟨((541917995409033/562949953421312), (40887547595307/1125899906842624)), (2177253/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((541917995409033/562949953421312), (40887547595307/1125899906842624)), (8305561074263762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083717489121675/2251799813685248), (9839994521439/140737488355328)), (4349957/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917173641384977/2251799813685248), (145688038892785/1125899906842624)), (4329399/1125899906842624), by norm_num⟩
  | 3 => ⟨((797285515944519/1125899906842624), (496152928573531/2251799813685248)), (16984979/2251799813685248), by norm_num⟩
  | 4 => ⟨((1019846006403737/2251799813685248), (351341661226751/1125899906842624)), (15770009/1125899906842624), by norm_num⟩
  | 5 => ⟨((485231432921437/4503599627370496), (1272988434967305/4503599627370496)), (96506993/4503599627370496), by norm_num⟩
  | 6 => ⟨((-615085765460995/9007199254740992), (548622482902419/9007199254740992)), (150706575/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-2027312047/33554432)), (1/16777216), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40997585/16777216), (-1035820333/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((360272208139331/9007199254740992), (347155696469125/4503599627370496)), (210690253/9007199254740992), by norm_num⟩
  | 1 => ⟨((-121680263/1073741824), (-938001777/4294967296)), (143/2147483648), by norm_num⟩
  | 2 => ⟨((344746145/2147483648), (166097447/536870912)), (51/536870912), by norm_num⟩
  | 3 => ⟨((-325579793/2147483648), (-627452671/2147483648)), (97/1073741824), by norm_num⟩
  | 4 => ⟨((461218507/4294967296), (111106705/536870912)), (69/1073741824), by norm_num⟩
  | 5 => ⟨((-522692171/8589934592), (-503662399/4294967296)), (315/8589934592), by norm_num⟩
  | 6 => ⟨((493632811/17179869184), (237830505/4294967296)), (299/17179869184), by norm_num⟩
  | 7 => ⟨((-399590591/34359738368), (-192521303/8589934592)), (61/8589934592), by norm_num⟩
  | 8 => ⟨((566062697/137438953472), (1090907849/137438953472)), (87/34359738368), by norm_num⟩
  | 9 => ⟨((-712789505/549755813888), (-1373677633/549755813888)), (441/549755813888), by norm_num⟩
  | 10 => ⟨((403896947/1099511627776), (97298045/137438953472)), (63/274877906944), by norm_num⟩
  | 11 => ⟨((-416118625/4398046511104), (-400968901/2199023255552)), (261/4398046511104), by norm_num⟩
  | 12 => ⟨((49123035/2199023255552), (757353627/17592186044416)), (31/2199023255552), by norm_num⟩
  | 13 => ⟨((-342587171/70368744177664), (-660229047/70368744177664)), (435/140737488355328), by norm_num⟩
  | 14 => ⟨((277320727/281474976710656), (534448499/281474976710656)), (177/281474976710656), by norm_num⟩
  | 15 => ⟨((-419044685/2251799813685248), (-25236777/70368744177664)), (269/2251799813685248), by norm_num⟩
  | 16 => ⟨((593621497/18014398509481984), (572009387/9007199254740992)), (383/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1422647408235/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778198858947601/633825300114114700748351602688), (1682603861055/633825300114114700748351602688)), (46183/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889100792851415/39614081257132168796771975168), (473131914837/9903520314283042199192993792)), (51961/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888835915517555/2475880078570760549798248448), (1005154735713/1237940039285380274899124224)), (220859/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770502294860905/154742504910672534362390528), (2009745894365/154742504910672534362390528)), (220887/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454097654167/4835703278458516698824704), (941769092123/4835703278458516698824704)), (207111/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314556061304587/151115727451828646838272), (12871074645/4722366482869645213696)), (45313/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117929693193173/4722366482869645213696), (669015526683/18889465931478580854784)), (147295/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648425981842601/2361183241434822606848), (2006065837109/4722366482869645213696)), (220991/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810251591363453/295147905179352825856), (2756747753973/590295810358705651712)), (303941/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911147001037263/36893488147419103232), (3443547170015/73786976294838206464)), (95011/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821329440520697/9223372036854775808), (1935355189439/4611686018427387904)), (427713/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592578866157699/1152921504606846976), (3866614125271/1152921504606846976)), (427917/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193350676647475/144115188075855872), (105583891945/4503599627370496)), (187329/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489794339760555/36028797018963968), (5058834832191/36028797018963968)), (281223/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486957470646181/9007199254740992), (6307488249041/9007199254740992)), (703865/9007199254740992), by norm_num⟩
  | 2 => ⟨((277919813499207/562949953421312), (6283466552369/2251799813685248)), (1410155/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104623238122921/1125899906842624), (18730718852047/2251799813685248)), (1060661/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167126780022161/2251799813685248), (18492636274685/1125899906842624)), (533391/281474976710656), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167126780022161/2251799813685248), (18492636274685/1125899906842624)), (2034725190282726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2085030179756439/2251799813685248), (71189076507635/2251799813685248)), (4176761/1125899906842624), by norm_num⟩
  | 2 => ⟨((964180505631775/1125899906842624), (131833542293877/2251799813685248)), (15997893/2251799813685248), by norm_num⟩
  | 3 => ⟨((1643661254607855/2251799813685248), (56448770754675/562949953421312)), (29273271/2251799813685248), by norm_num⟩
  | 4 => ⟨((294280033717303/562949953421312), (329630215957267/2251799813685248)), (6075707/281474976710656), by norm_num⟩
  | 5 => ⟨((1134164524645411/4503599627370496), (689251969746937/4503599627370496)), (130094319/4503599627370496), by norm_num⟩
  | 6 => ⟨((360272208139331/9007199254740992), (347155696469125/4503599627370496)), (210690253/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1035820333/16777216)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2614043/1048576), (-1056717399/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((367922571087735/4503599627370496), (-56890798405883/4503599627370496)), (213620291/18014398509481984), by norm_num⟩
  | 1 => ⟨((-253542187/1073741824), (156817967/4294967296)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((732831177/2147483648), (-28328889/536870912)), (109/2147483648), by norm_num⟩
  | 3 => ⟨((-1412103025/4294967296), (218349389/4294967296)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((255093919/1073741824), (-157777727/4294967296)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((-1179706015/8589934592), (91207257/4294967296)), (181/8589934592), by norm_num⟩
  | 6 => ⟨((284149079/4294967296), (-175748587/17179869184)), (177/17179869184), by norm_num⟩
  | 7 => ⟨((-938624541/34359738368), (72568393/17179869184)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((1356486933/137438953472), (-104874817/68719476736)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((-217819529/68719476736), (33680801/68719476736)), (35/68719476736), by norm_num⟩
  | 10 => ⟨((125915883/137438953472), (-77880029/549755813888)), (41/274877906944), by norm_num⟩
  | 11 => ⟨((-1033931/4294967296), (163710717/4398046511104)), (175/4398046511104), by norm_num⟩
  | 12 => ⟨((1020055881/17592186044416), (-78864139/8796093022208)), (171/17592186044416), by norm_num⟩
  | 13 => ⟨((-907181757/70368744177664), (2191795/1099511627776)), (153/70368744177664), by norm_num⟩
  | 14 => ⟨((1498338589/562949953421312), (-7240117/17592186044416)), (255/562949953421312), by norm_num⟩
  | 15 => ⟨((-1154868145/2251799813685248), (178573907/2251799813685248)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((52156223/562949953421312), (-258072489/18014398509481984)), (289/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-49959104877/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778124397420655/633825300114114700748351602688), (-236332737741/633825300114114700748351602688)), (184447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889017124181139/39614081257132168796771975168), (-132908532769/19807040628566084398385987584)), (103753/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944373574753467/1237940039285380274899124224), (-141179424309/1237940039285380274899124224)), (220479/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770413677154321/154742504910672534362390528), (-141139065347/77371252455336267181195264)), (220483/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774412636836853/4835703278458516698824704), (-66137504339/2417851639229258349412352)), (206707/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157268980766503/75557863725914323419136), (-231395571737/604462909807314587353088)), (180873/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378868668911/37778931862957161709568), (-375857206845/75557863725914323419136)), (146963/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648382103015057/2361183241434822606848), (-140876230253/2361183241434822606848)), (55113/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620382934165817/590295810358705651712), (-48397694591/73786976294838206464)), (303133/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911072158926057/36893488147419103232), (-60454385827/9223372036854775808)), (94733/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821161905810721/9223372036854775808), (-271809915297/4611686018427387904)), (426323/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592412404448373/1152921504606846976), (-543033399685/1152921504606846976)), (426353/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149150778370483/18014398509481984), (-474495343377/144115188075855872)), (186547/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489580066838777/36028797018963968), (-710427382921/36028797018963968)), (559709/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486693816542007/9007199254740992), (-885736657883/9007199254740992)), (699757/9007199254740992), by norm_num⟩
  | 2 => ⟨((277855462260545/562949953421312), (-1764599704163/4503599627370496)), (1399885/4503599627370496), by norm_num⟩
  | 1 => ⟨((552126322004089/562949953421312), (-657445548637/562949953421312)), (2100771/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165767202157247/2251799813685248), (-1297873367269/562949953421312)), (4205427/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165767202157247/2251799813685248), (-1297873367269/562949953421312)), (16042430886275481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520752399239609/562949953421312), (-9986292935283/2251799813685248)), (8108899/2251799813685248), by norm_num⟩
  | 2 => ⟨((963413627757949/1125899906842624), (-18475482496989/2251799813685248)), (15074069/2251799813685248), by norm_num⟩
  | 3 => ⟨((1648602112223255/2251799813685248), (-988072491437/70368744177664)), (26044615/2251799813685248), by norm_num⟩
  | 4 => ⟨((1206541180869129/2251799813685248), (-46297213782871/2251799813685248)), (38867305/2251799813685248), by norm_num⟩
  | 5 => ⟨((1291054542499573/4503599627370496), (-99226395968329/4503599627370496)), (86498725/4503599627370496), by norm_num⟩
  | 6 => ⟨((367922571087735/4503599627370496), (-56890798405883/4503599627370496)), (213620291/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1056717399/16777216)), (1/8388608), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-134560541/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((168363147308019/9007199254740992), (-690433396797361/9007199254740992)), (53084787/4503599627370496), by norm_num⟩
  | 1 => ⟨((-236384875/4294967296), (484690429/2147483648)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((87002605/1073741824), (-89196337/268435456)), (7/134217728), by norm_num⟩
  | 3 => ⟨((-341565149/4294967296), (175088781/536870912)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((251429435/4294967296), (-1031076463/4294967296)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((-74031863/2147483648), (1214376691/8589934592)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((290643071/17179869184), (-1191886021/17179869184)), (97/8589934592), by norm_num⟩
  | 7 => ⟨((-61127199/8589934592), (1002695903/34359738368)), (165/34359738368), by norm_num⟩
  | 8 => ⟨((359970615/137438953472), (-738094225/68719476736)), (245/137438953472), by norm_num⟩
  | 9 => ⟨((-235535891/274877906944), (241474823/68719476736)), (81/137438953472), by norm_num⟩
  | 10 => ⟨((277408423/1099511627776), (-568806305/549755813888)), (193/1099511627776), by norm_num⟩
  | 11 => ⟨((-297022609/4398046511104), (304511901/1099511627776)), (209/4398046511104), by norm_num⟩
  | 12 => ⟨((291521649/17592186044416), (-298872237/4398046511104)), (207/17592186044416), by norm_num⟩
  | 13 => ⟨((-66028285/17592186044416), (1083090541/70368744177664)), (95/35184372088832), by norm_num⟩
  | 14 => ⟨((222190007/281474976710656), (-227792429/70368744177664)), (161/281474976710656), by norm_num⟩
  | 15 => ⟨((-87229989/562949953421312), (357717817/562949953421312)), (255/2251799813685248), by norm_num⟩
  | 16 => ⟨((64210845/2251799813685248), (-263319571/2251799813685248)), (189/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-1734574484011/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778050336013085/633825300114114700748351602688), (-1025601755869/316912650057057350374175801344)), (92403/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888933700112607/39614081257132168796771975168), (-576773823353/9903520314283042199192993792)), (51983/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472164592564967/618970019642690137449562112), (-612663437923/618970019642690137449562112)), (110479/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442581184819349/38685626227668133590597632), (-2449939678669/154742504910672534362390528)), (3453/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774370863005671/4835703278458516698824704), (-574015003491/2417851639229258349412352)), (12951/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258078573684033/604462909807314587353088), (-502073594685/151115727451828646838272)), (90675/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471659588622931/18889465931478580854784), (-3262057505195/75557863725914323419136)), (36845/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296674393505209/4722366482869645213696), (-2445300515889/4722366482869645213696)), (110565/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101266187191747/36893488147419103232), (-26252110641/4611686018427387904)), (76037/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455497181193105/18446744073709551616), (-4197312728309/73786976294838206464)), (190165/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820985945232231/9223372036854775808), (-1179455221129/2305843009213693952)), (214035/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398058824651377/288230376151711744), (-2356315534485/576460752303423488)), (13385/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193049974621757/144115188075855872), (-4117720652735/144115188075855872)), (187529/144115188075855872), by norm_num⟩
  | 4 => ⟨((372335782019741/9007199254740992), (-6164935418363/36028797018963968)), (140787/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486393183335325/9007199254740992), (-7685828871255/9007199254740992)), (352459/9007199254740992), by norm_num⟩
  | 2 => ⟨((555557283708037/1125899906842624), (-1913849197325/562949953421312)), (176599/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207550488354299/2251799813685248), (-11407289178337/1125899906842624)), (1063301/2251799813685248), by norm_num⟩
  | 0 => ⟨((270465937253055/281474976710656), (-5628248639085/281474976710656)), (2141507/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((270465937253055/281474976710656), (-5628248639085/281474976710656)), (8169200905806731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32471867875219/35184372088832), (-86529868398393/2251799813685248)), (4201139/2251799813685248), by norm_num⟩
  | 2 => ⟨((1914657733077539/2251799813685248), (-159717868308047/2251799813685248)), (2019347/562949953421312), by norm_num⟩
  | 3 => ⟨((202083041266163/281474976710656), (-271609447525611/2251799813685248)), (14881907/2251799813685248), by norm_num⟩
  | 4 => ⟨((563955962890553/1125899906842624), (-195000151821737/1125899906842624)), (24958805/2251799813685248), by norm_num⟩
  | 5 => ⟨((15544303004173/70368744177664), (-781394493177115/4503599627370496)), (33648885/2251799813685248), by norm_num⟩
  | 6 => ⟨((168363147308019/9007199254740992), (-690433396797361/9007199254740992)), (53084787/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-134560541/2097152)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-136904639/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1046825684987571/18014398509481984), (-108488633032903/2251799813685248)), (249250729/18014398509481984), by norm_num⟩
  | 1 => ⟨((747682927/4294967296), (154973459/1073741824)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((-559964469/2147483648), (-928517985/4294967296)), (17/268435456), by norm_num⟩
  | 3 => ⟨((1118335755/4294967296), (463598549/2147483648)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((-837558629/4294967296), (-86801071/536870912)), (207/4294967296), by norm_num⟩
  | 5 => ⟨((501820283/4294967296), (832104863/8589934592)), (251/8589934592), by norm_num⟩
  | 6 => ⟨((-250553203/4294967296), (-830921131/17179869184)), (253/17179869184), by norm_num⟩
  | 7 => ⟨((857817505/34359738368), (11112577/536870912)), (219/34359738368), by norm_num⟩
  | 8 => ⟨((-80305987/8589934592), (-532644889/68719476736)), (83/34359738368), by norm_num⟩
  | 9 => ⟨((855378621/274877906944), (354591441/137438953472)), (223/274877906944), by norm_num⟩
  | 10 => ⟨((-1024994137/1099511627776), (-849808819/1099511627776)), (269/1099511627776), by norm_num⟩
  | 11 => ⟨((1116584733/4398046511104), (231436337/1099511627776)), (37/549755813888), by norm_num⟩
  | 12 => ⟨((-1114996307/17592186044416), (-924428405/17592186044416)), (149/8796093022208), by norm_num⟩
  | 13 => ⟨((1027763207/70368744177664), (426052309/35184372088832)), (277/70368744177664), by norm_num⟩
  | 14 => ⟨((-27490209/8796093022208), (-729336373/281474976710656)), (239/281474976710656), by norm_num⟩
  | 15 => ⟨((351374107/562949953421312), (291319535/562949953421312)), (193/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1052622753/9007199254740992), (-872715333/9007199254740992)), (291/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-3190572601887/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444494203708849/158456325028528675187087900672), (-3772703670989/633825300114114700748351602688)), (23143/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888850710710001/39614081257132168796771975168), (-1060831996473/9903520314283042199192993792)), (104167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472142455309323/618970019642690137449562112), (-4507346282193/2475880078570760549798248448)), (55353/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770235771341393/154742504910672534362390528), (-4506008219087/154742504910672534362390528)), (6921/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387164468460471/2417851639229258349412352), (-4222961409215/9671406556917033397649408)), (103849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629002379359115/302231454903657293676544), (-230854398863/37778931862957161709568)), (90901/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943258786475857/37778931862957161709568), (-5999551219725/75557863725914323419136)), (147775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648291540015667/2361183241434822606848), (-562166762903/590295810358705651712)), (55443/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810066129392935/295147905179352825856), (-3090025516445/295147905179352825856)), (152557/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455457134224935/18446744073709551616), (-3859695926815/36893488147419103232)), (47707/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455200827045733/2305843009213693952), (-8676521959847/9223372036854775808)), (13429/576460752303423488), by norm_num⟩
  | 6 => ⟨((796024818201499/576460752303423488), (-2166696793021/288230376151711744)), (215093/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192884126456113/144115188075855872), (-3786248763819/72057594037927936)), (188463/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489087592207557/36028797018963968), (-11336889760227/36028797018963968)), (141605/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486061980708261/9007199254740992), (-14132921674149/9007199254740992)), (177457/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110765797414763/2251799813685248), (-14075752649249/2251799813685248)), (178135/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103208543230303/1125899906842624), (-5242778723019/281474976710656)), (537805/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080558387622061/1125899906842624), (-82749245519647/2251799813685248)), (2178539/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080558387622061/1125899906842624), (-82749245519647/2251799813685248)), (8310466774947356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258880599102589/281474976710656), (-19854205238901/281474976710656)), (4341727/2251799813685248), by norm_num⟩
  | 2 => ⟨((946797841920201/1125899906842624), (-292167700703911/2251799813685248)), (8598921/2251799813685248), by norm_num⟩
  | 3 => ⟨((194308050123459/281474976710656), (-122845621899459/562949953421312)), (8346749/1125899906842624), by norm_num⟩
  | 4 => ⟨((482925438487519/1125899906842624), (-10600362035923/35184372088832)), (15166687/1125899906842624), by norm_num⟩
  | 5 => ⟨((419761930596613/4503599627370496), (-1163967791472843/4503599627370496)), (44299125/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1046825684987571/18014398509481984), (-108488633032903/2251799813685248)), (249250729/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-136904639/2097152)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22027651/8388608), (-1113074753/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1215090979853105/18014398509481984), (472658829776463/18014398509481984)), (464558281/18014398509481984), by norm_num⟩
  | 1 => ⟨((881998957/4294967296), (-171544601/2147483648)), (339/4294967296), by norm_num⟩
  | 2 => ⟨((-167829101/536870912), (522271387/4294967296)), (259/2147483648), by norm_num⟩
  | 3 => ⟨((681279285/2147483648), (-530022319/4294967296)), (33/268435456), by norm_num⟩
  | 4 => ⟨((-1037085035/4294967296), (403416211/4294967296)), (101/1073741824), by norm_num⟩
  | 5 => ⟨((157871433/1073741824), (-491283883/8589934592)), (247/4294967296), by norm_num⟩
  | 6 => ⟨((-1281714987/17179869184), (498574935/17179869184)), (503/17179869184), by norm_num⟩
  | 7 => ⟨((557458577/17179869184), (-433692165/34359738368)), (55/4294967296), by norm_num⟩
  | 8 => ⟨((-848597573/68719476736), (165048191/34359738368)), (21/4294967296), by norm_num⟩
  | 9 => ⟨((287063817/68719476736), (-223330187/137438953472)), (457/274877906944), by norm_num⟩
  | 10 => ⟨((-1398355571/1099511627776), (135986753/274877906944)), (559/1099511627776), by norm_num⟩
  | 11 => ⟨((774059075/2199023255552), (-301101615/2199023255552)), (311/2199023255552), by norm_num⟩
  | 12 => ⟨((-785546741/8796093022208), (9549069/274877906944)), (317/8796093022208), by norm_num⟩
  | 13 => ⟨((22996295/1099511627776), (-572501757/70368744177664)), (149/17592186044416), by norm_num⟩
  | 14 => ⟨((-1280232889/281474976710656), (497998413/281474976710656)), (65/35184372088832), by norm_num⟩
  | 15 => ⟨((259846517/281474976710656), (-404311291/1125899906842624)), (53/140737488355328), by norm_num⟩
  | 16 => ⟨((-791108551/4503599627370496), (307733699/4503599627370496)), (325/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (1804516463349/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888954933340485/316912650057057350374175801344), (4267216909395/633825300114114700748351602688)), (23155/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888775294431277/39614081257132168796771975168), (4799506944935/39614081257132168796771975168)), (104225/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236061194474087/309485009821345068724781056), (5098107987625/2475880078570760549798248448)), (55385/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770155353477991/154742504910672534362390528), (637071143975/19342813113834066795298816)), (221611/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548582320299571/9671406556917033397649408), (2388199491717/4835703278458516698824704)), (207835/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628969243870795/302231454903657293676544), (4177714982201/604462909807314587353088)), (181931/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886409579921165/75557863725914323419136), (6785723850253/75557863725914323419136)), (147889/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648250910379345/2361183241434822606848), (5086613761189/4722366482869645213696)), (55489/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810010049071473/295147905179352825856), (6989742206613/590295810358705651712)), (152695/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227710961693911/9223372036854775808), (2182663362709/18446744073709551616)), (382037/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820643977815753/9223372036854775808), (2453254879007/2305843009213693952)), (430205/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397972301720151/288230376151711744), (2450455114243/288230376151711744)), (215361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192742517980767/144115188075855872), (4282002453553/72057594037927936)), (377463/144115188075855872), by norm_num⟩
  | 4 => ⟨((744436361978719/18014398509481984), (12820858753171/36028797018963968)), (8865/562949953421312), by norm_num⟩
  | 3 => ⟨((1485789120096451/9007199254740992), (7991062497917/4503599627370496)), (355621/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110486567522301/2251799813685248), (7958162801991/1125899906842624)), (714311/2251799813685248), by norm_num⟩
  | 1 => ⟨((551386963759077/562949953421312), (23710421577499/1125899906842624)), (1079161/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079626982594771/1125899906842624), (46767167169577/1125899906842624)), (2189237/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079626982594771/1125899906842624), (46767167169577/1125899906842624)), (8351276402000045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066626431978631/2251799813685248), (179380405909753/2251799813685248)), (8760793/2251799813685248), by norm_num⟩
  | 2 => ⟨((941195450316541/1125899906842624), (164629327162725/1125899906842624)), (17476511/2251799813685248), by norm_num⟩
  | 3 => ⟨((762719718791609/1125899906842624), (550487206802437/2251799813685248)), (4291225/281474976710656), by norm_num⟩
  | 4 => ⟨((28087661542179/70368744177664), (372917206066899/1125899906842624)), (63297055/2251799813685248), by norm_num⟩
  | 5 => ⟨((27931186488897/562949953421312), (1190798260184019/4503599627370496)), (23115031/562949953421312), by norm_num⟩
  | 6 => ⟨((-1215090979853105/18014398509481984), (472658829776463/18014398509481984)), (464558281/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1113074753/16777216)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile020Terms2
