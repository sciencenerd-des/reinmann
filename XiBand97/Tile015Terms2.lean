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
namespace Reinmann.XiBand97.Tile015Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26461/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26461/1280))
  have he : value ((69/80), (26461/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-961615891/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((592792713562291/9007199254740992), (-572637692058589/9007199254740992)), (93245819/9007199254740992), by norm_num⟩
  | 1 => ⟨((-783715435/4294967296), (757069019/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((8487971/33554432), (-8199379/33554432)), (11/268435456), by norm_num⟩
  | 3 => ⟨((-502051257/2147483648), (30311341/134217728)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((695990827/4294967296), (-336163529/2147483648)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((-771878527/8589934592), (93204321/1073741824)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((713367233/17179869184), (-689112665/17179869184)), (123/17179869184), by norm_num⟩
  | 7 => ⟨((-565106841/34359738368), (68236643/4294967296)), (99/34359738368), by norm_num⟩
  | 8 => ⟨((783404427/137438953472), (-756768587/137438953472)), (139/137438953472), by norm_num⟩
  | 9 => ⟨((-965359235/549755813888), (932536911/549755813888)), (173/549755813888), by norm_num⟩
  | 10 => ⟨((1070617651/2199023255552), (-1034216529/2199023255552)), (97/1099511627776), by norm_num⟩
  | 11 => ⟨((-1079411791/8796093022208), (1042711667/8796093022208)), (99/4398046511104), by norm_num⟩
  | 12 => ⟨((31174635/1099511627776), (-963670203/35184372088832)), (185/35184372088832), by norm_num⟩
  | 13 => ⟨((-106380851/17592186044416), (822111119/140737488355328)), (5/4398046511104), by norm_num⟩
  | 14 => ⟨((674172223/562949953421312), (-651250291/562949953421312)), (129/562949953421312), by norm_num⟩
  | 15 => ⟨((-996907895/4503599627370496), (963012913/4503599627370496)), (193/4503599627370496), by norm_num⟩
  | 16 => ⟨((691003897/18014398509481984), (-333754843/9007199254740992)), (17/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-500271800743/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778280187024823/633825300114114700748351602688), (-1183472367145/633825300114114700748351602688)), (92317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236149038787303/4951760157141521099596496896), (-665565073759/19807040628566084398385987584)), (12983/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944466592656227/1237940039285380274899124224), (-1413980875829/2475880078570760549798248448)), (110365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885299800585359/77371252455336267181195264), (-1413593023147/154742504910672534362390528)), (55187/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774499729365021/4835703278458516698824704), (-1324831511205/9671406556917033397649408)), (51743/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629152069711305/302231454903657293676544), (-289703947005/151115727451828646838272)), (90561/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943502495828397/37778931862957161709568), (-941151953863/37778931862957161709568)), (147181/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296949452435745/4722366482869645213696), (-1411052999015/4722366482869645213696)), (110403/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810318666240469/295147905179352825856), (-1939101760783/590295810358705651712)), (18979/73786976294838206464), by norm_num⟩
  | 8 => ⟨((113903865189417/4611686018427387904), (-151389635667/4611686018427387904)), (94915/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821518472502903/9223372036854775808), (-2722756124779/9223372036854775808)), (213617/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796384080498331/576460752303423488), (-2719937249947/1152921504606846976)), (213689/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193516604279789/144115188075855872), (-594194416651/36028797018963968)), (187059/144115188075855872), by norm_num⟩
  | 4 => ⟨((372510954461809/9007199254740992), (-1779420575713/18014398509481984)), (140375/18014398509481984), by norm_num⟩
  | 3 => ⟨((743635169453205/4503599627370496), (-4437503434361/9007199254740992)), (175611/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223987282689771/4503599627370496), (-4420974054571/2251799813685248)), (703301/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105098575429123/1125899906842624), (-13180572919027/2251799813685248)), (1057103/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169057685156715/2251799813685248), (-6508382221891/562949953421312)), (530717/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169057685156715/2251799813685248), (-6508382221891/562949953421312)), (2024524690868186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((16320741622441/17592186044416), (-50153859647857/2251799813685248)), (2069407/1125899906842624), by norm_num⟩
  | 2 => ⟨((1936955076862183/2251799813685248), (-46529077319567/1125899906842624)), (122871/35184372088832), by norm_num⟩
  | 3 => ⟨((415571482741111/562949953421312), (-160093685039173/2251799813685248)), (14178441/2251799813685248), by norm_num⟩
  | 4 => ⟨((303930717070789/562949953421312), (-236363355800569/2251799813685248)), (22949201/2251799813685248), by norm_num⟩
  | 5 => ⟨((1263091370608043/4503599627370496), (-127610072229567/1125899906842624)), (59195705/4503599627370496), by norm_num⟩
  | 6 => ⟨((592792713562291/9007199254740992), (-572637692058589/9007199254740992)), (93245819/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-961615891/16777216)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1965284611/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-681294367775567/18014398509481984), (-704147593875623/9007199254740992)), (104673853/4503599627370496), by norm_num⟩
  | 1 => ⟨((460208009/4294967296), (475645151/2147483648)), (285/4294967296), by norm_num⟩
  | 2 => ⟨((-81491717/536870912), (-1347604189/4294967296)), (203/2147483648), by norm_num⟩
  | 3 => ⟨((19240285/134217728), (636341695/2147483648)), (193/2147483648), by norm_num⟩
  | 4 => ⟨((-218047329/2147483648), (-901445891/4294967296)), (275/4294967296), by norm_num⟩
  | 5 => ⟨((247109841/4294967296), (1021595411/8589934592)), (313/8589934592), by norm_num⟩
  | 6 => ⟨((-233371633/8589934592), (-482399625/8589934592)), (297/17179869184), by norm_num⟩
  | 7 => ⟨((188911893/17179869184), (97624361/4294967296)), (243/34359738368), by norm_num⟩
  | 8 => ⟨((-33451731/8589934592), (-1106362569/137438953472)), (173/68719476736), by norm_num⟩
  | 9 => ⟨((673961889/549755813888), (348284577/137438953472)), (219/274877906944), by norm_num⟩
  | 10 => ⟨((-381895563/1099511627776), (-789411609/1099511627776)), (125/549755813888), by norm_num⟩
  | 11 => ⟨((393451493/4398046511104), (813298729/4398046511104)), (259/4398046511104), by norm_num⟩
  | 12 => ⟨((-92894335/4398046511104), (-768082937/17592186044416)), (123/8796093022208), by norm_num⟩
  | 13 => ⟨((323925501/70368744177664), (83697801/8796093022208)), (431/140737488355328), by norm_num⟩
  | 14 => ⟨((-524428601/562949953421312), (-1084039893/562949953421312)), (351/562949953421312), by norm_num⟩
  | 15 => ⟨((396218163/2251799813685248), (819017677/2251799813685248)), (267/2251799813685248), by norm_num⟩
  | 16 => ⟨((-561285293/18014398509481984), (-580112953/9007199254740992)), (95/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-1316535133635/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111137198659059/39614081257132168796771975168), (-1557101981937/316912650057057350374175801344)), (17345/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889096448724259/39614081257132168796771975168), (-875682186805/9903520314283042199192993792)), (156135/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944415514958639/1237940039285380274899124224), (-1860360441897/1237940039285380274899124224)), (165927/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770497105856455/154742504910672534362390528), (-3719676735933/154742504910672534362390528)), (82983/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548903008491429/9671406556917033397649408), (-871521963505/2417851639229258349412352)), (77817/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258219384900347/604462909807314587353088), (-762304536875/151115727451828646838272)), (136221/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886866590176931/75557863725914323419136), (-4952901398039/75557863725914323419136)), (55359/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648422530521071/2361183241434822606848), (-1856429242723/2361183241434822606848)), (649/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1620492836367955/590295810358705651712), (-637778539429/73786976294838206464)), (228557/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822279788179567/73786976294838206464), (-6373359756861/73786976294838206464)), (71465/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821311691657061/9223372036854775808), (-1790987140381/2305843009213693952)), (321819/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796279462051247/576460752303423488), (-447272077039/72057594037927936)), (322101/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193330766321777/144115188075855872), (-6253272754489/144115188075855872)), (282157/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489759567971891/36028797018963968), (-9362857523819/36028797018963968)), (6623/562949953421312), by norm_num⟩
  | 3 => ⟨((1486905455255879/9007199254740992), (-5836889448909/4503599627370496)), (132739/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111614483173391/2251799813685248), (-23258367834341/4503599627370496)), (266317/1125899906842624), by norm_num⟩
  | 1 => ⟨((552247219679273/562949953421312), (-17332618899725/1125899906842624)), (803157/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083180691772257/1125899906842624), (-133681991067/4398046511104)), (202901/140737488355328), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083180691772257/1125899906842624), (-133681991067/4398046511104)), (774005890429449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2082084239030647/2251799813685248), (-131696425852575/2251799813685248)), (6443835/2251799813685248), by norm_num⟩
  | 2 => ⟨((239682209070973/281474976710656), (-121770616969525/1125899906842624)), (12670077/2251799813685248), by norm_num⟩
  | 3 => ⟨((1606417929105545/2251799813685248), (-103690391296109/562949953421312)), (12159173/1125899906842624), by norm_num⟩
  | 4 => ⟨((534805845608389/1125899906842624), (-295887942865461/1125899906842624)), (21827759/1125899906842624), by norm_num⟩
  | 5 => ⟨((705098620428223/4503599627370496), (-281095327440343/1125899906842624)), (128836917/4503599627370496), by norm_num⟩
  | 6 => ⟨((-681294367775567/18014398509481984), (-704147593875623/9007199254740992)), (104673853/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1965284611/33554432)), (3/33554432), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-2004933073/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1486373800938307/18014398509481984), (22845070874109/4503599627370496)), (123061025/9007199254740992), by norm_num⟩
  | 1 => ⟨((256071857/1073741824), (-15742957/1073741824)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-1480285727/4294967296), (91005997/4294967296)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((356548005/1073741824), (-21920097/1073741824)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-257639071/1073741824), (63357229/4294967296)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((148934539/1073741824), (-36625189/4294967296)), (207/8589934592), by norm_num⟩
  | 6 => ⟨((-573968247/8589934592), (8821701/2147483648)), (201/17179869184), by norm_num⟩
  | 7 => ⟨((236997373/8589934592), (-116562265/68719476736)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((-342505257/34359738368), (42113535/68719476736)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((1759942261/549755813888), (-108198909/549755813888)), (79/137438953472), by norm_num⟩
  | 10 => ⟨((-508688741/549755813888), (31273507/549755813888)), (23/137438953472), by norm_num⟩
  | 11 => ⟨((1069308779/4398046511104), (-65739681/4398046511104)), (195/4398046511104), by norm_num⟩
  | 12 => ⟨((-1030233299/17592186044416), (15834343/4398046511104)), (95/8796093022208), by norm_num⟩
  | 13 => ⟨((1832465989/140737488355328), (-56328785/70368744177664)), (85/35184372088832), by norm_num⟩
  | 14 => ⟨((-94580499/35184372088832), (93034931/562949953421312)), (283/562949953421312), by norm_num⟩
  | 15 => ⟨((1166390627/2251799813685248), (-71708143/2251799813685248)), (55/562949953421312), by norm_num⟩
  | 16 => ⟨((-26338301/281474976710656), (25907899/4503599627370496)), (5/281474976710656), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (4012293027149/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444528089607705/158456325028528675187087900672), (593132747093/79228162514264337593543950336)), (92667/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889002915805549/39614081257132168796771975168), (1334252190469/9903520314283042199192993792)), (104281/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944365585128857/1237940039285380274899124224), (1417281593541/618970019642690137449562112)), (55417/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110649794105313/9671406556917033397649408), (2833750208851/77371252455336267181195264)), (110873/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548808309495309/9671406556917033397649408), (2655777195841/4835703278458516698824704)), (103985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258135949958855/604462909807314587353088), (4645883211835/604462909807314587353088)), (91029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117920620907319/4722366482869645213696), (7546323102169/75557863725914323419136)), (147999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648370815373311/2361183241434822606848), (2828455317129/2361183241434822606848)), (27767/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620349096617233/590295810358705651712), (3886826047487/295147905179352825856)), (152829/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822097832435179/73786976294838206464), (9710167657675/73786976294838206464)), (191203/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821103860814259/9223372036854775808), (10914458801539/9223372036854775808)), (215333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592347188695465/1152921504606846976), (10902615334621/1152921504606846976)), (215619/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298285279296717/36028797018963968), (4763236595009/72057594037927936)), (188991/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489466362872105/36028797018963968), (14263101041623/36028797018963968)), (284133/36028797018963968), by norm_num⟩
  | 3 => ⟨((743261868058389/4503599627370496), (17782359937923/9007199254740992)), (356301/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111210078958431/2251799813685248), (2214085434451/281474976710656)), (179003/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103831588281707/1125899906842624), (26395178290337/1125899906842624)), (135321/281474976710656), by norm_num⟩
  | 0 => ⟨((270408201928203/281474976710656), (26048520867435/562949953421312)), (549871/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((270408201928203/281474976710656), (26048520867435/562949953421312)), (2097591402293968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((518347777573059/562949953421312), (50048738065217/562949953421312)), (2214781/1125899906842624), by norm_num⟩
  | 2 => ⟨((945659701063337/1125899906842624), (184333630290051/1125899906842624)), (4472419/1125899906842624), by norm_num⟩
  | 3 => ⟨((1528188034710515/2251799813685248), (309648992164585/1125899906842624)), (8977359/1125899906842624), by norm_num⟩
  | 4 => ⟨((108348256813063/281474976710656), (420287702228429/1125899906842624)), (34245945/2251799813685248), by norm_num⟩
  | 5 => ⟨((39746920160221/4503599627370496), (647125942470239/2251799813685248)), (51931977/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1486373800938307/18014398509481984), (22845070874109/4503599627370496)), (123061025/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-2004933073/33554432)), (1/16777216), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-510609325/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-271291628565173/9007199254740992), (1313689882818715/18014398509481984)), (15736569/1125899906842624), by norm_num⟩
  | 1 => ⟨((380898307/4294967296), (-922222065/4294967296)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((-560765911/4294967296), (678856649/2147483648)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((550380335/4294967296), (-666283993/2147483648)), (33/536870912), by norm_num⟩
  | 4 => ⟨((-50642541/536870912), (122614535/536870912)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((477164389/8589934592), (-288824813/2147483648)), (233/8589934592), by norm_num⟩
  | 6 => ⟨((-234163571/8589934592), (1133902717/17179869184)), (231/17179869184), by norm_num⟩
  | 7 => ⟨((393988769/34359738368), (-238479097/8589934592)), (49/8589934592), by norm_num⟩
  | 8 => ⟨((-72504743/17179869184), (702187149/68719476736)), (291/137438953472), by norm_num⟩
  | 9 => ⟨((47441287/34359738368), (-57431867/17179869184)), (3/4294967296), by norm_num⟩
  | 10 => ⟨((-447001519/1099511627776), (541134809/549755813888)), (57/274877906944), by norm_num⟩
  | 11 => ⟨((478606799/4398046511104), (-1158791581/4398046511104)), (247/4398046511104), by norm_num⟩
  | 12 => ⟨((-234871419/8796093022208), (1137330367/17592186044416)), (245/17592186044416), by norm_num⟩
  | 13 => ⟨((425578191/70368744177664), (-515199979/35184372088832)), (7/2199023255552), by norm_num⟩
  | 14 => ⟨((-358025433/281474976710656), (54177675/17592186044416)), (95/140737488355328), by norm_num⟩
  | 15 => ⟨((8784867/35184372088832), (-680630861/1125899906842624)), (75/562949953421312), by norm_num⟩
  | 16 => ⟨((-413864077/9007199254740992), (1002038019/9007199254740992)), (223/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (2556346968035/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778047692464813/633825300114114700748351602688), (755745562729/158456325028528675187087900672)), (46249/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888930580567487/39614081257132168796771975168), (1700050163527/19807040628566084398385987584)), (104079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888654861917509/2475880078570760549798248448), (3611670180289/2475880078570760549798248448)), (110607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770321013113213/154742504910672534362390528), (1805308532471/77371252455336267181195264)), (13829/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193592250184633/1208925819614629174706176), (3383834912407/9671406556917033397649408)), (1621/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258075083664153/604462909807314587353088), (2959737354945/604462909807314587353088)), (90803/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943316125208609/37778931862957161709568), (2403738711561/37778931862957161709568)), (147603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648334718593427/2361183241434822606848), (1801887547373/2361183241434822606848)), (55373/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810125783130285/295147905179352825856), (77378339649/9223372036854775808)), (76173/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821978519369389/73786976294838206464), (3092902189519/36893488147419103232)), (190539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820973202277097/9223372036854775808), (434556126659/576460752303423488)), (214503/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592220981734613/1152921504606846976), (3472619904383/576460752303423488)), (107343/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193035681413641/144115188075855872), (6068478485535/144115188075855872)), (23507/18014398509481984), by norm_num⟩
  | 4 => ⟨((744659084062817/18014398509481984), (9085527886897/36028797018963968)), (2207/281474976710656), by norm_num⟩
  | 3 => ⟨((743177924763183/4503599627370496), (1415859876111/1125899906842624)), (353843/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111068085415753/2251799813685248), (22563870728277/4503599627370496)), (709859/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207365668317407/2251799813685248), (4202725654573/281474976710656)), (535119/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081589276294517/1125899906842624), (66351902922915/2251799813685248)), (33787/35184372088832), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081589276294517/1125899906842624), (66351902922915/2251799813685248)), (128887176647889603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((519022477813957/562949953421312), (7967571787133/140737488355328)), (4281967/2251799813685248), by norm_num⟩
  | 2 => ⟨((238359214386827/281474976710656), (235067366879681/2251799813685248)), (4190257/1125899906842624), by norm_num⟩
  | 3 => ⟨((1590243802572553/2251799813685248), (398120454984655/2251799813685248)), (3985827/562949953421312), by norm_num⟩
  | 4 => ⟨((1052658162833719/2251799813685248), (140578345901135/562949953421312)), (28156237/2251799813685248), by norm_num⟩
  | 5 => ⟨((703342154650665/4503599627370496), (65716740196505/281474976710656)), (40386825/2251799813685248), by norm_num⟩
  | 6 => ⟨((-271291628565173/9007199254740992), (1313689882818715/18014398509481984)), (15736569/1125899906842624), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-510609325/8388608)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-259752171/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((843028674425083/18014398509481984), (1066964297751785/18014398509481984)), (166634437/18014398509481984), by norm_num⟩
  | 1 => ⟨((-301061655/2147483648), (-381033347/2147483648)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((225475029/1073741824), (1141473895/4294967296)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-900617095/4294967296), (-569925031/2147483648)), (185/4294967296), by norm_num⟩
  | 4 => ⟨((168625481/1073741824), (853671405/4294967296)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((-808250873/8589934592), (-127868549/1073741824)), (171/8589934592), by norm_num⟩
  | 6 => ⟨((807101075/17179869184), (1021493171/17179869184)), (173/17179869184), by norm_num⟩
  | 7 => ⟨((-345408391/17179869184), (-874320017/34359738368)), (75/17179869184), by norm_num⟩
  | 8 => ⟨((129343883/17179869184), (654807173/68719476736)), (57/34359738368), by norm_num⟩
  | 9 => ⟨((-344426351/137438953472), (-435917107/137438953472)), (77/137438953472), by norm_num⟩
  | 10 => ⟨((825447309/1099511627776), (1044712757/1099511627776)), (187/1099511627776), by norm_num⟩
  | 11 => ⟨((-899206961/4398046511104), (-569032677/2199023255552)), (103/2199023255552), by norm_num⟩
  | 12 => ⟨((897927771/17592186044416), (568223185/8796093022208)), (13/1099511627776), by norm_num⟩
  | 13 => ⟨((-827677293/70368744177664), (-523767549/35184372088832)), (97/35184372088832), by norm_num⟩
  | 14 => ⟨((708428451/281474976710656), (896609915/281474976710656)), (21/35184372088832), by norm_num⟩
  | 15 => ⟨((-565936527/1125899906842624), (-44766721/70368744177664)), (17/140737488355328), by norm_num⟩
  | 16 => ⟨((847697159/9007199254740992), (1072872887/9007199254740992)), (103/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1175098401371/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777983411331839/633825300114114700748351602688), (694749596045/316912650057057350374175801344)), (92337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472214623528871/9903520314283042199192993792), (1562837489143/39614081257132168796771975168)), (6493/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888578574656715/2475880078570760549798248448), (1660077328505/2475880078570760549798248448)), (13799/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885122534084555/77371252455336267181195264), (1659585367403/154742504910672534362390528)), (110403/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548667166531249/9671406556917033397649408), (1555338771337/9671406556917033397649408)), (103515/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258013466219439/604462909807314587353088), (340099784305/151115727451828646838272)), (22647/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886532802293025/75557863725914323419136), (2209669781987/75557863725914323419136)), (36807/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296595445639063/4722366482869645213696), (1656396345677/4722366482869645213696)), (110441/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202518849100065/73786976294838206464), (1138077438455/295147905179352825856)), (151889/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910926998896053/36893488147419103232), (2843109999131/73786976294838206464)), (94955/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910417549630951/4611686018427387904), (99863635025/288230376151711744)), (213717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199010669155085/144115188075855872), (399007757305/144115188075855872)), (213801/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192919783209553/144115188075855872), (2789038437941/144115188075855872)), (187171/144115188075855872), by norm_num⟩
  | 4 => ⟨((186143732067295/4503599627370496), (1043884717009/9007199254740992)), (70237/9007199254740992), by norm_num⟩
  | 3 => ⟨((185769388466631/1125899906842624), (2602709883079/4503599627370496)), (351519/9007199254740992), by norm_num⟩
  | 2 => ⟨((17357527121145/35184372088832), (5184472041925/2251799813685248)), (704043/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103439013102431/1125899906842624), (15449082462571/2251799813685248)), (1058593/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162485589606349/2251799813685248), (15241625737615/1125899906842624)), (2127363/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162485589606349/2251799813685248), (15241625737615/1125899906842624)), (8115245827681731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076301218349837/2251799813685248), (14637089771237/562949953421312)), (4143567/2251799813685248), by norm_num⟩
  | 2 => ⟨((956479082374501/1125899906842624), (107970547436463/2251799813685248)), (1964183/562949953421312), by norm_num⟩
  | 3 => ⟨((1619926992975591/2251799813685248), (183447159925799/2251799813685248)), (14102405/2251799813685248), by norm_num⟩
  | 4 => ⟨((575208903194313/1125899906842624), (131970437310841/1125899906842624)), (11294039/1125899906842624), by norm_num⟩
  | 5 => ⟨((139199356925519/562949953421312), (539377044359261/4503599627370496)), (28375209/2251799813685248), by norm_num⟩
  | 6 => ⟨((843028674425083/18014398509481984), (1066964297751785/18014398509481984)), (166634437/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-259752171/4194304)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-527965279/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((648197599174755/9007199254740992), (-138607172911247/18014398509481984)), (89761471/9007199254740992), by norm_num⟩
  | 1 => ⟨((-235253827/1073741824), (201221775/8589934592)), (263/8589934592), by norm_num⟩
  | 2 => ⟨((716235555/2147483648), (-38289013/1073741824)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-1453730145/4294967296), (38857253/1073741824)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((1106478511/4294967296), (-118301779/4294967296)), (5/134217728), by norm_num⟩
  | 5 => ⟨((-673739731/4294967296), (18008621/1073741824)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((42733661/536870912), (-146207069/17179869184)), (101/8589934592), by norm_num⟩
  | 7 => ⟨((-1189518535/34359738368), (127180201/34359738368)), (89/17179869184), by norm_num⟩
  | 8 => ⟨((1810757935/137438953472), (-12100093/8589934592)), (273/137438953472), by norm_num⟩
  | 9 => ⟨((-612543685/137438953472), (16372891/34359738368)), (187/274877906944), by norm_num⟩
  | 10 => ⟨((1491922395/1099511627776), (-159512429/1099511627776)), (115/549755813888), by norm_num⟩
  | 11 => ⟨((-825852947/2199023255552), (88298031/2199023255552)), (257/4398046511104), by norm_num⟩
  | 12 => ⟨((209527319/2199023255552), (-179216891/17592186044416)), (263/17592186044416), by norm_num⟩
  | 13 => ⟨((-1533439/68719476736), (83943053/35184372088832)), (249/70368744177664), by norm_num⟩
  | 14 => ⟨((1365895883/281474976710656), (-146038005/281474976710656)), (109/140737488355328), by norm_num⟩
  | 15 => ⟨((-554466755/562949953421312), (59282131/562949953421312)), (179/1125899906842624), by norm_num⟩
  | 16 => ⟨((1688086477/9007199254740992), (-90242889/4503599627370496)), (137/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-138744742929/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444479904281543/158456325028528675187087900672), (-82023900189/316912650057057350374175801344)), (11527/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888786798074113/39614081257132168796771975168), (-184512037183/39614081257132168796771975168)), (207489/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502493015933/2475880078570760549798248448), (-195991559401/2475880078570760549798248448)), (55115/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770169093748895/154742504910672534362390528), (-195932549443/154742504910672534362390528)), (220463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193574506794215/1208925819614629174706176), (-183624092159/9671406556917033397649408)), (206687/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257951356814943/604462909807314587353088), (-40152108997/151115727451828646838272)), (180855/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886432087601203/75557863725914323419136), (-130435654925/37778931862957161709568)), (293893/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648260047941095/2361183241434822606848), (-12221926165/295147905179352825856)), (220425/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620047489200563/590295810358705651712), (-268715659567/590295810358705651712)), (75773/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910862660568233/36893488147419103232), (-167822348565/36893488147419103232)), (189439/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820690959663881/9223372036854775808), (-377257022401/9223372036854775808)), (213127/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591941989162347/1152921504606846976), (-376828423747/1152921504606846976)), (106569/288230376151711744), by norm_num⟩
  | 5 => ⟨((74549700625053/9007199254740992), (-164621677333/72057594037927936)), (46627/18014398509481984), by norm_num⟩
  | 4 => ⟨((186120591525791/4503599627370496), (-492903640765/36028797018963968)), (279787/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485926727652727/9007199254740992), (-614450801815/9007199254740992)), (174889/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221315740470823/4503599627370496), (-1223880064791/4503599627370496)), (174923/562949953421312), by norm_num⟩
  | 1 => ⟨((1103114419527479/1125899906842624), (-1823317579763/2251799813685248)), (2099775/2251799813685248), by norm_num⟩
  | 0 => ⟨((540318969450463/562949953421312), (-899232967095/562949953421312)), (2101233/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540318969450463/562949953421312), (-899232967095/562949953421312)), (8015567783835982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((16206135329715/17592186044416), (-431541584757/140737488355328)), (8080475/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910927767387759/2251799813685248), (-6360661539449/1125899906842624)), (14937219/2251799813685248), by norm_num⟩
  | 3 => ⟨((405396061177475/562949953421312), (-5397799875823/562949953421312)), (25520891/2251799813685248), by norm_num⟩
  | 4 => ⟨((583770650218837/1125899906842624), (-31096857479197/2251799813685248)), (37246031/2251799813685248), by norm_num⟩
  | 5 => ⟨((604931959494787/2251799813685248), (-64493948707399/4503599627370496)), (39652295/2251799813685248), by norm_num⟩
  | 6 => ⟨((648197599174755/9007199254740992), (-138607172911247/18014398509481984)), (89761471/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-527965279/8388608)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile015Terms2
