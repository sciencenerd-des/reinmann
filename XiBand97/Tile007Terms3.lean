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
namespace Reinmann.XiBand97.Tile007Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11351/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11351/640))
  have he : value ((69/80), (11351/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-229942381/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-48444392267169/4503599627370496), (1237426496132419/18014398509481984)), (53013131/4503599627370496), by norm_num⟩
  | 1 => ⟨((142806695/4294967296), (-911936243/4294967296)), (315/8589934592), by norm_num⟩
  | 2 => ⟨((-110355389/2147483648), (1409416821/4294967296)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((227408795/4294967296), (-363047269/1073741824)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-10983285/268435456), (1122194521/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((217278721/8589934592), (-693750181/4294967296)), (247/8589934592), by norm_num⟩
  | 6 => ⟨((-27984073/2147483648), (357401877/4294967296)), (257/17179869184), by norm_num⟩
  | 7 => ⟨((197714189/34359738368), (-157820625/4294967296)), (229/34359738368), by norm_num⟩
  | 8 => ⟨((-76392869/34359738368), (121957563/8589934592)), (89/34359738368), by norm_num⟩
  | 9 => ⟨((104948267/137438953472), (-167544891/34359738368)), (123/137438953472), by norm_num⟩
  | 10 => ⟨((-259519639/1099511627776), (1657242787/1099511627776)), (153/549755813888), by norm_num⟩
  | 11 => ⟨((18231505/274877906944), (-465691619/1099511627776)), (87/1099511627776), by norm_num⟩
  | 12 => ⟨((-150278283/8796093022208), (119956047/1099511627776)), (181/8796093022208), by norm_num⟩
  | 13 => ⟨((71464085/17592186044416), (-114088995/4398046511104)), (173/35184372088832), by norm_num⟩
  | 14 => ⟨((-63113863/70368744177664), (806066119/140737488355328)), (77/70368744177664), by norm_num⟩
  | 15 => ⟨((6502921/35184372088832), (-1328845117/1125899906842624)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-160806439/4503599627370496), (16044987/70368744177664)), (199/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (2248479668445/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777854046373983/633825300114114700748351602688), (2658361596461/633825300114114700748351602688)), (46231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118044552519949/2475880078570760549798248448), (2989964379737/39614081257132168796771975168)), (104037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888423656131095/2475880078570760549798248448), (1587986512111/1237940039285380274899124224)), (110559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770089968350805/154742504910672534362390528), (3175001272643/154742504910672534362390528)), (110581/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387130392001975/2417851639229258349412352), (2975531569725/9671406556917033397649408)), (103693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257885875270281/604462909807314587353088), (325319801013/75557863725914323419136)), (90755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235790638372279/9444732965739290427392), (4227223813405/75557863725914323419136)), (2305/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1296439359562871/4722366482869645213696), (3168726826521/4722366482869645213696)), (55339/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619935664041387/590295810358705651712), (1088563270113/147573952589676412928)), (152245/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227698040330373/9223372036854775808), (2719349865551/36893488147419103232)), (190399/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820530666226175/9223372036854775808), (6112881457147/9223372036854775808)), (26791/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591779613006995/1152921504606846976), (6105818693843/1152921504606846976)), (214489/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298162698649745/36028797018963968), (5334655244433/144115188075855872)), (187859/144115188075855872), by norm_num⟩
  | 4 => ⟨((186092931689235/4503599627370496), (7986134357001/36028797018963968)), (35269/4503599627370496), by norm_num⟩
  | 3 => ⟨((5803289140725/35184372088832), (9954986347701/9007199254740992)), (176663/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220722149015769/4503599627370496), (9913570369113/2251799813685248)), (354283/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205278539681773/2251799813685248), (29534374643389/2251799813685248)), (1067651/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159138782362331/2251799813685248), (58247851971791/2251799813685248)), (2154603/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159138782362331/2251799813685248), (58247851971791/2251799813685248)), (8219158181197356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258598002413999/281474976710656), (27925483299461/562949953421312)), (530419/281474976710656), by norm_num⟩
  | 2 => ⟨((1895101851747925/2251799813685248), (102623320652897/1125899906842624)), (4108967/1125899906842624), by norm_num⟩
  | 3 => ⟨((1576199102229439/2251799813685248), (345468800236805/2251799813685248)), (15330427/2251799813685248), by norm_num⟩
  | 4 => ⟨((16410865152443/35184372088832), (60454709325423/281474976710656)), (817679/70368744177664), by norm_num⟩
  | 5 => ⟨((772017972604167/4503599627370496), (902322501651411/4503599627370496)), (71296703/4503599627370496), by norm_num⟩
  | 6 => ⟨((-48444392267169/4503599627370496), (1237426496132419/18014398509481984)), (53013131/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-229942381/4194304)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-932996575/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((713127479071759/18014398509481984), (485908199222997/9007199254740992)), (37715519/4503599627370496), by norm_num⟩
  | 1 => ⟨((-16659551/134217728), (-181622785/1073741824)), (115/4294967296), by norm_num⟩
  | 2 => ⟨((835774813/4294967296), (71184649/268435456)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-218380591/1073741824), (-1190394961/4294967296)), (193/4294967296), by norm_num⟩
  | 4 => ⟨((85591385/536870912), (933119129/4294967296)), (153/4294967296), by norm_num⟩
  | 5 => ⟨((-107348517/1073741824), (-1170315853/8589934592)), (97/4294967296), by norm_num⟩
  | 6 => ⟨((448787539/8589934592), (611586431/8589934592)), (205/17179869184), by norm_num⟩
  | 7 => ⟨((-804097561/34359738368), (-273946531/8589934592)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((630310813/68719476736), (858957763/68719476736)), (37/17179869184), by norm_num⟩
  | 9 => ⟨((-878371515/274877906944), (-598501577/137438953472)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((550825761/549755813888), (750639293/549755813888)), (133/549755813888), by norm_num⟩
  | 11 => ⟨((-628040359/2199023255552), (-855863695/2199023255552)), (153/2199023255552), by norm_num⟩
  | 12 => ⟨((328202819/4398046511104), (894518555/8796093022208)), (81/4398046511104), by norm_num⟩
  | 13 => ⟨((-316639397/17592186044416), (-431501193/17592186044416)), (79/17592186044416), by norm_num⟩
  | 14 => ⟨((141831571/35184372088832), (773125425/140737488355328)), (9/8796093022208), by norm_num⟩
  | 15 => ⟨((-237179771/281474976710656), (-323217373/281474976710656)), (61/281474976710656), by norm_num⟩
  | 16 => ⟨((92959475/562949953421312), (1013446203/4503599627370496)), (193/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (610754440239/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888898837081073/316912650057057350374175801344), (361022458485/158456325028528675187087900672)), (92343/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944324791577173/19807040628566084398385987584), (812111175229/19807040628566084398385987584)), (103895/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236044582561903/309485009821345068724781056), (862630189257/1237940039285380274899124224)), (110399/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770023214439199/154742504910672534362390528), (1724725292197/154742504910672534362390528)), (110411/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774229621424237/4835703278458516698824704), (1616361657801/9671406556917033397649408)), (103523/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831597164055/604462909807314587353088), (353437100205/151115727451828646838272)), (22649/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886237385344555/75557863725914323419136), (2296276597259/75557863725914323419136)), (147241/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296373988114261/4722366482869645213696), (1721276502039/4722366482869645213696)), (27613/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619846459544597/590295810358705651712), (1182621706507/295147905179352825856)), (151905/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821473837330225/73786976294838206464), (1477144183095/36893488147419103232)), (47483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910203885321155/4611686018427387904), (830115416609/2305843009213693952)), (213743/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397914616030889/288230376151711744), (3316575030879/1152921504606846976)), (213831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298136687290101/36028797018963968), (2897636587577/144115188075855872)), (93601/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488591292042437/36028797018963968), (4337736483133/36028797018963968)), (281001/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485458625749543/9007199254740992), (5406946493993/9007199254740992)), (351599/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220375666963297/4503599627370496), (2692088180429/1125899906842624)), (704243/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204809177811237/2251799813685248), (2004892420225/281474976710656)), (1058997/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158399086163737/2251799813685248), (31627475317127/2251799813685248)), (2128593/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158399086163737/2251799813685248), (31627475317127/2251799813685248)), (8119937905318450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034214118335601/1125899906842624), (60631245643841/2251799813685248)), (258775/140737488355328), by norm_num⟩
  | 2 => ⟨((949178340883353/1125899906842624), (55693840878787/1125899906842624)), (3914717/1125899906842624), by norm_num⟩
  | 3 => ⟨((1594880172622203/2251799813685248), (46952119954423/562949953421312)), (13975631/2251799813685248), by norm_num⟩
  | 4 => ⟨((1113940379907417/2251799813685248), (266037876805173/2251799813685248)), (22128255/2251799813685248), by norm_num⟩
  | 5 => ⟨((519623019320859/2251799813685248), (526423941874507/4503599627370496)), (54243741/4503599627370496), by norm_num⟩
  | 6 => ⟨((713127479071759/18014398509481984), (485908199222997/9007199254740992)), (37715519/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-932996575/16777216)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-1891321199/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1142568668836125/18014398509481984), (105670991825717/9007199254740992)), (42953213/9007199254740992), by norm_num⟩
  | 1 => ⟨((-54108273/268435456), (-160135317/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((687836017/2147483648), (254459329/4294967296)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((-1457319925/4294967296), (-269561815/4294967296)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((289465073/1073741824), (107085245/2147483648)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((-735948467/4294967296), (-136129069/4294967296)), (15/1073741824), by norm_num⟩
  | 6 => ⟨((194906987/2147483648), (144208503/8589934592)), (129/17179869184), by norm_num⟩
  | 7 => ⟨((-1415828335/34359738368), (-261887077/34359738368)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((562447333/34359738368), (208072807/68719476736)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((-794439067/137438953472), (-146948129/137438953472)), (69/137438953472), by norm_num⟩
  | 10 => ⟨((63119253/34359738368), (93401813/274877906944)), (89/549755813888), by norm_num⟩
  | 11 => ⟨((-1167106233/2199023255552), (-13492545/137438953472)), (105/2199023255552), by norm_num⟩
  | 12 => ⟨((618187739/4398046511104), (57173379/2199023255552)), (113/8796093022208), by norm_num⟩
  | 13 => ⟨((-302251371/8796093022208), (-223630863/35184372088832)), (7/2199023255552), by norm_num⟩
  | 14 => ⟨((548897787/70368744177664), (203060263/140737488355328)), (103/140737488355328), by norm_num⟩
  | 15 => ⟨((-465180457/281474976710656), (-172089719/562949953421312)), (89/562949953421312), by norm_num⟩
  | 16 => ⟨((1478368533/4503599627370496), (273455195/4503599627370496)), (143/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (238252429769/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888871111591601/316912650057057350374175801344), (281649239005/633825300114114700748351602688)), (23057/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118036704650843/2475880078570760549798248448), (316780787721/39614081257132168796771975168)), (103759/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145277524573/1237940039285380274899124224), (336485540397/2475880078570760549798248448)), (55123/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221244652332967/19342813113834066795298816), (336379795093/154742504910672534362390528)), (110249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774198744123411/4835703278458516698824704), (315243750483/9671406556917033397649408)), (1615/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1257777678227253/604462909807314587353088), (275726027127/604462909807314587353088)), (22611/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471537496250143/18889465931478580854784), (447844429093/75557863725914323419136)), (73487/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648154314167611/2361183241434822606848), (335699364673/4722366482869645213696)), (110235/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619756898986481/590295810358705651712), (230643953159/295147905179352825856)), (37895/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910681174828777/36893488147419103232), (576162170387/73786976294838206464)), (189485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910141491281453/4611686018427387904), (647567433857/9223372036854775808)), (3331/144115188075855872), by norm_num⟩
  | 6 => ⟨((198941808603333/144115188075855872), (323399784201/576460752303423488)), (213203/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596219571440219/72057594037927936), (565087001833/144115188075855872)), (186573/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488431656155737/36028797018963968), (845908327249/36028797018963968)), (69975/9007199254740992), by norm_num⟩
  | 3 => ⟨((371315542959133/2251799813685248), (263594621583/2251799813685248)), (349947/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219991981191813/4503599627370496), (524940919223/1125899906842624)), (700115/4503599627370496), by norm_num⟩
  | 1 => ⟨((551064131829121/562949953421312), (781814534191/562949953421312)), (65671/140737488355328), by norm_num⟩
  | 0 => ⟨((1078692121025499/1125899906842624), (48168278051/17592186044416)), (131487/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078692121025499/1125899906842624), (48168278051/17592186044416)), (501583099902105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1033455266690523/1125899906842624), (11814050143807/2251799813685248)), (2021343/1125899906842624), by norm_num⟩
  | 2 => ⟨((1897140036719911/2251799813685248), (21688059956061/2251799813685248)), (1865981/562949953421312), by norm_num⟩
  | 3 => ⟨((1598130493265945/2251799813685248), (36544355862689/2251799813685248)), (12720481/2251799813685248), by norm_num⟩
  | 4 => ⟨((566810061899633/1125899906842624), (51871972904505/2251799813685248)), (9234325/1125899906842624), by norm_num⟩
  | 5 => ⟨((1139003454672911/4503599627370496), (13056913849167/562949953421312)), (38892337/4503599627370496), by norm_num⟩
  | 6 => ⟨((1142568668836125/18014398509481984), (105670991825717/9007199254740992)), (42953213/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1891321199/33554432)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-478903789/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((120186668118597/2251799813685248), (-577802814399515/18014398509481984)), (110154893/18014398509481984), by norm_num⟩
  | 1 => ⟨((-737888261/4294967296), (443428877/4294967296)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((1187585343/4294967296), (-356835623/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-1274229917/4294967296), (765739707/4294967296)), (153/4294967296), by norm_num⟩
  | 4 => ⟨((1025396969/4294967296), (-308102629/2147483648)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((-660125103/4294967296), (793395283/8589934592)), (163/8589934592), by norm_num⟩
  | 6 => ⟨((11066983/134217728), (-425640149/8589934592)), (89/8589934592), by norm_num⟩
  | 7 => ⟨((-1302792925/34359738368), (782904449/34359738368)), (83/17179869184), by norm_num⟩
  | 8 => ⟨((1048382163/68719476736), (-630018051/68719476736)), (135/68719476736), by norm_num⟩
  | 9 => ⟨((-374956889/68719476736), (56331941/17179869184)), (49/68719476736), by norm_num⟩
  | 10 => ⟨((241387933/137438953472), (-290120837/274877906944)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-35318081/68719476736), (339586527/1099511627776)), (19/274877906944), by norm_num⟩
  | 12 => ⟨((1212634849/8796093022208), (-728724575/8796093022208)), (165/8796093022208), by norm_num⟩
  | 13 => ⟨((-600510923/17592186044416), (721745821/35184372088832)), (165/35184372088832), by norm_num⟩
  | 14 => ⟨((1104554339/140737488355328), (-5185737/1099511627776)), (77/70368744177664), by norm_num⟩
  | 15 => ⟨((-948112869/562949953421312), (284880955/281474976710656)), (67/281474976710656), by norm_num⟩
  | 16 => ⟨((381482199/1125899906842624), (-229249105/1125899906842624)), (55/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-704859688085/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888843838671029/316912650057057350374175801344), (-416599416227/316912650057057350374175801344)), (46141/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888525906856471/39614081257132168796771975168), (-468562577653/19807040628566084398385987584)), (6489/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888225346074859/2475880078570760549798248448), (-995413674239/2475880078570760549798248448)), (110319/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769892003024849/154742504910672534362390528), (-995096816305/154742504910672534362390528)), (55163/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96771021344975/604462909807314587353088), (-466283372349/4835703278458516698824704)), (51719/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257724167792497/604462909807314587353088), (-815659539701/604462909807314587353088)), (22629/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471515754341265/18889465931478580854784), (-1324816410437/75557863725914323419136)), (147101/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296243391113679/4722366482869645213696), (-993061095743/4722366482869645213696)), (55169/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619667179196439/590295810358705651712), (-1364563918057/590295810358705651712)), (75867/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821250172124603/73786976294838206464), (-1704363368131/73786976294838206464)), (189697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910078372407355/4611686018427387904), (-478891494401/2305843009213693952)), (106725/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795704091920461/576460752303423488), (-956632573711/576460752303423488)), (213501/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298082147694053/36028797018963968), (-52235070505/4503599627370496)), (186871/144115188075855872), by norm_num⟩
  | 4 => ⟨((744132861757253/18014398509481984), (-2502123089739/36028797018963968)), (140211/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485054575425329/9007199254740992), (-389830501327/1125899906842624)), (350731/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219576255457299/4503599627370496), (-3105170464069/2251799813685248)), (175519/1125899906842624), by norm_num⟩
  | 1 => ⟨((275453954683751/281474976710656), (-9248431405423/2251799813685248)), (1054659/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156129442210353/2251799813685248), (-18230262402887/2251799813685248)), (2115573/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156129442210353/2251799813685248), (-18230262402887/2251799813685248)), (8070270546920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064376149623759/2251799813685248), (-34911456397855/2251799813685248)), (1021409/562949953421312), by norm_num⟩
  | 2 => ⟨((118250689166921/140737488355328), (-16002838595677/562949953421312)), (7617841/2251799813685248), by norm_num⟩
  | 3 => ⟨((793944526023825/1125899906842624), (-107567455675383/2251799813685248)), (3308613/562949953421312), by norm_num⟩
  | 4 => ⟨((1114584373281739/2251799813685248), (-75852739744225/1125899906842624)), (19929337/2251799813685248), by norm_num⟩
  | 5 => ⟨((270735383591131/1125899906842624), (-300361614298765/4503599627370496)), (22414353/2251799813685248), by norm_num⟩
  | 6 => ⟨((120186668118597/2251799813685248), (-577802814399515/18014398509481984)), (110154893/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-478903789/8388608)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-15148095/262144)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((355575044949177/18014398509481984), (-128060958825239/2251799813685248)), (2447587/281474976710656), by norm_num⟩
  | 1 => ⟨((-276207405/4294967296), (795812543/4294967296)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((449955195/4294967296), (-648208523/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-488665821/4294967296), (703975315/2147483648)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((398030105/4294967296), (-143351221/536870912)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((-518728203/8589934592), (747283387/4294967296)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((4401215/134217728), (-811573805/8589934592)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((-65552381/4294967296), (1510963317/34359738368)), (31/4294967296), by norm_num⟩
  | 8 => ⟨((427151971/68719476736), (-153839511/8589934592)), (51/17179869184), by norm_num⟩
  | 9 => ⟨((-309267191/137438953472), (445532425/68719476736)), (149/137438953472), by norm_num⟩
  | 10 => ⟨((201524473/274877906944), (-1161270121/549755813888)), (49/137438953472), by norm_num⟩
  | 11 => ⟨((-119379307/549755813888), (687914575/1099511627776)), (235/2199023255552), by norm_num⟩
  | 12 => ⟨((129649769/2199023255552), (-747097365/4398046511104)), (257/8796093022208), by norm_num⟩
  | 13 => ⟨((-64986379/4398046511104), (374479283/8796093022208)), (65/8796093022208), by norm_num⟩
  | 14 => ⟨((120989655/35184372088832), (-697194089/70368744177664)), (61/35184372088832), by norm_num⟩
  | 15 => ⟨((-105118927/140737488355328), (605740173/281474976710656)), (107/281474976710656), by norm_num⟩
  | 16 => ⟨((85621903/562949953421312), (-246694995/562949953421312)), (11/140737488355328), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (-805488679111/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777634017869617/633825300114114700748351602688), (-1904193775381/633825300114114700748351602688)), (23097/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888465468655791/39614081257132168796771975168), (-2141699428889/39614081257132168796771975168)), (103949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888161033004441/2475880078570760549798248448), (-568725890373/618970019642690137449562112)), (27615/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769827580442129/154742504910672534362390528), (-2274170336515/154742504910672534362390528)), (110475/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774137914550549/4835703278458516698824704), (-2131255952057/9671406556917033397649408)), (25897/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628835551651301/302231454903657293676544), (-1864070571993/604462909807314587353088)), (2833/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1885976570099231/75557863725914323419136), (-3027655954043/75557863725914323419136)), (147347/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296178365640227/4722366482869645213696), (-1134733164381/2361183241434822606848)), (55269/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619577460871935/590295810358705651712), (-3118444693901/590295810358705651712)), (76017/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821137562628735/73786976294838206464), (-3894951056199/73786976294838206464)), (190109/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910014712918381/4611686018427387904), (-547194350311/1152921504606846976)), (213965/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591280075327835/1152921504606846976), (-1093057336619/288230376151711744)), (214081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192215610459701/144115188075855872), (-1909858865391/72057594037927936)), (187451/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488094489436347/36028797018963968), (-2858815574903/18014398509481984)), (281437/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484837462521557/9007199254740992), (-7126180337643/9007199254740992)), (352255/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219132882498967/4503599627370496), (-7094984108143/2251799813685248)), (705887/4503599627370496), by norm_num⟩
  | 1 => ⟨((137683995768789/140737488355328), (-21129611131403/2251799813685248)), (531145/1125899906842624), by norm_num⟩
  | 0 => ⟨((33666637086229/35184372088832), (-41641683370445/2251799813685248)), (1069251/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((33666637086229/35184372088832), (-41641683370445/2251799813685248)), (4078868870261764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257618718382717/281474976710656), (-79690803527935/2251799813685248)), (4171603/2251799813685248), by norm_num⟩
  | 2 => ⟨((941727415103989/1125899906842624), (-4558540805223/70368744177664)), (1982837/562949953421312), by norm_num⟩
  | 3 => ⟨((391478302674645/562949953421312), (-61005818695729/562949953421312)), (7147753/1125899906842624), by norm_num⟩
  | 4 => ⟨((1062499788064633/2251799813685248), (-169695044549777/1125899906842624)), (5745173/562949953421312), by norm_num⟩
  | 5 => ⟨((900364375996065/4503599627370496), (-320278823675147/2251799813685248)), (57227823/4503599627370496), by norm_num⟩
  | 6 => ⟨((355575044949177/18014398509481984), (-128060958825239/2251799813685248)), (2447587/281474976710656), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-15148095/262144)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-980708079/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-86350419967343/4503599627370496), (-247813517582569/4503599627370496)), (185085101/18014398509481984), by norm_num⟩
  | 1 => ⟨((542825503/8589934592), (1557832579/8589934592)), (293/8589934592), by norm_num⟩
  | 2 => ⟨((-111816519/1073741824), (-1283590511/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((491372007/4294967296), (1410168309/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-202435247/2147483648), (-1161921175/4294967296)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((66719355/1073741824), (765900529/4294967296)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((-293194813/8589934592), (-841427733/8589934592)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((138046039/8589934592), (396172649/8589934592)), (311/34359738368), by norm_num⟩
  | 8 => ⟨((-454977225/68719476736), (-652860211/34359738368)), (129/34359738368), by norm_num⟩
  | 9 => ⟨((333229047/137438953472), (478160167/68719476736)), (95/68719476736), by norm_num⟩
  | 10 => ⟨((-439307431/549755813888), (-1260750325/549755813888)), (63/137438953472), by norm_num⟩
  | 11 => ⟨((65812983/274877906944), (755495891/1099511627776)), (19/137438953472), by norm_num⟩
  | 12 => ⟨((-9037869/137438953472), (-414998535/2199023255552)), (169/4398046511104), by norm_num⟩
  | 13 => ⟨((146645375/8796093022208), (841703059/17592186044416)), (173/17592186044416), by norm_num⟩
  | 14 => ⟨((-276182419/70368744177664), (-1585209127/140737488355328)), (41/17592186044416), by norm_num⟩
  | 15 => ⟨((485467839/562949953421312), (696612091/281474976710656)), (145/281474976710656), by norm_num⟩
  | 16 => ⟨((-100001425/562949953421312), (-1147959905/2251799813685248)), (241/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-2482893624509/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55549413259339/19807040628566084398385987584), (-2934650982543/633825300114114700748351602688)), (46245/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944202972383847/19807040628566084398385987584), (-3300669579955/39614081257132168796771975168)), (52035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888097610211343/2475880078570760549798248448), (-3505944291627/2475880078570760549798248448)), (110595/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769763956924897/154742504910672534362390528), (-1752400251699/77371252455336267181195264)), (27655/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548215968980915/9671406556917033397649408), (-3284535646847/9671406556917033397649408)), (25933/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628809256423037/302231454903657293676544), (-2872754371971/604462909807314587353088)), (90791/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885890711981177/75557863725914323419136), (-1166487520321/18889465931478580854784)), (147583/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648056811861731/2361183241434822606848), (-3497472333977/4722366482869645213696)), (55365/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619487875582809/590295810358705651712), (-4805792354153/590295810358705651712)), (76161/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821024734824809/73786976294838206464), (-6002395807283/73786976294838206464)), (95253/36893488147419103232), by norm_num⟩
  | 7 => ⟨((454975333384569/2305843009213693952), (-843254953679/1152921504606846976)), (107231/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795575267746563/576460752303423488), (-6737728635761/1152921504606846976)), (13415/72057594037927936), by norm_num⟩
  | 5 => ⟨((298025159938949/36028797018963968), (-5886174466691/144115188075855872)), (94005/72057594037927936), by norm_num⟩
  | 4 => ⟨((92994924967453/2251799813685248), (-2202653733893/9007199254740992)), (282417/36028797018963968), by norm_num⟩
  | 3 => ⟨((742306109730241/4503599627370496), (-2745175732423/2251799813685248)), (88431/2251799813685248), by norm_num⟩
  | 2 => ⟨((554666404748187/1125899906842624), (-10931986303447/2251799813685248)), (177391/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202201492441335/2251799813685248), (-32553297750277/2251799813685248)), (1069653/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153016094607277/2251799813685248), (-64141467398271/2251799813685248)), (1080323/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153016094607277/2251799813685248), (-64141467398271/2251799813685248)), (4121105198386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1028369428679003/1125899906842624), (-122655318470959/2251799813685248)), (4254813/2251799813685248), by norm_num⟩
  | 2 => ⟨((58496685276481/70368744177664), (-56015183505141/562949953421312)), (2059001/562949953421312), by norm_num⟩
  | 3 => ⟨((191723507532487/281474976710656), (-93129488055995/562949953421312)), (15331995/2251799813685248), by norm_num⟩
  | 4 => ⟨((983096355019105/2251799813685248), (-507472808089921/2251799813685248)), (25959213/2251799813685248), by norm_num⟩
  | 5 => ⟨((314836953086397/2251799813685248), (-886214955472495/4503599627370496)), (68734357/4503599627370496), by norm_num⟩
  | 6 => ⟨((-86350419967343/4503599627370496), (-247813517582569/4503599627370496)), (185085101/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-980708079/16777216)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile007Terms3
