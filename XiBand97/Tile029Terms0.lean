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
namespace Reinmann.XiBand97.Tile029Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6223/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6223/256))
  have he : value ((69/80), (6223/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1130746323/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-515530560656167/2251799813685248), (1126089680914215/2251799813685248)), (107000523/2251799813685248), by norm_num⟩
  | 1 => ⟨((170392301/1073741824), (-372193283/1073741824)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-118106943/2147483648), (1031938899/8589934592)), (103/8589934592), by norm_num⟩
  | 3 => ⟨((436615971/34359738368), (-953714051/34359738368)), (97/34359738368), by norm_num⟩
  | 4 => ⟨((-605278259/274877906944), (1322128411/274877906944)), (137/274877906944), by norm_num⟩
  | 5 => ⟨((335637535/1099511627776), (-1466287329/2199023255552)), (77/1099511627776), by norm_num⟩
  | 6 => ⟨((-77548737/2199023255552), (1355137237/17592186044416)), (145/17592186044416), by norm_num⟩
  | 7 => ⟨((491453151/140737488355328), (-536748317/70368744177664)), (117/140737488355328), by norm_num⟩
  | 8 => ⟨((-170324683/562949953421312), (744091165/1125899906842624)), (83/1125899906842624), by norm_num⟩
  | 9 => ⟨((419769151/18014398509481984), (-458457505/9007199254740992)), (13/2251799813685248), by norm_num⟩
  | 10 => ⟨((-232769443/144115188075855872), (508445643/144115188075855872)), (59/144115188075855872), by norm_num⟩
  | 11 => ⟨((117340715/1152921504606846976), (-1025244113/4611686018427387904)), (121/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-433783391/73786976294838206464), (947526755/73786976294838206464)), (57/36893488147419103232), by norm_num⟩
  | 13 => ⟨((185031221/590295810358705651712), (-808339075/1180591620717411303424)), (99/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-293151701/18889465931478580854784), (640340515/18889465931478580854784)), (159/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((13546485/18889465931478580854784), (-946880475/604462909807314587353088)), (119/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-600941305/19342813113834066795298816), (1312655063/19342813113834066795298816)), (167/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2605383122707/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445260833739069/158456325028528675187087900672), (96589070911/19807040628566084398385987584)), (11563/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946150087352809/19807040628566084398385987584), (3477009140183/39614081257132168796771975168)), (52043/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946117232815487/1237940039285380274899124224), (461761941955/309485009821345068724781056)), (55307/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773899952838483/154742504910672534362390528), (3693840448705/154742504910672534362390528)), (6915/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552092551916085/9671406556917033397649408), (3462704323783/9671406556917033397649408)), (12969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630504804835209/302231454903657293676544), (3029595111083/604462909807314587353088)), (22703/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236424941495915/9444732965739290427392), (4922583447543/75557863725914323419136)), (4613/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((650121870191637/2361183241434822606848), (3691492393725/4722366482869645213696)), (27689/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((203145543895829/73786976294838206464), (5075078304733/590295810358705651712)), (76181/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914058338502959/36893488147419103232), (1585690437937/18446744073709551616)), (5955/4611686018427387904), by norm_num⟩
  | 7 => ⟨((114242171655125/576460752303423488), (7134112691931/9223372036854775808)), (419/36028797018963968), by norm_num⟩
  | 6 => ⟨((399779417695527/288230376151711744), (3566121783917/576460752303423488)), (107357/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149883102573449/18014398509481984), (6238608605151/144115188075855872)), (47021/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498350945206747/36028797018963968), (9353699499719/36028797018963968)), (141271/36028797018963968), by norm_num⟩
  | 3 => ⟨((374406920271813/2251799813685248), (5842370541635/4503599627370496)), (88477/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122311188806311/2251799813685248), (2918411632551/562949953421312)), (5547/70368744177664), by norm_num⟩
  | 1 => ⟨((1120475605097071/1125899906842624), (17482664930965/1125899906842624)), (133815/562949953421312), by norm_num⟩
  | 0 => ⟨((1114886907020539/1125899906842624), (34853700909303/1125899906842624)), (16899/35184372088832), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114886907020539/1125899906842624), (34853700909303/1125899906842624)), (64464569226014603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((551451344578679/562949953421312), (8628194781977/140737488355328)), (552219/562949953421312), by norm_num⟩
  | 2 => ⟨((1076143453511595/1125899906842624), (135231335144907/1125899906842624)), (2299179/1125899906842624), by norm_num⟩
  | 3 => ⟨((506171646166637/562949953421312), (129255109749437/562949953421312)), (1236863/281474976710656), by norm_num⟩
  | 4 => ⟨((26590158073903/35184372088832), (464874515254521/1125899906842624)), (11168821/1125899906842624), by norm_num⟩
  | 5 => ⟨((112775803721267/281474976710656), (175661609278375/281474976710656)), (26104423/1125899906842624), by norm_num⟩
  | 6 => ⟨((-515530560656167/2251799813685248), (1126089680914215/2251799813685248)), (107000523/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1130746323/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1792190519/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1905103103957/2251799813685248), (-218248703044497/562949953421312)), (207061515/4503599627370496), by norm_num⟩
  | 1 => ⟨((3992023/4294967296), (914652661/2147483648)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((-2192843/4294967296), (-2009697307/8589934592)), (243/8589934592), by norm_num⟩
  | 3 => ⟨((200757/1073741824), (367979693/4294967296)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((-1764433/34359738368), (-1617068051/68719476736)), (25/8589934592), by norm_num⟩
  | 5 => ⟨((775371/68719476736), (710612333/137438953472)), (89/137438953472), by norm_num⟩
  | 6 => ⟨((-4543105/2199023255552), (-1040916589/1099511627776)), (33/274877906944), by norm_num⟩
  | 7 => ⟨((2852063/8796093022208), (1306930007/8796093022208)), (21/1099511627776), by norm_num⟩
  | 8 => ⟨((-3133311/70368744177664), (-717904683/35184372088832)), (187/70368744177664), by norm_num⟩
  | 9 => ⟨((3059817/562949953421312), (701065695/281474976710656)), (185/562949953421312), by norm_num⟩
  | 10 => ⟨((-1344621/2251799813685248), (-1232319021/4503599627370496)), (165/4503599627370496), by norm_num⟩
  | 11 => ⟨((4297359/72057594037927936), (1969223011/72057594037927936)), (133/36028797018963968), by norm_num⟩
  | 12 => ⟨((-3147421/576460752303423488), (-721137533/288230376151711744)), (197/576460752303423488), by norm_num⟩
  | 13 => ⟨((1063937/2305843009213693952), (975077607/4611686018427387904)), (269/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-2671667/73786976294838206464), (-1224265419/73786976294838206464)), (171/73786976294838206464), by norm_num⟩
  | 15 => ⟨((3130801/1180591620717411303424), (1434659237/1180591620717411303424)), (203/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-214971/1180591620717411303424), (-394033567/4722366482869645213696)), (113/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-512245057729/2535301200456458802993406410752)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780505008902933/633825300114114700748351602688), (-2429371997717/633825300114114700748351602688)), (34665/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891694721239561/39614081257132168796771975168), (-1366403462159/19807040628566084398385987584)), (78007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945795683152469/1237940039285380274899124224), (-2903325982591/2475880078570760549798248448)), (5181/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((110828567054697/9671406556917033397649408), (-1451504714459/77371252455336267181195264)), (82911/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775745042506969/4835703278458516698824704), (-2721235005595/9671406556917033397649408)), (4859/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260482684183951/604462909807314587353088), (-2380744300669/604462909807314587353088)), (34021/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890543715003515/75557863725914323419136), (-1934039440751/37778931862957161709568)), (55299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324900564992647/1180591620717411303424), (-725126847547/1180591620717411303424)), (82975/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624282936810747/590295810358705651712), (-3987301053065/590295810358705651712)), (114133/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913507920401905/36893488147419103232), (-2491390718843/36893488147419103232)), (71365/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826637586779175/9223372036854775808), (-2801889982447/4611686018427387904)), (80329/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597882112176455/1152921504606846976), (-2800734304167/576460752303423488)), (160767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197985507788149/144115188075855872), (-4898684872757/144115188075855872)), (140795/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496735577329599/36028797018963968), (-1835706821139/9007199254740992)), (211439/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495614772104387/9007199254740992), (-1146179341691/1125899906842624)), (132365/4503599627370496), by norm_num⟩
  | 2 => ⟨((560153864094171/1125899906842624), (-9155787037573/2251799813685248)), (132689/1125899906842624), by norm_num⟩
  | 1 => ⟨((558747012344269/562949953421312), (-6849783088519/562949953421312)), (399687/1125899906842624), by norm_num⟩
  | 0 => ⟨((1109018124818629/1125899906842624), (-13631352369609/562949953421312)), (50367/70368744177664), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109018124818629/1125899906842624), (-13631352369609/562949953421312)), (192134857446169831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((136466165712893/140737488355328), (-53707853608691/1125899906842624)), (813303/562949953421312), by norm_num⟩
  | 2 => ⟨((528016913330815/562949953421312), (-13019460799497/140737488355328)), (103427/35184372088832), by norm_num⟩
  | 3 => ⟨((122608482926999/140737488355328), (-195384913711847/1125899906842624)), (6820923/1125899906842624), by norm_num⟩
  | 4 => ⟨((410305789777995/562949953421312), (-340433073475767/1125899906842624)), (7125971/562949953421312), by norm_num⟩
  | 5 => ⟨((990334369151249/2251799813685248), (-496248947993027/1125899906842624)), (7348407/281474976710656), by norm_num⟩
  | 6 => ⟨((-1905103103957/2251799813685248), (-218248703044497/562949953421312)), (207061515/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1792190519/67108864)), (3/67108864), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1130746323/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-890226746089451/4503599627370496), (-128904363749987/562949953421312)), (121976849/2251799813685248), by norm_num⟩
  | 1 => ⟨((294236259/1073741824), (170421021/536870912)), (163/2147483648), by norm_num⟩
  | 2 => ⟨((-815796133/4294967296), (-472507401/2147483648)), (57/1073741824), by norm_num⟩
  | 3 => ⟨((753955719/8589934592), (109172391/1073741824)), (213/8589934592), by norm_num⟩
  | 4 => ⟨((-522602281/17179869184), (-75672535/2147483648)), (149/17179869184), by norm_num⟩
  | 5 => ⟨((144896119/17179869184), (671388215/68719476736)), (167/68719476736), by norm_num⟩
  | 6 => ⟨((-267824897/137438953472), (-4847613/2147483648)), (39/68719476736), by norm_num⟩
  | 7 => ⟨((848649473/2199023255552), (983071973/2199023255552)), (249/2199023255552), by norm_num⟩
  | 8 => ⟨((-294119495/4398046511104), (-340706783/4398046511104)), (175/8796093022208), by norm_num⟩
  | 9 => ⟨((724864351/70368744177664), (13119997/1099511627776)), (217/70368744177664), by norm_num⟩
  | 10 => ⟨((-401950145/281474976710656), (-465617353/281474976710656)), (243/562949953421312), by norm_num⟩
  | 11 => ⟨((101312949/562949953421312), (938883943/4503599627370496)), (247/4503599627370496), by norm_num⟩
  | 12 => ⟨((-749064373/36028797018963968), (-867713011/36028797018963968)), (115/18014398509481984), by norm_num⟩
  | 13 => ⟨((639029979/288230376151711744), (740249633/288230376151711744)), (99/144115188075855872), by norm_num⟩
  | 14 => ⟨((-15819351/72057594037927936), (-36650139/144115188075855872)), (79/1152921504606846976), by norm_num⟩
  | 15 => ⟨((374276729/18446744073709551616), (433560585/18446744073709551616)), (59/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-518857719/295147905179352825856), (-300521297/147573952589676412928)), (165/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-371723017309/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780118389281659/633825300114114700748351602688), (-1762211977807/316912650057057350374175801344)), (92547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891259612216327/39614081257132168796771975168), (-3964540288483/39614081257132168796771975168)), (104137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891128856383133/2475880078570760549798248448), (-1052952087961/618970019642690137449562112)), (6917/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772794330660765/154742504910672534362390528), (-4211228116575/154742504910672534362390528)), (27675/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551056017501389/9671406556917033397649408), (-3947409836291/9671406556917033397649408)), (25953/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260102628563663/604462909807314587353088), (-3453367057829/604462909807314587353088)), (90867/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944962831321111/37778931862957161709568), (-5610565384815/75557863725914323419136)), (36929/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299138316765477/4722366482869645213696), (-4206912410247/4722366482869645213696)), (110837/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623644359067323/590295810358705651712), (-2891430282899/295147905179352825856)), (152483/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456554158960941/18446744073709551616), (-1806527382947/18446744073709551616)), (190727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228217141432211/1152921504606846976), (-4062990972133/4611686018427387904)), (107369/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596979972050729/1152921504606846976), (-8121742416625/1152921504606846976)), (107475/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197194243034619/144115188075855872), (-887719320077/18014398509481984)), (5885/4503599627370496), by norm_num⟩
  | 4 => ⟨((1495544904062341/36028797018963968), (-10643090282915/36028797018963968)), (282957/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494119840609889/9007199254740992), (-13287161900521/9007199254740992)), (88633/2251799813685248), by norm_num⟩
  | 2 => ⟨((559401474232809/1125899906842624), (-13262104108093/2251799813685248)), (355789/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115212362669383/1125899906842624), (-9915244908985/562949953421312)), (536829/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104357599084983/1125899906842624), (-39410186326775/1125899906842624)), (1086271/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104357599084983/1125899906842624), (-39410186326775/1125899906842624)), (4143795017722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((540923991763281/562949953421312), (-38656134960861/562949953421312)), (2207021/1125899906842624), by norm_num⟩
  | 2 => ⟨((1034210825761085/1125899906842624), (-74287352550929/562949953421312)), (4544439/1125899906842624), by norm_num⟩
  | 3 => ⟨((930382516917413/1125899906842624), (-272950672642839/1125899906842624)), (9548091/1125899906842624), by norm_num⟩
  | 4 => ⟨((351323218556755/562949953421312), (-225551607442527/562949953421312)), (20409515/1125899906842624), by norm_num⟩
  | 5 => ⟨((257765280328107/1125899906842624), (-281522420228549/562949953421312)), (83657423/2251799813685248), by norm_num⟩
  | 6 => ⟨((-890226746089451/4503599627370496), (-128904363749987/562949953421312)), (121976849/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1130746323/33554432)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1312755827/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((82157007297919/2251799813685248), (-555873270360113/2251799813685248)), (170542389/4503599627370496), by norm_num⟩
  | 1 => ⟨((-252202229/4294967296), (1706397087/4294967296)), (33/536870912), by norm_num⟩
  | 2 => ⟨((202951915/4294967296), (-1373170083/4294967296)), (107/2147483648), by norm_num⟩
  | 3 => ⟨((-54439751/2147483648), (1473354661/8589934592)), (29/1073741824), by norm_num⟩
  | 4 => ⟨((87617399/8589934592), (-1185636425/17179869184)), (189/17179869184), by norm_num⟩
  | 5 => ⟨((-112811811/34359738368), (763283285/34359738368)), (245/68719476736), by norm_num⟩
  | 6 => ⟨((242084807/274877906944), (-1637942743/274877906944)), (265/274877906944), by norm_num⟩
  | 7 => ⟨((-222640267/1099511627776), (376595307/274877906944)), (123/549755813888), by norm_num⟩
  | 8 => ⟨((179162843/4398046511104), (-606106765/2199023255552)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-64078105/8796093022208), (867103295/17592186044416)), (9/1099511627776), by norm_num⟩
  | 10 => ⟨((82503785/70368744177664), (-558219567/70368744177664)), (187/140737488355328), by norm_num⟩
  | 11 => ⟨((-96570705/562949953421312), (1306792341/1125899906842624)), (221/1125899906842624), by norm_num⟩
  | 12 => ⟨((207232739/9007199254740992), (-350533523/2251799813685248)), (239/9007199254740992), by norm_num⟩
  | 13 => ⟨((-51312035/18014398509481984), (694353159/36028797018963968)), (239/72057594037927936), by norm_num⟩
  | 14 => ⟨((188762365/576460752303423488), (-638581885/288230376151711744)), (111/288230376151711744), by norm_num⟩
  | 15 => ⟨((-40506841/1152921504606846976), (1096275089/4611686018427387904)), (3/72057594037927936), by norm_num⟩
  | 16 => ⟨((260772983/73786976294838206464), (-1764386691/73786976294838206464)), (311/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-1854997836861/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779825362969951/633825300114114700748351602688), (-2197780640117/633825300114114700748351602688)), (361/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((945465118176863/19807040628566084398385987584), (-618048882117/9903520314283042199192993792)), (51991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890779240333467/2475880078570760549798248448), (-2626335312143/2475880078570760549798248448)), (110497/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772445103532395/154742504910672534362390528), (-656479092903/38685626227668133590597632)), (110515/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550729030168069/9671406556917033397649408), (-2461351535711/9671406556917033397649408)), (103627/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259816927601125/604462909807314587353088), (-2153237600389/604462909807314587353088)), (90693/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944731086279035/37778931862957161709568), (-874544221347/18889465931478580854784)), (147411/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649395688062923/2361183241434822606848), (-163931429563/295147905179352825856)), (55295/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623168415109127/590295810358705651712), (-3605305816163/590295810358705651712)), (152113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825623354014085/73786976294838206464), (-1126213575561/18446744073709551616)), (95109/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825071953914097/9223372036854775808), (-5065517169589/9223372036854775808)), (214101/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596317622679341/1152921504606846976), (-2531231723677/576460752303423488)), (214233/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149577233203799/18014398509481984), (-1106555424793/36028797018963968)), (187603/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494686686052613/36028797018963968), (-1658117241269/9007199254740992)), (140851/18014398509481984), by norm_num⟩
  | 3 => ⟨((746529079076869/4503599627370496), (-8278584049897/9007199254740992)), (352649/9007199254740992), by norm_num⟩
  | 2 => ⟨((558878931434205/1125899906842624), (-1032574880833/281474976710656)), (44179/281474976710656), by norm_num⟩
  | 1 => ⟨((556843046319283/562949953421312), (-6172999939163/562949953421312)), (532109/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101469689838821/1125899906842624), (-3064098492231/140737488355328)), (1072081/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101469689838821/1125899906842624), (-3064098492231/140737488355328)), (4089664463523482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538517941733271/562949953421312), (-95923599470589/2251799813685248)), (33505/17592186044416), by norm_num⟩
  | 2 => ⟨((2056498900132741/2251799813685248), (-11470064753671/140737488355328)), (1071301/281474976710656), by norm_num⟩
  | 3 => ⟨((465794931022845/562949953421312), (-167604067871535/1125899906842624)), (4262787/562949953421312), by norm_num⟩
  | 4 => ⟨((46616518839483/70368744177664), (-554714498217165/2251799813685248)), (16646701/1125899906842624), by norm_num⟩
  | 5 => ⟨((425780755113045/1125899906842624), (-734952972626241/2251799813685248)), (60514309/2251799813685248), by norm_num⟩
  | 6 => ⟨((82157007297919/2251799813685248), (-555873270360113/2251799813685248)), (170542389/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1312755827/33554432)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1461468421/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((437007136414179/2251799813685248), (198912081484085/2251799813685248)), (42556657/4503599627370496), by norm_num⟩
  | 1 => ⟨((-186684531/536870912), (-339892011/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((1337975105/4294967296), (609004729/4294967296)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((-799109855/4294967296), (-363729997/4294967296)), (43/4294967296), by norm_num⟩
  | 4 => ⟨((715906325/8589934592), (325858333/8589934592)), (79/17179869184), by norm_num⟩
  | 5 => ⟨((-513092775/17179869184), (-467087803/34359738368)), (29/17179869184), by norm_num⟩
  | 6 => ⟨((612892559/68719476736), (557939329/137438953472)), (71/137438953472), by norm_num⟩
  | 7 => ⟨((-627517741/274877906944), (-285626593/274877906944)), (75/549755813888), by norm_num⟩
  | 8 => ⟨((1124360855/2199023255552), (511774153/2199023255552)), (69/2199023255552), by norm_num⟩
  | 9 => ⟨((-111921345/1099511627776), (-407544971/8796093022208)), (57/8796093022208), by norm_num⟩
  | 10 => ⟨((641715615/35184372088832), (584178049/70368744177664)), (21/17592186044416), by norm_num⟩
  | 11 => ⟨((-209054551/70368744177664), (-95155141/70368744177664)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((249716981/562949953421312), (454653667/2251799813685248)), (69/2251799813685248), by norm_num⟩
  | 13 => ⟨((-1101372961/18014398509481984), (-501310777/18014398509481984)), (39/9007199254740992), by norm_num⟩
  | 14 => ⟨((1127654533/144115188075855872), (513273333/144115188075855872)), (41/72057594037927936), by norm_num⟩
  | 15 => ⟨((-1077592367/1152921504606846976), (-490486589/1152921504606846976)), (5/72057594037927936), by norm_num⟩
  | 16 => ⟨((241348291/2305843009213693952), (439416995/9223372036854775808)), (73/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (556402891791/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792525707555/316912650057057350374175801344), (164762254555/158456325028528675187087900672)), (23067/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118166253659659/2475880078570760549798248448), (370664443495/19807040628566084398385987584)), (25951/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472623098224301/618970019642690137449562112), (787537754343/2475880078570760549798248448)), (13787/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772158499525963/154742504910672534362390528), (787398078331/154742504910672534362390528)), (55151/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460597457499/9671406556917033397649408), (184509331717/2417851639229258349412352)), (51707/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629791153706883/302231454903657293676544), (161408581979/151115727451828646838272)), (22623/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889081399082149/75557863725914323419136), (262219435011/18889465931478580854784)), (36765/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649253109785259/2361183241434822606848), (196603774817/1180591620717411303424)), (55153/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811388506337439/295147905179352825856), (270231426315/147573952589676412928)), (75843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456283782985517/18446744073709551616), (675282407547/36893488147419103232)), (47407/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824524120412177/9223372036854775808), (759285708443/4611686018427387904)), (53341/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595771557706417/1152921504606846976), (758777284493/576460752303423488)), (106701/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598071022893969/72057594037927936), (1326717190155/144115188075855872)), (46693/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493976923846989/36028797018963968), (1987791908403/36028797018963968)), (35031/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492177884105615/9007199254740992), (2480748132751/9007199254740992)), (87617/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233775905779071/4503599627370496), (2474770554239/2251799813685248)), (21919/281474976710656), by norm_num⟩
  | 1 => ⟨((556203518274789/562949953421312), (1848623502393/562949953421312)), (526649/2251799813685248), by norm_num⟩
  | 0 => ⟨((68688387931155/70368744177664), (7335068962625/1125899906842624)), (527843/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((68688387931155/70368744177664), (7335068962625/1125899906842624)), (2013561253074264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1072722731734651/1125899906842624), (28639650645719/2251799813685248)), (1037355/1125899906842624), by norm_num⟩
  | 2 => ⟨((1021875030622765/1125899906842624), (54573952959561/2251799813685248)), (4006215/2251799813685248), by norm_num⟩
  | 3 => ⟨((926799969325093/1125899906842624), (99063441630699/2251799813685248)), (933291/281474976710656), by norm_num⟩
  | 4 => ⟨((1521458144846945/2251799813685248), (40772716165347/562949953421312)), (6474477/1125899906842624), by norm_num⟩
  | 5 => ⟨((127022628881041/281474976710656), (220388973194829/2251799813685248)), (1210873/140737488355328), by norm_num⟩
  | 6 => ⟨((437007136414179/2251799813685248), (198912081484085/2251799813685248)), (42556657/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1461468421/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1587203127/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1654782100276959/9007199254740992), (149234967544141/4503599627370496)), (141819415/4503599627370496), by norm_num⟩
  | 1 => ⟨((383860741/1073741824), (-4327265/67108864)), (265/4294967296), by norm_num⟩
  | 2 => ⟨((-46684907/134217728), (67363751/1073741824)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((969009433/4294967296), (-174778409/4294967296)), (85/2147483648), by norm_num⟩
  | 4 => ⟨((-942802645/8589934592), (42512885/2147483648)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((1467687389/34359738368), (-132362007/17179869184)), (131/17179869184), by norm_num⟩
  | 6 => ⟨((-951995929/68719476736), (171709715/68719476736)), (171/68719476736), by norm_num⟩
  | 7 => ⟨((529285297/137438953472), (-190932387/274877906944)), (3/4294967296), by norm_num⟩
  | 8 => ⟨((-1029941631/1099511627776), (185768635/1099511627776)), (47/274877906944), by norm_num⟩
  | 9 => ⟨((1781487887/8796093022208), (-80330905/2199023255552)), (327/8796093022208), by norm_num⟩
  | 10 => ⟨((-10833173/274877906944), (250106757/35184372088832)), (1/137438953472), by norm_num⟩
  | 11 => ⟨((981195929/140737488355328), (-11061029/8796093022208)), (183/140737488355328), by norm_num⟩
  | 12 => ⟨((-1272879411/1125899906842624), (229586865/1125899906842624)), (239/1125899906842624), by norm_num⟩
  | 13 => ⟨((1524251671/9007199254740992), (-274926407/9007199254740992)), (9/281474976710656), by norm_num⟩
  | 14 => ⟨((-847444799/36028797018963968), (305704049/72057594037927936)), (161/36028797018963968), by norm_num⟩
  | 15 => ⟨((879494099/288230376151711744), (-317265393/576460752303423488)), (21/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1711416493/4611686018427387904), (154342487/2305843009213693952)), (329/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (964956204489/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779368998035157/633825300114114700748351602688), (4570889378887/633825300114114700748351602688)), (46325/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890416401592917/39614081257132168796771975168), (2570729275357/19807040628566084398385987584)), (26065/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472558185649673/618970019642690137449562112), (5461860642763/2475880078570760549798248448)), (110809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771897989339689/154742504910672534362390528), (5460804047115/154742504910672534362390528)), (433/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((387553864003317/2417851639229258349412352), (1279595288445/2417851639229258349412352)), (12995/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259366896051987/604462909807314587353088), (4477460860487/604462909807314587353088)), (22751/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236091205707367/9444732965739290427392), (3636884456665/37778931862957161709568)), (147957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298240909448583/4722366482869645213696), (5453484805761/4722366482869645213696)), (55517/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811204891984675/295147905179352825856), (3747774261363/295147905179352825856)), (152777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824672458934533/73786976294838206464), (1170618246621/9223372036854775808)), (47783/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823998618413453/9223372036854775808), (10529390827859/9223372036854775808)), (53811/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398809955348847/288230376151711744), (5260836987125/576460752303423488)), (215519/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195669775652393/144115188075855872), (9197783123045/144115188075855872)), (94445/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493254548739889/36028797018963968), (6889655576539/18014398509481984)), (70989/9007199254740992), by norm_num⟩
  | 3 => ⟨((745625269715831/4503599627370496), (17193752138649/9007199254740992)), (356033/9007199254740992), by norm_num⟩
  | 2 => ⟨((557962093731351/1125899906842624), (8574085473653/1125899906842624)), (357669/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110870836109525/1125899906842624), (25608301144893/1125899906842624)), (270299/562949953421312), by norm_num⟩
  | 0 => ⟨((547791294427067/562949953421312), (50760776634967/1125899906842624)), (274409/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547791294427067/562949953421312), (50760776634967/1125899906842624)), (1046787263036632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((531896550162499/562949953421312), (24696965840391/281474976710656)), (2235133/1125899906842624), by norm_num⟩
  | 2 => ⟨((996444454372217/1125899906842624), (186677069251361/1125899906842624)), (4615905/1125899906842624), by norm_num⟩
  | 3 => ⟨((850922197117459/1125899906842624), (330426051700487/1125899906842624)), (9700999/1125899906842624), by norm_num⟩
  | 4 => ⟨((136532387596773/281474976710656), (124863169536227/281474976710656)), (40715017/2251799813685248), by norm_num⟩
  | 5 => ⟨((43347110878399/1125899906842624), (242264756304873/562949953421312)), (151242215/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1654782100276959/9007199254740992), (149234967544141/4503599627370496)), (141819415/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1587203127/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-424029871/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((89939283314691/562949953421312), (-26136982410707/562949953421312)), (118920413/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1426875931/4294967296), (51832511/536870912)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((1483552543/4294967296), (-215565353/2147483648)), (1/33554432), by norm_num⟩
  | 3 => ⟨((-514160131/2147483648), (298837033/4294967296)), (91/4294967296), by norm_num⟩
  | 4 => ⟨((66822871/536870912), (-155353535/4294967296)), (97/8589934592), by norm_num⟩
  | 5 => ⟨((-889307225/17179869184), (258438875/17179869184)), (83/17179869184), by norm_num⟩
  | 6 => ⟨((1232841591/68719476736), (-358272355/68719476736)), (59/34359738368), by norm_num⟩
  | 7 => ⟨((-366231717/68719476736), (425717953/274877906944)), (143/274877906944), by norm_num⟩
  | 8 => ⟨((1523114893/1099511627776), (-221313899/549755813888)), (19/137438953472), by norm_num⟩
  | 9 => ⟨((-703828529/2199023255552), (409074947/4398046511104)), (143/4398046511104), by norm_num⟩
  | 10 => ⟨((1170856225/17592186044416), (-340258975/17592186044416)), (121/17592186044416), by norm_num⟩
  | 11 => ⟨((-221338825/17592186044416), (257290417/70368744177664)), (47/35184372088832), by norm_num⟩
  | 12 => ⟨((306840765/140737488355328), (-178340127/281474976710656)), (133/562949953421312), by norm_num⟩
  | 13 => ⟨((-1570602913/4503599627370496), (228214073/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 14 => ⟨((933136269/18014398509481984), (-271175899/18014398509481984)), (105/18014398509481984), by norm_num⟩
  | 15 => ⟨((-517440619/72057594037927936), (18796481/9007199254740992)), (119/144115188075855872), by norm_num⟩
  | 16 => ⟨((1075987519/1152921504606846976), (-312689467/1152921504606846976)), (63/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-368400996355/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779202421930359/633825300114114700748351602688), (-436185687193/633825300114114700748351602688)), (23061/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890229671300217/39614081257132168796771975168), (-490631604413/39614081257132168796771975168)), (103777/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236254399243871/309485009821345068724781056), (-130300178315/618970019642690137449562112)), (110265/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221462674874933/19342813113834066795298816), (-260546729775/77371252455336267181195264)), (110269/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775016085128153/4835703278458516698824704), (-122102798065/2417851639229258349412352)), (103381/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629603769061489/302231454903657293676544), (-213622951019/302231454903657293676544)), (90463/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888472594873065/75557863725914323419136), (-347030559461/37778931862957161709568)), (147009/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((2535253491695/9223372036854775808), (-130089781337/1180591620717411303424)), (110263/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811074848604371/295147905179352825856), (-715190526157/590295810358705651712)), (75811/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824351404820713/73786976294838206464), (-893533493671/73786976294838206464)), (94771/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823643000702831/9223372036854775808), (-502300205805/4611686018427387904)), (26657/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594891154080089/1152921504606846976), (-501910020813/576460752303423488)), (213283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597686248729969/72057594037927936), (-219366358027/36028797018963968)), (186653/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492824209175981/36028797018963968), (-657222983649/18014398509481984)), (140019/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490739800253145/9007199254740992), (-819997849749/4503599627370496)), (350153/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230908149756145/4503599627370496), (-3270824319813/4503599627370496)), (700625/4503599627370496), by norm_num⟩
  | 1 => ⟨((277566676207849/281474976710656), (-610422794435/281474976710656)), (1051737/2251799813685248), by norm_num⟩
  | 0 => ⟨((2189550618568543/2251799813685248), (-9675728656597/2251799813685248)), (2106703/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189550618568543/2251799813685248), (-9675728656597/2251799813685248)), (8036434182173918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1064490338442437/1125899906842624), (-18816501836797/2251799813685248)), (1028759/562949953421312), by norm_num⟩
  | 2 => ⟨((2012703187140997/2251799813685248), (-35580399797217/2251799813685248)), (7849955/2251799813685248), by norm_num⟩
  | 3 => ⟨((899215847267109/1125899906842624), (-7950616173381/281474976710656)), (14280963/2251799813685248), by norm_num⟩
  | 4 => ⟨((1434546247508667/2251799813685248), (-50798974332923/1125899906842624)), (11809077/1125899906842624), by norm_num⟩
  | 5 => ⟨((1818634836563939/4503599627370496), (-129449301067879/2251799813685248)), (64447809/4503599627370496), by norm_num⟩
  | 6 => ⟨((89939283314691/562949953421312), (-26136982410707/562949953421312)), (118920413/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-424029871/8388608)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile029Terms0
