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
namespace Reinmann.XiBand97.Tile028Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30757/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30757/1280))
  have he : value ((69/80), (30757/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1246117137/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((541345971314299/18014398509481984), (1129477185450309/18014398509481984)), (343587715/18014398509481984), by norm_num⟩
  | 1 => ⟨((-199475691/2147483648), (-832381709/4294967296)), (255/4294967296), by norm_num⟩
  | 2 => ⟨((616587829/4294967296), (80403975/268435456)), (99/1073741824), by norm_num⟩
  | 3 => ⟨((-635299719/4294967296), (-662752267/2147483648)), (205/2147483648), by norm_num⟩
  | 4 => ⟨((490934601/4294967296), (1024297697/4294967296)), (319/4294967296), by norm_num⟩
  | 5 => ⟨((-606999877/8589934592), (-1266459067/8589934592)), (397/8589934592), by norm_num⟩
  | 6 => ⟨((156355199/4294967296), (652446457/8589934592)), (411/17179869184), by norm_num⟩
  | 7 => ⟨((-552343495/34359738368), (-288105671/8589934592)), (365/34359738368), by norm_num⟩
  | 8 => ⟨((213414649/34359738368), (222636715/17179869184)), (71/17179869184), by norm_num⟩
  | 9 => ⟨((-293188329/137438953472), (-1223430289/274877906944)), (49/34359738368), by norm_num⟩
  | 10 => ⟨((362503029/549755813888), (47270937/34359738368)), (61/137438953472), by norm_num⟩
  | 11 => ⟨((-407459001/2199023255552), (-850132207/2199023255552)), (69/549755813888), by norm_num⟩
  | 12 => ⟨((419824357/8796093022208), (875931581/8796093022208)), (143/4398046511104), by norm_num⟩
  | 13 => ⟨((-199645371/17592186044416), (-833089755/35184372088832)), (137/17592186044416), by norm_num⟩
  | 14 => ⟨((176317805/70368744177664), (735747371/140737488355328)), (61/35184372088832), by norm_num⟩
  | 15 => ⟨((-290669771/562949953421312), (-1212920725/1125899906842624)), (101/281474976710656), by norm_num⟩
  | 16 => ⟨((449236301/4503599627370496), (937297363/4503599627370496)), (157/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (1463945817727/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777856229926525/633825300114114700748351602688), (1730812778053/633825300114114700748351602688)), (184741/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888715416230411/39614081257132168796771975168), (486678987901/9903520314283042199192993792)), (12991/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944213276521023/1237940039285380274899124224), (1033911676865/1237940039285380274899124224)), (220873/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885046522529603/77371252455336267181195264), (2067191014459/154742504910672534362390528)), (220901/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774262321650345/4835703278458516698824704), (1937319973235/9671406556917033397649408)), (207125/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257888756854351/604462909807314587353088), (423620915927/151115727451828646838272)), (181265/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943165073373487/37778931862957161709568), (2752277857735/75557863725914323419136)), (294613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296443451561769/4722366482869645213696), (257888521875/590295810358705651712)), (221009/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404985449280321/147573952589676412928), (2834987039277/590295810358705651712)), (303969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455398186910915/18446744073709551616), (221315985257/4611686018427387904)), (380083/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820541185514621/9223372036854775808), (1990004355793/4611686018427387904)), (213881/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397947857694959/288230376151711744), (1987707420399/576460752303423488)), (106993/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192662591869813/144115188075855872), (434165827767/18014398509481984)), (374713/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488764052691855/36028797018963968), (2599842018231/18014398509481984)), (562543/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485672826904155/9007199254740992), (3240803766695/4503599627370496)), (352005/4503599627370496), by norm_num⟩
  | 2 => ⟨((555199711374925/1125899906842624), (3227343363209/1125899906842624)), (1410523/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205430974039945/2251799813685248), (150234242187/17592186044416)), (2122067/2251799813685248), by norm_num⟩
  | 0 => ⟨((16871807162109/17592186044416), (37926807452001/2251799813685248)), (4269417/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((16871807162109/17592186044416), (37926807452001/2251799813685248)), (16286533364302825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070519850087345/2251799813685248), (72747500508353/2251799813685248)), (8332999/2251799813685248), by norm_num⟩
  | 2 => ⟨((950741763267151/1125899906842624), (133782002228941/2251799813685248)), (7931365/1125899906842624), by norm_num⟩
  | 3 => ⟨((99857399503715/140737488355328), (225938621931749/2251799813685248)), (7168681/562949953421312), by norm_num⟩
  | 4 => ⟨((277739586823043/562949953421312), (160310117064153/1125899906842624)), (46445393/2251799813685248), by norm_num⟩
  | 5 => ⟨((251228174904675/1125899906842624), (158182678251789/1125899906842624)), (118110377/4503599627370496), by norm_num⟩
  | 6 => ⟨((541345971314299/18014398509481984), (1129477185450309/18014398509481984)), (343587715/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1246117137/16777216)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1264037339/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1203524135092423/18014398509481984), (67138438661677/18014398509481984)), (79186271/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1799413187/8589934592), (-100380033/8589934592)), (239/8589934592), by norm_num⟩
  | 2 => ⟨((705256205/2147483648), (78685253/4294967296)), (189/4294967296), by norm_num⟩
  | 3 => ⟨((-737108917/2147483648), (-20559763/1073741824)), (199/4294967296), by norm_num⟩
  | 4 => ⟨((1155600373/4294967296), (32232509/2147483648)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((-724675657/4294967296), (-20212969/2147483648)), (25/1073741824), by norm_num⟩
  | 6 => ⟨((1514810887/17179869184), (42251765/8589934592)), (211/17179869184), by norm_num⟩
  | 7 => ⟨((-678525825/17179869184), (-75702951/34359738368)), (191/34359738368), by norm_num⟩
  | 8 => ⟨((265939225/17179869184), (59341541/68719476736)), (151/68719476736), by norm_num⟩
  | 9 => ⟨((-1482401603/274877906944), (-41347791/137438953472)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((464806165/274877906944), (405143/4294967296)), (67/274877906944), by norm_num⟩
  | 11 => ⟨((-1059925121/2199023255552), (-29563893/1099511627776)), (77/1099511627776), by norm_num⟩
  | 12 => ⟨((553898181/4398046511104), (61798277/8796093022208)), (81/4398046511104), by norm_num⟩
  | 13 => ⟨((-66797867/2199023255552), (-29810483/17592186044416)), (79/17592186044416), by norm_num⟩
  | 14 => ⟨((478729887/70368744177664), (106823539/281474976710656)), (285/281474976710656), by norm_num⟩
  | 15 => ⟨((-1601125111/1125899906842624), (-89318557/1125899906842624)), (15/70368744177664), by norm_num⟩
  | 16 => ⟨((1255079631/4503599627370496), (70014455/4503599627370496)), (95/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (18147696411/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55556212150649/19807040628566084398385987584), (21454534073/158456325028528675187087900672)), (184417/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888650897980085/39614081257132168796771975168), (96522958173/39614081257132168796771975168)), (207471/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888358139167929/2475880078570760549798248448), (102527370473/2475880078570760549798248448)), (220439/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221253098109877/19342813113834066795298816), (102495580709/154742504910672534362390528)), (220441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774230406278827/4835703278458516698824704), (96055844241/9671406556917033397649408)), (206665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628916533995265/302231454903657293676544), (84015116739/604462909807314587353088)), (180833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886239957740067/75557863725914323419136), (136461322479/75557863725914323419136)), (293857/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648188038366361/2361183241434822606848), (25572672061/1180591620717411303424)), (55099/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619849589931731/590295810358705651712), (70279945205/295147905179352825856)), (303049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910739068743939/36893488147419103232), (21945657915/9223372036854775808)), (189409/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820413139658947/9223372036854775808), (98663011969/4611686018427387904)), (106545/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397916123944957/288230376151711744), (197095167949/1152921504606846976)), (426193/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192552770223315/144115188075855872), (43049730937/36028797018963968)), (372933/144115188075855872), by norm_num⟩
  | 4 => ⟨((744300902555625/18014398509481984), (128890299877/18014398509481984)), (559427/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485474347879453/9007199254740992), (160660834661/4503599627370496)), (699337/9007199254740992), by norm_num⟩
  | 2 => ⟨((34693981353469/70368744177664), (319969628985/2251799813685248)), (349709/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204886962087107/2251799813685248), (953177160827/2251799813685248)), (2098683/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079314988715101/1125899906842624), (7342178065/8796093022208)), (4199207/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079314988715101/1125899906842624), (7342178065/8796093022208)), (16018703469283293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2069313541218969/2251799813685248), (450456970803/281474976710656)), (8057935/2251799813685248), by norm_num⟩
  | 2 => ⟨((1901610222859643/2251799813685248), (6623229676131/2251799813685248)), (14835629/2251799813685248), by norm_num⟩
  | 3 => ⟨((401465257983453/562949953421312), (11186430679969/2251799813685248)), (25144193/2251799813685248), by norm_num⟩
  | 4 => ⟨((1145157088112545/2251799813685248), (15955106671753/2251799813685248)), (36112761/2251799813685248), by norm_num⟩
  | 5 => ⟨((291129385271537/1125899906842624), (32455999659841/4503599627370496)), (74484363/4503599627370496), by norm_num⟩
  | 6 => ⟨((1203524135092423/18014398509481984), (67138438661677/18014398509481984)), (79186271/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1264037339/16777216)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1281194743/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((329892867391181/9007199254740992), (-956457767866031/18014398509481984)), (147760799/9007199254740992), by norm_num⟩
  | 1 => ⟨((-499924321/4294967296), (724714821/4294967296)), (113/2147483648), by norm_num⟩
  | 2 => ⟨((794393201/4294967296), (-287897839/1073741824)), (361/4294967296), by norm_num⟩
  | 3 => ⟨((-210385363/1073741824), (1219939773/4294967296)), (385/4294967296), by norm_num⟩
  | 4 => ⟨((668616009/4294967296), (-969258567/4294967296)), (77/1073741824), by norm_num⟩
  | 5 => ⟨((-849959067/8589934592), (154017795/1073741824)), (197/4294967296), by norm_num⟩
  | 6 => ⟨((450202611/8589934592), (-652635791/8589934592)), (105/4294967296), by norm_num⟩
  | 7 => ⟨((-408790895/17179869184), (1185206671/34359738368)), (3/268435456), by norm_num⟩
  | 8 => ⟨((649579735/68719476736), (-470831325/34359738368)), (307/68719476736), by norm_num⟩
  | 9 => ⟨((-229377707/68719476736), (332517177/68719476736)), (219/137438953472), by norm_num⟩
  | 10 => ⟨((36448735/34359738368), (-422702995/274877906944)), (35/68719476736), by norm_num⟩
  | 11 => ⟨((-673955153/2199023255552), (244249613/549755813888)), (163/1099511627776), by norm_num⟩
  | 12 => ⟨((178488813/2199023255552), (-1034984557/8796093022208)), (87/2199023255552), by norm_num⟩
  | 13 => ⟨((-349075111/17592186044416), (1012072811/35184372088832)), (171/17592186044416), by norm_num⟩
  | 14 => ⟨((633931139/140737488355328), (-459488839/70368744177664)), (39/17592186044416), by norm_num⟩
  | 15 => ⟨((-537244609/562949953421312), (778816141/562949953421312)), (133/281474976710656), by norm_num⟩
  | 16 => ⟨((53356009/281474976710656), (-618779905/2251799813685248)), (425/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-157442413671/1267650600228229401496703205376)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777741076438113/633825300114114700748351602688), (-1488959790847/633825300114114700748351602688)), (184693/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888585921860099/39614081257132168796771975168), (-837342135389/19807040628566084398385987584)), (207799/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944144516975339/1237940039285380274899124224), (-1778854729775/2475880078570760549798248448)), (27601/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769955603170847/154742504910672534362390528), (-1778295540675/154742504910672534362390528)), (220833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548395873512305/9671406556917033397649408), (-1666558169551/9671406556917033397649408)), (103529/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257776165219403/604462909807314587353088), (-728822383523/302231454903657293676544)), (90601/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943073669424081/37778931862957161709568), (-2367560258057/75557863725914323419136)), (294501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648153239923329/2361183241434822606848), (-887348668093/2361183241434822606848)), (220919/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619753678895643/590295810358705651712), (-152414313255/36893488147419103232)), (151917/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455339481580919/18446744073709551616), (-3045918394997/73786976294838206464)), (189949/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227534682478443/1152921504606846976), (-3423405405321/9223372036854775808)), (427529/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795764132292543/576460752303423488), (-854835990741/288230376151711744)), (427711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192432949669995/144115188075855872), (-373420385685/18014398509481984)), (374451/144115188075855872), by norm_num⟩
  | 4 => ⟨((744210421408985/18014398509481984), (-2235967221587/18014398509481984)), (281043/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485246001287263/9007199254740992), (-5574010222409/9007199254740992)), (703325/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109975863718407/2251799813685248), (-1387554576917/562949953421312)), (704405/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102088267841907/1125899906842624), (-2066522851595/281474976710656)), (1059321/1125899906842624), by norm_num⟩
  | 0 => ⟨((33705419257655/35184372088832), (-32593391075521/2251799813685248)), (2129571/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((33705419257655/35184372088832), (-32593391075521/2251799813685248)), (8123668674949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((258250095074269/281474976710656), (-31223348492777/1125899906842624)), (4141761/1125899906842624), by norm_num⟩
  | 2 => ⟨((1893800473245481/2251799813685248), (-28647067711051/562949953421312)), (1957439/281474976710656), by norm_num⟩
  | 3 => ⟨((1586886071724855/2251799813685248), (-48185304980105/562949953421312)), (27933557/2251799813685248), by norm_num⟩
  | 4 => ⟨((68863199220113/140737488355328), (-67914198118351/562949953421312)), (44152523/2251799813685248), by norm_num⟩
  | 5 => ⟨((63293286170567/281474976710656), (-531689346973761/4503599627370496)), (53860985/2251799813685248), by norm_num⟩
  | 6 => ⟨((329892867391181/9007199254740992), (-956457767866031/18014398509481984)), (147760799/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1281194743/16777216)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1297651647/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-413000788907219/18014398509481984), (-1042955364850647/18014398509481984)), (198993455/9007199254740992), by norm_num⟩
  | 1 => ⟨((316953243/4294967296), (800405457/4294967296)), (307/4294967296), by norm_num⟩
  | 2 => ⟨((-255058283/2147483648), (-161025361/536870912)), (31/268435456), by norm_num⟩
  | 3 => ⟨((547333961/4294967296), (691094189/2147483648)), (267/2147483648), by norm_num⟩
  | 4 => ⟨((-220225007/2147483648), (-1112273189/4294967296)), (431/4294967296), by norm_num⟩
  | 5 => ⟨((567101561/8589934592), (22376683/134217728)), (557/8589934592), by norm_num⟩
  | 6 => ⟨((-304238251/8589934592), (-768296149/8589934592)), (75/2147483648), by norm_num⟩
  | 7 => ⟨((2185949/134217728), (353292843/8589934592)), (277/17179869184), by norm_num⟩
  | 8 => ⟨((-450323097/68719476736), (-35537681/2147483648)), (7/1073741824), by norm_num⟩
  | 9 => ⟨((40264837/17179869184), (813449829/137438953472)), (161/68719476736), by norm_num⟩
  | 10 => ⟨((-414744033/549755813888), (-261839399/137438953472)), (13/17179869184), by norm_num⟩
  | 11 => ⟨((485458015/2199023255552), (306483095/549755813888)), (489/2199023255552), by norm_num⟩
  | 12 => ⟨((-130219089/2199023255552), (-1315374701/8796093022208)), (527/8796093022208), by norm_num⟩
  | 13 => ⟨((515888095/35184372088832), (1302777793/35184372088832)), (131/8796093022208), by norm_num⟩
  | 14 => ⟨((-118612837/35184372088832), (-1198137127/140737488355328)), (121/35184372088832), by norm_num⟩
  | 15 => ⟨((407253327/562949953421312), (257110309/140737488355328)), (209/281474976710656), by norm_num⟩
  | 16 => ⟨((-40965559/281474976710656), (-413803079/1125899906842624)), (169/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-634320347557/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777683223421971/633825300114114700748351602688), (-46863491231/9903520314283042199192993792)), (184991/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888520654052923/39614081257132168796771975168), (-421669781475/4951760157141521099596496896)), (208153/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888219438755951/2475880078570760549798248448), (-218699815/151115727451828646838272)), (110603/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884942864582733/77371252455336267181195264), (-895508983853/38685626227668133590597632)), (221257/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387082517664633/2417851639229258349412352), (-1678472961389/4835703278458516698824704)), (25935/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257718292044311/604462909807314587353088), (-91753606283/18889465931478580854784)), (90799/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886052741170163/75557863725914323419136), (-596114441255/9444732965739290427392)), (73799/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296235047668045/4722366482869645213696), (-1787349840469/2361183241434822606848)), (221483/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619654674454891/590295810358705651712), (-4911985171911/590295810358705651712)), (38085/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821232995033971/73786976294838206464), (-3067572254475/36893488147419103232)), (381061/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820135298819175/9223372036854775808), (-3447696122207/4611686018427387904)), (53623/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795692045967409/576460752303423488), (-6887093808021/1152921504606846976)), (107337/288230376151711744), by norm_num⟩
  | 5 => ⟨((596152271178045/72057594037927936), (-6016882639711/144115188075855872)), (376089/144115188075855872), by norm_num⟩
  | 4 => ⟨((372055934112699/9007199254740992), (-1125837911785/4503599627370496)), (564953/36028797018963968), by norm_num⟩
  | 3 => ⟨((371247947435893/2251799813685248), (-2806464093035/2251799813685248)), (176907/2251799813685248), by norm_num⟩
  | 2 => ⟨((277427496440449/562949953421312), (-11177198903335/2251799813685248)), (1419579/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203321102722859/2251799813685248), (-33289194229023/2251799813685248)), (2140209/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155207949896193/2251799813685248), (-32807037118025/1125899906842624)), (2161995/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155207949896193/2251799813685248), (-32807037118025/1125899906842624)), (8247356419089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060847537314235/2251799813685248), (-125599063965799/2251799813685248)), (8529011/2251799813685248), by norm_num⟩
  | 2 => ⟨((939541210872599/1125899906842624), (-114948282742451/1125899906842624)), (8281477/1125899906842624), by norm_num⟩
  | 3 => ⟨((386146483332133/562949953421312), (-191844138362939/1125899906842624)), (7756223/562949953421312), by norm_num⟩
  | 4 => ⟨((994106580049835/2251799813685248), (-65796203487107/281474976710656)), (53134831/2251799813685248), by norm_num⟩
  | 5 => ⟨((39478581921665/281474976710656), (-464754910672347/2251799813685248)), (71756155/2251799813685248), by norm_num⟩
  | 6 => ⟨((-413000788907219/18014398509481984), (-1042955364850647/18014398509481984)), (198993455/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1297651647/16777216)), (1/8388608), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-328365753/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1050371654890085/18014398509481984), (-269681398144223/18014398509481984)), (94724071/4503599627370496), by norm_num⟩
  | 1 => ⟨((1631837965/8589934592), (209486015/4294967296)), (591/8589934592), by norm_num⟩
  | 2 => ⟨((-664585703/2147483648), (-170631415/2147483648)), (483/4294967296), by norm_num⟩
  | 3 => ⟨((1443522919/4294967296), (370622415/4294967296)), (263/2147483648), by norm_num⟩
  | 4 => ⟨((-18371629/67108864), (-150940451/2147483648)), (215/2147483648), by norm_num⟩
  | 5 => ⟨((766163723/4294967296), (393422849/8589934592)), (281/4294967296), by norm_num⟩
  | 6 => ⟨((-416039229/4294967296), (-213634937/8589934592)), (153/4294967296), by norm_num⟩
  | 7 => ⟨((774569127/17179869184), (397738999/34359738368)), (143/8589934592), by norm_num⟩
  | 8 => ⟨((-19715789/1073741824), (-161984007/34359738368)), (117/17179869184), by norm_num⟩
  | 9 => ⟨((913577869/137438953472), (14659987/8589934592)), (85/34359738368), by norm_num⟩
  | 10 => ⟨((-1190609957/549755813888), (-305687379/549755813888)), (445/549755813888), by norm_num⟩
  | 11 => ⟨((1410589883/2199023255552), (181083453/1099511627776)), (529/2199023255552), by norm_num⟩
  | 12 => ⟨((-1531946005/8796093022208), (-196662457/4398046511104)), (9/137438953472), by norm_num⟩
  | 13 => ⟨((767881227/17592186044416), (197152391/17592186044416)), (579/35184372088832), by norm_num⟩
  | 14 => ⟨((-714808905/70368744177664), (-367052299/140737488355328)), (541/140737488355328), by norm_num⟩
  | 15 => ⟨((1242088757/562949953421312), (318904487/562949953421312)), (59/70368744177664), by norm_num⟩
  | 16 => ⟨((-505855635/1125899906842624), (-259755401/2251799813685248)), (193/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-3764902722669/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((13887697945347/4951760157141521099596496896), (-278134896387/39614081257132168796771975168)), (46319/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236056903949145/4951760157141521099596496896), (-5005191722789/39614081257132168796771975168)), (208493/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236018690057755/309485009821345068724781056), (-5316489477043/2475880078570760549798248448)), (221589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769815353628493/154742504910672534362390528), (-5314772319931/154742504910672534362390528)), (221663/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774131804102669/4835703278458516698824704), (-2490387541283/4835703278458516698824704)), (207887/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628829826249067/302231454903657293676544), (-4356354805047/604462909807314587353088)), (45495/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942978271878197/37778931862957161709568), (-7075658920127/75557863725914323419136)), (295863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324040526502551/1180591620717411303424), (-5303754979137/4722366482869645213696)), (111013/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404888273004513/147573952589676412928), (-7287807920543/590295810358705651712)), (152747/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821104088891347/73786976294838206464), (-4551240574163/36893488147419103232)), (382181/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819987633777601/9223372036854775808), (-5115144763093/4611686018427387904)), (26899/576460752303423488), by norm_num⟩
  | 6 => ⟨((1591233128096195/1152921504606846976), (-10217797098039/1152921504606846976)), (430923/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298042187291465/36028797018963968), (-278954122699/4503599627370496)), (377665/144115188075855872), by norm_num⟩
  | 4 => ⟨((186001584404855/4503599627370496), (-13361750442307/36028797018963968)), (283857/18014398509481984), by norm_num⟩
  | 3 => ⟨((23198673853455/140737488355328), (-16653180677969/9007199254740992)), (355887/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109414194150265/2251799813685248), (-4144955238283/562949953421312)), (714979/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202338967198233/2251799813685248), (-12343430946323/562949953421312)), (1080505/1125899906842624), by norm_num⟩
  | 0 => ⟨((1076434950528165/1125899906842624), (-97290849966421/2251799813685248)), (4386621/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076434950528165/1125899906842624), (-97290849966421/2251799813685248)), (16733631142623137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054082815566673/2251799813685248), (-186033004592985/2251799813685248)), (8766857/2251799813685248), by norm_num⟩
  | 2 => ⟨((1858356994692131/2251799813685248), (-169698565361059/1125899906842624)), (17442737/2251799813685248), by norm_num⟩
  | 3 => ⟨((185312893218257/281474976710656), (-560192809345395/2251799813685248)), (34048185/2251799813685248), by norm_num⟩
  | 4 => ⟨((418331945418663/1125899906842624), (-184405291498739/562949953421312)), (30886445/1125899906842624), by norm_num⟩
  | 5 => ⟨((138486095220087/4503599627370496), (-548131313409521/2251799813685248)), (172747399/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1050371654890085/18014398509481984), (-269681398144223/18014398509481984)), (94724071/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-328365753/4194304)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-664338789/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-832124181621773/18014398509481984), (639887723560289/18014398509481984)), (24122163/2251799813685248), by norm_num⟩
  | 1 => ⟨((326936907/2147483648), (-251408285/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-1077530711/4294967296), (414300347/2147483648)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((18496695/67108864), (-910310905/4294967296)), (281/4294967296), by norm_num⟩
  | 4 => ⟨((-243848357/1073741824), (187514765/1073741824)), (233/4294967296), by norm_num⟩
  | 5 => ⟨((160736881/1073741824), (-123603615/1073741824)), (155/4294967296), by norm_num⟩
  | 6 => ⟨((-706350051/8589934592), (543169801/8589934592)), (43/2147483648), by norm_num⟩
  | 7 => ⟨((665147011/17179869184), (-127871361/4294967296)), (163/17179869184), by norm_num⟩
  | 8 => ⟨((-274027005/17179869184), (842886291/68719476736)), (271/68719476736), by norm_num⟩
  | 9 => ⟨((401399247/68719476736), (-617336825/137438953472)), (25/17179869184), by norm_num⟩
  | 10 => ⟨((-1058357149/549755813888), (813856587/549755813888)), (133/274877906944), by norm_num⟩
  | 11 => ⟨((634213183/1099511627776), (-487697917/1099511627776)), (161/1099511627776), by norm_num⟩
  | 12 => ⟨((-174188599/1099511627776), (535790925/4398046511104)), (179/4398046511104), by norm_num⟩
  | 13 => ⟨((706581177/17592186044416), (-543347533/17592186044416)), (183/17592186044416), by norm_num⟩
  | 14 => ⟨((-665364655/70368744177664), (511652809/70368744177664)), (87/35184372088832), by norm_num⟩
  | 15 => ⟨((584782229/281474976710656), (-449686451/281474976710656)), (77/140737488355328), by norm_num⟩
  | 16 => ⟨((-481836707/1125899906842624), (11578853/35184372088832)), (1/8796093022208), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (3238362820507/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777577983938861/633825300114114700748351602688), (3827576235737/633825300114114700748351602688)), (46289/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888402123826263/39614081257132168796771975168), (4304955319997/39614081257132168796771975168)), (52087/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59002916038105/77371252455336267181195264), (71448242351/38685626227668133590597632)), (110713/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110609962084945/9671406556917033397649408), (1142798637571/38685626227668133590597632)), (110745/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774105703825341/4835703278458516698824704), (2141954568497/4835703278458516698824704)), (103857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257614238973141/604462909807314587353088), (1873417660661/302231454903657293676544)), (90909/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885883237449389/75557863725914323419136), (95088069215/1180591620717411303424)), (147789/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296107555112981/4722366482869645213696), (2280814479305/2361183241434822606848)), (110897/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404869695110841/147573952589676412928), (6268019787921/590295810358705651712)), (152573/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821012241634657/73786976294838206464), (3822606803/36028797018963968)), (190851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227485716996651/1152921504606846976), (2199648597123/2305843009213693952)), (214893/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591133014223003/1152921504606846976), (4393869814623/576460752303423488)), (215125/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192083150931889/144115188075855872), (7677074106183/144115188075855872)), (188495/144115188075855872), by norm_num⟩
  | 4 => ⟨((92993016682873/2251799813685248), (5745624419717/18014398509481984)), (283265/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484566566119409/9007199254740992), (14321503032935/9007199254740992)), (354999/9007199254740992), by norm_num⟩
  | 2 => ⟨((277318999194427/562949953421312), (14257817971403/2251799813685248)), (356377/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100987880069157/1125899906842624), (21228045614835/1125899906842624)), (538023/1125899906842624), by norm_num⟩
  | 0 => ⟨((538086613601995/562949953421312), (10456137309143/281474976710656)), (544971/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538086613601995/562949953421312), (10456137309143/281474976710656)), (2078899385692405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2054178200040383/2251799813685248), (159909277386823/2251799813685248)), (2164585/1125899906842624), by norm_num⟩
  | 2 => ⟨((232818048202897/281474976710656), (291750758300877/2251799813685248)), (4256667/1125899906842624), by norm_num⟩
  | 3 => ⟨((187847131374723/281474976710656), (482635031384329/2251799813685248)), (16289401/2251799813685248), by norm_num⟩
  | 4 => ⟨((112432412906829/281474976710656), (644189456597357/2251799813685248)), (28724733/2251799813685248), by norm_num⟩
  | 5 => ⟨((349984025955861/4503599627370496), (1029260587506255/4503599627370496)), (19691315/1125899906842624), by norm_num⟩
  | 6 => ⟨((-832124181621773/18014398509481984), (639887723560289/18014398509481984)), (24122163/2251799813685248), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-664338789/8388608)), (1/16777216), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile028Terms3
