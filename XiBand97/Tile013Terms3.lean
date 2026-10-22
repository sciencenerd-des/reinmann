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
namespace Reinmann.XiBand97.Tile013Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5149/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5149/256))
  have he : value ((69/80), (5149/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-65191025/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((247205057150773/4503599627370496), (768770920766543/18014398509481984)), (133103617/9007199254740992), by norm_num⟩
  | 1 => ⟨((-182180721/1073741824), (-566554917/4294967296)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((563128343/2147483648), (437811325/2147483648)), (77/1073741824), by norm_num⟩
  | 3 => ⟨((-1160435743/4294967296), (-902195595/4294967296)), (5/67108864), by norm_num⟩
  | 4 => ⟨((896739037/4294967296), (697181221/4294967296)), (125/2147483648), by norm_num⟩
  | 5 => ⟨((-1108743373/8589934592), (-862006701/8589934592)), (311/8589934592), by norm_num⟩
  | 6 => ⟨((1142390945/17179869184), (222041609/4294967296)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((-252227065/8589934592), (-784388617/34359738368)), (143/17179869184), by norm_num⟩
  | 8 => ⟨((389822283/34359738368), (606144629/68719476736)), (223/68719476736), by norm_num⟩
  | 9 => ⟨((-535536545/137438953472), (-416359729/137438953472)), (77/68719476736), by norm_num⟩
  | 10 => ⟨((331073239/274877906944), (514794239/549755813888)), (3/8589934592), by norm_num⟩
  | 11 => ⟨((-744262863/2199023255552), (-4520599/17179869184)), (109/1099511627776), by norm_num⟩
  | 12 => ⟨((766849369/8796093022208), (596196839/8796093022208)), (227/8796093022208), by norm_num⟩
  | 13 => ⟨((-729342755/35184372088832), (-567036843/35184372088832)), (109/17592186044416), by norm_num⟩
  | 14 => ⟨((644122691/140737488355328), (62597677/17592186044416)), (97/70368744177664), by norm_num⟩
  | 15 => ⟨((-1061872311/1125899906842624), (-206391549/281474976710656)), (161/562949953421312), by norm_num⟩
  | 16 => ⟨((410286549/2251799813685248), (39872815/281474976710656)), (251/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (860826830937/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777857281085913/633825300114114700748351602688), (1017749469027/633825300114114700748351602688)), (23075/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472179164067995/9903520314283042199192993792), (1144705149715/39614081257132168796771975168)), (207689/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888427947616721/2475880078570760549798248448), (151989828785/309485009821345068724781056)), (220685/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885047263095207/77371252455336267181195264), (1215546902677/154742504910672534362390528)), (220701/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774263061876221/4835703278458516698824704), (569590209139/4835703278458516698824704)), (103463/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628945072028161/302231454903657293676544), (124548530049/75557863725914323419136)), (90539/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886332572908177/75557863725914323419136), (404597836093/18889465931478580854784)), (294285/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296445421466541/4722366482869645213696), (1213146781811/4722366482869645213696)), (27593/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619944749615633/590295810358705651712), (1667026599979/590295810358705651712)), (151785/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455399200871799/18446744073709551616), (2082209146139/73786976294838206464)), (379535/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910273124785321/4611686018427387904), (2340322899613/9223372036854775808)), (427075/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591797119948379/1152921504606846976), (2337622913771/1152921504606846976)), (6675/18014398509481984), by norm_num⟩
  | 5 => ⟨((1192668271184587/144115188075855872), (2042386687419/144115188075855872)), (93485/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488773969361085/36028797018963968), (3057523596787/36028797018963968)), (561191/36028797018963968), by norm_num⟩
  | 3 => ⟨((742843828871489/4503599627370496), (1905664423605/4503599627370496)), (350991/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220835768460249/4503599627370496), (7591022988749/4503599627370496)), (702725/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205504359311097/2251799813685248), (11307769642351/2251799813685248)), (1055957/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079904590794399/1125899906842624), (11151202065431/1125899906842624)), (2119459/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079904590794399/1125899906842624), (11151202065431/1125899906842624)), (8085094456199264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2071355666386613/2251799813685248), (42782610532779/2251799813685248)), (8215467/2251799813685248), by norm_num⟩
  | 2 => ⟨((476139566097703/562949953421312), (78708597639373/2251799813685248)), (7713223/1125899906842624), by norm_num⟩
  | 3 => ⟨((1608112371761277/2251799813685248), (33285620951213/562949953421312)), (13586803/1125899906842624), by norm_num⟩
  | 4 => ⟨((1140553642295019/2251799813685248), (95083086032947/1125899906842624)), (21012603/1125899906842624), by norm_num⟩
  | 5 => ⟨((1123278748197833/4503599627370496), (385282419641187/4503599627370496)), (49670291/2251799813685248), by norm_num⟩
  | 6 => ⟨((247205057150773/4503599627370496), (768770920766543/18014398509481984)), (133103617/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-65191025/1048576)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1058056419/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1172760885461337/18014398509481984), (-34823173684111/2251799813685248)), (93063123/18014398509481984), by norm_num⟩
  | 1 => ⟨((-27397163/134217728), (208259315/4294967296)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((687229169/2147483648), (-326497939/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-1436535389/4294967296), (341244133/4294967296)), (15/536870912), by norm_num⟩
  | 4 => ⟨((1126062101/4294967296), (-267492251/4294967296)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-706152241/4294967296), (167744081/4294967296)), (123/8589934592), by norm_num⟩
  | 6 => ⟨((1476090845/17179869184), (-350640397/17179869184)), (131/17179869184), by norm_num⟩
  | 7 => ⟨((-1322364087/34359738368), (314123125/34359738368)), (15/4294967296), by norm_num⟩
  | 8 => ⟨((259141559/17179869184), (-123116405/34359738368)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((-361127493/68719476736), (343138467/274877906944)), (17/34359738368), by norm_num⟩
  | 10 => ⟨((226462633/137438953472), (-26897717/68719476736)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((-1032832401/2199023255552), (122672925/1099511627776)), (101/2199023255552), by norm_num⟩
  | 12 => ⟨((539740003/4398046511104), (-256426831/8796093022208)), (107/8796093022208), by norm_num⟩
  | 13 => ⟨((-520723587/17592186044416), (61848065/8796093022208)), (105/35184372088832), by norm_num⟩
  | 14 => ⟨((116623271/17592186044416), (-110813857/70368744177664)), (3/4398046511104), by norm_num⟩
  | 15 => ⟨((-1560198791/1125899906842624), (370619955/1125899906842624)), (163/1125899906842624), by norm_num⟩
  | 16 => ⟨((1222998571/4503599627370496), (-290519181/4503599627370496)), (129/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-37975026869/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798723578379/633825300114114700748351602688), (-5611845227/9903520314283042199192993792)), (23059/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472162705255415/9903520314283042199192993792), (-201979453053/19807040628566084398385987584)), (12971/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118022378288705/154742504910672534362390528), (-214544006119/1237940039285380274899124224)), (6891/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221253086619889/19342813113834066795298816), (-428954966493/154742504910672534362390528)), (110259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387115180170127/2417851639229258349412352), (-402003978231/9671406556917033397649408)), (103371/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628916490950555/302231454903657293676544), (-351612243663/604462909807314587353088)), (90453/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29472496987099/1180591620717411303424), (-71388151911/9444732965739290427392)), (9187/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((81023497155193/295147905179352825856), (-107024363763/1180591620717411303424)), (110249/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404962351676487/147573952589676412928), (-294129072389/295147905179352825856)), (151601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821477885793789/73786976294838206464), (-734759353053/73786976294838206464)), (94757/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910206412701495/4611686018427387904), (-412915218271/4611686018427387904)), (106611/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591664142738515/1152921504606846976), (-206216062791/288230376151711744)), (53311/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192552417801851/144115188075855872), (-180167696099/36028797018963968)), (93307/72057594037927936), by norm_num⟩
  | 4 => ⟨((186075148720717/4503599627370496), (-67427444249/2251799813685248)), (279973/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485473427638767/9007199254740992), (-672382526883/4503599627370496)), (350057/9007199254740992), by norm_num⟩
  | 2 => ⟨((277551564464077/562949953421312), (-2678212689699/4503599627370496)), (175097/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204882409228645/2251799813685248), (-249321524871/140737488355328)), (525641/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158616462843361/2251799813685248), (-983287605825/281474976710656)), (1052713/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158616462843361/2251799813685248), (-983287605825/281474976710656)), (4015781406882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034630859868407/1125899906842624), (-1885194945611/281474976710656)), (4051311/2251799813685248), by norm_num⟩
  | 2 => ⟨((475354934451527/562949953421312), (-27718000234203/2251799813685248)), (3750033/1125899906842624), by norm_num⟩
  | 3 => ⟨((802608808699127/1125899906842624), (-23405079091633/1125899906842624)), (12850753/2251799813685248), by norm_num⟩
  | 4 => ⟨((1143322062933809/2251799813685248), (-33369081093405/1125899906842624)), (4713963/562949953421312), by norm_num⟩
  | 5 => ⟨((289264469554939/1125899906842624), (-67770867378267/2251799813685248)), (5066329/562949953421312), by norm_num⟩
  | 6 => ⟨((1172760885461337/18014398509481984), (-34823173684111/2251799813685248)), (93063123/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1058056419/16777216)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-536208971/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((538170520708849/18014398509481984), (-257451593529441/4503599627370496)), (78504177/4503599627370496), by norm_num⟩
  | 1 => ⟨((-407775613/4294967296), (780291579/4294967296)), (239/4294967296), by norm_num⟩
  | 2 => ⟨((80995803/536870912), (-1239904321/4294967296)), (191/2147483648), by norm_num⟩
  | 3 => ⟨((-343212029/2147483648), (1313494225/4294967296)), (407/4294967296), by norm_num⟩
  | 4 => ⟨((17042911/134217728), (-521794419/2147483648)), (325/4294967296), by norm_num⟩
  | 5 => ⟨((-346645047/4294967296), (1326632601/8589934592)), (415/8589934592), by norm_num⟩
  | 6 => ⟨((367218873/8589934592), (-1405369939/17179869184)), (221/8589934592), by norm_num⟩
  | 7 => ⟨((-666880769/34359738368), (1276097519/34359738368)), (403/34359738368), by norm_num⟩
  | 8 => ⟨((529845745/68719476736), (-253469163/17179869184)), (161/34359738368), by norm_num⟩
  | 9 => ⟨((-187097589/68719476736), (358017175/68719476736)), (229/137438953472), by norm_num⟩
  | 10 => ⟨((475684967/549755813888), (-910238283/549755813888)), (293/549755813888), by norm_num⟩
  | 11 => ⟨((-549728157/2199023255552), (1051922277/2199023255552)), (85/549755813888), by norm_num⟩
  | 12 => ⟨((582355225/8796093022208), (-1114355207/8796093022208)), (181/4398046511104), by norm_num⟩
  | 13 => ⟨((-569463463/35184372088832), (544843205/17592186044416)), (89/8796093022208), by norm_num⟩
  | 14 => ⟨((517081583/140737488355328), (-247363005/35184372088832)), (325/140737488355328), by norm_num⟩
  | 15 => ⟨((-109554207/140737488355328), (52408863/35184372088832)), (277/562949953421312), by norm_num⟩
  | 16 => ⟨((348169167/2251799813685248), (-666232751/2251799813685248)), (221/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-1418853342949/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777740756538759/633825300114114700748351602688), (-1677292293339/633825300114114700748351602688)), (92365/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944292772274281/19807040628566084398385987584), (-1886507971375/39614081257132168796771975168)), (51961/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472072152405663/618970019642690137449562112), (-2003854470299/2475880078570760549798248448)), (110429/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884977576255699/77371252455336267181195264), (-2003224501781/154742504910672534362390528)), (110443/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548395423065417/9671406556917033397649408), (-1877353894581/9671406556917033397649408)), (103555/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257775743151171/604462909807314587353088), (-821007940477/302231454903657293676544)), (181251/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943073300339969/37778931862957161709568), (-2667022485171/75557863725914323419136)), (73647/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162038235063459/590295810358705651712), (-1999170842447/4722366482869645213696)), (110495/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809876390313153/295147905179352825856), (-2747080062987/590295810358705651712)), (75985/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821356692403369/73786976294838206464), (-1715591195347/36893488147419103232)), (380043/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820275919225323/9223372036854775808), (-1928207747847/4611686018427387904)), (427711/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795763266938505/576460752303423488), (-3851839689281/1152921504606846976)), (427915/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149053902755515/18014398509481984), (-3365218896603/144115188075855872)), (374655/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488417826395077/36028797018963968), (-629695504321/4503599627370496)), (562443/36028797018963968), by norm_num⟩
  | 3 => ⟨((742620745233173/4503599627370496), (-1569757869421/2251799813685248)), (703861/9007199254740992), by norm_num⟩
  | 2 => ⟨((138746281161919/281474976710656), (-6252223919745/2251799813685248)), (705075/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102077111024229/1125899906842624), (-9311588510961/1125899906842624)), (2121325/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157080607949975/2251799813685248), (-4589452699643/281474976710656)), (4267205/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157080607949975/2251799813685248), (-4589452699643/281474976710656)), (16278095253951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065747001156279/2251799813685248), (-35171223869325/1125899906842624)), (8314575/2251799813685248), by norm_num⟩
  | 2 => ⟨((946434622413571/1125899906842624), (-8066308758165/140737488355328)), (7887325/1125899906842624), by norm_num⟩
  | 3 => ⟨((791877064308959/1125899906842624), (-216977977169255/2251799813685248)), (14164333/1125899906842624), by norm_num⟩
  | 4 => ⟨((546495670347777/1125899906842624), (-305213425343151/2251799813685248)), (45308059/2251799813685248), by norm_num⟩
  | 5 => ⟨((978306179023183/4503599627370496), (-592584880657109/4503599627370496)), (112532109/4503599627370496), by norm_num⟩
  | 6 => ⟨((538170520708849/18014398509481984), (-257451593529441/4503599627370496)), (78504177/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-536208971/8388608)), (1/8388608), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1086193115/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-186783194354953/9007199254740992), (-264430248120251/4503599627370496)), (197727593/18014398509481984), by norm_num⟩
  | 1 => ⟨((286689715/4294967296), (202934297/1073741824)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-461409297/4294967296), (-653220303/2147483648)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((495073077/4294967296), (1401756695/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-199197345/2147483648), (-1128020185/4294967296)), (109/2147483648), by norm_num⟩
  | 5 => ⟨((512953215/8589934592), (726191381/4294967296)), (283/8589934592), by norm_num⟩
  | 6 => ⟨((-17199299/536870912), (-1558346587/17179869184)), (153/8589934592), by norm_num⟩
  | 7 => ⟨((506170585/34359738368), (716589165/17179869184)), (71/8589934592), by norm_num⟩
  | 8 => ⟨((-407325065/68719476736), (-576652885/34359738368)), (115/34359738368), by norm_num⟩
  | 9 => ⟨((291361957/137438953472), (206241559/34359738368)), (83/68719476736), by norm_num⟩
  | 10 => ⟨((-23446449/34359738368), (-531092775/274877906944)), (27/68719476736), by norm_num⟩
  | 11 => ⟨((439105209/2199023255552), (1243288505/2199023255552)), (255/2199023255552), by norm_num⟩
  | 12 => ⟨((-235570857/4398046511104), (-83374819/549755813888)), (275/8796093022208), by norm_num⟩
  | 13 => ⟨((233314873/17592186044416), (1321221855/35184372088832)), (137/17592186044416), by norm_num⟩
  | 14 => ⟨((-26821843/8796093022208), (-303774935/35184372088832)), (127/70368744177664), by norm_num⟩
  | 15 => ⟨((184183855/281474976710656), (1043001381/562949953421312)), (219/562949953421312), by norm_num⟩
  | 16 => ⟨((-296432479/2251799813685248), (-839322983/2251799813685248)), (89/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-2488381257387/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777683407663893/633825300114114700748351602688), (-91920615257/19807040628566084398385987584)), (46245/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944260435670825/19807040628566084398385987584), (-827086261761/9903520314283042199192993792)), (52035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888219683118927/2475880078570760549798248448), (-3514120847081/2475880078570760549798248448)), (27649/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442471497172685/38685626227668133590597632), (-1756500535017/77371252455336267181195264)), (110621/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548330330059691/9671406556917033397649408), (-823062291571/2417851639229258349412352)), (103733/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39303704221909/18889465931478580854784), (-1439764581527/302231454903657293676544)), (11349/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886053166256045/75557863725914323419136), (-4677006800679/75557863725914323419136)), (147585/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296235392803463/4722366482869645213696), (-3505806540403/4722366482869645213696)), (110731/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619655191726313/590295810358705651712), (-4817319490797/590295810358705651712)), (152325/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821233705581217/73786976294838206464), (-1504226486807/18446744073709551616)), (190509/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820136185952775/9223372036854775808), (-6762502412831/9223372036854775808)), (214465/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591385088517337/1152921504606846976), (-6754364564249/1152921504606846976)), (214643/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596152768568761/72057594037927936), (-2950462537437/72057594037927936)), (188013/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488225473272431/36028797018963968), (-8833127648953/36028797018963968)), (141211/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484994386900687/9007199254740992), (-11009517266425/9007199254740992)), (88433/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109713218113213/2251799813685248), (-21923607832457/4503599627370496)), (44349/281474976710656), by norm_num⟩
  | 1 => ⟨((275416743481625/281474976710656), (-32647718929829/2251799813685248)), (267423/562949953421312), by norm_num⟩
  | 0 => ⟨((538811516491095/562949953421312), (-32174948246531/1125899906842624)), (2160753/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538811516491095/562949953421312), (-32174948246531/1125899906842624)), (8242618569380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1030496731430357/1125899906842624), (-30795335451003/562949953421312)), (532463/281474976710656), by norm_num⟩
  | 2 => ⟨((1879616644989017/2251799813685248), (-112743565685349/1125899906842624)), (8263559/2251799813685248), by norm_num⟩
  | 3 => ⟨((1546369381746785/2251799813685248), (-376436095943679/2251799813685248)), (15450441/2251799813685248), by norm_num⟩
  | 4 => ⟨((999002716317417/2251799813685248), (-517016876379373/2251799813685248)), (26386177/2251799813685248), by norm_num⟩
  | 5 => ⟨((648991950623395/4503599627370496), (-458745276330443/2251799813685248)), (71057759/4503599627370496), by norm_num⟩
  | 6 => ⟨((-186783194354953/9007199254740992), (-264430248120251/4503599627370496)), (197727593/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1086193115/16777216)), (1/16777216), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1099427943/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-490010617530727/9007199254740992), (-232145993251099/9007199254740992)), (48943361/2251799813685248), by norm_num⟩
  | 1 => ⟨((190317857/1073741824), (360657719/4294967296)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-620073951/2147483648), (-587528833/4294967296)), (125/1073741824), by norm_num⟩
  | 3 => ⟨((1346840529/4294967296), (638075219/4294967296)), (545/4294967296), by norm_num⟩
  | 4 => ⟨((-274258529/1073741824), (-259863833/2147483648)), (223/2147483648), by norm_num⟩
  | 5 => ⟨((714848611/4294967296), (169332291/2147483648)), (73/1073741824), by norm_num⟩
  | 6 => ⟨((-776348595/8589934592), (-183900317/4294967296)), (159/4294967296), by norm_num⟩
  | 7 => ⟨((1445382097/34359738368), (42797499/2147483648)), (297/17179869184), by norm_num⟩
  | 8 => ⟨((-588649301/34359738368), (-557753533/68719476736)), (243/34359738368), by norm_num⟩
  | 9 => ⟨((213097361/34359738368), (403825523/137438953472)), (177/68719476736), by norm_num⟩
  | 10 => ⟨((-1110866839/549755813888), (-526281015/549755813888)), (463/549755813888), by norm_num⟩
  | 11 => ⟨((1316113237/2199023255552), (623517947/2199023255552)), (551/2199023255552), by norm_num⟩
  | 12 => ⟨((-1429341327/8796093022208), (-677160555/8796093022208)), (75/1099511627776), by norm_num⟩
  | 13 => ⟨((1432902163/35184372088832), (339423763/17592186044416)), (603/35184372088832), by norm_num⟩
  | 14 => ⟨((-83366671/8796093022208), (-631928793/140737488355328)), (141/35184372088832), by norm_num⟩
  | 15 => ⟨((1158897759/562949953421312), (549036003/562949953421312)), (123/140737488355328), by norm_num⟩
  | 16 => ⟨((-471975097/1125899906842624), (-447203075/2251799813685248)), (403/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-878988966223/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777626695863213/633825300114114700748351602688), (-4155900291585/633825300114114700748351602688)), (185219/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888456834050851/39614081257132168796771975168), (-4674236753015/39614081257132168796771975168)), (26053/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118009457660555/154742504910672534362390528), (-4964951182009/2475880078570760549798248448)), (27689/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769817267541855/154742504910672534362390528), (-2481674046543/77371252455336267181195264)), (55395/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548265521190723/9671406556917033397649408), (-4651436065621/9671406556917033397649408)), (51951/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257661444936339/604462909807314587353088), (-2034152179605/302231454903657293676544)), (90951/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471489919638231/18889465931478580854784), (-3303902090277/37778931862957161709568)), (18483/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648082325593057/2361183241434822606848), (-2476531375515/2361183241434822606848)), (55479/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619556906552765/590295810358705651712), (-3402964596147/295147905179352825856)), (305329/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455277332158157/18446744073709551616), (-8500617351839/73786976294838206464)), (381953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909997087797131/4611686018427387904), (-9553859074725/9223372036854775808)), (107525/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591240476842245/1152921504606846976), (-9542199507289/1152921504606846976)), (107651/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192176084429379/144115188075855872), (-4168160472989/72057594037927936)), (188673/72057594037927936), by norm_num⟩
  | 4 => ⟨((372006370413603/9007199254740992), (-12478307642403/36028797018963968)), (283577/18014398509481984), by norm_num⟩
  | 3 => ⟨((371183568938393/2251799813685248), (-7776077865267/4503599627370496)), (710933/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218876049864633/4503599627370496), (-15483713020995/2251799813685248)), (1427851/4503599627370496), by norm_num⟩
  | 1 => ⟨((275304207291211/281474976710656), (-46109978737137/2251799813685248)), (2156787/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076575413547437/1125899906842624), (-45430815924163/1125899906842624)), (4373901/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076575413547437/1125899906842624), (-45430815924163/1125899906842624)), (16685108193404387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2055157221326631/2251799813685248), (-173762158231317/2251799813685248)), (4358775/1125899906842624), by norm_num⟩
  | 2 => ⟨((1862278294567773/2251799813685248), (-317176111403931/2251799813685248)), (2157243/281474976710656), by norm_num⟩
  | 3 => ⟨((747730713073865/1125899906842624), (-131155128496141/562949953421312)), (33406969/2251799813685248), by norm_num⟩
  | 4 => ⟨((435469037141617/1125899906842624), (-348410075026045/1125899906842624)), (29969279/1125899906842624), by norm_num⟩
  | 5 => ⟨((121225166668269/2251799813685248), (-1078048227768351/4503599627370496)), (83461389/2251799813685248), by norm_num⟩
  | 6 => ⟨((-490010617530727/9007199254740992), (-232145993251099/9007199254740992)), (48943361/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1099427943/16777216)), (1/8388608), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1112163223/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-498760623054961/9007199254740992), (326861309980569/18014398509481984)), (46475657/4503599627370496), by norm_num⟩
  | 1 => ⟨((1567681931/8589934592), (-513687875/8589934592)), (295/8589934592), by norm_num⟩
  | 2 => ⟨((-161463247/536870912), (423257859/4294967296)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((1419084059/4294967296), (-464996285/4294967296)), (271/4294967296), by norm_num⟩
  | 4 => ⟨((-1169267389/4294967296), (383137975/4294967296)), (225/4294967296), by norm_num⟩
  | 5 => ⟨((1541485827/8589934592), (-505104105/8589934592)), (299/8589934592), by norm_num⟩
  | 6 => ⟨((-211686909/2147483648), (69364197/2147483648)), (83/4294967296), by norm_num⟩
  | 7 => ⟨((1594709757/34359738368), (-522544177/34359738368)), (315/34359738368), by norm_num⟩
  | 8 => ⟨((-656987901/34359738368), (430555091/68719476736)), (261/68719476736), by norm_num⟩
  | 9 => ⟨((481183321/68719476736), (-78835519/34359738368)), (3/2147483648), by norm_num⟩
  | 10 => ⟨((-1268721383/549755813888), (25982901/34359738368)), (255/549755813888), by norm_num⟩
  | 11 => ⟨((190068123/274877906944), (-498242345/2199023255552)), (77/549755813888), by norm_num⟩
  | 12 => ⟨((-417622351/2199023255552), (273687581/4398046511104)), (171/4398046511104), by norm_num⟩
  | 13 => ⟨((423512351/8796093022208), (-277547575/17592186044416)), (175/17592186044416), by norm_num⟩
  | 14 => ⟨((-1595231565/140737488355328), (65339395/17592186044416)), (83/35184372088832), by norm_num⟩
  | 15 => ⟨((43813525/17592186044416), (-459409039/562949953421312)), (147/281474976710656), by norm_num⟩
  | 16 => ⟨((-1155217847/2251799813685248), (47316789/281474976710656)), (61/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (3679805669795/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888787847192917/316912650057057350374175801344), (543667337267/79228162514264337593543950336)), (92629/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944199712024839/19807040628566084398385987584), (4891786195189/39614081257132168796771975168)), (26059/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472022569271871/618970019642690137449562112), (5196013633251/2475880078570760549798248448)), (55391/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884878084437435/77371252455336267181195264), (2597158116441/77371252455336267181195264)), (55409/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548208184747393/9671406556917033397649408), (4867868510483/9671406556917033397649408)), (51965/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39300350599387/18889465931478580854784), (4257582584297/604462909807314587353088)), (90977/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117867372260541/4722366482869645213696), (3457596767693/37778931862957161709568)), (147909/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296103267217531/4722366482869645213696), (5183440523285/4722366482869645213696)), (110995/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619472354100879/590295810358705651712), (1780607955259/147573952589676412928)), (152719/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821003414346145/73786976294838206464), (8895845580213/73786976294838206464)), (47763/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909937357625149/4611686018427387904), (4998970502153/4611686018427387904)), (26893/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397780158575047/288230376151711744), (312049829105/36028797018963968)), (13463/72057594037927936), by norm_num⟩
  | 5 => ⟨((149008849246331/18014398509481984), (4361759672787/72057594037927936)), (188779/144115188075855872), by norm_num⟩
  | 4 => ⟨((5811979272791/140737488355328), (6528781029573/18014398509481984)), (141881/18014398509481984), by norm_num⟩
  | 3 => ⟨((742267154740777/4503599627370496), (16273526142797/9007199254740992)), (11117/281474976710656), by norm_num⟩
  | 2 => ⟨((69327240988741/140737488355328), (16201042974141/2251799813685248)), (714621/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201816272070487/2251799813685248), (24120904131747/1125899906842624)), (269947/562949953421312), by norm_num⟩
  | 0 => ⟨((1075936673064041/1125899906842624), (11880612950771/281474976710656)), (2191153/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1075936673064041/1125899906842624), (11880612950771/281474976710656)), (8358585366255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2052369547234073/2251799813685248), (181654331359683/2251799813685248)), (4372807/2251799813685248), by norm_num⟩
  | 2 => ⟨((463986900268949/562949953421312), (165566146484233/1125899906842624)), (271143/70368744177664), by norm_num⟩
  | 3 => ⟨((1480989954002453/2251799813685248), (545842646436469/2251799813685248)), (16854399/2251799813685248), by norm_num⟩
  | 4 => ⟨((841720937033683/2251799813685248), (717992310795633/2251799813685248)), (1896319/140737488355328), by norm_num⟩
  | 5 => ⟨((171401717245353/4503599627370496), (536769882431791/2251799813685248)), (42031643/2251799813685248), by norm_num⟩
  | 6 => ⟨((-498760623054961/9007199254740992), (326861309980569/18014398509481984)), (46475657/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1112163223/16777216)), (1/16777216), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile013Terms3
