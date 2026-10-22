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
namespace Reinmann.XiBand97.Tile045Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨45,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (7297/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (7297/256))
  have he : value ((69/80), (7297/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1325896821/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((762220120667013/2251799813685248), (-976150713815399/2251799813685248)), (73775845/2251799813685248), by norm_num⟩
  | 1 => ⟨((-251927723/1073741824), (645271411/2147483648)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((174622991/2147483648), (-894536119/8589934592)), (73/8589934592), by norm_num⟩
  | 3 => ⟨((-645543647/34359738368), (413363459/17179869184)), (35/17179869184), by norm_num⟩
  | 4 => ⟨((447456759/137438953472), (-1146086865/274877906944)), (99/274877906944), by norm_num⟩
  | 5 => ⟨((-248122713/549755813888), (635525503/1099511627776)), (57/1099511627776), by norm_num⟩
  | 6 => ⟨((458628157/8796093022208), (-587350281/8796093022208)), (27/4398046511104), by norm_num⟩
  | 7 => ⟨((-726621289/140737488355328), (930560437/140737488355328)), (87/140737488355328), by norm_num⟩
  | 8 => ⟨((251827749/562949953421312), (-645015343/1125899906842624)), (31/562949953421312), by norm_num⟩
  | 9 => ⟨((-620635357/18014398509481984), (397413837/9007199254740992)), (39/9007199254740992), by norm_num⟩
  | 10 => ⟨((688306637/288230376151711744), (-440746049/144115188075855872)), (89/288230376151711744), by norm_num⟩
  | 11 => ⟨((-693960443/4611686018427387904), (888732745/4611686018427387904)), (23/1152921504606846976), by norm_num⟩
  | 12 => ⟨((641355633/73786976294838206464), (-410681731/36893488147419103232)), (87/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-273571599/590295810358705651712), (700708637/1180591620717411303424)), (77/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((216714723/9444732965739290427392), (-8673111/295147905179352825856)), (125/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-640918183/604462909807314587353088), (410401617/302231454903657293676544)), (47/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((888501263/19342813113834066795298816), (-1137874895/19342813113834066795298816)), (33/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1182571212377/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111315460967297/39614081257132168796771975168), (-87682654957/39614081257132168796771975168)), (46169/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946152482873391/19807040628566084398385987584), (-1578201766763/39614081257132168796771975168)), (51945/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892239855099649/2475880078570760549798248448), (-419184232377/618970019642690137449562112)), (13799/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886952839311233/77371252455336267181195264), (-1676621676901/154742504910672534362390528)), (55203/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776049138553825/4835703278458516698824704), (-785855184413/4835703278458516698824704)), (51759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261014976407971/604462909807314587353088), (-1375124122407/604462909807314587353088)), (45295/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472852230624687/18889465931478580854784), (-558586777713/18889465931478580854784)), (73615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40632855281539/147573952589676412928), (-1675559449873/4722366482869645213696)), (27611/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812587896019361/295147905179352825856), (-2303567820063/590295810358705651712)), (75945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228516550605691/9223372036854775808), (-719742540119/18446744073709551616)), (23739/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827894401240763/9223372036854775808), (-1619084122037/4611686018427387904)), (106859/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799569887726141/576460752303423488), (-1618663405745/576460752303423488)), (106901/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199086916587377/144115188075855872), (-707928604483/36028797018963968)), (46793/72057594037927936), by norm_num⟩
  | 4 => ⟨((749194796844057/18014398509481984), (-1061419679205/9007199254740992)), (140473/36028797018963968), by norm_num⟩
  | 3 => ⟨((748842807374069/4503599627370496), (-1325946549037/2251799813685248)), (175757/9007199254740992), by norm_num⟩
  | 2 => ⟨((561191768735029/1125899906842624), (-5298818684085/2251799813685248)), (88003/1125899906842624), by norm_num⟩
  | 1 => ⟨((280155024241713/281474976710656), (-7935812013113/1125899906842624)), (132315/562949953421312), by norm_num⟩
  | 0 => ⟨((1115319353803009/1125899906842624), (-3955494164271/281474976710656)), (531751/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115319353803009/1125899906842624), (-3955494164271/281474976710656)), (2028469089988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((552307944278063/562949953421312), (-15673290914955/562949953421312)), (534227/562949953421312), by norm_num⟩
  | 2 => ⟨((1082861492081673/1125899906842624), (-30754005867489/562949953421312)), (2156007/1125899906842624), by norm_num⟩
  | 3 => ⟨((519054033321423/562949953421312), (-118313638641459/1125899906842624)), (2191375/562949953421312), by norm_num⟩
  | 4 => ⟨((472364476840233/562949953421312), (-218176308428691/1125899906842624)), (9003123/1125899906842624), by norm_num⟩
  | 5 => ⟨((187608127780207/281474976710656), (-366138187465921/1125899906842624)), (37196129/2251799813685248), by norm_num⟩
  | 6 => ⟨((762220120667013/2251799813685248), (-976150713815399/2251799813685248)), (73775845/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1325896821/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1050748371/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1737063339210855/4503599627370496), (44091695363071/1125899906842624)), (58242741/2251799813685248), by norm_num⟩
  | 1 => ⟨((-909976545/2147483648), (-184782709/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((999711415/4294967296), (101502277/4294967296)), (71/4294967296), by norm_num⟩
  | 3 => ⟨((-1464393661/17179869184), (-74341099/8589934592)), (107/17179869184), by norm_num⟩
  | 4 => ⟨((201100109/8589934592), (81672045/34359738368)), (15/8589934592), by norm_num⟩
  | 5 => ⟨((-1413958727/274877906944), (-35890365/68719476736)), (27/68719476736), by norm_num⟩
  | 6 => ⟨((258898739/274877906944), (105145589/1099511627776)), (81/1099511627776), by norm_num⟩
  | 7 => ⟨((-650124197/4398046511104), (-66008135/4398046511104)), (13/1099511627776), by norm_num⟩
  | 8 => ⟨((11159913/549755813888), (145034697/70368744177664)), (117/70368744177664), by norm_num⟩
  | 9 => ⟨((-1394963065/562949953421312), (-4426025/17592186044416)), (117/562949953421312), by norm_num⟩
  | 10 => ⟨((1226018853/4503599627370496), (31119907/1125899906842624)), (105/4503599627370496), by norm_num⟩
  | 11 => ⟨((-489788865/18014398509481984), (-12432259/4503599627370496)), (43/18014398509481984), by norm_num⟩
  | 12 => ⟨((717450755/288230376151711744), (72843907/288230376151711744)), (129/576460752303423488), by norm_num⟩
  | 13 => ⟨((-1940185147/9223372036854775808), (-196990059/9223372036854775808)), (177/9223372036854775808), by norm_num⟩
  | 14 => ⟨((609003213/36893488147419103232), (61833057/36893488147419103232)), (113/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-178415577/147573952589676412928), (-18114815/147573952589676412928)), (67/590295810358705651712), by norm_num⟩
  | 16 => ⟨((1568076363/18889465931478580854784), (159209267/18889465931478580854784)), (75/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (65902272473/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780508143341803/633825300114114700748351602688), (156273967817/633825300114114700748351602688)), (11527/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891698434684409/39614081257132168796771975168), (5493540797/1237940039285380274899124224)), (103743/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891595543395237/2475880078570760549798248448), (93381162359/1237940039285380274899124224)), (110229/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773261510388889/154742504910672534362390528), (46685501891/38685626227668133590597632)), (55115/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551494521802439/9671406556917033397649408), (175049048233/9671406556917033397649408)), (51671/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39390213840709/18889465931478580854784), (153146336855/604462909807314587353088)), (45213/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945275495610261/37778931862957161709568), (248822341691/75557863725914323419136)), (287/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1299608170452615/4722366482869645213696), (186581364985/4722366482869645213696)), (55105/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624291800006665/590295810358705651712), (128245939995/295147905179352825856)), (151543/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827028023592347/73786976294838206464), (160264314567/36893488147419103232)), (189433/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826652809107339/9223372036854775808), (180238096905/4611686018427387904)), (1665/72057594037927936), by norm_num⟩
  | 6 => ⟨((1597899228831125/1152921504606846976), (360328110891/1152921504606846976)), (106565/576460752303423488), by norm_num⟩
  | 5 => ⟨((599001306932635/72057594037927936), (315120585575/144115188075855872)), (186499/144115188075855872), by norm_num⟩
  | 4 => ⟨((748382744586789/18014398509481984), (472348059917/36028797018963968)), (139885/18014398509481984), by norm_num⟩
  | 3 => ⟨((46739362259677/281474976710656), (589853102357/9007199254740992)), (174875/4503599627370496), by norm_num⟩
  | 2 => ⟨((280090917565405/562949953421312), (147245265571/562949953421312)), (174903/1125899906842624), by norm_num⟩
  | 1 => ⟨((2235211318953675/2251799813685248), (440647352721/562949953421312)), (524851/1125899906842624), by norm_num⟩
  | 0 => ⟨((1109351783735367/1125899906842624), (3507802210379/2251799813685248)), (1050273/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109351783735367/1125899906842624), (3507802210379/2251799813685248)), (4006473545554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1093044147555625/1125899906842624), (6912491271071/2251799813685248)), (4145891/2251799813685248), by norm_num⟩
  | 2 => ⟨((2122273135668191/2251799813685248), (13421544993395/2251799813685248)), (2018817/562949953421312), by norm_num⟩
  | 3 => ⟨((2000117016235985/2251799813685248), (25299037867871/2251799813685248)), (15317799/2251799813685248), by norm_num⟩
  | 4 => ⟨((222035059078679/281474976710656), (44942748308621/2251799813685248)), (13777831/1125899906842624), by norm_num⟩
  | 5 => ⟨((1400280987526473/2251799813685248), (17726026470411/562949953421312)), (22286623/1125899906842624), by norm_num⟩
  | 6 => ⟨((1737063339210855/4503599627370496), (44091695363071/1125899906842624)), (58242741/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1050748371/33554432)), (1/16777216), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1325896821/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-330305297542535/4503599627370496), (-1321683589014733/4503599627370496)), (229965985/4503599627370496), by norm_num⟩
  | 1 => ⟨((27292989/268435456), (436840655/1073741824)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-151344467/2147483648), (-605589737/2147483648)), (107/2147483648), by norm_num⟩
  | 3 => ⟨((279743975/8589934592), (1119367517/8589934592)), (199/8589934592), by norm_num⟩
  | 4 => ⟨((-387807495/34359738368), (-1551772877/34359738368)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((215046137/68719476736), (215121399/17179869184)), (39/17179869184), by norm_num⟩
  | 6 => ⟨((-397489663/549755813888), (-795257553/274877906944)), (291/549755813888), by norm_num⟩
  | 7 => ⟨((314878673/2199023255552), (1259955499/2199023255552)), (233/2199023255552), by norm_num⟩
  | 8 => ⟨((-13641079/549755813888), (-436667301/4398046511104)), (163/8796093022208), by norm_num⟩
  | 9 => ⟨((268950057/70368744177664), (538088371/35184372088832)), (203/70368744177664), by norm_num⟩
  | 10 => ⟨((-149137579/281474976710656), (-1193518199/562949953421312)), (227/562949953421312), by norm_num⟩
  | 11 => ⟨((150362607/2251799813685248), (601660927/2251799813685248)), (231/4503599627370496), by norm_num⟩
  | 12 => ⟨((-34741139/4503599627370496), (-556052767/18014398509481984)), (215/36028797018963968), by norm_num⟩
  | 13 => ⟨((237102499/288230376151711744), (948741927/288230376151711744)), (185/288230376151711744), by norm_num⟩
  | 14 => ⟨((-375650123/4611686018427387904), (-1503126381/4611686018427387904)), (295/4611686018427387904), by norm_num⟩
  | 15 => ⟨((277739545/36893488147419103232), (1111347001/36893488147419103232)), (55/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-385028765/590295810358705651712), (-1540654081/590295810358705651712)), (307/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-2365142424753/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111257551588329/39614081257132168796771975168), (-1401541643927/316912650057057350374175801344)), (23119/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891262496588923/39614081257132168796771975168), (-3153125727981/39614081257132168796771975168)), (26013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891132100769109/2475880078570760549798248448), (-1674893224947/1237940039285380274899124224)), (110577/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886398888593801/77371252455336267181195264), (-837331402071/38685626227668133590597632)), (13825/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551059463315735/9671406556917033397649408), (-1569751567413/4835703278458516698824704)), (3241/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((630052929128797/302231454903657293676544), (-2746575643935/604462909807314587353088)), (22693/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889931313092571/75557863725914323419136), (-1115566868515/18889465931478580854784)), (73775/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299142906336991/4722366482869645213696), (-836474363141/1180591620717411303424)), (110703/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((12684775319849/4611686018427387904), (-574912996169/73786976294838206464)), (152281/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913113047191639/36893488147419103232), (-5747172587549/73786976294838206464)), (95225/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825748948577631/9223372036854775808), (-1615719511185/2305843009213693952)), (214391/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596993257985901/1152921504606846976), (-403719660017/72057594037927936)), (214559/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598603759282001/72057594037927936), (-5648291886845/144115188075855872)), (187929/144115188075855872), by norm_num⟩
  | 4 => ⟨((186946014103277/4503599627370496), (-1058109068153/4503599627370496)), (282273/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494154606931893/9007199254740992), (-10567854645775/9007199254740992)), (176753/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118846324429567/2251799813685248), (-5274003526807/1125899906842624)), (354505/2251799813685248), by norm_num⟩
  | 1 => ⟨((557649434397569/562949953421312), (-7886207186907/562949953421312)), (33391/70368744177664), by norm_num⟩
  | 0 => ⟨((552307944278063/562949953421312), (-31346581829911/1125899906842624)), (1078531/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552307944278063/562949953421312), (-31346581829911/1125899906842624)), (4114269260886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082861492081673/1125899906842624), (-15377002933745/281474976710656)), (2176341/1125899906842624), by norm_num⟩
  | 2 => ⟨((519054033321423/562949953421312), (-118313638641463/1125899906842624)), (4424085/1125899906842624), by norm_num⟩
  | 3 => ⟨((944728953680465/1125899906842624), (-109088154214349/562949953421312)), (4544017/562949953421312), by norm_num⟩
  | 4 => ⟨((1500865022241647/2251799813685248), (-732276374931865/2251799813685248)), (4693367/281474976710656), by norm_num⟩
  | 5 => ⟨((381110060333493/1125899906842624), (-976150713815423/2251799813685248)), (37235823/1125899906842624), by norm_num⟩
  | 6 => ⟨((-330305297542535/4503599627370496), (-1321683589014733/4503599627370496)), (229965985/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1325896821/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-384829635/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-355835553122011/4503599627370496), (-266500530643273/1125899906842624)), (24149199/562949953421312), by norm_num⟩
  | 1 => ⟨((136541183/1073741824), (102261557/268435456)), (75/1073741824), by norm_num⟩
  | 2 => ⟨((-439509113/4294967296), (-1316669015/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((235787543/4294967296), (706365677/4294967296)), (263/8589934592), by norm_num⟩
  | 4 => ⟨((-379485411/17179869184), (-1136851701/17179869184)), (213/17179869184), by norm_num⟩
  | 5 => ⟨((244303283/34359738368), (1463753783/68719476736)), (69/17179869184), by norm_num⟩
  | 6 => ⟨((-524254621/274877906944), (-785273611/137438953472)), (149/137438953472), by norm_num⟩
  | 7 => ⟨((482145865/1099511627776), (361099749/274877906944)), (69/274877906944), by norm_num⟩
  | 8 => ⟨((-387991917/4398046511104), (-1162335253/4398046511104)), (7/137438953472), by norm_num⟩
  | 9 => ⟨((277532845/17592186044416), (831425077/17592186044416)), (81/8796093022208), by norm_num⟩
  | 10 => ⟨((-178668753/70368744177664), (-4181647/549755813888)), (211/140737488355328), by norm_num⟩
  | 11 => ⟨((209131829/562949953421312), (626511241/562949953421312)), (249/1125899906842624), by norm_num⟩
  | 12 => ⟨((-56097449/1125899906842624), (-1344441259/9007199254740992)), (269/9007199254740992), by norm_num⟩
  | 13 => ⟨((222240889/36028797018963968), (665782995/36028797018963968)), (67/18014398509481984), by norm_num⟩
  | 14 => ⟨((-408780471/576460752303423488), (-1224613021/576460752303423488)), (249/576460752303423488), by norm_num⟩
  | 15 => ⟨((87720905/1152921504606846976), (525583633/2305843009213693952)), (27/576460752303423488), by norm_num⟩
  | 16 => ⟨((-70590675/9223372036854775808), (-845894225/36893488147419103232)), (11/2305843009213693952), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-2465805083849/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779823384389453/633825300114114700748351602688), (-1460729109193/316912650057057350374175801344)), (11561/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890927894835909/39614081257132168796771975168), (-3286227830767/39614081257132168796771975168)), (104067/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890776606617603/2475880078570760549798248448), (-872780390313/618970019642690137449562112)), (27/604462909807314587353088), by norm_num⟩
  | 14 => ⟨((886221152902533/77371252455336267181195264), (-3490564134183/154742504910672534362390528)), (13827/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550726233110923/9671406556917033397649408), (-408976457255/1208925819614629174706176)), (6483/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259814306072015/604462909807314587353088), (-1431121518773/302231454903657293676544)), (22697/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889457586305821/75557863725914323419136), (-1162508686465/18889465931478580854784)), (147577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298787651130355/4722366482869645213696), (-1743277379507/2361183241434822606848)), (55363/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811581414975349/295147905179352825856), (-4792434648205/590295810358705651712)), (152315/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825615678214367/73786976294838206464), (-1497044118345/18446744073709551616)), (5953/2305843009213693952), by norm_num⟩
  | 7 => ⟨((228132795606561/1152921504606846976), (-6733444752081/9223372036854775808)), (13403/576460752303423488), by norm_num⟩
  | 6 => ⟨((99769177675213/72057594037927936), (-1682344614493/288230376151711744)), (214625/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196607095523415/144115188075855872), (-5883632852475/144115188075855872)), (93997/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494667860334507/36028797018963968), (-4408152947135/18014398509481984)), (282387/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493029963487143/9007199254740992), (-11004388687289/9007199254740992)), (353677/9007199254740992), by norm_num⟩
  | 2 => ⟨((139715337039549/281474976710656), (-10980412688573/2251799813685248)), (354719/2251799813685248), by norm_num⟩
  | 1 => ⟨((278403997407213/281474976710656), (-16410730032393/1125899906842624)), (16709/35184372088832), by norm_num⟩
  | 0 => ⟨((1101260529532957/1125899906842624), (-16291105693795/562949953421312)), (1079833/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101260529532957/1125899906842624), (-16291105693795/562949953421312)), (4119235996726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538108736862021/562949953421312), (-31869176956125/562949953421312)), (2174903/1125899906842624), by norm_num⟩
  | 2 => ⟨((1025119076726991/1125899906842624), (-60925780178041/562949953421312)), (2202055/562949953421312), by norm_num⟩
  | 3 => ⟨((920171777626055/1125899906842624), (-110944461662017/562949953421312)), (8973063/1125899906842624), by norm_num⟩
  | 4 => ⟨((1416611549923621/2251799813685248), (-181344650416733/562949953421312)), (36407439/2251799813685248), by norm_num⟩
  | 5 => ⟨((328762387895749/1125899906842624), (-14260533104227/35184372088832)), (69264041/2251799813685248), by norm_num⟩
  | 6 => ⟨((-355835553122011/4503599627370496), (-266500530643273/1125899906842624)), (24149199/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-384829635/8388608)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1713696781/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((664439708094039/4503599627370496), (-693314422219053/4503599627370496)), (27420083/2251799813685248), by norm_num⟩
  | 1 => ⟨((-141920583/536870912), (296176119/1073741824)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((508575097/2147483648), (-265338183/1073741824)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((-151874041/1073741824), (633896269/4294967296)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((272121751/4294967296), (-567894821/8589934592)), (51/8589934592), by norm_num⟩
  | 5 => ⟨((-780122759/34359738368), (814024739/34359738368)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((931861561/137438953472), (-486178845/68719476736)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-477049079/274877906944), (248890157/137438953472)), (3/17179869184), by norm_num⟩
  | 8 => ⟨((854757205/2199023255552), (-891902591/2199023255552)), (11/274877906944), by norm_num⟩
  | 9 => ⟨((-170168813/2199023255552), (710255517/8796093022208)), (9/1099511627776), by norm_num⟩
  | 10 => ⟨((975685063/70368744177664), (-1018085639/70368744177664)), (105/70368744177664), by norm_num⟩
  | 11 => ⟨((-19865829/8796093022208), (20729143/8796093022208)), (35/140737488355328), by norm_num⟩
  | 12 => ⟨((759355461/2251799813685248), (-396177475/1125899906842624)), (85/2251799813685248), by norm_num⟩
  | 13 => ⟨((-837281439/18014398509481984), (873667375/18014398509481984)), (3/562949953421312), by norm_num⟩
  | 14 => ⟨((857261113/144115188075855872), (-447257655/72057594037927936)), (25/36028797018963968), by norm_num⟩
  | 15 => ⟨((-819203049/1152921504606846976), (213700837/288230376151711744)), (97/1152921504606846976), by norm_num⟩
  | 16 => ⟨((366953705/4611686018427387904), (-765800997/9223372036854775808)), (89/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-262691662005/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55612014242563/19807040628566084398385987584), (-38894181827/19807040628566084398385987584)), (23081/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945329676956663/19807040628566084398385987584), (-1399998849889/39614081257132168796771975168)), (1623/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((945245800168359/1237940039285380274899124224), (-743632096519/1237940039285380274899124224)), (27593/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772157657629661/154742504910672534362390528), (-371750086453/38685626227668133590597632)), (6899/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550459755785237/9671406556917033397649408), (-1393782546823/9671406556917033397649408)), (12937/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157447689822999/75557863725914323419136), (-1219279518931/604462909807314587353088)), (11321/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472270004776457/18889465931478580854784), (-1980803969495/75557863725914323419136)), (73597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324626274696409/1180591620717411303424), (-1485143528525/4722366482869645213696)), (55207/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811387666138753/295147905179352825856), (-127582876113/36893488147419103232)), (18981/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825132822662465/73786976294838206464), (-1275269246907/36893488147419103232)), (47463/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824521235711745/9223372036854775808), (-2867817908789/9223372036854775808)), (53411/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797884157513927/576460752303423488), (-2865896688321/1152921504606846976)), (26715/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196138806368459/144115188075855872), (-1252749905113/72057594037927936)), (93545/144115188075855872), by norm_num⟩
  | 4 => ⟨((746985631094215/18014398509481984), (-938483520221/9007199254740992)), (140401/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492169406250333/9007199254740992), (-2342437059945/4503599627370496)), (175649/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233754762271649/4503599627370496), (-9347153274307/4503599627370496)), (175871/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224771939144497/2251799813685248), (-6982183249915/1125899906842624)), (66091/281474976710656), by norm_num⟩
  | 0 => ⟨((1098951387456567/1125899906842624), (-3463002749315/281474976710656)), (1061925/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098951387456567/1125899906842624), (-3463002749315/281474976710656)), (4050922402388762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144954922627643/2251799813685248), (-54081847283181/2251799813685248)), (1049573/1125899906842624), by norm_num⟩
  | 2 => ⟨((63808774568283/70368744177664), (-6439466990463/140737488355328)), (4099921/2251799813685248), by norm_num⟩
  | 3 => ⟨((923408385489357/1125899906842624), (-46713296061893/562949953421312)), (976327/281474976710656), by norm_num⟩
  | 4 => ⟨((749582190341333/1125899906842624), (-306495801520149/2251799813685248)), (7054009/1125899906842624), by norm_num⟩
  | 5 => ⟨((956370167041493/2251799813685248), (-408106960197145/2251799813685248)), (22625713/2251799813685248), by norm_num⟩
  | 6 => ⟨((664439708094039/4503599627370496), (-693314422219053/4503599627370496)), (27420083/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1713696781/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1861131483/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((98579005096467/1125899906842624), (742537474781015/4503599627370496)), (111363389/4503599627370496), by norm_num⟩
  | 1 => ⟨((-731757685/4294967296), (-1377974709/4294967296)), (13/268435456), by norm_num⟩
  | 2 => ⟨((711967353/4294967296), (670353743/2147483648)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((-230904083/2147483648), (-869632101/4294967296)), (67/2147483648), by norm_num⟩
  | 4 => ⟨((449318599/8589934592), (423056483/4294967296)), (33/2147483648), by norm_num⟩
  | 5 => ⟨((-349733449/17179869184), (-658583923/17179869184)), (13/2147483648), by norm_num⟩
  | 6 => ⟨((56712489/8589934592), (854363427/68719476736)), (17/8589934592), by norm_num⟩
  | 7 => ⟨((-492667/268435456), (-950008265/274877906944)), (153/274877906944), by norm_num⟩
  | 8 => ⟨((245423543/549755813888), (462157681/549755813888)), (151/1099511627776), by norm_num⟩
  | 9 => ⟨((-212254295/2199023255552), (-799393175/4398046511104)), (33/1099511627776), by norm_num⟩
  | 10 => ⟨((660844459/35184372088832), (622218917/17592186044416)), (207/35184372088832), by norm_num⟩
  | 11 => ⟨((-233807989/70368744177664), (-220142201/35184372088832)), (37/35184372088832), by norm_num⟩
  | 12 => ⟨((606625785/1125899906842624), (1142338515/1125899906842624)), (97/562949953421312), by norm_num⟩
  | 13 => ⟨((-726424167/9007199254740992), (-1367931145/9007199254740992)), (117/4503599627370496), by norm_num⟩
  | 14 => ⟨((100968297/9007199254740992), (95066825/4503599627370496)), (33/9007199254740992), by norm_num⟩
  | 15 => ⟨((-209573583/144115188075855872), (-789297065/288230376151711744)), (139/288230376151711744), by norm_num⟩
  | 16 => ⟨((203905681/1152921504606846976), (767950585/2305843009213693952)), (137/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (1410242937291/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444844669051281/158456325028528675187087900672), (1670040680015/633825300114114700748351602688)), (92365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890427846831865/39614081257132168796771975168), (1878516628419/39614081257132168796771975168)), (103921/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890245615582403/2475880078570760549798248448), (1995582027773/2475880078570760549798248448)), (27607/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771911663361311/154742504910672534362390528), (1995197491693/154742504910672534362390528)), (55221/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387557281517767/2417851639229258349412352), (29220143271/151115727451828646838272)), (51777/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157422463440027/75557863725914323419136), (1635919645821/604462909807314587353088)), (177/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((1888752057307779/75557863725914323419136), (2657603933117/75557863725914323419136)), (147291/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324564777755109/1180591620717411303424), (996266680527/2361183241434822606848)), (110493/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811218536258781/295147905179352825856), (684661423705/147573952589676412928)), (75983/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824709958253199/73786976294838206464), (3421676312343/73786976294838206464)), (2969/1152921504606846976), by norm_num⟩
  | 7 => ⟨((28500710295603/144115188075855872), (961786161043/2305843009213693952)), (26731/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595292470719729/1152921504606846976), (3844344861297/1152921504606846976)), (213949/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195722367195019/144115188075855872), (1680327185031/72057594037927936)), (93659/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493346453994569/36028797018963968), (2517346357255/18014398509481984)), (70301/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491388137584043/9007199254740992), (6282373746315/9007199254740992)), (351903/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232191461975337/4503599627370496), (12531824296139/4503599627370496)), (704999/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222425124225927/2251799813685248), (18715614569345/2251799813685248)), (1060489/2251799813685248), by norm_num⟩
  | 0 => ⟨((274150242955877/281474976710656), (37103856438285/2251799813685248)), (133311/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274150242955877/281474976710656), (37103856438285/2251799813685248)), (508541107714605287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1067758785712071/1125899906842624), (72276629176967/2251799813685248)), (4225233/2251799813685248), by norm_num⟩
  | 2 => ⟨((1011460112717817/1125899906842624), (68544286518133/1125899906842624)), (2071331/562949953421312), by norm_num⟩
  | 3 => ⟨((1808958743518579/2251799813685248), (246308970616103/2251799813685248)), (15895173/2251799813685248), by norm_num⟩
  | 4 => ⟨((713132581152987/1125899906842624), (395739233385815/2251799813685248)), (7253939/562949953421312), by norm_num⟩
  | 5 => ⟨((416916006688449/1125899906842624), (250656865013293/1125899906842624)), (46955183/2251799813685248), by norm_num⟩
  | 6 => ⟨((98579005096467/1125899906842624), (742537474781015/4503599627370496)), (111363389/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1861131483/33554432)), (1/16777216), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1988845231/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-342376729722273/2251799813685248), (-608389868000491/9007199254740992)), (398030345/9007199254740992), by norm_num⟩
  | 1 => ⟨((1357941427/4294967296), (603252013/4294967296)), (397/4294967296), by norm_num⟩
  | 2 => ⟨((-1411879907/4294967296), (-39200853/268435456)), (415/4294967296), by norm_num⟩
  | 3 => ⟨((978640577/4294967296), (108687843/1073741824)), (145/2147483648), by norm_num⟩
  | 4 => ⟨((-1017512935/8589934592), (-7062813/134217728)), (19/536870912), by norm_num⟩
  | 5 => ⟨((846343467/17179869184), (375979693/17179869184)), (255/17179869184), by norm_num⟩
  | 6 => ⟨((-146660147/8589934592), (-16288079/2147483648)), (89/17179869184), by norm_num⟩
  | 7 => ⟨((1394154067/274877906944), (38708695/17179869184)), (213/137438953472), by norm_num⟩
  | 8 => ⟨((-1449530941/1099511627776), (-643939747/1099511627776)), (223/549755813888), by norm_num⟩
  | 9 => ⟨((1339651047/4398046511104), (595126693/4398046511104)), (415/4398046511104), by norm_num⟩
  | 10 => ⟨((-1114290415/17592186044416), (-495012467/17592186044416)), (87/4398046511104), by norm_num⟩
  | 11 => ⟨((842582465/70368744177664), (374308905/70368744177664)), (265/70368744177664), by norm_num⟩
  | 12 => ⟨((-146008415/70368744177664), (-129725581/140737488355328)), (185/281474976710656), by norm_num⟩
  | 13 => ⟨((186840593/562949953421312), (332008323/2251799813685248)), (239/2251799813685248), by norm_num⟩
  | 14 => ⟨((-888055065/18014398509481984), (-394509657/18014398509481984)), (143/9007199254740992), by norm_num⟩
  | 15 => ⟨((984884583/144115188075855872), (218762605/72057594037927936)), (5/2251799813685248), by norm_num⟩
  | 16 => ⟨((-512002479/576460752303423488), (-454904049/1152921504606846976)), (335/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-3547713617719/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889596543901597/316912650057057350374175801344), (-1050120600661/158456325028528675187087900672)), (17365/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890218636069897/39614081257132168796771975168), (-590596692037/4951760157141521099596496896)), (156325/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890022782277151/2475880078570760549798248448), (-1254787642791/618970019642690137449562112)), (166141/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771688215222927/154742504910672534362390528), (-2509057030675/77371252455336267181195264)), (166193/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550018990559283/9671406556917033397649408), (-4703380713591/9671406556917033397649408)), (155861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259195186490525/604462909807314587353088), (-4114356987053/604462909807314587353088)), (68217/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888450988181085/75557863725914323419136), (-6683765645157/75557863725914323419136)), (221807/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298032240431533/4722366482869645213696), (-1252754501627/1180591620717411303424)), (166447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622123390441235/590295810358705651712), (-3443607483363/295147905179352825856)), (229011/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824315256092929/73786976294838206464), (-4302308547185/36893488147419103232)), (71621/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455899462348519/2305843009213693952), (-9674142948143/9223372036854775808)), (322599/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797420203204581/576460752303423488), (-9666580254113/1152921504606846976)), (322979/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195321809190901/144115188075855872), (-1056218954827/18014398509481984)), (141517/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492735638256581/36028797018963968), (-6328810091989/18014398509481984)), (425407/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490607210719689/9007199254740992), (-7896136791023/4503599627370496)), (133315/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115288804362245/2251799813685248), (-15747668450313/2251799813685248)), (267757/1125899906842624), by norm_num⟩
  | 1 => ⟨((554968780343045/562949953421312), (-5877517207899/281474976710656)), (808919/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093794845053939/1125899906842624), (-46574882535137/1125899906842624)), (820251/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093794845053939/1125899906842624), (-46574882535137/1125899906842624)), (3129009248973655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1060678605731809/1125899906842624), (-45246798686383/562949953421312)), (830793/281474976710656), by norm_num⟩
  | 2 => ⟨((991962080025131/1125899906842624), (-42625735247715/281474976710656)), (6795531/1125899906842624), by norm_num⟩
  | 3 => ⟨((848137129701999/1125899906842624), (-300439587867089/1125899906842624)), (3508113/281474976710656), by norm_num⟩
  | 4 => ⟨((1117457495108097/2251799813685248), (-905281075711331/2251799813685248)), (57260323/2251799813685248), by norm_num⟩
  | 5 => ⟨((381186129178877/4503599627370496), (-898492945141125/2251799813685248)), (205742385/4503599627370496), by norm_num⟩
  | 6 => ⟨((-342376729722273/2251799813685248), (-608389868000491/9007199254740992)), (398030345/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1988845231/33554432)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile045Terms0
