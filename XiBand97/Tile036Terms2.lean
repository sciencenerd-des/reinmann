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
namespace Reinmann.XiBand97.Tile036Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33263/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33263/1280))
  have he : value ((69/80), (33263/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-604403261/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1613511588977217/18014398509481984), (-168707485541769/9007199254740992)), (566271513/18014398509481984), by norm_num⟩
  | 1 => ⟨((533295159/2147483648), (223043667/4294967296)), (47/536870912), by norm_num⟩
  | 2 => ⟨((-92413009/268435456), (-154602089/2147483648)), (131/1073741824), by norm_num⟩
  | 3 => ⟨((170815511/536870912), (285765339/4294967296)), (243/2147483648), by norm_num⟩
  | 4 => ⟨((-947202319/4294967296), (-198077439/4294967296)), (169/2147483648), by norm_num⟩
  | 5 => ⟨((1050480987/8589934592), (219674909/8589934592)), (377/8589934592), by norm_num⟩
  | 6 => ⟨((-970850579/17179869184), (-203022725/17179869184)), (175/8589934592), by norm_num⟩
  | 7 => ⟨((384538481/17179869184), (40207037/8589934592)), (557/68719476736), by norm_num⟩
  | 8 => ⟨((-66635441/8589934592), (-222955155/137438953472)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((328449195/137438953472), (17171193/34359738368)), (15/17179869184), by norm_num⟩
  | 10 => ⟨((-728523627/1099511627776), (-304695399/2199023255552)), (535/2199023255552), by norm_num⟩
  | 11 => ⟨((734507779/4398046511104), (19199887/549755813888)), (541/8796093022208), by norm_num⟩
  | 12 => ⟨((-42426833/1099511627776), (-141955707/17592186044416)), (251/17592186044416), by norm_num⟩
  | 13 => ⟨((289556083/35184372088832), (121103013/70368744177664)), (215/70368744177664), by norm_num⟩
  | 14 => ⟨((-229377123/140737488355328), (-191867913/562949953421312)), (171/281474976710656), by norm_num⟩
  | 15 => ⟨((1356732639/4503599627370496), (141858883/2251799813685248)), (127/1125899906842624), by norm_num⟩
  | 16 => ⟨((-235103851/4503599627370496), (-98329085/9007199254740992)), (177/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-119492025427/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778269976215159/633825300114114700748351602688), (-4522837704689/633825300114114700748351602688)), (92645/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((3689805188473/77371252455336267181195264), (-5087107352085/39614081257132168796771975168)), (208509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888919629013725/2475880078570760549798248448), (-2701865030259/1237940039285380274899124224)), (221607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770585202882343/154742504910672534362390528), (-5402243521637/154742504910672534362390528)), (110841/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193623133297303/1208925819614629174706176), (-2531512072945/4835703278458516698824704)), (103953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629145326449255/302231454903657293676544), (-2214283649851/302231454903657293676544)), (90999/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471745350711403/18889465931478580854784), (-3596731128147/37778931862957161709568)), (147947/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324232574584843/1180591620717411303424), (-2696253867137/2361183241434822606848)), (222051/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810304310998909/295147905179352825856), (-7410492385745/590295810358705651712)), (76383/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455605599917739/18446744073709551616), (-4628404574531/36893488147419103232)), (47779/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821469218599667/9223372036854775808), (-2601310702299/2305843009213693952)), (430449/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796356409727745/576460752303423488), (-5197207023401/576460752303423488)), (430995/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193461349027215/144115188075855872), (-9082937630603/144115188075855872)), (377737/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489947315067175/36028797018963968), (-13600076393591/36028797018963968)), (17745/1125899906842624), by norm_num⟩
  | 3 => ⟨((1487125971966979/9007199254740992), (-8478780661403/4503599627370496)), (88995/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111813858990273/2251799813685248), (-4223461771025/562949953421312)), (715209/2251799813685248), by norm_num⟩
  | 1 => ⟨((552370517173453/562949953421312), (-196732737059/8796093022208)), (270239/281474976710656), by norm_num⟩
  | 0 => ⟨((541733150088923/562949953421312), (-49729497482549/1125899906842624)), (2194615/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((541733150088923/562949953421312), (-49729497482549/1125899906842624)), (8371791843894576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040435471734117/1125899906842624), (-186934615867/2199023255552)), (2208837/562949953421312), by norm_num⟩
  | 2 => ⟨((953322280288357/1125899906842624), (-44222680399575/281474976710656)), (8915753/1125899906842624), by norm_num⟩
  | 3 => ⟨((779405911105813/1125899906842624), (-599107842717019/2251799813685248)), (35799631/2251799813685248), by norm_num⟩
  | 4 => ⟨((229923201573633/562949953421312), (-414733309031853/1125899906842624)), (68614207/2251799813685248), by norm_num⟩
  | 5 => ⟨((70086153533153/2251799813685248), (-1355101776025415/4503599627370496)), (213193355/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1613511588977217/18014398509481984), (-168707485541769/9007199254740992)), (566271513/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-604403261/8388608)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1235237935/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-156559330897589/9007199254740992), (383194973293737/4503599627370496)), (66699135/2251799813685248), by norm_num⟩
  | 1 => ⟨((26438593/536870912), (-1035378563/4294967296)), (181/2147483648), by norm_num⟩
  | 2 => ⟨((-149812349/2147483648), (1466724181/4294967296)), (515/4294967296), by norm_num⟩
  | 3 => ⟨((141483449/2147483648), (-1385180841/4294967296)), (489/4294967296), by norm_num⟩
  | 4 => ⟨((-100213199/2147483648), (981128211/4294967296)), (87/1073741824), by norm_num⟩
  | 5 => ⟨((113570149/4294967296), (-138987277/1073741824)), (99/2147483648), by norm_num⟩
  | 6 => ⟨((-53628077/4294967296), (1050081621/17179869184)), (47/2147483648), by norm_num⟩
  | 7 => ⟨((347290933/68719476736), (-1700060149/68719476736)), (611/68719476736), by norm_num⟩
  | 8 => ⟨((-122993663/68719476736), (1204158275/137438953472)), (435/137438953472), by norm_num⟩
  | 9 => ⟨((77437175/137438953472), (-1516283241/549755813888)), (275/274877906944), by norm_num⟩
  | 10 => ⟨((-87758415/549755813888), (1718381565/2199023255552)), (625/2199023255552), by norm_num⟩
  | 11 => ⟨((361655727/8796093022208), (-1770378757/8796093022208)), (323/4398046511104), by norm_num⟩
  | 12 => ⟨((-341549277/35184372088832), (1671953573/35184372088832)), (153/8796093022208), by norm_num⟩
  | 13 => ⟨((148874149/70368744177664), (-1457538823/140737488355328)), (67/17592186044416), by norm_num⟩
  | 14 => ⟨((-241024129/562949953421312), (294965603/140737488355328)), (109/140737488355328), by norm_num⟩
  | 15 => ⟨((364198815/4503599627370496), (-111426731/281474976710656)), (661/4503599627370496), by norm_num⟩
  | 16 => ⟨((-64490809/4503599627370496), (1262782805/18014398509481984)), (235/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1154312803463/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889098190291641/316912650057057350374175801344), (2730474422165/633825300114114700748351602688)), (92469/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889097867536697/39614081257132168796771975168), (3071127595279/39614081257132168796771975168)), (104045/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888832625572989/2475880078570760549798248448), (1631129648977/1237940039285380274899124224)), (221135/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885249400301285/77371252455336267181195264), (1630672057147/77371252455336267181195264)), (55295/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548904702520453/9671406556917033397649408), (3056538024869/9671406556917033397649408)), (207405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258220972291381/604462909807314587353088), (2673499027295/604462909807314587353088)), (181527/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943434683295189/37778931862957161709568), (2171307308067/37778931862957161709568)), (147535/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296847315453687/4722366482869645213696), (3255368039201/4722366482869645213696)), (110691/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810248107747601/295147905179352825856), (4473543898857/590295810358705651712)), (19033/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822284430437595/73786976294838206464), (1397012873295/18446744073709551616)), (380851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821317488423799/9223372036854775808), (3140614488611/4611686018427387904)), (214361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398141359287253/288230376151711744), (1568643378467/288230376151711744)), (107263/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193337268988085/144115188075855872), (685346537283/18014398509481984)), (375793/144115188075855872), by norm_num⟩
  | 4 => ⟨((186221365540103/4503599627370496), (4104609526795/18014398509481984)), (282217/18014398509481984), by norm_num⟩
  | 3 => ⟨((743461221617965/4503599627370496), (1279428008365/1125899906842624)), (22089/281474976710656), by norm_num⟩
  | 2 => ⟨((2223271273786201/4503599627370496), (20392725422455/4503599627370496)), (1417619/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104536503786767/1125899906842624), (30394398262167/2251799813685248)), (534067/562949953421312), by norm_num⟩
  | 0 => ⟨((2166611350290665/2251799813685248), (60013730649193/2251799813685248)), (4312059/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166611350290665/2251799813685248), (60013730649193/2251799813685248)), (16449199685103606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520761555582661/562949953421312), (3608958409835/70368744177664)), (8527703/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921016409777267/2251799813685248), (106831907688661/1125899906842624)), (16651957/2251799813685248), by norm_num⟩
  | 3 => ⟨((1618550547203033/2251799813685248), (364554338286155/2251799813685248)), (31571727/2251799813685248), by norm_num⟩
  | 4 => ⟨((552181857635499/1125899906842624), (524069342338769/2251799813685248)), (55608893/2251799813685248), by norm_num⟩
  | 5 => ⟨((839302440905041/4503599627370496), (514044954127321/2251799813685248)), (40214659/1125899906842624), by norm_num⟩
  | 6 => ⟨((-156559330897589/9007199254740992), (383194973293737/4503599627370496)), (66699135/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1235237935/16777216)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1260158135/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1428291660395219/18014398509481984), (26342117608865/1125899906842624)), (239798049/18014398509481984), by norm_num⟩
  | 1 => ⟨((-984261961/4294967296), (-290445377/4294967296)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((88902593/268435456), (209873779/2147483648)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((-10706731/33554432), (-404408829/4294967296)), (237/4294967296), by norm_num⟩
  | 4 => ⟨((990285853/4294967296), (292222965/4294967296)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((-1144917705/8589934592), (-168926601/4294967296)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((1103079267/17179869184), (162753559/8589934592)), (49/4294967296), by norm_num⟩
  | 7 => ⟨((-455472737/17179869184), (-67202613/8589934592)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((41140173/4294967296), (388481069/137438953472)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((-845585025/274877906944), (-249523269/274877906944)), (155/274877906944), by norm_num⟩
  | 10 => ⟨((488811015/549755813888), (72121501/274877906944)), (181/1099511627776), by norm_num⟩
  | 11 => ⟨((-1027524039/4398046511104), (-303211563/4398046511104)), (3/68719476736), by norm_num⟩
  | 12 => ⟨((15468367/274877906944), (73032845/4398046511104)), (187/17592186044416), by norm_num⟩
  | 13 => ⟨((-880429905/70368744177664), (-64951407/17592186044416)), (21/8796093022208), by norm_num⟩
  | 14 => ⟨((1454154133/562949953421312), (107276407/140737488355328)), (35/70368744177664), by norm_num⟩
  | 15 => ⟨((-1120812277/2251799813685248), (-41342493/281474976710656)), (109/1125899906842624), by norm_num⟩
  | 16 => ⟨((404945519/4503599627370496), (477980697/18014398509481984)), (317/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (186889398567/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778124322619009/633825300114114700748351602688), (442042379733/633825300114114700748351602688)), (184487/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944508517950251/19807040628566084398385987584), (248595273751/19807040628566084398385987584)), (103777/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888747050222711/2475880078570760549798248448), (528130688707/2475880078570760549798248448)), (220533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770413571705059/154742504910672534362390528), (527979708905/154742504910672534362390528)), (55135/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387206292067417/2417851639229258349412352), (494820621893/9671406556917033397649408)), (51691/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314537936840941/151115727451828646838272), (108201939355/151115727451828646838272)), (180927/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886757564589365/75557863725914323419136), (703012213599/75557863725914323419136)), (294021/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296764065761931/4722366482869645213696), (526996462357/4722366482869645213696)), (13783/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405095680980205/147573952589676412928), (724193524085/590295810358705651712)), (18953/36893488147419103232), by norm_num⟩
  | 8 => ⟨((227768003627575/9223372036854775808), (452301231933/36893488147419103232)), (379091/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821161545153983/9223372036854775808), (1016799313381/9223372036854775808)), (53315/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796205999617537/576460752303423488), (507851199503/576460752303423488)), (426575/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193205822406555/144115188075855872), (887507161825/144115188075855872)), (93329/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489579360336917/36028797018963968), (1328799840969/36028797018963968)), (280049/18014398509481984), by norm_num⟩
  | 3 => ⟨((185836594966217/1125899906842624), (103543884169/562949953421312)), (700341/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222841066317007/4503599627370496), (12892761515/17592186044416)), (2737/8796093022208), by norm_num⟩
  | 1 => ⟨((1104250027578975/1125899906842624), (2459400688801/1125899906842624)), (2103691/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165751656170591/2251799813685248), (2427567439979/562949953421312)), (2107095/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165751656170591/2251799813685248), (2427567439979/562949953421312)), (8037929539207076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65092180907373/70368744177664), (18678421311337/2251799813685248)), (2035663/562949953421312), by norm_num⟩
  | 2 => ⟨((1926605959311341/2251799813685248), (34555659427203/2251799813685248)), (15199245/2251799813685248), by norm_num⟩
  | 3 => ⟨((1647844717947111/2251799813685248), (7391325260773/281474976710656)), (6618745/562949953421312), by norm_num⟩
  | 4 => ⟨((75270228560107/140737488355328), (86542373548993/2251799813685248)), (20069341/1125899906842624), by norm_num⟩
  | 5 => ⟨((640778935822323/2251799813685248), (185140840959743/4503599627370496)), (46019777/2251799813685248), by norm_num⟩
  | 6 => ⟨((1428291660395219/18014398509481984), (26342117608865/1125899906842624)), (239798049/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1260158135/16777216)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1283730621/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((621698456480661/18014398509481984), (-319537627708771/4503599627370496)), (194042933/9007199254740992), by norm_num⟩
  | 1 => ⟨((-436437885/4294967296), (224318277/1073741824)), (137/2147483648), by norm_num⟩
  | 2 => ⟨((80316545/536870912), (-1320982957/4294967296)), (405/4294967296), by norm_num⟩
  | 3 => ⟨((-315316221/2147483648), (1296517903/4294967296)), (399/4294967296), by norm_num⟩
  | 4 => ⟨((232107343/2147483648), (-954379463/4294967296)), (37/536870912), by norm_num⟩
  | 5 => ⟨((-273370363/4294967296), (1124044837/8589934592)), (351/8589934592), by norm_num⟩
  | 6 => ⟨((268307451/8589934592), (-137903393/2147483648)), (173/8589934592), by norm_num⟩
  | 7 => ⟨((-451437095/34359738368), (464055001/17179869184)), (293/34359738368), by norm_num⟩
  | 8 => ⟨((332307245/68719476736), (-1366381633/137438953472)), (217/68719476736), by norm_num⟩
  | 9 => ⟨((-217435201/137438953472), (111756315/34359738368)), (143/137438953472), by norm_num⟩
  | 10 => ⟨((512179745/1099511627776), (-32905965/34359738368)), (169/549755813888), by norm_num⟩
  | 11 => ⟨((-548393457/4398046511104), (4404073/17179869184)), (91/1099511627776), by norm_num⟩
  | 12 => ⟨((16819907/549755813888), (-553281033/8796093022208)), (45/2199023255552), by norm_num⟩
  | 13 => ⟨((-243816319/35184372088832), (1002524455/70368744177664)), (41/8796093022208), by norm_num⟩
  | 14 => ⟨((410229871/281474976710656), (-105424003/35184372088832)), (139/140737488355328), by norm_num⟩
  | 15 => ⟨((-644211639/2251799813685248), (1324435387/2251799813685248)), (439/2251799813685248), by norm_num⟩
  | 16 => ⟨((474210465/9007199254740992), (-974929795/9007199254740992)), (325/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-182053650029/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444512750353767/158456325028528675187087900672), (-861142809851/316912650057057350374175801344)), (184739/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888934485326757/39614081257132168796771975168), (-1937144956445/39614081257132168796771975168)), (103927/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944329626669503/1237940039285380274899124224), (-1028841713213/1237940039285380274899124224)), (110435/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770325677184297/154742504910672534362390528), (-64283873879/4835703278458516698824704)), (110449/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((6049776029329/37778931862957161709568), (-60246234971/302231454903657293676544)), (207123/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258079452151923/604462909807314587353088), (-1686258142267/604462909807314587353088)), (90631/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886639890940127/75557863725914323419136), (-2738976715011/75557863725914323419136)), (18413/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324168910263507/1180591620717411303424), (-2053189418633/4722366482869645213696)), (110503/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405065216241259/147573952589676412928), (-2821441420345/590295810358705651712)), (75991/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227748911695661/9223372036854775808), (-3524262541599/73786976294838206464)), (95019/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910494576376569/4611686018427387904), (-3961306854391/9223372036854775808)), (53469/1152921504606846976), by norm_num⟩
  | 6 => ⟨((49757465696885/36028797018963968), (-989237657951/288230376151711744)), (213981/576460752303423488), by norm_num⟩
  | 5 => ⟨((596526786183365/72057594037927936), (-1728718553945/72057594037927936)), (374701/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489349410767287/36028797018963968), (-5176381391819/36028797018963968)), (562523/36028797018963968), by norm_num⟩
  | 3 => ⟨((46450080646605/281474976710656), (-1613351433809/2251799813685248)), (703981/9007199254740992), by norm_num⟩
  | 2 => ⟨((277781566887327/562949953421312), (-12855734070679/4503599627370496)), (88153/281474976710656), by norm_num⟩
  | 1 => ⟨((1103798505244977/1125899906842624), (-19156381095295/2251799813685248)), (265239/281474976710656), by norm_num⟩
  | 0 => ⟨((2163865679239955/2251799813685248), (-37806713822925/2251799813685248)), (4268921/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163865679239955/2251799813685248), (-37806713822925/2251799813685248)), (16284641274459075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2078730667679497/2251799813685248), (-72660677906699/2251799813685248)), (4173891/1125899906842624), by norm_num⟩
  | 2 => ⟨((1916618692482335/2251799813685248), (-67076113329917/1125899906842624)), (15951105/2251799813685248), by norm_num⟩
  | 3 => ⟨((1623337194647203/2251799813685248), (-228367249781027/2251799813685248)), (29054149/2251799813685248), by norm_num⟩
  | 4 => ⟨((573557212114051/1125899906842624), (-329262884165641/2251799813685248)), (47783731/2251799813685248), by norm_num⟩
  | 5 => ⟨((1072437654577291/4503599627370496), (-670933892957765/4503599627370496)), (125316323/4503599627370496), by norm_num⟩
  | 6 => ⟨((621698456480661/18014398509481984), (-319537627708771/4503599627370496)), (194042933/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1283730621/16777216)), (1/8388608), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1306093717/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-524133535849233/9007199254740992), (-216541899088363/4503599627370496)), (249240581/9007199254740992), by norm_num⟩
  | 1 => ⟨((187178105/1073741824), (618650013/4294967296)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((-280367745/1073741824), (-926654905/4294967296)), (269/2147483648), by norm_num⟩
  | 3 => ⟨((1119875603/4294967296), (925336669/4294967296)), (539/4294967296), by norm_num⟩
  | 4 => ⟨((-13104873/67108864), (-693015231/4294967296)), (203/2147483648), by norm_num⟩
  | 5 => ⟨((1005022489/8589934592), (415217619/4294967296)), (489/8589934592), by norm_num⟩
  | 6 => ⟨((-1003592769/17179869184), (-829253881/17179869184)), (245/8589934592), by norm_num⟩
  | 7 => ⟨((429499321/17179869184), (354888945/17179869184)), (421/34359738368), by norm_num⟩
  | 8 => ⟨((-643332489/68719476736), (-531576133/68719476736)), (317/68719476736), by norm_num⟩
  | 9 => ⟨((53534775/17179869184), (707759901/274877906944)), (53/34359738368), by norm_num⟩
  | 10 => ⟨((-1026405461/1099511627776), (-848103671/1099511627776)), (255/549755813888), by norm_num⟩
  | 11 => ⟨((1118122169/4398046511104), (115485979/549755813888)), (279/2199023255552), by norm_num⟩
  | 12 => ⟨((-279132889/4398046511104), (-230643383/4398046511104)), (559/17592186044416), by norm_num⟩
  | 13 => ⟨((128647293/8796093022208), (850394863/70368744177664)), (517/70368744177664), by norm_num⟩
  | 14 => ⟨((-880897937/281474976710656), (-727872953/281474976710656)), (445/281474976710656), by norm_num⟩
  | 15 => ⟨((703715835/1125899906842624), (581469999/1125899906842624)), (357/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1054072119/9007199254740992), (-870964221/9007199254740992)), (537/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-3192738096335/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777976804472333/633825300114114700748351602688), (-3775264267431/633825300114114700748351602688)), (185143/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944425349241155/19807040628566084398385987584), (-4246207978043/39614081257132168796771975168)), (104167/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888569807485765/2475880078570760549798248448), (-1127601365883/618970019642690137449562112)), (221411/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770235756736183/154742504910672534362390528), (-4509066488625/154742504910672534362390528)), (221473/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548657859243183/9671406556917033397649408), (-2112913784081/4835703278458516698824704)), (103849/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258004745038861/604462909807314587353088), (-3696177302193/604462909807314587353088)), (90901/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943258774513319/37778931862957161709568), (-1500905787289/18889465931478580854784)), (295551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162072882575645/590295810358705651712), (-4500386461235/4722366482869645213696)), (221773/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405033057417315/147573952589676412928), (-3092122721567/295147905179352825856)), (152557/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821828496901187/73786976294838206464), (-1931157748441/18446744073709551616)), (381657/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910401629119939/4611686018427387904), (-4341205334085/4611686018427387904)), (214865/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796024790146405/576460752303423488), (-4336334612951/576460752303423488)), (430187/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18638813600633/2251799813685248), (-7577636839673/144115188075855872)), (11779/4503599627370496), by norm_num⟩
  | 4 => ⟨((744543747196403/18014398509481984), (-11344583761387/36028797018963968)), (283211/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486061834410563/9007199254740992), (-3535628247737/2251799813685248)), (354917/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221531230567745/4503599627370496), (-28170609408609/4503599627370496)), (178137/562949953421312), by norm_num⟩
  | 1 => ⟨((2206416362372315/2251799813685248), (-20985344875471/1125899906842624)), (2151255/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080557312535399/1125899906842624), (-41402690675631/1125899906842624)), (4357187/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080557312535399/1125899906842624), (-41402690675631/1125899906842624)), (16621349343306731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071036538493129/2251799813685248), (-158941234105449/2251799813685248)), (8683881/2251799813685248), by norm_num⟩
  | 2 => ⟨((473391329233701/562949953421312), (-73091111675433/562949953421312)), (17199453/2251799813685248), by norm_num⟩
  | 3 => ⟨((777181128298209/1125899906842624), (-491705499587199/2251799813685248)), (33392665/2251799813685248), by norm_num⟩
  | 4 => ⟨((965568836622671/2251799813685248), (-339412262703943/1125899906842624)), (30341799/1125899906842624), by norm_num⟩
  | 5 => ⟨((418794280997773/4503599627370496), (-1164316300739595/4503599627370496)), (88629289/2251799813685248), by norm_num⟩
  | 6 => ⟨((-524133535849233/9007199254740992), (-216541899088363/4503599627370496)), (249240581/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1306093717/16777216)), (1/8388608), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1327365487/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-546234475610675/9007199254740992), (44474538419093/1125899906842624)), (475693251/18014398509481984), by norm_num⟩
  | 1 => ⟨((792991217/4294967296), (-516524239/4294967296)), (347/4294967296), by norm_num⟩
  | 2 => ⟨((-1207139777/4294967296), (393142409/2147483648)), (265/2147483648), by norm_num⟩
  | 3 => ⟨((153131839/536870912), (-199488481/1073741824)), (135/1073741824), by norm_num⟩
  | 4 => ⟨((-58276665/268435456), (607347157/4294967296)), (413/4294967296), by norm_num⟩
  | 5 => ⟨((1135517531/8589934592), (-739632819/8589934592)), (505/8589934592), by norm_num⟩
  | 6 => ⟨((-576184767/8589934592), (750609571/17179869184)), (257/8589934592), by norm_num⟩
  | 7 => ⟨((501202129/17179869184), (-652927909/34359738368)), (449/34359738368), by norm_num⟩
  | 8 => ⟨((-190740141/17179869184), (496963417/68719476736)), (343/68719476736), by norm_num⟩
  | 9 => ⟨((1032378025/274877906944), (-672451677/274877906944)), (233/137438953472), by norm_num⟩
  | 10 => ⟨((-1257239225/1099511627776), (102364711/137438953472)), (285/549755813888), by norm_num⟩
  | 11 => ⟨((695944187/2199023255552), (-453311505/2199023255552)), (317/2199023255552), by norm_num⟩
  | 12 => ⟨((-176568141/2199023255552), (57504877/1099511627776)), (323/8796093022208), by norm_num⟩
  | 13 => ⟨((661619283/35184372088832), (-430953571/35184372088832)), (19/2199023255552), by norm_num⟩
  | 14 => ⟨((-575518501/140737488355328), (374870805/140737488355328)), (531/281474976710656), by norm_num⟩
  | 15 => ⟨((934495461/1125899906842624), (-152173677/281474976710656)), (433/1125899906842624), by norm_num⟩
  | 16 => ⟨((-177818275/1125899906842624), (231648087/2251799813685248)), (331/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (1670117901243/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777911267070353/633825300114114700748351602688), (246837431717/39614081257132168796771975168)), (92589/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944388473310189/19807040628566084398385987584), (4442048026027/39614081257132168796771975168)), (26047/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472122853467081/618970019642690137449562112), (4718410186451/2475880078570760549798248448)), (221457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770157326888301/154742504910672534362390528), (2358493237771/77371252455336267181195264)), (110761/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774292146407865/4835703278458516698824704), (4420662545173/9671406556917033397649408)), (103873/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257940336025791/604462909807314587353088), (3866567920199/604462909807314587353088)), (181847/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471603203129969/18889465931478580854784), (6280339228725/75557863725914323419136)), (18477/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296504445465971/4722366482869645213696), (4707775981301/4722366482869645213696)), (110919/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620024032091925/590295810358705651712), (808645797073/73786976294838206464)), (76303/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821693097677243/73786976294838206464), (8080422842419/73786976294838206464)), (381793/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820650725397633/9223372036854775808), (567636419175/576460752303423488)), (214949/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795948393751195/576460752303423488), (4535912216605/576460752303423488)), (430377/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192750085605627/144115188075855872), (1981551068019/36028797018963968)), (188559/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488885938093219/36028797018963968), (2966512391913/9007199254740992)), (566755/36028797018963968), by norm_num⟩
  | 3 => ⟨((742904441486541/4503599627370496), (7395962034649/4503599627370496)), (355167/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221022338489401/4503599627370496), (14731090369847/2251799813685248)), (1426347/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205645652277089/2251799813685248), (1371561385369/70368744177664)), (538441/562949953421312), by norm_num⟩
  | 0 => ⟨((1079772159904541/1125899906842624), (86571869954151/2251799813685248)), (2182375/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079772159904541/1125899906842624), (86571869954151/2251799813685248)), (8325099949363326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2067740192647133/2251799813685248), (83025049064539/1125899906842624)), (8707467/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886480691304249/2251799813685248), (304954694291921/2251799813685248)), (17275653/2251799813685248), by norm_num⟩
  | 3 => ⟨((192391215908143/281474976710656), (127740294454237/562949953421312)), (33625083/2251799813685248), by norm_num⟩
  | 4 => ⟨((936068552499589/2251799813685248), (349247536782327/1125899906842624)), (15306529/562949953421312), by norm_num⟩
  | 5 => ⟨((172452704198893/2251799813685248), (1161451863466851/4503599627370496)), (44443553/1125899906842624), by norm_num⟩
  | 6 => ⟨((-546234475610675/9007199254740992), (44474538419093/1125899906842624)), (475693251/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1327365487/16777216)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile036Terms2
