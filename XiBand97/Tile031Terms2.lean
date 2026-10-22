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
namespace Reinmann.XiBand97.Tile031Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63483/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63483/2560))
  have he : value ((69/80), (63483/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1153513881/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1542598253436695/18014398509481984), (290542225403185/9007199254740992)), (281209267/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1019714003/4294967296), (-384118127/4294967296)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((353405943/1073741824), (532500793/4294967296)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((-81654111/268435456), (-492135231/4294967296)), (245/4294967296), by norm_num⟩
  | 4 => ⟨((905573069/4294967296), (85280537/1073741824)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((-1004312671/8589934592), (-47289571/1073741824)), (193/8589934592), by norm_num⟩
  | 6 => ⟨((928181995/17179869184), (174819375/8589934592)), (45/4294967296), by norm_num⟩
  | 7 => ⟨((-367638133/17179869184), (-553945403/68719476736)), (287/68719476736), by norm_num⟩
  | 8 => ⟨((1019309341/137438953472), (191982847/68719476736)), (201/137438953472), by norm_num⟩
  | 9 => ⟨((-1256055815/549755813888), (-473146201/549755813888)), (125/274877906944), by norm_num⟩
  | 10 => ⟨((1393010475/2199023255552), (65591991/274877906944)), (279/2199023255552), by norm_num⟩
  | 11 => ⟨((-175556597/1099511627776), (-529046151/8796093022208)), (71/2199023255552), by norm_num⟩
  | 12 => ⟨((162248747/4398046511104), (3819863/274877906944)), (33/4398046511104), by norm_num⟩
  | 13 => ⟨((-1107320729/140737488355328), (-13034965/4398046511104)), (227/140737488355328), by norm_num⟩
  | 14 => ⟨((219296069/140737488355328), (330428315/562949953421312)), (181/562949953421312), by norm_num⟩
  | 15 => ⟨((-1297104657/4503599627370496), (-488608971/4503599627370496)), (135/2251799813685248), by norm_num⟩
  | 16 => ⟨((224771109/4503599627370496), (338677931/18014398509481984)), (189/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (234635045833/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778280772442101/633825300114114700748351602688), (555066451267/633825300114114700748351602688)), (184509/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889193001380049/39614081257132168796771975168), (624320390921/39614081257132168796771975168)), (207581/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888933962541699/2475880078570760549798248448), (663178673083/2475880078570760549798248448)), (110281/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770600426674665/154742504910672534362390528), (662996794527/154742504910672534362390528)), (55143/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549000283894309/9671406556917033397649408), (38835394937/604462909807314587353088)), (51699/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629152456326687/302231454903657293676544), (67937804015/75557863725914323419136)), (180957/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235875793011193/9444732965739290427392), (882829562863/75557863725914323419136)), (36759/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648475275305873/2361183241434822606848), (661805686429/4722366482869645213696)), (110285/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620638978563451/590295810358705651712), (909468843319/590295810358705651712)), (151655/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822464104475747/73786976294838206464), (35502051237/2305843009213693952)), (379177/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821521296434373/9223372036854775808), (1277015415449/9223372036854775808)), (426629/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398192833492747/288230376151711744), (637846857127/576460752303423488)), (426697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193519772324949/144115188075855872), (557373459963/72057594037927936)), (186719/72057594037927936), by norm_num⟩
  | 4 => ⟨((745024675426821/18014398509481984), (208644349771/4503599627370496)), (280155/18014398509481984), by norm_num⟩
  | 3 => ⟨((185909827039463/1125899906842624), (2081264014225/9007199254740992)), (700659/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224007899063703/4503599627370496), (1036757658039/1125899906842624)), (701069/2251799813685248), by norm_num⟩
  | 1 => ⟨((552559538240843/562949953421312), (6181945770135/2251799813685248)), (1052637/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084589771938323/1125899906842624), (1526293461973/281474976710656)), (4218919/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084589771938323/1125899906842624), (1526293461973/281474976710656)), (16093898781783293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044762232500949/1125899906842624), (23524681265489/2251799813685248)), (4087001/1125899906842624), by norm_num⟩
  | 2 => ⟨((969348841020695/1125899906842624), (43658762858821/2251799813685248)), (15340679/2251799813685248), by norm_num⟩
  | 3 => ⟨((1668284450485967/2251799813685248), (75176436058647/2251799813685248)), (27010123/2251799813685248), by norm_num⟩
  | 4 => ⟨((308366833312011/562949953421312), (55695749931847/1125899906842624)), (20912647/1125899906842624), by norm_num⟩
  | 5 => ⟨((83768192157727/281474976710656), (244067479619351/4503599627370496)), (99918505/4503599627370496), by norm_num⟩
  | 6 => ⟨((1542598253436695/18014398509481984), (290542225403185/9007199254740992)), (281209267/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1153513881/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1178736281/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((324431406125101/9007199254740992), (-1423528906683853/18014398509481984)), (431420567/18014398509481984), by norm_num⟩
  | 1 => ⟨((-438300795/4294967296), (961580537/4294967296)), (293/4294967296), by norm_num⟩
  | 2 => ⟨((620899831/4294967296), (-340545351/1073741824)), (209/2147483648), by norm_num⟩
  | 3 => ⟨((-293190281/2147483648), (1286450177/4294967296)), (397/4294967296), by norm_num⟩
  | 4 => ⟨((103833827/1073741824), (-113899619/536870912)), (283/4294967296), by norm_num⟩
  | 5 => ⟨((-470693415/8589934592), (1032646145/8589934592)), (323/8589934592), by norm_num⟩
  | 6 => ⟨((444524955/17179869184), (-975235613/17179869184)), (307/17179869184), by norm_num⟩
  | 7 => ⟨((-44979787/4294967296), (789443015/34359738368)), (125/17179869184), by norm_num⟩
  | 8 => ⟨((509749331/137438953472), (-559165121/68719476736)), (89/34359738368), by norm_num⟩
  | 9 => ⟨((-641879381/549755813888), (1408208073/549755813888)), (451/549755813888), by norm_num⟩
  | 10 => ⟨((181858123/549755813888), (-797950781/1099511627776)), (129/549755813888), by norm_num⟩
  | 11 => ⟨((-374722081/4398046511104), (822096291/4398046511104)), (67/1099511627776), by norm_num⟩
  | 12 => ⟨((22118075/1099511627776), (-388195697/8796093022208)), (127/8796093022208), by norm_num⟩
  | 13 => ⟨((-617011449/140737488355328), (1353650743/140737488355328)), (445/140737488355328), by norm_num⟩
  | 14 => ⟨((249732153/281474976710656), (-273941525/140737488355328)), (181/281474976710656), by norm_num⟩
  | 15 => ⟨((-188678525/1125899906842624), (827877103/2251799813685248)), (275/2251799813685248), by norm_num⟩
  | 16 => ⟨((534566515/18014398509481984), (-293194057/4503599627370496)), (49/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-744520020645/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778198714020457/633825300114114700748351602688), (-440282059391/158456325028528675187087900672)), (184747/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889100621787983/39614081257132168796771975168), (-990424337591/19807040628566084398385987584)), (207863/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944417861565717/1237940039285380274899124224), (-1052063571721/1237940039285380274899124224)), (13805/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885251045263549/77371252455336267181195264), (-131471077589/9671406556917033397649408)), (220909/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548907991060477/9671406556917033397649408), (-492859902535/2417851639229258349412352)), (207133/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112026913631/302231454903657293676544), (-26943489837/9444732965739290427392)), (181273/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117929672271177/4722366482869645213696), (-2800949132209/75557863725914323419136)), (294625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648425845935107/2361183241434822606848), (-2099685283537/4722366482869645213696)), (55255/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810251387651701/295147905179352825856), (-2885400068077/590295810358705651712)), (303985/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911146721176333/36893488147419103232), (-901062747621/18446744073709551616)), (380105/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910664370797949/4611686018427387904), (-2025674435333/4611686018427387904)), (427789/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398144520216643/288230376151711744), (-1011765285603/288230376151711744)), (214001/576460752303423488), by norm_num⟩
  | 5 => ⟨((596674946301913/72057594037927936), (-1768180245299/72057594037927936)), (374743/144115188075855872), by norm_num⟩
  | 4 => ⟨((372448242621641/9007199254740992), (-5294918914431/36028797018963968)), (562595/36028797018963968), by norm_num⟩
  | 3 => ⟨((371738855582233/2251799813685248), (-6601842352043/9007199254740992)), (88011/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111676703364479/2251799813685248), (-6576696594635/2251799813685248)), (705357/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104618166051771/1125899906842624), (-9802402862753/1125899906842624)), (2122441/2251799813685248), by norm_num⟩
  | 0 => ⟨((541774159536885/562949953421312), (-9677783851429/562949953421312)), (2135245/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541774159536885/562949953421312), (-9677783851429/562949953421312)), (8145313267234420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2084914146689863/2251799813685248), (-37254986383229/1125899906842624)), (8366535/2251799813685248), by norm_num⟩
  | 2 => ⟨((1927931264867171/2251799813685248), (-137975760852407/2251799813685248)), (8023315/1125899906842624), by norm_num⟩
  | 3 => ⟨((410547335180037/562949953421312), (-236262372458277/2251799813685248)), (29443867/2251799813685248), by norm_num⟩
  | 4 => ⟨((586412234800995/1125899906842624), (-344602168724105/2251799813685248)), (49124157/2251799813685248), by norm_num⟩
  | 5 => ⟨((1116232956562009/4503599627370496), (-717928571272253/4503599627370496)), (132413735/4503599627370496), by norm_num⟩
  | 6 => ⟨((324431406125101/9007199254740992), (-1423528906683853/18014398509481984)), (431420567/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1178736281/16777216)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1202516593/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-622390231200809/9007199254740992), (-817422106728439/18014398509481984)), (542334415/18014398509481984), by norm_num⟩
  | 1 => ⟨((857801031/4294967296), (563300555/4294967296)), (47/536870912), by norm_num⟩
  | 2 => ⟨((-1239681937/4294967296), (-101759251/536870912)), (273/2147483648), by norm_num⟩
  | 3 => ⟨((1194380553/4294967296), (784325507/4294967296)), (529/4294967296), by norm_num⟩
  | 4 => ⟨((-863050955/4294967296), (-283374037/2147483648)), (3/33554432), by norm_num⟩
  | 5 => ⟨((997815243/8589934592), (655245051/8589934592)), (223/4294967296), by norm_num⟩
  | 6 => ⟨((-961352333/17179869184), (-631300597/17179869184)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((793904467/34359738368), (32583811/2147483648)), (359/34359738368), by norm_num⟩
  | 8 => ⟨((-1147339525/137438953472), (-753434617/137438953472)), (521/137438953472), by norm_num⟩
  | 9 => ⟨((736941725/274877906944), (241967349/137438953472)), (337/274877906944), by norm_num⟩
  | 10 => ⟨((-213003555/274877906944), (-279750237/549755813888)), (49/137438953472), by norm_num⟩
  | 11 => ⟨((895504669/4398046511104), (588059771/4398046511104)), (207/2199023255552), by norm_num⟩
  | 12 => ⟨((-215695117/4398046511104), (-566570451/17592186044416)), (401/17592186044416), by norm_num⟩
  | 13 => ⟨((383654815/35184372088832), (251938343/35184372088832)), (359/70368744177664), by norm_num⟩
  | 14 => ⟨((-79207503/35184372088832), (-208055849/140737488355328)), (595/562949953421312), by norm_num⟩
  | 15 => ⟨((488403477/1125899906842624), (641449333/2251799813685248)), (461/2251799813685248), by norm_num⟩
  | 16 => ⟨((-44114613/562949953421312), (-463506759/9007199254740992)), (335/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-3335384003579/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889058043576817/316912650057057350374175801344), (-986132101105/158456325028528675187087900672)), (185177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472251829108379/9903520314283042199192993792), (-2218308949529/19807040628566084398385987584)), (104187/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888736119340887/2475880078570760549798248448), (-4712706014711/2475880078570760549798248448)), (221455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770401962077705/154742504910672534362390528), (-4711355738747/154742504910672534362390528)), (13845/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548813563628821/9671406556917033397649408), (-4415461694253/9671406556917033397649408)), (207745/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258140873308913/604462909807314587353088), (-3862095073225/604462909807314587353088)), (90923/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886738545580267/75557863725914323419136), (-6273216767533/75557863725914323419136)), (295629/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296748622736947/4722366482869645213696), (-73477526069/73786976294838206464)), (221835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620359576732577/590295810358705651712), (-3231101835021/295147905179352825856)), (38151/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455528057452349/18446744073709551616), (-4036014726023/36893488147419103232)), (381787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455280459591041/2305843009213693952), (-4536582811683/4611686018427387904)), (107473/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398091846774583/288230376151711744), (-9063338062785/1152921504606846976)), (215185/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193161282687451/144115188075855872), (-7919374187331/144115188075855872)), (377111/144115188075855872), by norm_num⟩
  | 4 => ⟨((744750789267837/18014398509481984), (-11856991517995/36028797018963968)), (283371/18014398509481984), by norm_num⟩
  | 3 => ⟨((743288205930795/4503599627370496), (-461958441571/281474976710656)), (710313/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111275665477467/2251799813685248), (-14724921878875/2251799813685248)), (178287/562949953421312), by norm_num⟩
  | 1 => ⟨((1103961988467995/1125899906842624), (-21943382020067/1125899906842624)), (538413/562949953421312), by norm_num⟩
  | 0 => ⟨((2164040311202511/2251799813685248), (-86625960514209/2251799813685248)), (4364379/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164040311202511/2251799813685248), (-86625960514209/2251799813685248)), (16648784646041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038184296636591/1125899906842624), (-83249882787133/1125899906842624)), (8724365/2251799813685248), by norm_num⟩
  | 2 => ⟨((1902293595177337/2251799813685248), (-153528249680403/1125899906842624)), (17379523/2251799813685248), by norm_num⟩
  | 3 => ⟨((97822783996865/140737488355328), (-518795328556041/2251799813685248)), (8525947/562949953421312), by norm_num⟩
  | 4 => ⟨((968377137014427/2251799813685248), (-721200924600683/2251799813685248)), (3945229/140737488355328), by norm_num⟩
  | 5 => ⟨((185462092726575/2251799813685248), (-620298911415211/2251799813685248)), (94726325/2251799813685248), by norm_num⟩
  | 6 => ⟨((-622390231200809/9007199254740992), (-817422106728439/18014398509481984)), (542334415/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1202516593/16777216)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-612505419/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-128814980194377/2251799813685248), (978880255853535/18014398509481984)), (521060399/18014398509481984), by norm_num⟩
  | 1 => ⟨((45214635/268435456), (-171795677/1073741824)), (367/4294967296), by norm_num⟩
  | 2 => ⟨((-532526935/2147483648), (15807559/67108864)), (543/4294967296), by norm_num⟩
  | 3 => ⟨((522664355/2147483648), (-124118381/536870912)), (535/4294967296), by norm_num⟩
  | 4 => ⟨((-384738325/2147483648), (365458999/2147483648)), (395/4294967296), by norm_num⟩
  | 5 => ⟨((906270817/8589934592), (-430428689/4294967296)), (117/2147483648), by norm_num⟩
  | 6 => ⟨((-889486373/17179869184), (422457003/8589934592)), (461/17179869184), by norm_num⟩
  | 7 => ⟨((748296671/34359738368), (-88849919/4294967296)), (195/17179869184), by norm_num⟩
  | 8 => ⟨((-550828471/68719476736), (261613165/34359738368)), (289/68719476736), by norm_num⟩
  | 9 => ⟨((45052245/17179869184), (-684714667/274877906944)), (95/68719476736), by norm_num⟩
  | 10 => ⟨((-106122869/137438953472), (403220111/549755813888)), (449/1099511627776), by norm_num⟩
  | 11 => ⟨((454505181/2199023255552), (-863459645/4398046511104)), (483/4398046511104), by norm_num⟩
  | 12 => ⟨((-892175181/17592186044416), (847468079/17592186044416)), (119/4398046511104), by norm_num⟩
  | 13 => ⟨((808293963/70368744177664), (-95973771/8796093022208)), (433/70368744177664), by norm_num⟩
  | 14 => ⟨((-84999009/35184372088832), (322958757/140737488355328)), (183/140737488355328), by norm_num⟩
  | 15 => ⟨((266959355/562949953421312), (-1014327843/2251799813685248)), (577/2251799813685248), by norm_num⟩
  | 16 => ⟨((-786045531/9007199254740992), (373328305/4503599627370496)), (427/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (193917178267/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222255671830525/79228162514264337593543950336), (1834518382297/316912650057057350374175801344)), (185123/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472231961350123/9903520314283042199192993792), (4126744972253/39614081257132168796771975168)), (104155/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((29510184154187/38685626227668133590597632), (136985292801/77371252455336267181195264)), (221383/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770317746082509/154742504910672534362390528), (547781299743/19342813113834066795298816)), (221443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548734735876695/9671406556917033397649408), (1026750303951/2417851639229258349412352)), (51917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258072023682941/604462909807314587353088), (1796133976613/302231454903657293676544)), (90887/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886626898487025/75557863725914323419136), (5834889862571/75557863725914323419136)), (295503/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324166272897317/1180591620717411303424), (546742615819/590295810358705651712)), (221733/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810122526420655/295147905179352825856), (3005276219597/295147905179352825856)), (152527/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821969571500387/73786976294838206464), (3753884492789/36893488147419103232)), (381575/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820962029555227/9223372036854775808), (2109697558471/2305843009213693952)), (429627/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592208429064615/1152921504606846976), (8429485051145/1152921504606846976)), (430071/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193023149523531/144115188075855872), (7365340933201/144115188075855872)), (94203/36028797018963968), by norm_num⟩
  | 4 => ⟨((372324071002545/9007199254740992), (11027119030219/36028797018963968)), (141555/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486323116581479/9007199254740992), (1718424060097/1125899906842624)), (709529/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222054664066071/4503599627370496), (13692743654079/2251799813685248)), (1424331/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207203628770681/2251799813685248), (10201440212425/562949953421312)), (268715/281474976710656), by norm_num⟩
  | 0 => ⟨((2162697284251383/2251799813685248), (40263141005059/1125899906842624)), (2176277/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162697284251383/2251799813685248), (40263141005059/1125899906842624)), (8301837925437545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037120403160937/1125899906842624), (77339899557557/1125899906842624)), (8671955/2251799813685248), by norm_num⟩
  | 2 => ⟨((475014370322105/562949953421312), (71241490759597/562949953421312)), (8583845/1125899906842624), by norm_num⟩
  | 3 => ⟨((195899565020291/281474976710656), (480905724117207/2251799813685248)), (33317177/2251799813685248), by norm_num⟩
  | 4 => ⟨((988025047252801/2251799813685248), (334698392273683/1125899906842624)), (60606619/2251799813685248), by norm_num⟩
  | 5 => ⟨((469048301387207/4503599627370496), (1174848289201841/4503599627370496)), (697017/17592186044416), by norm_num⟩
  | 6 => ⟨((-128814980194377/2251799813685248), (978880255853535/18014398509481984)), (521060399/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-612505419/8388608)), (1/8388608), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-311587753/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((604763896913367/18014398509481984), (1217937103289877/18014398509481984)), (92536869/4503599627370496), by norm_num⟩
  | 1 => ⟨((-431945497/4294967296), (-869897243/4294967296)), (267/4294967296), by norm_num⟩
  | 2 => ⟨((646996533/4294967296), (1302989623/4294967296)), (201/2147483648), by norm_num⟩
  | 3 => ⟨((-161519033/1073741824), (-650568011/2147483648)), (101/1073741824), by norm_num⟩
  | 4 => ⟨((120966945/1073741824), (974463793/4294967296)), (19/268435456), by norm_num⟩
  | 5 => ⟨((-289907665/4294967296), (-583846527/4294967296)), (183/4294967296), by norm_num⟩
  | 6 => ⟨((578990499/17179869184), (1166031923/17179869184)), (367/17179869184), by norm_num⟩
  | 7 => ⟨((-247785789/17179869184), (-998034133/34359738368)), (79/8589934592), by norm_num⟩
  | 8 => ⟨((371149943/68719476736), (373730383/34359738368)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((-247081303/137438953472), (-248799149/68719476736)), (5/4294967296), by norm_num⟩
  | 10 => ⟨((592151547/1099511627776), (1192537025/1099511627776)), (193/549755813888), by norm_num⟩
  | 11 => ⟨((-322532273/2199023255552), (-1299098783/4398046511104)), (423/4398046511104), by norm_num⟩
  | 12 => ⟨((644146893/17592186044416), (1297250717/17592186044416)), (53/2199023255552), by norm_num⟩
  | 13 => ⟨((-593751273/70368744177664), (-9341865/549755813888)), (393/70368744177664), by norm_num⟩
  | 14 => ⟨((63525709/35184372088832), (1023477997/281474976710656)), (169/140737488355328), by norm_num⟩
  | 15 => ⟨((-405986169/1125899906842624), (-408808809/562949953421312)), (271/1125899906842624), by norm_num⟩
  | 16 => ⟨((608112935/9007199254740992), (1224681743/9007199254740992)), (51/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (722893682019/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777982879464007/633825300114114700748351602688), (854788148771/316912650057057350374175801344)), (184737/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857866548557/39614081257132168796771975168), (961421619575/19807040628566084398385987584)), (207851/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944288934438137/1237940039285380274899124224), (1021241295393/1237940039285380274899124224)), (110433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442561079643467/38685626227668133590597632), (1020938609907/77371252455336267181195264)), (220895/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387166604317331/2417851639229258349412352), (478404231357/2417851639229258349412352)), (207119/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258012764140357/604462909807314587353088), (418443027499/151115727451828646838272)), (45315/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886531574362177/75557863725914323419136), (2718675186781/75557863725914323419136)), (147301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648297224304075/2361183241434822606848), (2037953029399/4722366482869645213696)), (221001/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810074649206691/295147905179352825856), (2800474772021/590295810358705651712)), (303957/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227731493111495/9223372036854775808), (437253670897/9223372036854775808)), (190033/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820832535957201/9223372036854775808), (3931760435475/9223372036854775808)), (106935/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592082473396555/1152921504606846976), (981840431515/288230376151711744)), (106987/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192916908200771/144115188075855872), (3431499203341/144115188075855872)), (374689/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489144836134005/36028797018963968), (5137379774019/36028797018963968)), (562501/36028797018963968), by norm_num⟩
  | 3 => ⟨((743073799401179/4503599627370496), (3202244460115/4503599627370496)), (703947/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221744774837867/4503599627370496), (3189352550879/1125899906842624)), (1410363/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206840859013951/2251799813685248), (19007684129549/2251799813685248)), (1060871/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081187606495675/1125899906842624), (9376140318107/562949953421312)), (4268423/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081187606495675/1125899906842624), (9376140318107/562949953421312)), (16282741555220793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037938617197287/1125899906842624), (72030322746043/2251799813685248)), (2085003/562949953421312), by norm_num⟩
  | 2 => ⟨((1911394564794285/2251799813685248), (33201465393563/562949953421312)), (3977613/562949953421312), by norm_num⟩
  | 3 => ⟨((807307950591397/1125899906842624), (225459119805513/2251799813685248)), (7221813/562949953421312), by norm_num⟩
  | 4 => ⟨((1135159829978627/2251799813685248), (323323483457345/2251799813685248)), (47210869/2251799813685248), by norm_num⟩
  | 5 => ⟨((1051647448806137/4503599627370496), (651965291548495/4503599627370496)), (30578325/1125899906842624), by norm_num⟩
  | 6 => ⟨((604763896913367/18014398509481984), (1217937103289877/18014398509481984)), (92536869/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-311587753/4194304)), (1/8388608), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1266649779/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((648636087756387/9007199254740992), (-16267952259795/2251799813685248)), (89215989/9007199254740992), by norm_num⟩
  | 1 => ⟨((-117706485/536870912), (94467441/4294967296)), (261/8589934592), by norm_num⟩
  | 2 => ⟨((1433440139/4294967296), (-71902061/2147483648)), (25/536870912), by norm_num⟩
  | 3 => ⟨((-363678389/1073741824), (36484573/1073741824)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((138403377/536870912), (-111078101/4294967296)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((-674195499/4294967296), (33817977/2147483648)), (97/4294967296), by norm_num⟩
  | 6 => ⟨((171050277/2147483648), (-137279453/17179869184)), (199/17179869184), by norm_num⟩
  | 7 => ⟨((-1190323215/34359738368), (119414393/34359738368)), (175/34359738368), by norm_num⟩
  | 8 => ⟨((452995717/34359738368), (-181779899/137438953472)), (269/137438953472), by norm_num⟩
  | 9 => ⟨((-1225916111/274877906944), (122985107/274877906944)), (183/274877906944), by norm_num⟩
  | 10 => ⟨((1492931643/1099511627776), (-149772367/1099511627776)), (225/1099511627776), by norm_num⟩
  | 11 => ⟨((-1652823231/4398046511104), (10363303/274877906944)), (251/4398046511104), by norm_num⟩
  | 12 => ⟨((1677352471/17592186044416), (-168273645/17592186044416)), (257/17592186044416), by norm_num⟩
  | 13 => ⟨((-1571303765/70368744177664), (157634735/70368744177664)), (243/70368744177664), by norm_num⟩
  | 14 => ⟨((1366819877/281474976710656), (-137120711/281474976710656)), (213/281474976710656), by norm_num⟩
  | 15 => ⟨((-277420919/281474976710656), (111324555/1125899906842624)), (87/562949953421312), by norm_num⟩
  | 16 => ⟨((1689228425/9007199254740992), (-169465053/9007199254740992)), (267/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-130243509417/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777919618840525/633825300114114700748351602688), (-76998092981/316912650057057350374175801344)), (92215/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888786800096719/39614081257132168796771975168), (-173206528537/39614081257132168796771975168)), (207487/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118031405955663/154742504910672534362390528), (-91991336035/1237940039285380274899124224)), (220457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770169096164767/154742504910672534362390528), (-91963638911/77371252455336267181195264)), (55115/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548596056768501/9671406556917033397649408), (-21546623771/1208925819614629174706176)), (51671/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157243919884705/75557863725914323419136), (-18845945021/75557863725914323419136)), (180851/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117902005722413/4722366482869645213696), (-122443540003/37778931862957161709568)), (293889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324130024773853/1180591620717411303424), (-91784468387/2361183241434822606848)), (110211/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620047494016601/590295810358705651712), (-126125393601/295147905179352825856)), (303087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821725327752357/73786976294838206464), (-157539458715/36893488147419103232)), (189435/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820690967924515/9223372036854775808), (-354141552975/9223372036854775808)), (426245/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795970999221441/576460752303423488), (-88434803985/288230376151711744)), (426265/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192795219265561/144115188075855872), (-309069801917/144115188075855872)), (186503/72057594037927936), by norm_num⟩
  | 4 => ⟨((186120593548005/4503599627370496), (-462702219353/36028797018963968)), (559555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485926751848385/9007199254740992), (-72100235993/1125899906842624)), (87441/1125899906842624), by norm_num⟩
  | 2 => ⟨((2221315800712507/4503599627370496), (-574444962679/2251799813685248)), (1399313/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206228958798837/2251799813685248), (-855799224645/1125899906842624)), (131227/140737488355328), by norm_num⟩
  | 0 => ⟨((540319058339055/562949953421312), (-3376539142813/2251799813685248)), (4202039/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540319058339055/562949953421312), (-3376539142813/2251799813685248)), (16029506691939543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037193343623481/1125899906842624), (-6481600856353/2251799813685248)), (504927/140737488355328), by norm_num⟩
  | 2 => ⟨((955466398683883/1125899906842624), (-11941866631975/2251799813685248)), (3732789/562949953421312), by norm_num⟩
  | 3 => ⟨((405400329736809/562949953421312), (-20268324448865/2251799813685248)), (25500263/2251799813685248), by norm_num⟩
  | 4 => ⟨((1167590483246639/2251799813685248), (-14595942969433/1125899906842624)), (37186351/2251799813685248), by norm_num⟩
  | 5 => ⟨((302516982656143/1125899906842624), (-60545645315531/4503599627370496)), (19763733/1125899906842624), by norm_num⟩
  | 6 => ⟨((648636087756387/9007199254740992), (-16267952259795/2251799813685248)), (89215989/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1266649779/16777216)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile031Terms2
