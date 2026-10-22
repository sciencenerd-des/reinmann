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
namespace Reinmann.XiBand97.Tile017Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53817/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53817/2560))
  have he : value ((69/80), (53817/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1955756865/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-273409975136955/18014398509481984), (-1625581586992967/18014398509481984)), (139311927/9007199254740992), by norm_num⟩
  | 1 => ⟨((90367009/2147483648), (1074569029/4294967296)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((-125275275/2147483648), (-744834493/2147483648)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((57889469/1073741824), (1376746477/4294967296)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-160503689/4294967296), (-954287939/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((178004287/8589934592), (1058339191/8589934592)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((-164510893/17179869184), (-489056551/8589934592)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((130320299/34359738368), (1549660203/68719476736)), (281/68719476736), by norm_num⟩
  | 8 => ⟨((-22582787/17179869184), (-1074142601/137438953472)), (197/137438953472), by norm_num⟩
  | 9 => ⟨((55655805/137438953472), (1323624739/549755813888)), (245/549755813888), by norm_num⟩
  | 10 => ⟨((-61724263/549755813888), (-733973405/1099511627776)), (137/1099511627776), by norm_num⟩
  | 11 => ⟨((62231271/2199023255552), (370001161/2199023255552)), (139/4398046511104), by norm_num⟩
  | 12 => ⟨((-230055627/35184372088832), (-170976841/4398046511104)), (259/35184372088832), by norm_num⟩
  | 13 => ⟨((196261427/140737488355328), (145861065/17592186044416)), (223/140737488355328), by norm_num⟩
  | 14 => ⟨((-155472063/562949953421312), (-462185993/281474976710656)), (89/281474976710656), by norm_num⟩
  | 15 => ⟨((114949357/2251799813685248), (1366881783/4503599627370496)), (265/4503599627370496), by norm_num⟩
  | 16 => ⟨((-159353645/18014398509481984), (-473725127/9007199254740992)), (185/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-2263195046513/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222284637194391/79228162514264337593543950336), (-1338486796093/316912650057057350374175801344)), (5779/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889188663197773/39614081257132168796771975168), (-3010965146223/39614081257132168796771975168)), (104039/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472232270896637/618970019642690137449562112), (-3198369696341/2475880078570760549798248448)), (110561/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442648811170585/38685626227668133590597632), (-3197491617795/154742504910672534362390528)), (110583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548995104035527/9671406556917033397649408), (-2996715715031/9671406556917033397649408)), (103695/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258300058801649/604462909807314587353088), (-2621193890947/604462909807314587353088)), (90757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471749463594633/18889465931478580854784), (-4257692571669/75557863725914323419136)), (147523/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162117957120695/590295810358705651712), (-3191741038383/4722366482869645213696)), (110681/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202578580689549/73786976294838206464), (-4386161555061/590295810358705651712)), (152249/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822449908588155/73786976294838206464), (-5478980591705/73786976294838206464)), (95203/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821503569637325/9223372036854775808), (-6158739891099/9223372036854775808)), (214335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199093927016829/144115188075855872), (-6152353671817/1152921504606846976)), (214497/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298374971365807/36028797018963968), (-5376132350471/144115188075855872)), (46967/36028797018963968), by norm_num⟩
  | 4 => ⟨((745007309216721/18014398509481984), (-8049862747295/36028797018963968)), (141083/18014398509481984), by norm_num⟩
  | 3 => ⟨((743613328299295/4503599627370496), (-10037282286311/9007199254740992)), (353347/9007199254740992), by norm_num⟩
  | 2 => ⟨((555969621197013/1125899906842624), (-19999591787723/4503599627370496)), (88577/562949953421312), by norm_num⟩
  | 1 => ⟨((2209980774757213/2251799813685248), (-29812534628187/2251799813685248)), (533873/1125899906842624), by norm_num⟩
  | 0 => ⟨((542103657031991/562949953421312), (-58881123328375/2251799813685248)), (1077427/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((542103657031991/562949953421312), (-58881123328375/2251799813685248)), (4110057835105514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086577583069149/2251799813685248), (-113401456354949/2251799813685248)), (4262811/2251799813685248), by norm_num⟩
  | 2 => ⟨((963883666185887/1125899906842624), (-210161609641829/2251799813685248)), (4164711/1125899906842624), by norm_num⟩
  | 3 => ⟨((1630748418787205/2251799813685248), (-89959747559251/562949953421312)), (15816427/2251799813685248), by norm_num⟩
  | 4 => ⟨((561740944089935/1125899906842624), (-521189193444885/2251799813685248)), (27963393/2251799813685248), by norm_num⟩
  | 5 => ⟨((879805897206577/4503599627370496), (-130017467714439/562949953421312)), (81695689/4503599627370496), by norm_num⟩
  | 6 => ⟨((-273409975136955/18014398509481984), (-1625581586992967/18014398509481984)), (139311927/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1955756865/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-999260439/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-387823919991565/4503599627370496), (-202334042425021/18014398509481984)), (98872651/4503599627370496), by norm_num⟩
  | 1 => ⟨((261971451/1073741824), (34168691/1073741824)), (269/4294967296), by norm_num⟩
  | 2 => ⟨((-742221011/2147483648), (-193614383/4294967296)), (3/33554432), by norm_num⟩
  | 3 => ⟨((87619603/268435456), (182850285/4294967296)), (365/4294967296), by norm_num⟩
  | 4 => ⟨((-496490057/2147483648), (-129513467/4294967296)), (65/1073741824), by norm_num⟩
  | 5 => ⟨((281332451/2147483648), (146775713/8589934592)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((-132845809/2147483648), (-34653909/4294967296)), (141/8589934592), by norm_num⟩
  | 7 => ⟨((1720596657/68719476736), (224415811/68719476736)), (459/68719476736), by norm_num⟩
  | 8 => ⟨((-38084511/4294967296), (-39738617/34359738368)), (327/137438953472), by norm_num⟩
  | 9 => ⟨((383649937/137438953472), (200156409/549755813888)), (207/274877906944), by norm_num⟩
  | 10 => ⟨((-869569697/1099511627776), (-56708581/549755813888)), (59/274877906944), by norm_num⟩
  | 11 => ⟨((1791764705/8796093022208), (116849097/4398046511104)), (61/1099511627776), by norm_num⟩
  | 12 => ⟨((-1692150557/35184372088832), (-110352807/17592186044416)), (463/35184372088832), by norm_num⟩
  | 13 => ⟨((184393213/17592186044416), (96200937/70368744177664)), (405/140737488355328), by norm_num⟩
  | 14 => ⟨((-597057499/281474976710656), (-77873651/281474976710656)), (329/562949953421312), by norm_num⟩
  | 15 => ⟨((1804364025/4503599627370496), (29417689/562949953421312)), (499/4503599627370496), by norm_num⟩
  | 16 => ⟨((-639018529/9007199254740992), (-83346589/9007199254740992)), (355/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-245208155085/633825300114114700748351602688)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889094418260465/316912650057057350374175801344), (-2320114941199/316912650057057350374175801344)), (138985/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944544481487029/19807040628566084398385987584), (-5219121386883/39614081257132168796771975168)), (156403/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888822611148889/2475880078570760549798248448), (-5543930969137/2475880078570760549798248448)), (166229/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221311020533449/19342813113834066795298816), (-5542372430335/154742504910672534362390528)), (166287/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774447035336599/4835703278458516698824704), (-5194318516323/9671406556917033397649408)), (155955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157276376212597/75557863725914323419136), (-4543373413015/604462909807314587353088)), (68261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235856492698107/9444732965739290427392), (-7379878870327/75557863725914323419136)), (110981/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162104145820595/590295810358705651712), (-2766097416845/2361183241434822606848)), (41643/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405118751944307/147573952589676412928), (-7602358518193/590295810358705651712)), (229199/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822255295184577/73786976294838206464), (-4748168257705/36893488147419103232)), (286743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821281107369215/9223372036854775808), (-10674291545355/9223372036854775808)), (161461/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796262280342759/576460752303423488), (-10662938698009/1152921504606846976)), (323343/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193296457739605/144115188075855872), (-4658653796147/72057594037927936)), (35425/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489699651197279/36028797018963968), (-6975227170783/18014398509481984)), (6657/562949953421312), by norm_num⟩
  | 3 => ⟨((371703956561743/2251799813685248), (-17393476774335/9007199254740992)), (33389/562949953421312), by norm_num⟩
  | 2 => ⟨((1111502876925239/2251799813685248), (-8663341297577/1125899906842624)), (536725/2251799813685248), by norm_num⟩
  | 1 => ⟨((552136256940513/562949953421312), (-25823363222375/1125899906842624)), (811355/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082521329283617/1125899906842624), (-25491019599707/562949953421312)), (1647889/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082521329283617/1125899906842624), (-25491019599707/562949953421312)), (6286197666648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((259626378181341/281474976710656), (-98035614903827/1125899906842624)), (829509/281474976710656), by norm_num⟩
  | 2 => ⟨((118669820433781/140737488355328), (-180851825108599/1125899906842624)), (837349/140737488355328), by norm_num⟩
  | 3 => ⟨((771448948623627/1125899906842624), (-304988441410487/1125899906842624)), (13448877/1125899906842624), by norm_num⟩
  | 4 => ⟨((891936357551695/2251799813685248), (-417946588393077/1125899906842624)), (25716095/1125899906842624), by norm_num⟩
  | 5 => ⟨((86005036803393/4503599627370496), (-662193424898445/2251799813685248)), (157857831/4503599627370496), by norm_num⟩
  | 6 => ⟨((-387823919991565/4503599627370496), (-202334042425021/18014398509481984)), (98872651/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-999260439/16777216)), (3/33554432), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1019419931/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-44531561352181/1125899906842624), (326916855204919/4503599627370496)), (66890655/4503599627370496), by norm_num⟩
  | 1 => ⟨((491000241/4294967296), (-450568793/2147483648)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((-709586615/4294967296), (1302311315/4294967296)), (271/4294967296), by norm_num⟩
  | 3 => ⟨((683656371/4294967296), (-627360641/2147483648)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-494005267/4294967296), (226663185/1073741824)), (3/67108864), by norm_num⟩
  | 5 => ⟨((571143549/8589934592), (-524112695/4294967296)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-550272395/17179869184), (1009920355/17179869184)), (109/8589934592), by norm_num⟩
  | 7 => ⟨((227213113/17179869184), (-834012935/34359738368)), (91/17179869184), by norm_num⟩
  | 8 => ⟨((-656730365/137438953472), (1205303717/137438953472)), (265/137438953472), by norm_num⟩
  | 9 => ⟨((421821089/274877906944), (-774172405/274877906944)), (43/68719476736), by norm_num⟩
  | 10 => ⟨((-487687905/1099511627776), (447529211/549755813888)), (201/1099511627776), by norm_num⟩
  | 11 => ⟨((512581581/4398046511104), (-940746031/4398046511104)), (213/4398046511104), by norm_num⟩
  | 12 => ⟨((-246925221/8796093022208), (906368587/17592186044416)), (207/17592186044416), by norm_num⟩
  | 13 => ⟨((439203499/70368744177664), (-806074513/70368744177664)), (93/35184372088832), by norm_num⟩
  | 14 => ⟨((-181351627/140737488355328), (1331345719/562949953421312)), (155/281474976710656), by norm_num⟩
  | 15 => ⟨((559118529/2251799813685248), (-1026155751/2251799813685248)), (241/2251799813685248), by norm_num⟩
  | 16 => ⟨((-404015101/9007199254740992), (741492901/9007199254740992)), (11/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (2696002577495/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778118978293905/633825300114114700748351602688), (3188376131333/633825300114114700748351602688)), (46257/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944505364272225/19807040628566084398385987584), (1793069818809/19807040628566084398385987584)), (104099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944369978357833/1237940039285380274899124224), (3809303667693/2475880078570760549798248448)), (27657/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885203018863439/77371252455336267181195264), (3808213091913/154742504910672534362390528)), (110655/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548817637522321/9671406556917033397649408), (3569041378427/9671406556917033397649408)), (103767/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258144690719775/604462909807314587353088), (1560876597447/302231454903657293676544)), (11353/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886745222323013/75557863725914323419136), (5070678486505/75557863725914323419136)), (147641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81047127756211/295147905179352825856), (3801110532249/4722366482869645213696)), (110777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620367702671255/590295810358705651712), (5223443720291/590295810358705651712)), (152393/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911061696531141/36893488147419103232), (815585304115/9223372036854775808)), (190603/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821135777574031/9223372036854775808), (3666958266607/4611686018427387904)), (107291/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796191524151129/576460752303423488), (7325984043511/1152921504606846976)), (214775/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193176918411531/144115188075855872), (1600330235259/36028797018963968)), (188145/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489528883800727/36028797018963968), (9584173589131/36028797018963968)), (282653/36028797018963968), by norm_num⟩
  | 3 => ⟨((743308627721927/4503599627370496), (11949103597449/9007199254740992)), (177039/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111326520319521/2251799813685248), (2975633506145/562949953421312)), (710447/4503599627370496), by norm_num⟩
  | 1 => ⟨((552031550440903/562949953421312), (35475456972203/2251799813685248)), (535707/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164641035622965/2251799813685248), (17506635902643/562949953421312)), (541475/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164641035622965/2251799813685248), (17506635902643/562949953421312)), (2065563204051780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1039339080642425/1125899906842624), (134632154209311/2251799813685248)), (4298843/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910816874175725/2251799813685248), (124281437923925/1125899906842624)), (1056341/281474976710656), by norm_num⟩
  | 3 => ⟨((797015258987551/1125899906842624), (421847567956239/2251799813685248)), (16207775/2251799813685248), by norm_num⟩
  | 4 => ⟨((1049372998116639/2251799813685248), (298622414465575/1125899906842624)), (7254841/562949953421312), by norm_num⟩
  | 5 => ⟨((41327069738101/281474976710656), (1113300734703309/4503599627370496)), (42440543/2251799813685248), by norm_num⟩
  | 6 => ⟨((-44531561352181/1125899906842624), (326916855204919/4503599627370496)), (66890655/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1019419931/16777216)), (1/16777216), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-519244587/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((846211827129713/18014398509481984), (1141973398448579/18014398509481984)), (44245893/4503599627370496), by norm_num⟩
  | 1 => ⟨((-594048283/4294967296), (-801675555/4294967296)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((218642365/1073741824), (147530297/536870912)), (47/1073741824), by norm_num⟩
  | 3 => ⟨((-107296517/536870912), (-579191943/2147483648)), (187/4294967296), by norm_num⟩
  | 4 => ⟨((315928047/2147483648), (852697667/4294967296)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((-744184685/8589934592), (-1004286499/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((730402131/17179869184), (985686771/17179869184)), (165/17179869184), by norm_num⟩
  | 7 => ⟨((-38404009/2147483648), (-414613507/17179869184)), (141/34359738368), by norm_num⟩
  | 8 => ⟨((113078261/17179869184), (1220804171/137438953472)), (105/68719476736), by norm_num⟩
  | 9 => ⟨((-591914737/274877906944), (-199699077/68719476736)), (139/274877906944), by norm_num⟩
  | 10 => ⟨((348571365/549755813888), (470401397/549755813888)), (83/549755813888), by norm_num⟩
  | 11 => ⟨((-746434265/4398046511104), (-503661167/2199023255552)), (45/1099511627776), by norm_num⟩
  | 12 => ⟨((1430879/34359738368), (494333191/8796093022208)), (179/17592186044416), by norm_num⟩
  | 13 => ⟨((-165932737/17592186044416), (-895713179/70368744177664)), (41/17592186044416), by norm_num⟩
  | 14 => ⟨((558375793/281474976710656), (753535085/281474976710656)), (35/70368744177664), by norm_num⟩
  | 15 => ⟨((-876855173/2251799813685248), (-591663487/1125899906842624)), (111/1125899906842624), by norm_num⟩
  | 16 => ⟨((322730819/4503599627370496), (871058517/9007199254740992)), (165/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1215434043387/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222256435518597/79228162514264337593543950336), (1437299234517/633825300114114700748351602688)), (46171/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944467527490707/19807040628566084398385987584), (1616606263663/39614081257132168796771975168)), (51947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888659893992857/2475880078570760549798248448), (1717199326267/2475880078570760549798248448)), (55199/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770326357614491/154742504910672534362390528), (858349560711/77371252455336267181195264)), (55205/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387185835910255/2417851639229258349412352), (804437077873/4835703278458516698824704)), (51761/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314520022365147/151115727451828646838272), (1407233837455/604462909807314587353088)), (45297/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886641005598977/75557863725914323419136), (1142879870173/37778931862957161709568)), (147239/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162084568265357/590295810358705651712), (1713449436209/4722366482869645213696)), (110451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620262221533915/590295810358705651712), (2354579507257/590295810358705651712)), (75951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821993157168039/73786976294838206464), (2941105725533/73786976294838206464)), (189929/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820991479739811/9223372036854775808), (206614580671/576460752303423488)), (213739/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592241516703705/1152921504606846976), (1651099365833/576460752303423488)), (213827/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596528091227611/72057594037927936), (721335041861/36028797018963968)), (187197/144115188075855872), by norm_num⟩
  | 4 => ⟨((744676984364905/18014398509481984), (4319855679285/36028797018963968)), (8781/1125899906842624), by norm_num⟩
  | 3 => ⟨((1486409398290823/9007199254740992), (1346394504447/2251799813685248)), (175793/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222269511573399/4503599627370496), (670534171171/281474976710656)), (704211/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103815380795559/1125899906842624), (15986699894333/2251799813685248)), (1058927/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163965928348161/2251799813685248), (31551328830345/2251799813685248)), (532091/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163965928348161/2251799813685248), (31551328830345/2251799813685248)), (2029766084911155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1039558006943499/1125899906842624), (3790079393827/140737488355328)), (2075167/1125899906842624), by norm_num⟩
  | 2 => ⟨((239755217653493/281474976710656), (55990872465435/1125899906842624)), (3943827/1125899906842624), by norm_num⟩
  | 3 => ⟨((1628183903210605/2251799813685248), (47691997247623/562949953421312)), (14221623/2251799813685248), by norm_num⟩
  | 4 => ⟨((580555691753891/1125899906842624), (137936492859837/1125899906842624)), (11487899/1125899906842624), by norm_num⟩
  | 5 => ⟨((564914222361365/2251799813685248), (142250328903423/1125899906842624)), (58647955/4503599627370496), by norm_num⟩
  | 6 => ⟨((846211827129713/18014398509481984), (1141973398448579/18014398509481984)), (44245893/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-519244587/8388608)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-264145017/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1345505271795365/18014398509481984), (-196788521389819/18014398509481984)), (96950417/9007199254740992), by norm_num⟩
  | 1 => ⟨((-961011307/4294967296), (70276943/2147483648)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((719733147/2147483648), (-105265453/2147483648)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((-1437418545/4294967296), (105115705/2147483648)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((538265141/2147483648), (-157449255/4294967296)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-322499651/2147483648), (94335163/4294967296)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((322040871/4294967296), (-23550241/2147483648)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((-1102569407/34359738368), (161257639/34359738368)), (85/17179869184), by norm_num⟩
  | 8 => ⟨((825750689/68719476736), (-241542357/137438953472)), (257/137438953472), by norm_num⟩
  | 9 => ⟨((-549717331/137438953472), (160799163/274877906944)), (173/274877906944), by norm_num⟩
  | 10 => ⟨((164680595/137438953472), (-192684497/1099511627776)), (209/1099511627776), by norm_num⟩
  | 11 => ⟨((-717583961/2199023255552), (104951121/2199023255552)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((1433126287/17592186044416), (-26200455/2199023255552)), (29/2199023255552), by norm_num⟩
  | 13 => ⟨((-1321003899/70368744177664), (193205043/70368744177664)), (27/8796093022208), by norm_num⟩
  | 14 => ⟨((565339145/140737488355328), (-82684369/140737488355328)), (93/140737488355328), by norm_num⟩
  | 15 => ⟨((-225813963/281474976710656), (132106791/1125899906842624)), (299/2251799813685248), by norm_num⟩
  | 16 => ⟨((676478177/4503599627370496), (-197878289/9007199254740992)), (113/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-94586903279/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777984419724829/633825300114114700748351602688), (-111844612787/316912650057057350374175801344)), (46111/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472214920987211/9903520314283042199192993792), (-125797160715/19807040628566084398385987584)), (207503/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888579912779881/2475880078570760549798248448), (-133624275599/1237940039285380274899124224)), (220475/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885123244681501/77371252455336267181195264), (-33396171695/19342813113834066795298816)), (220479/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96791786693335/604462909807314587353088), (-250387194643/9671406556917033397649408)), (206703/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014797325497/604462909807314587353088), (-219004739581/604462909807314587353088)), (90435/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943267565193781/37778931862957161709568), (-355725176621/75557863725914323419136)), (9185/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648298667979727/2361183241434822606848), (-133328063585/2361183241434822606848)), (6889/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1620153626084023/590295810358705651712), (-366428471003/590295810358705651712)), (151563/295147905179352825856), by norm_num⟩
  | 8 => ⟨((14233264765545/576460752303423488), (-457700292645/73786976294838206464)), (94731/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910419979581821/4611686018427387904), (-514452218673/9223372036854775808)), (53289/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592090813289099/1152921504606846976), (-513877087227/1152921504606846976)), (106585/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192925234094843/144115188075855872), (-224498148019/72057594037927936)), (373081/144115188075855872), by norm_num⟩
  | 4 => ⟨((744579687503367/18014398509481984), (-336102149647/18014398509481984)), (279843/18014398509481984), by norm_num⟩
  | 3 => ⟨((743084672182041/4503599627370496), (-838002485141/9007199254740992)), (174931/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221798919739005/4503599627370496), (-834632858669/2251799813685248)), (1399803/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103474247125395/1125899906842624), (-621779549375/562949953421312)), (525153/562949953421312), by norm_num⟩
  | 0 => ⟨((2162694862925551/2251799813685248), (-2453759923811/1125899906842624)), (525621/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162694862925551/2251799813685248), (-2453759923811/1125899906842624)), (2005084992528819949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2077105148489583/2251799813685248), (-9426653203943/2251799813685248)), (1011935/281474976710656), by norm_num⟩
  | 2 => ⟨((1915923835623137/2251799813685248), (-17390666598281/2251799813685248)), (7501323/1125899906842624), by norm_num⟩
  | 3 => ⟨((1630012439967805/2251799813685248), (-29593387876245/2251799813685248)), (6440367/562949953421312), by norm_num⟩
  | 4 => ⟨((589764856027975/1125899906842624), (-21421793396513/1125899906842624)), (37973077/2251799813685248), by norm_num⟩
  | 5 => ⟨((1234083740702997/4503599627370496), (-89768696642207/4503599627370496)), (82453647/4503599627370496), by norm_num⟩
  | 6 => ⟨((1345505271795365/18014398509481984), (-196788521389819/18014398509481984)), (96950417/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-264145017/4194304)), (1/8388608), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1073788119/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((507585268892833/18014398509481984), (-600460168014733/9007199254740992)), (22818021/1125899906842624), by norm_num⟩
  | 1 => ⟨((-368441281/4294967296), (871712901/4294967296)), (267/4294967296), by norm_num⟩
  | 2 => ⟨((280431937/2147483648), (-1326974743/4294967296)), (409/4294967296), by norm_num⟩
  | 3 => ⟨((-284593775/2147483648), (1346668127/4294967296)), (417/4294967296), by norm_num⟩
  | 4 => ⟨((433226067/4294967296), (-256247583/1073741824)), (319/4294967296), by norm_num⟩
  | 5 => ⟨((-527586593/8589934592), (624121213/4294967296)), (195/4294967296), by norm_num⟩
  | 6 => ⟨((535416407/17179869184), (-633383679/8589934592)), (199/8589934592), by norm_num⟩
  | 7 => ⟨((-465739219/34359738368), (275478689/8589934592)), (87/8589934592), by norm_num⟩
  | 8 => ⟨((44311047/8589934592), (-419350525/34359738368)), (267/68719476736), by norm_num⟩
  | 9 => ⟨((-479665695/274877906944), (567432037/137438953472)), (91/68719476736), by norm_num⟩
  | 10 => ⟨((584141189/1099511627776), (-1382047655/1099511627776)), (223/549755813888), by norm_num⟩
  | 11 => ⟨((-323351083/2199023255552), (191257959/549755813888)), (31/274877906944), by norm_num⟩
  | 12 => ⟨((82037469/2199023255552), (-388192765/4398046511104)), (253/8796093022208), by norm_num⟩
  | 13 => ⟨((-614805945/70368744177664), (181824859/8796093022208)), (119/17592186044416), by norm_num⟩
  | 14 => ⟨((133699321/70368744177664), (-79081409/17592186044416)), (13/8796093022208), by norm_num⟩
  | 15 => ⟨((-54273411/140737488355328), (513632265/562949953421312)), (85/281474976710656), by norm_num⟩
  | 16 => ⟨((330473235/4503599627370496), (-390941239/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-381309055247/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222239735938299/79228162514264337593543950336), (-1803395514869/633825300114114700748351602688)), (184755/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888784757456707/39614081257132168796771975168), (-2028359143375/39614081257132168796771975168)), (207873/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888500198087019/2475880078570760549798248448), (-2154554443327/2475880078570760549798248448)), (220891/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770166656366501/154742504910672534362390528), (-2153905450473/154742504910672534362390528)), (220921/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548593618072589/9671406556917033397649408), (-252324632933/1208925819614629174706176)), (207145/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257949073970869/604462909807314587353088), (-882791712561/302231454903657293676544)), (45321/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886428094961685/75557863725914323419136), (-2867781798659/75557863725914323419136)), (147323/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648258427026323/2361183241434822606848), (-268713388485/590295810358705651712)), (221037/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620042630285967/590295810358705651712), (-2954013413949/590295810358705651712)), (152005/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821718646346775/73786976294838206464), (-1844884001247/36893488147419103232)), (380139/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820682625494115/9223372036854775808), (-4147212737687/9223372036854775808)), (427831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591932626017339/1152921504606846976), (-4142497331855/1152921504606846976)), (214025/576460752303423488), by norm_num⟩
  | 5 => ⟨((596392931413891/72057594037927936), (-3619387099243/144115188075855872)), (187395/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488948410527083/36028797018963968), (-5418501408533/36028797018963968)), (562679/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485902316723255/9007199254740992), (-6754651037467/9007199254740992)), (704215/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221254963001231/4503599627370496), (-6727013198993/2251799813685248)), (1411035/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206108030850363/2251799813685248), (-20043379295253/2251799813685248)), (2123091/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160917167134745/2251799813685248), (-39539280081719/2251799813685248)), (1068121/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160917167134745/2251799813685248), (-39539280081719/2251799813685248)), (4074558260204124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((518252068876043/562949953421312), (-37943474631035/1125899906842624)), (8350135/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905855243063071/2251799813685248), (-139723143120417/2251799813685248)), (249017/35184372088832), by norm_num⟩
  | 3 => ⟨((802194233437425/1125899906842624), (-118257441569591/1125899906842624)), (14477559/1125899906842624), by norm_num⟩
  | 4 => ⟨((1118271281217305/2251799813685248), (-168514869060113/1125899906842624)), (47343085/2251799813685248), by norm_num⟩
  | 5 => ⟨((1009807006029821/4503599627370496), (-167373082973671/1125899906842624)), (61194109/2251799813685248), by norm_num⟩
  | 6 => ⟨((507585268892833/18014398509481984), (-600460168014733/9007199254740992)), (22818021/1125899906842624), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1073788119/16777216)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile017Terms2
