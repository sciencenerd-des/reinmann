/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile056Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨56,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78161/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78161/2560))
  have he : value ((69/80), (78161/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-22723512985/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-837442958462973/2251799813685248), (-57027235319885/140737488355328)), (3436673/1125899906842624), by norm_num⟩
  | 1 => ⟨((2214321997/8589934592), (9650455903/34359738368)), (75/34359738368), by norm_num⟩
  | 2 => ⟨((-12278808393/137438953472), (-13378372601/137438953472)), (53/68719476736), by norm_num⟩
  | 3 => ⟨((5674014279/274877906944), (12364241665/549755813888)), (25/137438953472), by norm_num⟩
  | 4 => ⟨((-491615875/137438953472), (-4285119625/1099511627776)), (141/4398046511104), by norm_num⟩
  | 5 => ⟨((8723511237/17592186044416), (9504699477/17592186044416)), (5/1099511627776), by norm_num⟩
  | 6 => ⟨((-16124472583/281474976710656), (-4392103763/70368744177664)), (75/140737488355328), by norm_num⟩
  | 7 => ⟨((12773294525/2251799813685248), (108727655/17592186044416)), (121/2251799813685248), by norm_num⟩
  | 8 => ⟨((-8853773087/18014398509481984), (-4823313121/9007199254740992)), (43/9007199254740992), by norm_num⟩
  | 9 => ⟨((10910165071/288230376151711744), (2971791903/72057594037927936)), (27/72057594037927936), by norm_num⟩
  | 10 => ⟨((-6049880127/2305843009213693952), (-1647911343/576460752303423488)), (61/2305843009213693952), by norm_num⟩
  | 11 => ⟨((12199148663/73786976294838206464), (415361855/2305843009213693952)), (125/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-11274407335/1180591620717411303424), (-6142013839/590295810358705651712)), (117/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((9618244501/18889465931478580854784), (5239777939/9444732965739290427392)), (51/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-7619267495/302231454903657293676544), (-16603141967/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((5633358701/4835703278458516698824704), (12275649113/9671406556917033397649408)), (123/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-15618986803/309485009821345068724781056), (-17017663145/309485009821345068724781056)), (173/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-1506707902499/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111315101010397/39614081257132168796771975168), (-1787456318957/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236537267081605/4951760157141521099596496896), (-4021544504975/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((946116086510681/1237940039285380274899124224), (-2136314192205/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886948758582711/77371252455336267181195264), (-2136166386647/77371252455336267181195264)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776045058247957/4835703278458516698824704), (-1001249443705/2417851639229258349412352)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261007326732839/604462909807314587353088), (-3504058725401/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891395537364515/75557863725914323419136), (-5693505793933/75557863725914323419136)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650120247636567/2361183241434822606848), (-1067403286109/1180591620717411303424)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625159484385131/590295810358705651712), (-1467469684999/147573952589676412928)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457027496654615/18446744073709551616), (-7336088537977/73786976294838206464)), (2981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913933192827591/4611686018427387904), (-8251365820877/9223372036854775808)), (839/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599108267821451/1152921504606846976), (-4124598216367/576460752303423488)), (6719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18735240958487/2251799813685248), (-7215603353115/144115188075855872)), (5887/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498334504902295/36028797018963968), (-10818510577909/36028797018963968)), (8845/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497603037406213/9007199254740992), (-844659769053/562949953421312)), (5541/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122280413627097/2251799813685248), (-1687706279533/281474976710656)), (5561/1125899906842624), by norm_num⟩
  | 1 => ⟨((560207071630761/562949953421312), (-20220094287461/1125899906842624)), (8391/562949953421312), by norm_num⟩
  | 0 => ⟨((1114702965910983/1125899906842624), (-2519373197235/70368744177664)), (33961/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114702965910983/1125899906842624), (-2519373197235/70368744177664)), (129550938132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102174181642969/1125899906842624), (-79818186554647/1125899906842624)), (69679/1125899906842624), by norm_num⟩
  | 2 => ⟨((536644943494247/562949953421312), (-156272407363101/1125899906842624)), (73151/562949953421312), by norm_num⟩
  | 3 => ⟨((1001447916778555/1125899906842624), (-297940506822703/1125899906842624)), (319545/1125899906842624), by norm_num⟩
  | 4 => ⟨((811909992050575/1125899906842624), (-530014965039425/1125899906842624)), (23049/35184372088832), by norm_num⟩
  | 5 => ⟨((671963768229883/2251799813685248), (-1528819545810639/2251799813685248)), (1758169/1125899906842624), by norm_num⟩
  | 6 => ⟨((-837442958462973/2251799813685248), (-57027235319885/140737488355328)), (3436673/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-22723512985/1073741824)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-9003978991/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-230274277971377/1125899906842624), (-370816194066065/1125899906842624)), (9626997/2251799813685248), by norm_num⟩
  | 1 => ⟨((3860201287/17179869184), (3108087369/8589934592)), (163/34359738368), by norm_num⟩
  | 2 => ⟨((-8481729141/68719476736), (-13658331911/68719476736)), (181/68719476736), by norm_num⟩
  | 3 => ⟨((6212087909/137438953472), (20006948373/274877906944)), (67/68719476736), by norm_num⟩
  | 4 => ⟨((-6824676115/549755813888), (-10989939671/549755813888)), (149/549755813888), by norm_num⟩
  | 5 => ⟨((5998138437/2199023255552), (19317892439/4398046511104)), (265/4398046511104), by norm_num⟩
  | 6 => ⟨((-8786171461/17592186044416), (-14148582683/17592186044416)), (49/4398046511104), by norm_num⟩
  | 7 => ⟨((5515769107/70368744177664), (2220543829/17592186044416)), (249/140737488355328), by norm_num⟩
  | 8 => ⟨((-12119383445/1125899906842624), (-1219758369/70368744177664)), (69/281474976710656), by norm_num⟩
  | 9 => ⟨((11835114297/9007199254740992), (19058368475/9007199254740992)), (273/9007199254740992), by norm_num⟩
  | 10 => ⟨((-10401761603/72057594037927936), (-16750206247/72057594037927936)), (243/72057594037927936), by norm_num⟩
  | 11 => ⟨((8310911361/576460752303423488), (6691629971/288230376151711744)), (49/144115188075855872), by norm_num⟩
  | 12 => ⟨((-12173959135/9223372036854775808), (-9802009223/4611686018427387904)), (145/4611686018427387904), by norm_num⟩
  | 13 => ⟨((2057609401/18446744073709551616), (13253671121/73786976294838206464)), (99/36893488147419103232), by norm_num⟩
  | 14 => ⟨((-10333782735/1180591620717411303424), (-4160184561/295147905179352825856)), (251/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((6054837707/9444732965739290427392), (19500500829/18889465931478580854784)), (297/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-6651919111/151115727451828646838272), (-10711744923/151115727451828646838272)), (165/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-346251932433/1267650600228229401496703205376)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890251201980319/316912650057057350374175801344), (-1642133459593/316912650057057350374175801344)), (723/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891691635101995/39614081257132168796771975168), (-3694475051395/39614081257132168796771975168)), (1627/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891587894856137/2475880078570760549798248448), (-3924998695873/2475880078570760549798248448)), (1729/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443313346249487/38685626227668133590597632), (-3924569947861/154742504910672534362390528)), (3459/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775743198870555/4835703278458516698824704), (-28740849511/75557863725914323419136)), (6487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260479228007861/604462909807314587353088), (-3218519507091/604462909807314587353088)), (2839/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59079302124369/2361183241434822606848), (-5229239772595/75557863725914323419136)), (4615/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299597347968085/4722366482869645213696), (-1960591050773/2361183241434822606848)), (6925/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624275570914615/590295810358705651712), (-2695205067813/295147905179352825856)), (4763/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913502858060915/36893488147419103232), (-3368094722919/36893488147419103232)), (2979/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826624936065057/9223372036854775808), (-118370400597/144115188075855872)), (13415/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597867887189203/1152921504606846976), (-7572570446011/1152921504606846976)), (13427/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197971291634897/144115188075855872), (-206952215891/4503599627370496)), (11763/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496710718941553/36028797018963968), (-9926647057329/36028797018963968)), (17671/36028797018963968), by norm_num⟩
  | 3 => ⟨((747788762145831/4503599627370496), (-6197974334261/4503599627370496)), (11069/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120261238038987/2251799813685248), (-12377395765917/2251799813685248)), (22211/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117401253319409/1125899906842624), (-9259833663267/562949953421312)), (33499/1125899906842624), by norm_num⟩
  | 0 => ⟨((554370427955441/562949953421312), (-287916931881/8796093022208)), (67729/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554370427955441/562949953421312), (-287916931881/8796093022208)), (258365635398482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((272659254038313/281474976710656), (-18145855476915/281474976710656)), (34457/281474976710656), by norm_num⟩
  | 2 => ⟨((525899656208681/562949953421312), (-35155064056075/281474976710656)), (284795/1125899906842624), by norm_num⟩
  | 3 => ⟨((965012724965895/1125899906842624), (-131365397500957/562949953421312)), (603243/1125899906842624), by norm_num⟩
  | 4 => ⟨((765807052175451/1125899906842624), (-450374955848881/1125899906842624)), (328905/281474976710656), by norm_num⟩
  | 5 => ⟨((681451056127309/2251799813685248), (-306333018784493/562949953421312)), (5684461/2251799813685248), by norm_num⟩
  | 6 => ⟨((-230274277971377/1125899906842624), (-370816194066065/1125899906842624)), (9626997/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-9003978991/268435456)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-22723512985/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-116554159024305/4503599627370496), (1357337187620499/4503599627370496)), (13837541/4503599627370496), by norm_num⟩
  | 1 => ⟨((2465490317/68719476736), (-7177997167/17179869184)), (295/68719476736), by norm_num⟩
  | 2 => ⟨((-854473831/34359738368), (9950816997/34359738368)), (103/34359738368), by norm_num⟩
  | 3 => ⟨((1579403005/137438953472), (-9196507661/68719476736)), (3/2147483648), by norm_num⟩
  | 4 => ⟨((-273689685/68719476736), (25498133425/549755813888)), (67/137438953472), by norm_num⟩
  | 5 => ⟨((2428252589/2199023255552), (-28278334869/2199023255552)), (75/549755813888), by norm_num⟩
  | 6 => ⟨((-1122090957/4398046511104), (26134730781/8796093022208)), (279/8796093022208), by norm_num⟩
  | 7 => ⟨((888884781/17592186044416), (-20703102807/35184372088832)), (223/35184372088832), by norm_num⟩
  | 8 => ⟨((-2464511919/281474976710656), (3587574335/35184372088832)), (39/35184372088832), by norm_num⟩
  | 9 => ⟨((1518461767/1125899906842624), (-17683321141/1125899906842624)), (97/562949953421312), by norm_num⟩
  | 10 => ⟨((-421006997/2251799813685248), (19611430707/9007199254740992)), (217/9007199254740992), by norm_num⟩
  | 11 => ⟨((848930365/36028797018963968), (-2471565073/9007199254740992)), (55/18014398509481984), by norm_num⟩
  | 12 => ⟨((-196144563/72057594037927936), (9136844597/288230376151711744)), (205/576460752303423488), by norm_num⟩
  | 13 => ⟨((1338654039/4611686018427387904), (-31178722815/9223372036854775808)), (11/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1060439169/36893488147419103232), (24698792929/73786976294838206464)), (281/73786976294838206464), by norm_num⟩
  | 15 => ⟨((784043115/295147905179352825856), (-18261225261/590295810358705651712)), (105/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-1086914549/4722366482869645213696), (25315433607/9444732965739290427392)), (293/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (1078859386945/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780121528744929/633825300114114700748351602688), (2557252101065/633825300114114700748351602688)), (5779/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472815832332797/9903520314283042199192993792), (2876596859207/39614081257132168796771975168)), (3251/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118195814840717/154742504910672534362390528), (3056010588923/2475880078570760549798248448)), (6909/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110799923264347/9671406556917033397649408), (1527795165573/77371252455336267181195264)), (6911/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775530229075899/4835703278458516698824704), (2864169441389/9671406556917033397649408)), (6481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630053395348859/302231454903657293676544), (156606362543/37778931862957161709568)), (709/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944966472212777/37778931862957161709568), (1017732095983/18889465931478580854784)), (2305/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299144231385261/4722366482869645213696), (1526231973693/2361183241434822606848)), (6917/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202956653474523/73786976294838206464), (4195948008129/590295810358705651712)), (4757/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228278603143127/9223372036854775808), (5243150365379/73786976294838206464)), (5949/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912876180141733/4611686018427387904), (5896090655941/9223372036854775808)), (13393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596997093754535/1152921504606846976), (2946512173715/576460752303423488)), (13403/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197211351333135/144115188075855872), (2576473747867/72057594037927936)), (5869/72057594037927936), by norm_num⟩
  | 4 => ⟨((373893703356467/9007199254740992), (7722525602387/36028797018963968)), (17629/36028797018963968), by norm_num⟩
  | 3 => ⟨((373541161086115/2251799813685248), (4820547042195/4503599627370496)), (22073/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118858847605065/2251799813685248), (2405752159045/562949953421312)), (11065/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115323844419945/1125899906842624), (14389330689143/1125899906842624)), (33337/1125899906842624), by norm_num⟩
  | 0 => ⟨((69043153880993/70368744177664), (28598121259861/1125899906842624)), (16811/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((69043153880993/70368744177664), (28598121259861/1125899906842624)), (64128876806163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((135394269629833/140737488355328), (56118792794333/1125899906842624)), (135371/1125899906842624), by norm_num⟩
  | 2 => ⟨((1039234128979279/1125899906842624), (107976389968153/1125899906842624)), (273959/1125899906842624), by norm_num⟩
  | 3 => ⟨((948884237001805/1125899906842624), (12458117823897/70368744177664)), (279145/562949953421312), by norm_num⟩
  | 4 => ⟨((764409772905317/1125899906842624), (167990942057473/562949953421312)), (569355/562949953421312), by norm_num⟩
  | 5 => ⟨((52340184903935/140737488355328), (456217882559085/1125899906842624)), (4451647/2251799813685248), by norm_num⟩
  | 6 => ⟨((-116554159024305/4503599627370496), (1357337187620499/4503599627370496)), (13837541/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-22723512985/536870912)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-13190590803/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((120709828987793/1125899906842624), (507406559346827/2251799813685248)), (4727005/2251799813685248), by norm_num⟩
  | 1 => ⟨((-5928801733/34359738368), (-12460927637/34359738368)), (59/17179869184), by norm_num⟩
  | 2 => ⟨((2385509571/17179869184), (20055089363/68719476736)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((-10238212117/137438953472), (-5379570193/34359738368)), (13/8589934592), by norm_num⟩
  | 4 => ⟨((1029860421/34359738368), (8658084221/137438953472)), (169/274877906944), by norm_num⟩
  | 5 => ⟨((-10607976999/1099511627776), (-22295438391/1099511627776)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((5690960119/2199023255552), (11961041273/2199023255552)), (15/274877906944), by norm_num⟩
  | 7 => ⟨((-10467710827/17592186044416), (-22000632339/17592186044416)), (223/17592186044416), by norm_num⟩
  | 8 => ⟨((8423565331/70368744177664), (4426081473/17592186044416)), (91/35184372088832), by norm_num⟩
  | 9 => ⟨((-6025424623/281474976710656), (-12664005913/281474976710656)), (33/70368744177664), by norm_num⟩
  | 10 => ⟨((7758037461/2251799813685248), (509548281/70368744177664)), (43/562949953421312), by norm_num⟩
  | 11 => ⟨((-9080785175/18014398509481984), (-2385705663/2251799813685248)), (203/18014398509481984), by norm_num⟩
  | 12 => ⟨((9743306623/144115188075855872), (20478107423/144115188075855872)), (55/36028797018963968), by norm_num⟩
  | 13 => ⟨((-4824999099/576460752303423488), (-20281995361/1152921504606846976)), (55/288230376151711744), by norm_num⟩
  | 14 => ⟨((8874898831/9223372036854775808), (18652921299/9223372036854775808)), (51/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-7617919279/73786976294838206464), (-8005524991/36893488147419103232)), (177/73786976294838206464), by norm_num⟩
  | 16 => ⟨((6130284051/590295810358705651712), (12884395429/590295810358705651712)), (9/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (1467655813711/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444956581958469/158456325028528675187087900672), (869431076857/316912650057057350374175801344)), (2887/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890931378205543/39614081257132168796771975168), (1955977541981/39614081257132168796771975168)), (203/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1890780524678919/2475880078570760549798248448), (519482899243/618970019642690137449562112)), (6903/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772446467858941/154742504910672534362390528), (2077600291921/154742504910672534362390528)), (863/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550730394167897/9671406556917033397649408), (973699160263/4835703278458516698824704)), (3237/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629909103001961/302231454903657293676544), (1703621643075/604462909807314587353088)), (5665/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889464409069093/75557863725914323419136), (2767725520881/75557863725914323419136)), (1151/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649396596320379/2361183241434822606848), (2075217087395/4722366482869645213696)), (1727/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811585569371945/295147905179352825856), (1426243022765/295147905179352825856)), (2375/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825627097164015/73786976294838206464), (1782100920363/36893488147419103232)), (5939/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28516822345015/144115188075855872), (1001948738899/2305843009213693952)), (13369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798161439779767/576460752303423488), (1001345232025/288230376151711744)), (13375/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196623117754077/144115188075855872), (3501994065937/144115188075855872)), (5855/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494695866574739/36028797018963968), (2623783221113/18014398509481984)), (4395/9007199254740992), by norm_num⟩
  | 3 => ⟨((373267976891879/2251799813685248), (1637493382517/2251799813685248)), (22001/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235550024563763/4503599627370496), (3267881994875/1125899906842624)), (22039/2251799813685248), by norm_num⟩
  | 1 => ⟨((139215034946681/140737488355328), (9768182445565/1125899906842624)), (66311/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203143384717621/2251799813685248), (9697436136871/562949953421312)), (66699/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203143384717621/2251799813685248), (9697436136871/562949953421312)), (254436497214889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2154870117606825/2251799813685248), (75903167391079/2251799813685248)), (66407/562949953421312), by norm_num⟩
  | 2 => ⟨((2059554275095567/2251799813685248), (145271765499495/2251799813685248)), (65787/281474976710656), by norm_num⟩
  | 3 => ⟨((1874349531677793/2251799813685248), (132869309192947/1125899906842624)), (1030635/2251799813685248), by norm_num⟩
  | 4 => ⟨((1528807815276031/2251799813685248), (442390173312205/2251799813685248)), (1959011/2251799813685248), by norm_num⟩
  | 5 => ⟨((951036702992289/2251799813685248), (300350657394429/1125899906842624)), (3429789/2251799813685248), by norm_num⟩
  | 6 => ⟨((120709828987793/1125899906842624), (507406559346827/2251799813685248)), (4727005/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-13190590803/268435456)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-29369714475/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-129233854189325/2251799813685248), (462428226180715/2251799813685248)), (10245517/4503599627370496), by norm_num⟩
  | 1 => ⟨((7066527771/68719476736), (-6321412301/17179869184)), (141/34359738368), by norm_num⟩
  | 2 => ⟨((-395672439/4294967296), (22652900699/68719476736)), (255/68719476736), by norm_num⟩
  | 3 => ⟨((1890532905/34359738368), (-13529516445/68719476736)), (77/34359738368), by norm_num⟩
  | 4 => ⟨((-6774760469/274877906944), (24241639205/274877906944)), (139/137438953472), by norm_num⟩
  | 5 => ⟨((4855496489/549755813888), (-8687037319/274877906944)), (201/549755813888), by norm_num⟩
  | 6 => ⟨((-724990151/274877906944), (20753441835/2199023255552)), (121/1099511627776), by norm_num⟩
  | 7 => ⟨((1484580535/2199023255552), (-21248671959/8796093022208)), (125/4398046511104), by norm_num⟩
  | 8 => ⟨((-5320022463/35184372088832), (4759063649/8796093022208)), (113/17592186044416), by norm_num⟩
  | 9 => ⟨((4236533611/140737488355328), (-473727631/4398046511104)), (181/140737488355328), by norm_num⟩
  | 10 => ⟨((-6072679371/1125899906842624), (21729432799/1125899906842624)), (131/562949953421312), by norm_num⟩
  | 11 => ⟨((30911309/35184372088832), (-1769723499/562949953421312)), (173/4503599627370496), by norm_num⟩
  | 12 => ⟨((-4726240479/36028797018963968), (4227891783/9007199254740992)), (209/36028797018963968), by norm_num⟩
  | 13 => ⟨((1302813251/72057594037927936), (-18647052645/288230376151711744)), (233/288230376151711744), by norm_num⟩
  | 14 => ⟨((-5335606809/2305843009213693952), (19092018943/2305843009213693952)), (15/144115188075855872), by norm_num⟩
  | 15 => ⟨((5098732813/18446744073709551616), (-9122214861/9223372036854775808)), (231/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-4567851399/147573952589676412928), (8172407429/73786976294838206464)), (209/147573952589676412928), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (2401119118211/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444895240308265/158456325028528675187087900672), (2844081547445/633825300114114700748351602688)), (5781/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945327609990865/19807040628566084398385987584), (3199147403845/39614081257132168796771975168)), (6505/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118155434413641/154742504910672534362390528), (3398557315395/2475880078570760549798248448)), (6913/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886076359236893/77371252455336267181195264), (3397953468273/154742504910672534362390528)), (3457/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387613704486329/2417851639229258349412352), (1592469934681/4835703278458516698824704)), (6483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629788445378475/302231454903657293676544), (5441759705/1180591620717411303424)), (5675/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236133990400445/9444732965739290427392), (2263170805181/37778931862957161709568)), (1153/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298498523484647/4722366482869645213696), (212106515239/295147905179352825856)), (865/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622765473908813/590295810358705651712), (4664634254379/590295810358705651712)), (595/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912559637424851/36893488147419103232), (364264364239/4611686018427387904)), (11905/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912252156053549/4611686018427387904), (6553235470913/9223372036854775808)), (6701/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595749291311337/1152921504606846976), (6548833154021/1152921504606846976)), (13413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196119801813199/144115188075855872), (2862639260873/72057594037927936)), (2937/36028797018963968), by norm_num⟩
  | 4 => ⟨((746969023648105/18014398509481984), (8578022106369/36028797018963968)), (8823/18014398509481984), by norm_num⟩
  | 3 => ⟨((373029917496905/2251799813685248), (83634547921/70368744177664)), (22099/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116815361252285/2251799813685248), (5339643889249/1125899906842624)), (22163/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112262380390083/1125899906842624), (15954179515211/1125899906842624)), (16701/562949953421312), by norm_num⟩
  | 0 => ⟨((1098582867589713/1125899906842624), (15824926854063/562949953421312)), (67441/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098582867589713/1125899906842624), (15824926854063/562949953421312)), (257267002585982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((535519452658791/562949953421312), (61763904294075/1125899906842624)), (67701/562949953421312), by norm_num⟩
  | 2 => ⟨((507731437706765/562949953421312), (117508748408685/1125899906842624)), (272465/1125899906842624), by norm_num⟩
  | 3 => ⟨((1807188257513095/2251799813685248), (26495643800157/140737488355328)), (548353/1125899906842624), by norm_num⟩
  | 4 => ⟨((2676862636201/4398046511104), (340226452173151/1125899906842624)), (543317/562949953421312), by norm_num⟩
  | 5 => ⟨((78570550431951/281474976710656), (414156364817943/1125899906842624)), (989739/562949953421312), by norm_num⟩
  | 6 => ⟨((-129233854189325/2251799813685248), (462428226180715/2251799813685248)), (10245517/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-29369714475/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-7974120753/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1616726314655475/9007199254740992), (-231075795709221/4503599627370496)), (18137315/9007199254740992), by norm_num⟩
  | 1 => ⟨((24002106811/68719476736), (6861156251/68719476736)), (271/68719476736), by norm_num⟩
  | 2 => ⟨((-23352971621/68719476736), (-834449599/8589934592)), (133/34359738368), by norm_num⟩
  | 3 => ⟨((15147594829/68719476736), (4330037183/68719476736)), (87/34359738368), by norm_num⟩
  | 4 => ⟨((-1842241157/17179869184), (-2106465825/68719476736)), (171/137438953472), by norm_num⟩
  | 5 => ⟨((22942948893/549755813888), (1639597291/137438953472)), (67/137438953472), by norm_num⟩
  | 6 => ⟨((-7440819517/549755813888), (-1063503003/274877906944)), (175/1099511627776), by norm_num⟩
  | 7 => ⟨((4136904633/1099511627776), (2365121471/2199023255552)), (49/1099511627776), by norm_num⟩
  | 8 => ⟨((-8050044711/8796093022208), (-2301156937/8796093022208)), (3/274877906944), by norm_num⟩
  | 9 => ⟨((6962072757/35184372088832), (3980306345/70368744177664)), (21/8796093022208), by norm_num⟩
  | 10 => ⟨((-10838054429/281474976710656), (-6196254811/562949953421312)), (33/70368744177664), by norm_num⟩
  | 11 => ⟨((15338094625/2251799813685248), (1096123193/562949953421312)), (47/562949953421312), by norm_num⟩
  | 12 => ⟨((-9948851333/9007199254740992), (-5687885989/18014398509481984)), (123/9007199254740992), by norm_num⟩
  | 13 => ⟨((11913582019/72057594037927936), (6811147737/144115188075855872)), (37/18014398509481984), by norm_num⟩
  | 14 => ⟨((-26494583043/1152921504606846976), (-473352911/72057594037927936)), (331/1152921504606846976), by norm_num⟩
  | 15 => ⟨((13748287477/4611686018427387904), (3930036197/4611686018427387904)), (173/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-13376466067/36893488147419103232), (-3823748661/36893488147419103232)), (169/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-1864793825709/5070602400912917605986812821504)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779369739043553/633825300114114700748351602688), (-1104164915985/158456325028528675187087900672)), (5791/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945208638948661/19807040628566084398385987584), (-4967978916789/39614081257132168796771975168)), (1629/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236279216026747/309485009821345068724781056), (-164924076965/77371252455336267181195264)), (6925/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((6921480610493/604462909807314587353088), (-1319137455905/38685626227668133590597632)), (433/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550216502656211/9671406556917033397649408), (-618210130257/1208925819614629174706176)), (6497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259367876957115/604462909807314587353088), (-2163193253535/302231454903657293676544)), (711/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944365680798751/37778931862957161709568), (-7028344842879/75557863725914323419136)), (4623/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298242303043467/4722366482869645213696), (-2634739791591/2361183241434822606848)), (6939/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622411873302367/590295810358705651712), (-7242643526271/590295810358705651712)), (9547/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912337665022871/36893488147419103232), (-9048968153465/73786976294838206464)), (11943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824002204719513/9223372036854775808), (-10174126983609/9223372036854775808)), (13449/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595243852437635/1152921504606846976), (-10166674495139/1152921504606846976)), (6733/576460752303423488), by norm_num⟩
  | 5 => ⟨((597836901127001/72057594037927936), (-8887456485427/144115188075855872)), (5901/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493261585300243/36028797018963968), (-6657209122283/18014398509481984)), (17739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491261074285715/9007199254740992), (-16613683601617/9007199254740992)), (22239/9007199254740992), by norm_num⟩
  | 2 => ⟨((557968660526127/1125899906842624), (-8284839652207/1125899906842624)), (11169/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110896998353739/1125899906842624), (-24744525003149/1125899906842624)), (16877/562949953421312), by norm_num⟩
  | 0 => ⟨((136957568867419/140737488355328), (-24524591485571/562949953421312)), (68499/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((136957568867419/140737488355328), (-24524591485571/562949953421312)), (261302952293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66506035153157/70368744177664), (-47731822794083/562949953421312)), (17411/140737488355328), by norm_num⟩
  | 2 => ⟨((124698938573921/140737488355328), (-45111708639461/281474976710656)), (286905/1125899906842624), by norm_num⟩
  | 3 => ⟨((854985200781449/1125899906842624), (-319765955771161/1125899906842624)), (600383/1125899906842624), by norm_num⟩
  | 4 => ⟨((1116883345071519/2251799813685248), (-121411840535969/281474976710656)), (626433/562949953421312), by norm_num⟩
  | 5 => ⟨((270019531240107/4503599627370496), (-963516289609621/2251799813685248)), (2323659/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1616726314655475/9007199254740992), (-231075795709221/4503599627370496)), (18137315/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-7974120753/134217728)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-481443911/268435456), (-8521317369/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((37083959665685/281474976710656), (-114391194418307/1125899906842624)), (19583907/9007199254740992), by norm_num⟩
  | 1 => ⟨((-18826642153/68719476736), (14518420513/68719476736)), (157/34359738368), by norm_num⟩
  | 2 => ⟨((4893612723/17179869184), (-1886887921/8589934592)), (165/34359738368), by norm_num⟩
  | 3 => ⟨((-13567975447/68719476736), (2615782085/17179869184)), (231/68719476736), by norm_num⟩
  | 4 => ⟨((14106905891/137438953472), (-10878731863/137438953472)), (243/137438953472), by norm_num⟩
  | 5 => ⟨((-5866897227/137438953472), (9048674783/274877906944)), (51/68719476736), by norm_num⟩
  | 6 => ⟨((8133246543/549755813888), (-12544126827/1099511627776)), (285/1099511627776), by norm_num⟩
  | 7 => ⟨((-9664348989/2199023255552), (14905587673/4398046511104)), (171/2199023255552), by norm_num⟩
  | 8 => ⟨((10048224381/8796093022208), (-7748824553/8796093022208)), (45/2199023255552), by norm_num⟩
  | 9 => ⟨((-9286531199/35184372088832), (3580717261/17592186044416)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((15448639003/281474976710656), (-11913427555/281474976710656)), (141/140737488355328), by norm_num⟩
  | 11 => ⟨((-11681651529/1125899906842624), (9008464059/1125899906842624)), (215/1125899906842624), by norm_num⟩
  | 12 => ⟨((16194207643/9007199254740992), (-12488382927/9007199254740992)), (301/9007199254740992), by norm_num⟩
  | 13 => ⟨((-10361510187/36028797018963968), (7990419153/36028797018963968)), (97/18014398509481984), by norm_num⟩
  | 14 => ⟨((6156044205/144115188075855872), (-9494634013/288230376151711744)), (233/288230376151711744), by norm_num⟩
  | 15 => ⟨((-13654542989/2305843009213693952), (10529886075/2305843009213693952)), (261/2305843009213693952), by norm_num⟩
  | 16 => ⟨((7098455981/9223372036854775808), (-10948141267/18446744073709551616)), (137/9223372036854775808), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (-213924256867/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889600987371985/316912650057057350374175801344), (-1013142742961/633825300114114700748351602688)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236278642826971/4951760157141521099596496896), (-1139605766401/39614081257132168796771975168)), (12981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472508649829851/618970019642690137449562112), (-151326197779/309485009821345068724781056)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771700767376413/154742504910672534362390528), (-1210360418321/154742504910672534362390528)), (13795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775015769413917/4835703278458516698824704), (-283612056229/2417851639229258349412352)), (6467/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629603473182753/302231454903657293676544), (-992377607617/604462909807314587353088)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888471559710863/75557863725914323419136), (-1612117673509/75557863725914323419136)), (18393/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649024473533001/2361183241434822606848), (-604327237207/2361183241434822606848)), (13797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202768554607977/73786976294838206464), (-1661195319381/590295810358705651712)), (9487/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824349672947469/73786976294838206464), (-1037718909165/36893488147419103232)), (23721/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227955104688995/1152921504606846976), (-291676996669/1152921504606846976)), (26693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99680545172409/72057594037927936), (-291450353903/144115188075855872)), (6675/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195370068971229/144115188075855872), (-1019057255219/72057594037927936)), (23371/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492819965687729/36028797018963968), (-1526550186363/18014398509481984)), (17537/18014398509481984), by norm_num⟩
  | 3 => ⟨((372683361934229/2251799813685248), (-1904630366813/4503599627370496)), (43873/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230892312889795/4503599627370496), (-7597218034241/4503599627370496)), (87835/4503599627370496), by norm_num⟩
  | 1 => ⟨((555125467216917/562949953421312), (-2835677720881/562949953421312)), (32995/562949953421312), by norm_num⟩
  | 0 => ⟨((2189456658498363/2251799813685248), (-22473809517549/2251799813685248)), (264875/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189456658498363/2251799813685248), (-22473809517549/2251799813685248)), (1010417946822356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1064307616999957/1125899906842624), (-43703202736741/2251799813685248)), (130093/562949953421312), by norm_num⟩
  | 2 => ⟨((2011321262645831/2251799813685248), (-41312421537049/1125899906842624)), (502005/1125899906842624), by norm_num⟩
  | 3 => ⟨((1793492624137283/2251799813685248), (-36900505694983/562949953421312)), (233407/281474976710656), by norm_num⟩
  | 4 => ⟨((44337164990889/70368744177664), (-235121379400339/2251799813685248)), (1609611/1125899906842624), by norm_num⟩
  | 5 => ⟨((1698017557433/4398046511104), (-296285389576901/2251799813685248)), (4728935/2251799813685248), by norm_num⟩
  | 6 => ⟨((37083959665685/281474976710656), (-114391194418307/1125899906842624)), (19583907/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-8521317369/134217728)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile056Terms0
