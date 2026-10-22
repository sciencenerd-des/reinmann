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
namespace Reinmann.XiBand97.Tile021Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28251/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28251/1280))
  have he : value ((69/80), (28251/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1144586769/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((786053082097837/18014398509481984), (975138310823337/18014398509481984)), (305728895/18014398509481984), by norm_num⟩
  | 1 => ⟨((-144822803/1073741824), (-718639831/4294967296)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((895306865/4294967296), (1110673113/4294967296)), (353/4294967296), by norm_num⟩
  | 3 => ⟨((-115309647/536870912), (-71523703/268435456)), (183/2147483648), by norm_num⟩
  | 4 => ⟨((178213507/1073741824), (442165605/2147483648)), (285/4294967296), by norm_num⟩
  | 5 => ⟨((-881384825/8589934592), (-1093402125/8589934592)), (355/8589934592), by norm_num⟩
  | 6 => ⟨((908132637/17179869184), (1126584129/17179869184)), (23/1073741824), by norm_num⟩
  | 7 => ⟨((-802021867/34359738368), (-994948391/34359738368)), (327/34359738368), by norm_num⟩
  | 8 => ⟨((309885455/34359738368), (768856929/68719476736)), (127/34359738368), by norm_num⟩
  | 9 => ⟨((-851439197/274877906944), (-528126535/137438953472)), (351/274877906944), by norm_num⟩
  | 10 => ⟨((526366941/549755813888), (81623077/68719476736)), (219/549755813888), by norm_num⟩
  | 11 => ⟨((-73955571/274877906944), (-733964789/2199023255552)), (31/274877906944), by norm_num⟩
  | 12 => ⟨((152399873/2199023255552), (378119387/4398046511104)), (257/8796093022208), by norm_num⟩
  | 13 => ⟨((-144945993/8796093022208), (-719251125/35184372088832)), (123/17592186044416), by norm_num⟩
  | 14 => ⟨((256019553/70368744177664), (317605109/70368744177664)), (219/140737488355328), by norm_num⟩
  | 15 => ⟨((-105515641/140737488355328), (-65448725/70368744177664)), (363/1125899906842624), by norm_num⟩
  | 16 => ⟨((163076663/1125899906842624), (404609575/2251799813685248)), (141/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (1162386285511/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444464205920555/158456325028528675187087900672), (1374281077643/633825300114114700748351602688)), (184671/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888716116677701/39614081257132168796771975168), (1545710677269/39614081257132168796771975168)), (51943/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888427340778379/2475880078570760549798248448), (820935573483/1237940039285380274899124224)), (110389/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885046940843823/77371252455336267181195264), (820684569833/77371252455336267181195264)), (220801/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193565684943163/1208925819614629174706176), (1538250394907/9671406556917033397649408)), (103513/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157236192553259/75557863725914323419136), (1345436157487/604462909807314587353088)), (45293/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886331517182751/75557863725914323419136), (546333749297/18889465931478580854784)), (294449/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162055570534691/590295810358705651712), (819063916925/2361183241434822606848)), (55219/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809971732430069/295147905179352825856), (2251007410341/590295810358705651712)), (303769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227699379827181/9223372036854775808), (702908339749/18446744073709551616)), (379809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455136011496113/2305843009213693952), (3160167070265/9223372036854775808)), (213709/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591794644348573/1152921504606846976), (3156520482033/1152921504606846976)), (213793/576460752303423488), by norm_num⟩
  | 5 => ⟨((596332899935899/72057594037927936), (2757858483055/144115188075855872)), (187163/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488769654192181/36028797018963968), (4128607510631/36028797018963968)), (561867/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485681204203365/9007199254740992), (5146474704305/9007199254740992)), (175749/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110409850832653/2251799813685248), (5125108928319/2251799813685248)), (703993/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102736213054777/1125899906842624), (15268925479471/2251799813685248)), (2116989/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159714378527313/2251799813685248), (30114801803643/2251799813685248)), (4254157/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159714378527313/2251799813685248), (30114801803643/2251799813685248)), (16228321084029387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070991953719823/2251799813685248), (57766565275077/2251799813685248)), (4137081/1125899906842624), by norm_num⟩
  | 2 => ⟨((237902514150155/281474976710656), (106256418667097/2251799813685248)), (15644103/2251799813685248), by norm_num⟩
  | 3 => ⟨((1603586762393487/2251799813685248), (22451968413767/281474976710656)), (27921185/2251799813685248), by norm_num⟩
  | 4 => ⟨((1127644061612297/2251799813685248), (255821528142473/2251799813685248)), (22110815/1125899906842624), by norm_num⟩
  | 5 => ⟨((1071264388688611/4503599627370496), (512435653097119/4503599627370496)), (108675921/4503599627370496), by norm_num⟩
  | 6 => ⟨((786053082097837/18014398509481984), (975138310823337/18014398509481984)), (305728895/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1144586769/16777216)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1161046879/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((600325717019939/9007199254740992), (-53418273169887/9007199254740992)), (81718659/18014398509481984), by norm_num⟩
  | 1 => ⟨((-897559077/4294967296), (159733473/8589934592)), (125/8589934592), by norm_num⟩
  | 2 => ⟨((1407145647/4294967296), (-125210845/4294967296)), (25/1073741824), by norm_num⟩
  | 3 => ⟨((-367674753/1073741824), (16358245/536870912)), (53/2147483648), by norm_num⟩
  | 4 => ⟨((1152842061/4294967296), (-102582365/4294967296)), (85/4294967296), by norm_num⟩
  | 5 => ⟨((-1445891845/8589934592), (128658565/8589934592)), (109/8589934592), by norm_num⟩
  | 6 => ⟨((377798793/4294967296), (-134469395/17179869184)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((-1353812491/34359738368), (60232573/17179869184)), (53/17179869184), by norm_num⟩
  | 8 => ⟨((1061217809/68719476736), (-47214721/34359738368)), (85/68719476736), by norm_num⟩
  | 9 => ⟨((-1478863245/274877906944), (131592431/274877906944)), (15/34359738368), by norm_num⟩
  | 10 => ⟨((463696715/274877906944), (-82521461/549755813888)), (153/1099511627776), by norm_num⟩
  | 11 => ⟨((-132174397/274877906944), (5880581/137438953472)), (89/2199023255552), by norm_num⟩
  | 12 => ⟨((1105152153/8796093022208), (-49169407/4398046511104)), (95/8796093022208), by norm_num⟩
  | 13 => ⟨((-533107413/17592186044416), (94874087/35184372088832)), (93/35184372088832), by norm_num⟩
  | 14 => ⟨((1910348811/281474976710656), (-169986943/281474976710656)), (169/281474976710656), by norm_num⟩
  | 15 => ⟨((-399325843/281474976710656), (142131487/1125899906842624)), (143/1125899906842624), by norm_num⟩
  | 16 => ⟨((1252083871/4503599627370496), (-55706557/2251799813685248)), (57/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-57802357327/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222224847843995/79228162514264337593543950336), (-68334989559/316912650057057350374175801344)), (46107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944325445410729/19807040628566084398385987584), (-76858990435/19807040628566084398385987584)), (51871/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236044766389653/309485009821345068724781056), (-10205020563/154742504910672534362390528)), (110227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221253097041085/19342813113834066795298816), (-163229702029/154742504910672534362390528)), (27557/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48389400125353/302231454903657293676544), (-76487038349/4835703278458516698824704)), (25835/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257833059982543/604462909807314587353088), (-133798573159/604462909807314587353088)), (11303/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886239943734531/75557863725914323419136), (-217321964573/75557863725914323419136)), (36735/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296376065361133/4722366482869645213696), (-20362924911/590295810358705651712)), (861/36893488147419103232), by norm_num⟩
  | 9 => ⟨((101240598305511/36893488147419103232), (-223849152973/590295810358705651712)), (151539/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113842382129715/4611686018427387904), (-279597083507/73786976294838206464)), (189429/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56887909700845/288230376151711744), (-314252259365/9223372036854775808)), (213115/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591664462940129/1152921504606846976), (-156942303917/576460752303423488)), (53281/288230376151711744), by norm_num⟩
  | 5 => ⟨((596276368720637/72057594037927936), (-137118002345/72057594037927936)), (93247/72057594037927936), by norm_num⟩
  | 4 => ⟨((744300873936081/18014398509481984), (-205264701249/18014398509481984)), (279763/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485474262279185/9007199254740992), (-511721951111/9007199254740992)), (349741/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220414593522897/4503599627370496), (-254784372353/1125899906842624)), (699599/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204886538582663/2251799813685248), (-1517985541549/2251799813685248)), (1049703/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158628720310129/2251799813685248), (-1496679629021/1125899906842624)), (2100687/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158628720310129/2251799813685248), (-1496679629021/1125899906842624)), (8013484963423918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((517327180199267/562949953421312), (-2869505195509/1125899906842624)), (4033123/2251799813685248), by norm_num⟩
  | 2 => ⟨((950796251892101/1125899906842624), (-10547815288645/2251799813685248)), (7433097/2251799813685248), by norm_num⟩
  | 3 => ⟨((802900589134327/1125899906842624), (-8907384378615/1125899906842624)), (12623791/2251799813685248), by norm_num⟩
  | 4 => ⟨((1144986353792953/2251799813685248), (-25408099323115/2251799813685248)), (18204273/2251799813685248), by norm_num⟩
  | 5 => ⟨((1163822974757583/4503599627370496), (-51677643499173/4503599627370496)), (9461845/1125899906842624), by norm_num⟩
  | 6 => ⟨((600325717019939/9007199254740992), (-53418273169887/9007199254740992)), (81718659/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1161046879/16777216)), (1/16777216), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1176806343/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((300049898532643/9007199254740992), (-497495957545345/9007199254740992)), (38106203/2251799813685248), by norm_num⟩
  | 1 => ⟨((-56837483/536870912), (753912417/4294967296)), (29/536870912), by norm_num⟩
  | 2 => ⟨((361265161/2147483648), (-598993561/2147483648)), (185/2147483648), by norm_num⟩
  | 3 => ⟨((-765413419/4294967296), (1269089187/4294967296)), (197/2147483648), by norm_num⟩
  | 4 => ⟨((304065631/2147483648), (-504154219/2147483648)), (315/4294967296), by norm_num⟩
  | 5 => ⟨((-386534777/4294967296), (1281783397/8589934592)), (403/8589934592), by norm_num⟩
  | 6 => ⟨((409476109/8589934592), (-678929439/8589934592)), (215/8589934592), by norm_num⟩
  | 7 => ⟨((-743621209/34359738368), (1232956745/34359738368)), (393/34359738368), by norm_num⟩
  | 8 => ⟨((295408529/34359738368), (-489800363/34359738368)), (157/34359738368), by norm_num⟩
  | 9 => ⟨((-417255203/137438953472), (10809805/2147483648)), (223/137438953472), by norm_num⟩
  | 10 => ⟨((265211899/274877906944), (-109933255/68719476736)), (285/549755813888), by norm_num⟩
  | 11 => ⟨((-153246853/549755813888), (1016360151/2199023255552)), (331/2199023255552), by norm_num⟩
  | 12 => ⟨((649368997/8796093022208), (-1076682423/8796093022208)), (353/8796093022208), by norm_num⟩
  | 13 => ⟨((-158748433/8796093022208), (1052847599/35184372088832)), (347/35184372088832), by norm_num⟩
  | 14 => ⟨((576584075/140737488355328), (-956001813/140737488355328)), (317/140737488355328), by norm_num⟩
  | 15 => ⟨((-488644061/562949953421312), (810193393/562949953421312)), (135/281474976710656), by norm_num⟩
  | 16 => ⟨((776468565/4503599627370496), (-321854777/1125899906842624)), (431/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-1339196364979/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888870460622679/316912650057057350374175801344), (-1583126087985/633825300114114700748351602688)), (23089/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888585738814975/39614081257132168796771975168), (-445149046755/9903520314283042199192993792)), (103911/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888288828096429/2475880078570760549798248448), (-1891354671725/2475880078570760549798248448)), (220833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55311105766951/4835703278458516698824704), (-945380047499/77371252455336267181195264)), (55215/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((6048420527293/37778931862957161709568), (-885978051783/4835703278458516698824704)), (51771/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((9826374691105/4722366482869645213696), (-193728798631/75557863725914323419136)), (181227/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886146980740601/75557863725914323419136), (-1258645741143/37778931862957161709568)), (18409/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296306189089321/4722366482869645213696), (-117933386061/295147905179352825856)), (220955/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619753243118205/590295810358705651712), (-1296427333103/295147905179352825856)), (303887/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821357327711847/73786976294838206464), (-3238550566903/73786976294838206464)), (189985/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820276712435065/9223372036854775808), (-3639910666123/9223372036854775808)), (106905/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591527424966485/1152921504606846976), (-3635592068925/1152921504606846976)), (106953/288230376151711744), by norm_num⟩
  | 5 => ⟨((596216055773295/72057594037927936), (-794072809353/36028797018963968)), (187277/72057594037927936), by norm_num⟩
  | 4 => ⟨((186052422432511/4503599627370496), (-4754749684561/36028797018963968)), (70283/4503599627370496), by norm_num⟩
  | 3 => ⟨((742621906475669/4503599627370496), (-740815194869/1125899906842624)), (87949/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219946279981647/4503599627370496), (-5901222087149/2251799813685248)), (176185/562949953421312), by norm_num⟩
  | 1 => ⟨((1102082855327077/1125899906842624), (-8788842207937/1125899906842624)), (2119983/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078557352449053/1125899906842624), (-8663630790037/562949953421312)), (4263173/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078557352449053/1125899906842624), (-8663630790037/562949953421312)), (16262714394576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032938826497839/1125899906842624), (-66394695519267/2251799813685248)), (2074761/562949953421312), by norm_num⟩
  | 2 => ⟨((946674343705619/1125899906842624), (-15228187350081/281474976710656)), (1964631/281474976710656), by norm_num⟩
  | 3 => ⟨((792683207953855/1125899906842624), (-51216397400339/562949953421312)), (28130911/2251799813685248), by norm_num⟩
  | 4 => ⟨((1097529517439953/2251799813685248), (-288468827073559/2251799813685248)), (11182357/562949953421312), by norm_num⟩
  | 5 => ⟨((995964890523365/4503599627370496), (-140599999453933/1125899906842624)), (110125091/4503599627370496), by norm_num⟩
  | 6 => ⟨((300049898532643/9007199254740992), (-497495957545345/9007199254740992)), (38106203/2251799813685248), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1176806343/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1191922381/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-196676439340079/9007199254740992), (-1050523230367993/18014398509481984)), (198371987/18014398509481984), by norm_num⟩
  | 1 => ⟨((301874655/4294967296), (403106669/2147483648)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-485848515/4294967296), (-162193789/536870912)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((521295347/4294967296), (1392217777/4294967296)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-52437031/536870912), (-1120344037/4294967296)), (55/1073741824), by norm_num⟩
  | 5 => ⟨((540122533/8589934592), (1442499335/8589934592)), (143/4294967296), by norm_num⟩
  | 6 => ⟨((-579529121/17179869184), (-1547742079/17179869184)), (309/17179869184), by norm_num⟩
  | 7 => ⟨((532980651/34359738368), (1423425589/34359738368)), (143/17179869184), by norm_num⟩
  | 8 => ⟨((-428899633/68719476736), (-572728777/34359738368)), (29/8589934592), by norm_num⟩
  | 9 => ⟨((306794369/137438953472), (409676181/68719476736)), (167/137438953472), by norm_num⟩
  | 10 => ⟨((-395013191/549755813888), (-263739351/137438953472)), (217/549755813888), by norm_num⟩
  | 11 => ⟨((462363059/2199023255552), (617413979/1099511627776)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-62012053/1099511627776), (-165614911/1099511627776)), (277/8796093022208), by norm_num⟩
  | 13 => ⟨((491345473/35184372088832), (656115487/17592186044416)), (277/35184372088832), by norm_num⟩
  | 14 => ⟨((-451880019/140737488355328), (-1206831017/140737488355328)), (257/140737488355328), by norm_num⟩
  | 15 => ⟨((387878845/562949953421312), (1035903783/562949953421312)), (111/281474976710656), by norm_num⟩
  | 16 => ⟨((-312133459/2251799813685248), (-833611411/2251799813685248)), (45/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-2512831323807/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27776301812361/9903520314283042199192993792), (-185647597719/39614081257132168796771975168)), (92493/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944260381612923/19807040628566084398385987584), (-3340851651955/39614081257132168796771975168)), (104073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888219561531851/2475880078570760549798248448), (-3548649311001/2475880078570760549798248448)), (13825/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769885859559397/154742504910672534362390528), (-1773759253037/77371252455336267181195264)), (110625/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774165100495051/4835703278458516698824704), (-3324597548089/9671406556917033397649408)), (103737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314429603540983/151115727451828646838272), (-726955571403/151115727451828646838272)), (22699/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471513238686779/18889465931478580854784), (-4722961172023/75557863725914323419136)), (18449/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296235221075287/4722366482869645213696), (-221265819781/295147905179352825856)), (110737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619654934348847/590295810358705651712), (-1216163085203/147573952589676412928)), (38083/147573952589676412928), by norm_num⟩
  | 8 => ⟨((14228385562781/576460752303423488), (-1519006310565/18446744073709551616)), (23815/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455033936135969/2305843009213693952), (-3414473674041/4611686018427387904)), (214479/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591384592650189/1152921504606846976), (-6820729210421/1152921504606846976)), (214659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74519065135407/9007199254740992), (-2979451942281/72057594037927936)), (94015/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488224609086197/36028797018963968), (-1114989440753/4503599627370496)), (141225/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484993094639227/9007199254740992), (-11117686914199/9007199254740992)), (353773/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219423219598643/4503599627370496), (-11069501551567/2251799813685248)), (709687/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101663778264165/1125899906842624), (-32968457284239/2251799813685248)), (1069899/2251799813685248), by norm_num⟩
  | 0 => ⟨((134701693788773/140737488355328), (-64981988159243/2251799813685248)), (1080687/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((134701693788773/140737488355328), (-64981988159243/2251799813685248)), (4122493748191451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060920854624437/2251799813685248), (-124390224283559/2251799813685248)), (4262105/2251799813685248), by norm_num⟩
  | 2 => ⟨((1879350826574025/2251799813685248), (-227692005105771/2251799813685248)), (8272517/2251799813685248), by norm_num⟩
  | 3 => ⟨((386370477851215/562949953421312), (-380063232441177/2251799813685248)), (15481437/2251799813685248), by norm_num⟩
  | 4 => ⟨((31142675630341/70368744177664), (-521698995939257/2251799813685248)), (13238391/1125899906842624), by norm_num⟩
  | 5 => ⟨((640352831153917/4503599627370496), (-923540858776213/4503599627370496)), (35703673/2251799813685248), by norm_num⟩
  | 6 => ⟨((-196676439340079/9007199254740992), (-1050523230367993/18014398509481984)), (198371987/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1191922381/16777216)), (1/16777216), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-603222739/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-509924544559593/9007199254740992), (-184334278773865/9007199254740992)), (96496439/4503599627370496), by norm_num⟩
  | 1 => ⟨((99026167/536870912), (71594581/1073741824)), (301/4294967296), by norm_num⟩
  | 2 => ⟨((-80659203/268435456), (-466524113/4294967296)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((43799245/134217728), (506660199/4294967296)), (537/4294967296), by norm_num⟩
  | 4 => ⟨((-285404337/1073741824), (-25792935/268435456)), (439/4294967296), by norm_num⟩
  | 5 => ⟨((371949953/2147483648), (268914791/4294967296)), (287/4294967296), by norm_num⟩
  | 6 => ⟨((-201974809/2147483648), (-292050117/8589934592)), (313/8589934592), by norm_num⟩
  | 7 => ⟨((1504122117/34359738368), (271864993/17179869184)), (585/34359738368), by norm_num⟩
  | 8 => ⟨((-612571883/34359738368), (-110720299/17179869184)), (479/68719476736), by norm_num⟩
  | 9 => ⟨((443515185/68719476736), (320655487/137438953472)), (87/34359738368), by norm_num⟩
  | 10 => ⟨((-1156012231/549755813888), (-417890613/549755813888)), (455/549755813888), by norm_num⟩
  | 11 => ⟨((1369599799/2199023255552), (123775269/549755813888)), (541/2199023255552), by norm_num⟩
  | 12 => ⟨((-1487429455/8796093022208), (-537695701/8796093022208)), (295/4398046511104), by norm_num⟩
  | 13 => ⟨((1491135003/35184372088832), (539035231/35184372088832)), (297/17592186044416), by norm_num⟩
  | 14 => ⟨((-694037399/70368744177664), (-501779663/140737488355328)), (555/140737488355328), by norm_num⟩
  | 15 => ⟨((1205995119/562949953421312), (435959089/562949953421312)), (121/140737488355328), by norm_num⟩
  | 16 => ⟨((-982312131/2251799813685248), (-5548425/35184372088832)), (99/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-3640429332601/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777626028049115/633825300114114700748351602688), (-4303029362775/633825300114114700748351602688)), (5789/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944228023259775/19807040628566084398385987584), (-4839714384615/39614081257132168796771975168)), (208459/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944075218459613/1237940039285380274899124224), (-5140720496237/2475880078570760549798248448)), (110775/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221227040868073/19342813113834066795298816), (-642382548391/19342813113834066795298816)), (110811/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774132290524729/4835703278458516698824704), (-4816105759055/9671406556917033397649408)), (103923/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628830282019109/302231454903657293676544), (-4212329760565/604462909807314587353088)), (181941/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942979068974707/37778931862957161709568), (-6841731873461/75557863725914323419136)), (295795/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324040850088249/1180591620717411303424), (-5128409138479/4722366482869645213696)), (221971/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404888757972459/147573952589676412928), (-1761717246655/147573952589676412928)), (76353/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910553376773929/36893488147419103232), (-8801549875923/73786976294838206464)), (382067/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909995480300223/4611686018427387904), (-4946037568221/4611686018427387904)), (215121/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397809216319949/288230376151711744), (-9879999319683/1152921504606846976)), (107691/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192172479491639/144115188075855872), (-8631427551825/144115188075855872)), (188753/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488019187898933/36028797018963968), (-6460015611165/18014398509481984)), (283717/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484724864841419/9007199254740992), (-16102671938543/9007199254740992)), (355677/4503599627370496), by norm_num⟩
  | 2 => ⟨((554713156595685/1125899906842624), (-32063544958785/4503599627370496)), (178613/562949953421312), by norm_num⟩
  | 1 => ⟨((1101193560930331/1125899906842624), (-47741878220127/2251799813685248)), (2158899/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153012763858989/2251799813685248), (-47038173385451/1125899906842624)), (4380259/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153012763858989/2251799813685248), (-47038173385451/1125899906842624)), (16709362038619231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((256828647366867/281474976710656), (-179898385410639/2251799813685248)), (8742193/2251799813685248), by norm_num⟩
  | 2 => ⟨((232543852721617/281474976710656), (-328292479341725/2251799813685248)), (17350275/2251799813685248), by norm_num⟩
  | 3 => ⟨((744544254711355/1125899906842624), (-542445363050039/2251799813685248)), (33727301/2251799813685248), by norm_num⟩
  | 4 => ⟨((427022332383289/1125899906842624), (-717425369873797/2251799813685248)), (15214087/562949953421312), by norm_num⟩
  | 5 => ⟨((95342901608265/2251799813685248), (-544198738968853/2251799813685248)), (169879985/4503599627370496), by norm_num⟩
  | 6 => ⟨((-509924544559593/9007199254740992), (-184334278773865/9007199254740992)), (96496439/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-603222739/8388608)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1220420401/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-232028682841113/4503599627370496), (122599448873959/4503599627370496)), (190586835/9007199254740992), by norm_num⟩
  | 1 => ⟨((182325527/1073741824), (-385349067/4294967296)), (301/4294967296), by norm_num⟩
  | 2 => ⟨((-1201830387/4294967296), (635023831/4294967296)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((41260801/134217728), (-87205623/536870912)), (549/4294967296), by norm_num⟩
  | 4 => ⟨((-135988869/536870912), (287415507/2147483648)), (455/4294967296), by norm_num⟩
  | 5 => ⟨((179278851/1073741824), (-189454925/2147483648)), (151/2147483648), by norm_num⟩
  | 6 => ⟨((-787831795/8589934592), (416275017/8589934592)), (167/4294967296), by norm_num⟩
  | 7 => ⟨((741875735/17179869184), (-48999091/2147483648)), (79/4294967296), by norm_num⟩
  | 8 => ⟨((-1222550699/68719476736), (322986021/34359738368)), (523/68719476736), by norm_num⟩
  | 9 => ⟨((223851537/34359738368), (-29569701/8589934592)), (385/137438953472), by norm_num⟩
  | 10 => ⟨((-1180445037/549755813888), (155931057/137438953472)), (509/549755813888), by norm_num⟩
  | 11 => ⟨((11052711/17179869184), (-373762419/1099511627776)), (153/549755813888), by norm_num⟩
  | 12 => ⟨((-97141153/549755813888), (410619987/4398046511104)), (169/2199023255552), by norm_num⟩
  | 13 => ⟨((788089583/17592186044416), (-104102807/4398046511104)), (43/2199023255552), by norm_num⟩
  | 14 => ⟨((-371059243/35184372088832), (392120993/70368744177664)), (325/70368744177664), by norm_num⟩
  | 15 => ⟨((1304480781/562949953421312), (-344631153/281474976710656)), (287/281474976710656), by norm_num⟩
  | 16 => ⟨((-537419481/1125899906842624), (283962015/1125899906842624)), (475/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1729542103165/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888788437843095/316912650057057350374175801344), (1022114355263/158456325028528675187087900672)), (92603/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888400817005859/39614081257132168796771975168), (4598370990133/39614081257132168796771975168)), (208409/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118005740224125/154742504910672534362390528), (2442175425655/1237940039285380274899124224)), (110747/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769757832554073/154742504910672534362390528), (4882755712655/154742504910672534362390528)), (221561/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12095389434459/75557863725914323419136), (2287944585757/4835703278458516698824704)), (103893/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257612777248299/604462909807314587353088), (2001104653381/302231454903657293676544)), (181885/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471470170263831/18889465931478580854784), (6500415656945/75557863725914323419136)), (295697/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648052739782431/2361183241434822606848), (4872535339619/4722366482869645213696)), (221891/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619475669783143/590295810358705651712), (3347613395001/295147905179352825856)), (305291/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910503984399723/36893488147419103232), (8362273651709/73786976294838206464)), (190951/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819880401407683/9223372036854775808), (1174783721637/1152921504606846976)), (430035/9223372036854775808), by norm_num⟩
  | 6 => ⟨((388458745541/281474976710656), (4693334849127/576460752303423488)), (430531/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192077169555601/144115188075855872), (8200299691487/144115188075855872)), (377273/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487877824480559/36028797018963968), (12274411411665/36028797018963968)), (283513/18014398509481984), by norm_num⟩
  | 3 => ⟨((742275476143563/4503599627370496), (1912190632173/1125899906842624)), (355371/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218513132993787/4503599627370496), (7614723097875/1125899906842624)), (713687/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100949279724155/1125899906842624), (708578566143/35184372088832)), (2155831/2251799813685248), by norm_num⟩
  | 0 => ⟨((2152117443148587/2251799813685248), (44673656593011/1125899906842624)), (4371031/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152117443148587/2251799813685248), (44673656593011/1125899906842624)), (16674160012252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2053302659779477/2251799813685248), (85392098372815/1125899906842624)), (2175485/562949953421312), by norm_num⟩
  | 2 => ⟨((1859350260779735/2251799813685248), (311458987868199/2251799813685248)), (17189691/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492218211723977/2251799813685248), (257177101976559/1125899906842624)), (33142859/2251799813685248), by norm_num⟩
  | 4 => ⟨((435685919403563/1125899906842624), (681702437091431/2251799813685248)), (7383377/281474976710656), by norm_num⟩
  | 5 => ⟨((4087989235037/70368744177664), (1055184928105141/4503599627370496)), (162954921/4503599627370496), by norm_num⟩
  | 6 => ⟨((-232028682841113/4503599627370496), (122599448873959/4503599627370496)), (190586835/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1220420401/16777216)), (1/8388608), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile021Terms3
