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
namespace Reinmann.XiBand97.Tile030Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (31473/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (31473/1280))
  have he : value ((69/80), (31473/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-637562907/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((515024523235045/9007199254740992), (-356291009912181/9007199254740992)), (256610747/18014398509481984), by norm_num⟩
  | 1 => ⟨((-379553477/2147483648), (525145835/4294967296)), (191/4294967296), by norm_num⟩
  | 2 => ⟨((1173215911/4294967296), (-811624035/4294967296)), (297/4294967296), by norm_num⟩
  | 3 => ⟨((-1208820063/4294967296), (836254783/4294967296)), (77/1073741824), by norm_num⟩
  | 4 => ⟨((934128533/4294967296), (-646224759/4294967296)), (15/268435456), by norm_num⟩
  | 5 => ⟨((-1154972381/8589934592), (399501633/4294967296)), (299/8589934592), by norm_num⟩
  | 6 => ⟨((1190022887/17179869184), (-823251005/17179869184)), (155/8589934592), by norm_num⟩
  | 7 => ⟨((-1050974647/34359738368), (363529115/17179869184)), (69/8589934592), by norm_num⟩
  | 8 => ⟨((812151813/68719476736), (-140460491/17179869184)), (215/68719476736), by norm_num⟩
  | 9 => ⟨((-1115731437/274877906944), (385928303/137438953472)), (149/137438953472), by norm_num⟩
  | 10 => ⟨((86219331/68719476736), (-477168307/549755813888)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((-775294873/2199023255552), (536344543/2199023255552)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((399411561/4398046511104), (-552621251/8796093022208)), (219/8796093022208), by norm_num⟩
  | 13 => ⟨((-23742271/1099511627776), (262796269/17592186044416)), (105/17592186044416), by norm_num⟩
  | 14 => ⟨((670979361/140737488355328), (-464179671/140737488355328)), (187/140737488355328), by norm_num⟩
  | 15 => ⟨((-1106147035/1125899906842624), (382613085/562949953421312)), (155/562949953421312), by norm_num⟩
  | 16 => ⟨((854786861/4503599627370496), (-147834161/1125899906842624)), (121/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-788337316025/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222232171338735/79228162514264337593543950336), (-932045628649/633825300114114700748351602688)), (23073/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888716762000423/39614081257132168796771975168), (-1048310529519/39614081257132168796771975168)), (207669/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888428066521043/2475880078570760549798248448), (-556763595605/1237940039285380274899124224)), (110331/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770094652474735/154742504910672534362390528), (-278296693561/38685626227668133590597632)), (220677/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774263124989421/4835703278458516698824704), (-260812763157/2417851639229258349412352)), (103451/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39309070697877/18889465931478580854784), (-228120821451/151115727451828646838272)), (2829/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((235791597470973/9444732965739290427392), (-741054044125/37778931862957161709568)), (147123/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162055698678099/590295810358705651712), (-1110988817351/4722366482869645213696)), (27589/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619945001351601/590295810358705651712), (-763323933859/295147905179352825856)), (151761/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821597149297157/73786976294838206464), (-1906868333951/73786976294838206464)), (94867/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455136670335779/2305843009213693952), (-2143246652575/9223372036854775808)), (426993/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397949401254881/288230376151711744), (-535193532835/288230376151711744)), (427107/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192668755415871/144115188075855872), (-1870399565711/144115188075855872)), (46731/18014398509481984), by norm_num⟩
  | 4 => ⟨((744387407439785/18014398509481984), (-175003325267/2251799813685248)), (140257/9007199254740992), by norm_num⟩
  | 3 => ⟨((371422230564183/2251799813685248), (-436297748335/1125899906842624)), (350869/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220838916609115/4503599627370496), (-6951795163457/4503599627370496)), (1404841/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102755308177707/1125899906842624), (-10355566481521/2251799813685248)), (263837/281474976710656), by norm_num⟩
  | 0 => ⟨((2159827757522785/2251799813685248), (-10212197846061/1125899906842624)), (4235257/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159827757522785/2251799813685248), (-10212197846061/1125899906842624)), (16156223305709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035713467484659/1125899906842624), (-39180371610635/2251799813685248)), (8201377/2251799813685248), by norm_num⟩
  | 2 => ⟨((952410249643173/1125899906842624), (-72083918457701/2251799813685248)), (15374269/2251799813685248), by norm_num⟩
  | 3 => ⟨((804499809703711/1125899906842624), (-121953048146319/2251799813685248)), (26994817/2251799813685248), by norm_num⟩
  | 4 => ⟨((285772209152163/562949953421312), (-174280508294269/2251799813685248)), (41501693/2251799813685248), by norm_num⟩
  | 5 => ⟨((283390731505409/1125899906842624), (-176941220315339/2251799813685248)), (97118863/4503599627370496), by norm_num⟩
  | 6 => ⟨((515024523235045/9007199254740992), (-356291009912181/9007199254740992)), (256610747/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-637562907/8388608)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-80841449/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-153144630794053/18014398509481984), (-597813649006681/9007199254740992)), (202796161/9007199254740992), by norm_num⟩
  | 1 => ⟨((28621203/1073741824), (1787606467/8589934592)), (609/8589934592), by norm_num⟩
  | 2 => ⟨((-179483233/4294967296), (-700628717/2147483648)), (479/4294967296), by norm_num⟩
  | 3 => ⟨((93794773/2147483648), (366136215/1073741824)), (503/4294967296), by norm_num⟩
  | 4 => ⟨((-36761621/1073741824), (-17937781/67108864)), (99/1073741824), by norm_num⟩
  | 5 => ⟨((11526585/536870912), (1439841499/8589934592)), (249/4294967296), by norm_num⟩
  | 6 => ⟨((-192754883/17179869184), (-376217891/4294967296)), (261/8589934592), by norm_num⟩
  | 7 => ⟨((21585065/4294967296), (1348147453/34359738368)), (235/17179869184), by norm_num⟩
  | 8 => ⟨((-135359693/68719476736), (-1056777135/68719476736)), (185/34359738368), by norm_num⟩
  | 9 => ⟨((23578863/34359738368), (1472674931/274877906944)), (259/137438953472), by norm_num⟩
  | 10 => ⟨((-236580443/1099511627776), (-1847025491/1099511627776)), (163/274877906944), by norm_num⟩
  | 11 => ⟨((134872111/2199023255552), (1052970499/2199023255552)), (373/2199023255552), by norm_num⟩
  | 12 => ⟨((-140963575/8796093022208), (-275131909/2199023255552)), (49/1099511627776), by norm_num⟩
  | 13 => ⟨((135997069/35184372088832), (530876621/17592186044416)), (95/8796093022208), by norm_num⟩
  | 14 => ⟨((-121833721/140737488355328), (-951177471/140737488355328)), (683/281474976710656), by norm_num⟩
  | 15 => ⟨((203738095/1125899906842624), (397654861/281474976710656)), (573/1125899906842624), by norm_num⟩
  | 16 => ⟨((-159704905/4503599627370496), (-311711129/1125899906842624)), (451/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-553020495695/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888897562139845/316912650057057350374175801344), (-1307581612475/316912650057057350374175801344)), (184915/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888646575371497/39614081257132168796771975168), (-2941368572517/39614081257132168796771975168)), (208063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888353277904621/2475880078570760549798248448), (-781085463351/618970019642690137449562112)), (221105/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770019621924247/154742504910672534362390528), (-1561686111705/77371252455336267181195264)), (55287/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387113913001485/2417851639229258349412352), (-2927131598131/9671406556917033397649408)), (207373/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314457058131307/151115727451828646838272), (-1280105351951/302231454903657293676544)), (90749/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886231500776689/75557863725914323419136), (-4158413070945/75557863725914323419136)), (295019/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20255768909827/73786976294838206464), (-389640316345/590295810358705651712)), (221339/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619839298532919/590295810358705651712), (-2141651660393/295147905179352825856)), (19029/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455366000095667/18446744073709551616), (-5350021813595/73786976294838206464)), (95191/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910197744304543/4611686018427387904), (-6013131662655/9223372036854775808)), (428613/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397911166567835/288230376151711744), (-3003042563577/576460752303423488)), (428931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596266487784011/72057594037927936), (-5247406834749/144115188075855872)), (375671/144115188075855872), by norm_num⟩
  | 4 => ⟨((744283621373343/18014398509481984), (-7855299175345/36028797018963968)), (282111/18014398509481984), by norm_num⟩
  | 3 => ⟨((742711330276929/4503599627370496), (-4895754511093/4503599627370496)), (353265/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110143066770677/2251799813685248), (-19500390594763/4503599627370496)), (1416829/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102315622738547/1125899906842624), (-14522388264023/1125899906842624)), (266837/281474976710656), by norm_num⟩
  | 0 => ⟨((2157870932455755/2251799813685248), (-7158857286957/281474976710656)), (67303/35184372088832), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157870932455755/2251799813685248), (-7158857286957/281474976710656)), (256740570202577103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2066403497170709/2251799813685248), (-109763860572255/2251799813685248)), (8474541/2251799813685248), by norm_num⟩
  | 2 => ⟨((1890920890104835/2251799813685248), (-25181681778615/281474976710656)), (4094951/562949953421312), by norm_num⟩
  | 3 => ⟨((1569854610045817/2251799813685248), (-84584016454335/562949953421312)), (30440257/2251799813685248), by norm_num⟩
  | 4 => ⟨((521798649455307/1125899906842624), (-471745693769169/2251799813685248)), (6448821/281474976710656), by norm_num⟩
  | 5 => ⟨((192413046097023/1125899906842624), (-109315341621001/562949953421312)), (34717743/1125899906842624), by norm_num⟩
  | 6 => ⟨((-153144630794053/18014398509481984), (-597813649006681/9007199254740992)), (202796161/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-80841449/1048576)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-40969375/524288)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1071609029646393/18014398509481984), (-449202365436723/18014398509481984)), (208221635/9007199254740992), by norm_num⟩
  | 1 => ⟨((811965747/4294967296), (85090953/1073741824)), (317/4294967296), by norm_num⟩
  | 2 => ⟨((-645117713/2147483648), (-270423629/2147483648)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((683406273/2147483648), (572947233/4294967296)), (537/4294967296), by norm_num⟩
  | 4 => ⟨((-542975481/2147483648), (-455214287/4294967296)), (107/1073741824), by norm_num⟩
  | 5 => ⟨((690242123/4294967296), (578678203/8589934592)), (273/4294967296), by norm_num⟩
  | 6 => ⟨((-365604437/4294967296), (-613023493/17179869184)), (581/17179869184), by norm_num⟩
  | 7 => ⟨((1327897807/34359738368), (69579345/4294967296)), (529/34359738368), by norm_num⟩
  | 8 => ⟨((-527516339/34359738368), (-27640863/4294967296)), (211/34359738368), by norm_num⟩
  | 9 => ⟨((745100143/137438953472), (624669515/274877906944)), (299/137438953472), by norm_num⟩
  | 10 => ⟨((-947187345/549755813888), (-397046669/549755813888)), (191/274877906944), by norm_num⟩
  | 11 => ⟨((136827835/274877906944), (458849341/2199023255552)), (443/2199023255552), by norm_num⟩
  | 12 => ⟨((-1159589933/8796093022208), (-486082635/8796093022208)), (471/8796093022208), by norm_num⟩
  | 13 => ⟨((566959881/17592186044416), (237661043/17592186044416)), (231/17592186044416), by norm_num⟩
  | 14 => ⟨((-128702073/17592186044416), (-431599765/140737488355328)), (211/70368744177664), by norm_num⟩
  | 15 => ⟨((436290257/281474976710656), (182886305/281474976710656)), (359/562949953421312), by norm_num⟩
  | 16 => ⟨((-693276961/2251799813685248), (-290611261/2251799813685248)), (143/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-1787611553177/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777732683007987/633825300114114700748351602688), (-1056609231859/158456325028528675187087900672)), (185233/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944288011032559/19807040628566084398385987584), (-2376798215087/19807040628566084398385987584)), (208441/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888277900600961/2475880078570760549798248448), (-5049282019047/2475880078570760549798248448)), (110765/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769943778953429/154742504910672534362390528), (-5047691455877/154742504910672534362390528)), (6925/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548384054879429/9671406556917033397649408), (-4730521241847/9671406556917033397649408)), (12989/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257765091181953/604462909807314587353088), (-2068758561305/302231454903657293676544)), (181921/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471531992784573/18889465931478580854784), (-6720299651549/75557863725914323419136)), (18485/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324072688672655/1180591620717411303424), (-5037455909865/4722366482869645213696)), (110971/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619730110588085/590295810358705651712), (-6922004657023/590295810358705651712)), (38171/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821325551444657/73786976294838206464), (-4322881858123/36893488147419103232)), (382007/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820237038502275/9223372036854775808), (-2429304959255/2305843009213693952)), (430167/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591482855526527/1152921504606846976), (-4852824241587/576460752303423488)), (53835/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192387621673921/144115188075855872), (-4239718564371/72057594037927936)), (377421/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488341700932501/36028797018963968), (-6346588150903/18014398509481984)), (283643/18014398509481984), by norm_num⟩
  | 3 => ⟨((371281912991951/2251799813685248), (-15821076632627/9007199254740992)), (711131/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109828561621647/2251799813685248), (-15753126388835/2251799813685248)), (714173/2251799813685248), by norm_num⟩
  | 1 => ⟨((275448890241359/281474976710656), (-46920610486859/2251799813685248)), (2157775/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155409475818203/2251799813685248), (-46246020413109/1125899906842624)), (2188429/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155409475818203/2251799813685248), (-46246020413109/1125899906842624)), (8348194126609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2059346129548479/2251799813685248), (-88532834945185/1125899906842624)), (4369281/1125899906842624), by norm_num⟩
  | 2 => ⟨((1869417611747337/2251799813685248), (-323864936615197/2251799813685248)), (17357693/2251799813685248), by norm_num⟩
  | 3 => ⟨((1505388573771405/2251799813685248), (-33608605694895/140737488355328)), (16906621/1125899906842624), by norm_num⟩
  | 4 => ⟨((877978993326531/2251799813685248), (-718984139687727/2251799813685248)), (61359561/2251799813685248), by norm_num⟩
  | 5 => ⟨((225516422958243/4503599627370496), (-560665266374347/2251799813685248)), (87031679/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1071609029646393/18014398509481984), (-449202365436723/18014398509481984)), (208221635/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-40969375/524288)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-165982501/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-921487770363885/18014398509481984), (639676350804491/18014398509481984)), (411035525/18014398509481984), by norm_num⟩
  | 1 => ⟨((707186391/4294967296), (-490913091/4294967296)), (317/4294967296), by norm_num⟩
  | 2 => ⟨((-1138172589/4294967296), (197523535/1073741824)), (1/8388608), by norm_num⟩
  | 3 => ⟨((1221212077/4294967296), (-847738309/4294967296)), (551/4294967296), by norm_num⟩
  | 4 => ⟨((-245683127/1073741824), (682191087/4294967296)), (445/4294967296), by norm_num⟩
  | 5 => ⟨((1265317565/8589934592), (-878355359/8589934592)), (575/8589934592), by norm_num⟩
  | 6 => ⟨((-678816687/8589934592), (29451217/536870912)), (155/4294967296), by norm_num⟩
  | 7 => ⟨((624293321/17179869184), (-216685281/8589934592)), (143/8589934592), by norm_num⟩
  | 8 => ⟨((-1004761339/68719476736), (697483013/68719476736)), (463/68719476736), by norm_num⟩
  | 9 => ⟨((2807467/536870912), (-249456801/68719476736)), (333/137438953472), by norm_num⟩
  | 10 => ⟨((-57836081/34359738368), (642376373/549755813888)), (215/274877906944), by norm_num⟩
  | 11 => ⟨((1083154403/2199023255552), (-751901737/2199023255552)), (253/1099511627776), by norm_num⟩
  | 12 => ⟨((-1162179841/8796093022208), (806759441/8796093022208)), (545/8796093022208), by norm_num⟩
  | 13 => ⟨((1151050029/35184372088832), (-799033373/35184372088832)), (271/17592186044416), by norm_num⟩
  | 14 => ⟨((-529298159/70368744177664), (734854059/140737488355328)), (501/140737488355328), by norm_num⟩
  | 15 => ⟨((454332013/281474976710656), (-630774391/562949953421312)), (27/35184372088832), by norm_num⟩
  | 16 => ⟨((-731219167/2251799813685248), (253798055/1125899906842624)), (175/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (3301840349029/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888839938257671/316912650057057350374175801344), (487878930067/79228162514264337593543950336)), (185169/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236064588352977/4951760157141521099596496896), (2194921976219/19807040628566084398385987584)), (208365/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944107499854809/1237940039285380274899124224), (2331443458813/1237940039285380274899124224)), (221445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769881014685009/154742504910672534362390528), (2330699900965/77371252455336267181195264)), (221509/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774162679217011/4835703278458516698824704), (4368482741047/9671406556917033397649408)), (207733/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257713876729715/604462909807314587353088), (1910421686345/302231454903657293676544)), (45459/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943022509579497/37778931862957161709568), (3102955485375/37778931862957161709568)), (295611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296228778021473/4722366482869645213696), (4651844820109/4722366482869645213696)), (221821/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619645277833093/590295810358705651712), (6392082645321/590295810358705651712)), (305187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14228281932989/576460752303423488), (1995950287109/18446744073709551616)), (381759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820119183403717/9223372036854775808), (8973117022845/9223372036854775808)), (429855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591365988326231/1152921504606846976), (4481151115755/576460752303423488)), (53791/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192286471499281/144115188075855872), (3914930294495/72057594037927936)), (377071/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488192186031655/36028797018963968), (11720515085687/36028797018963968)), (566671/36028797018963968), by norm_num⟩
  | 3 => ⟨((742472305498793/4503599627370496), (3652058254507/2251799813685248)), (710209/9007199254740992), by norm_num⟩
  | 2 => ⟨((554825634374827/1125899906842624), (29089520576059/4503599627370496)), (1426037/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101543884103783/1125899906842624), (10829480284911/562949953421312)), (1076575/1125899906842624), by norm_num⟩
  | 0 => ⟨((269314447394467/281474976710656), (85376420684097/2251799813685248)), (2181469/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((269314447394467/281474976710656), (85376420684097/2251799813685248)), (8321643833640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257274659777093/281474976710656), (40843956762613/562949953421312)), (8679733/2251799813685248), by norm_num⟩
  | 2 => ⟨((1869386590056263/2251799813685248), (37332324183309/281474976710656)), (4281611/562949953421312), by norm_num⟩
  | 3 => ⟨((1512305510878247/2251799813685248), (495877445444471/2251799813685248)), (32978869/2251799813685248), by norm_num⟩
  | 4 => ⟨((453231567239461/1125899906842624), (666061155976917/2251799813685248)), (58821929/2251799813685248), by norm_num⟩
  | 5 => ⟨((167882574805509/2251799813685248), (67030812367529/281474976710656)), (164311079/4503599627370496), by norm_num⟩
  | 6 => ⟨((-921487770363885/18014398509481984), (639676350804491/18014398509481984)), (411035525/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-165982501/2097152)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1344039451/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((413577418967/18014398509481984), (135554906936685/2251799813685248)), (705818771/36028797018963968), by norm_num⟩
  | 1 => ⟨((-321263/4294967296), (-1684764759/8589934592)), (275/4294967296), by norm_num⟩
  | 2 => ⟨((523353/4294967296), (1372281557/4294967296)), (225/2147483648), by norm_num⟩
  | 3 => ⟨((-284189/2147483648), (-745170965/2147483648)), (245/2147483648), by norm_num⟩
  | 4 => ⟨((231479/2147483648), (1213919471/4294967296)), (401/4294967296), by norm_num⟩
  | 5 => ⟨((-603345/8589934592), (-1582026731/8589934592)), (525/8589934592), by norm_num⟩
  | 6 => ⟨((163813/4294967296), (1718131939/17179869184)), (143/4294967296), by norm_num⟩
  | 7 => ⟨((-152491/8589934592), (-799691389/17179869184)), (267/17179869184), by norm_num⟩
  | 8 => ⟨((248415/34359738368), (1302735873/68719476736)), (437/68719476736), by norm_num⟩
  | 9 => ⟨((-719431/274877906944), (-1886417439/274877906944)), (635/274877906944), by norm_num⟩
  | 10 => ⟨((468795/549755813888), (614613013/274877906944)), (415/549755813888), by norm_num⟩
  | 11 => ⟨((-555411/2199023255552), (-1456340749/2199023255552)), (247/1099511627776), by norm_num⟩
  | 12 => ⟨((301597/4398046511104), (790816459/4398046511104)), (269/4398046511104), by norm_num⟩
  | 13 => ⟨((-604697/35184372088832), (-1585573149/35184372088832)), (541/35184372088832), by norm_num⟩
  | 14 => ⟨((562903/140737488355328), (1475985825/140737488355328)), (505/140737488355328), by norm_num⟩
  | 15 => ⟨((-489065/562949953421312), (-641187241/281474976710656)), (55/70368744177664), by norm_num⟩
  | 16 => ⟨((398355/2251799813685248), (1044524965/2251799813685248)), (719/4503599627370496), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (127852550825/633825300114114700748351602688)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888816413175131/316912650057057350374175801344), (2417970981077/633825300114114700748351602688)), (184877/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888464063533523/39614081257132168796771975168), (1359778520573/19807040628566084398385987584)), (208017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944079726401231/1237940039285380274899124224), (361087640713/309485009821345068724781056)), (110527/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769825902196179/154742504910672534362390528), (2887769799109/154742504910672534362390528)), (110547/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96767134478969/604462909807314587353088), (2706295033377/9671406556917033397649408)), (103659/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257669531563713/604462909807314587353088), (2367019429837/604462909807314587353088)), (181445/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471493455318419/18889465931478580854784), (3844553626351/75557863725914323419136)), (294929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296176133829243/4722366482869645213696), (2881794801623/4722366482869645213696)), (221267/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619574115971561/590295810358705651712), (494979547397/73786976294838206464)), (304355/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821132967964555/73786976294838206464), (2472925624351/36893488147419103232)), (190307/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820023689362571/9223372036854775808), (5558664190963/9223372036854775808)), (428425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397818407803219/288230376151711744), (693987296721/144115188075855872)), (214359/576460752303423488), by norm_num⟩
  | 5 => ⟨((298052294525993/36028797018963968), (4850309508543/144115188075855872)), (375459/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488083259231423/36028797018963968), (7260286034795/36028797018963968)), (281925/18014398509481984), by norm_num⟩
  | 3 => ⟨((371205167485729/2251799813685248), (9048851605559/9007199254740992)), (705973/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219091085107485/4503599627370496), (9009204410801/2251799813685248)), (353859/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202860887653929/2251799813685248), (26830157355779/2251799813685248)), (266489/281474976710656), by norm_num⟩
  | 0 => ⟨((2154418375841645/2251799813685248), (3304697294507/140737488355328)), (1074761/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154418375841645/2251799813685248), (3304697294507/140737488355328)), (4099887850047874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1030003361705405/1125899906842624), (101177030527993/2251799813685248)), (4214075/1125899906842624), by norm_num⟩
  | 2 => ⟨((1880003223760375/2251799813685248), (185118909661247/2251799813685248)), (2022247/281474976710656), by norm_num⟩
  | 3 => ⟨((1554375788364141/2251799813685248), (309107536848563/2251799813685248)), (29673595/2251799813685248), by norm_num⟩
  | 4 => ⟨((515262637471827/1125899906842624), (26671402379901/140737488355328)), (6139117/281474976710656), by norm_num⟩
  | 5 => ⟨((97685552296121/562949953421312), (195296609253719/1125899906842624)), (127135099/4503599627370496), by norm_num⟩
  | 6 => ⟨((413577418967/18014398509481984), (135554906936685/2251799813685248)), (705818771/36028797018963968), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1344039451/16777216)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-169951025/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((840430995743043/18014398509481984), (314468875167831/9007199254740992)), (221063851/18014398509481984), by norm_num⟩
  | 1 => ⟨((-660401215/4294967296), (-123553051/1073741824)), (175/4294967296), by norm_num⟩
  | 2 => ⟨((1088287335/4294967296), (814421401/4294967296)), (291/4294967296), by norm_num⟩
  | 3 => ⟨((-74725365/268435456), (-894733359/4294967296)), (161/2147483648), by norm_num⟩
  | 4 => ⟨((985130451/4294967296), (737223797/4294967296)), (267/4294967296), by norm_num⟩
  | 5 => ⟨((-162341463/1073741824), (-242976937/2147483648)), (89/2147483648), by norm_num⟩
  | 6 => ⟨((713401305/8589934592), (266937449/4294967296)), (197/8589934592), by norm_num⟩
  | 7 => ⟨((-671786949/17179869184), (-251366367/8589934592)), (187/17179869184), by norm_num⟩
  | 8 => ⟨((69190631/4294967296), (828462539/68719476736)), (155/34359738368), by norm_num⟩
  | 9 => ⟨((-50675785/8589934592), (-606772751/137438953472)), (229/137438953472), by norm_num⟩
  | 10 => ⟨((1068922371/549755813888), (799929601/549755813888)), (19/34359738368), by norm_num⟩
  | 11 => ⟨((-640544319/1099511627776), (-479352267/1099511627776)), (23/137438953472), by norm_num⟩
  | 12 => ⟨((175927465/1099511627776), (526622291/4398046511104)), (51/1099511627776), by norm_num⟩
  | 13 => ⟨((-356817369/8796093022208), (-133512397/4398046511104)), (13/1099511627776), by norm_num⟩
  | 14 => ⟨((672006765/70368744177664), (251448617/35184372088832)), (99/35184372088832), by norm_num⟩
  | 15 => ⟨((-73827489/35184372088832), (-441991265/281474976710656)), (175/281474976710656), by norm_num⟩
  | 16 => ⟨((7603855/17592186044416), (728365553/2251799813685248)), (145/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (418428300295/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777585320960473/633825300114114700748351602688), (494560463833/316912650057057350374175801344)), (184595/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118025673464747/2475880078570760549798248448), (1112489668751/39614081257132168796771975168)), (207683/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051521377205/1237940039285380274899124224), (295419435209/618970019642690137449562112)), (220677/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769769726490797/154742504910672534362390528), (590646302303/77371252455336267181195264)), (110347/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774110867861897/4835703278458516698824704), (1107052784235/9671406556917033397649408)), (103459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157202989521207/75557863725914323419136), (121032793779/75557863725914323419136)), (181071/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471475040451325/18889465931478580854784), (1572660169241/75557863725914323419136)), (2299/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1296121296091735/4722366482869645213696), (1178825163079/4722366482869645213696)), (220733/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619499374318635/590295810358705651712), (1619796689853/590295810358705651712)), (303555/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910520264824443/36893488147419103232), (2023115365417/73786976294838206464)), (189757/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819921053186793/9223372036854775808), (2273765072421/9223372036854775808)), (213525/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397793171825257/288230376151711744), (567742189005/288230376151711744)), (427171/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192122750628515/144115188075855872), (1983956372461/144115188075855872)), (373911/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487957401568953/36028797018963968), (185603961253/2251799813685248)), (140285/9007199254740992), by norm_num⟩
  | 3 => ⟨((371167484783941/2251799813685248), (3701130262459/9007199254740992)), (701907/9007199254740992), by norm_num⟩
  | 2 => ⟨((277351159742617/562949953421312), (3684757896881/2251799813685248)), (702633/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202486897068583/2251799813685248), (5486384159035/1125899906842624)), (2111553/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076931397065125/1125899906842624), (21621645159567/2251799813685248)), (4237875/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076931397065125/1125899906842624), (21621645159567/2251799813685248)), (16166210183150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029988858735989/1125899906842624), (10340629920575/562949953421312)), (8188501/2251799813685248), by norm_num⟩
  | 2 => ⟨((941868214187423/1125899906842624), (75678013974597/2251799813685248)), (7641367/1125899906842624), by norm_num⟩
  | 3 => ⟨((1573290728712387/2251799813685248), (3956763576535/70368744177664)), (13298345/1125899906842624), by norm_num⟩
  | 4 => ⟨((1092109511970805/2251799813685248), (88464552315335/1125899906842624)), (20078119/1125899906842624), by norm_num⟩
  | 5 => ⟨((257882443859647/1125899906842624), (343238252241265/4503599627370496)), (90522821/4503599627370496), by norm_num⟩
  | 6 => ⟨((840430995743043/18014398509481984), (314468875167831/9007199254740992)), (221063851/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-169951025/2097152)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile030Terms3
