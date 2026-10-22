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
namespace Reinmann.XiBand97.Tile018Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27177/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27177/1280))
  have he : value ((69/80), (27177/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-987635957/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-560740875926197/9007199254740992), (-302029302255707/4503599627370496)), (225876027/9007199254740992), by norm_num⟩
  | 1 => ⟨((185335139/1073741824), (798609769/4294967296)), (301/4294967296), by norm_num⟩
  | 2 => ⟨((-1027716233/4294967296), (-276777055/1073741824)), (105/1073741824), by norm_num⟩
  | 3 => ⟨((949811479/4294967296), (1023185255/4294967296)), (195/2147483648), by norm_num⟩
  | 4 => ⟨((-658359149/4294967296), (-709217975/4294967296)), (17/268435456), by norm_num⟩
  | 5 => ⟨((730143661/8589934592), (12289811/134217728)), (19/536870912), by norm_num⟩
  | 6 => ⟨((-674796027/17179869184), (-90865577/2147483648)), (283/17179869184), by norm_num⟩
  | 7 => ⟨((267275979/17179869184), (575846569/34359738368)), (113/17179869184), by norm_num⟩
  | 8 => ⟨((-741046365/137438953472), (-199573213/34359738368)), (315/137438953472), by norm_num⟩
  | 9 => ⟨((228290755/137438953472), (983705671/549755813888)), (391/549755813888), by norm_num⟩
  | 10 => ⟨((-253182549/549755813888), (-272741125/549755813888)), (109/549755813888), by norm_num⟩
  | 11 => ⟨((255262211/2199023255552), (1099925771/8796093022208)), (221/4398046511104), by norm_num⟩
  | 12 => ⟨((-943649503/35184372088832), (-1016547263/35184372088832)), (411/35184372088832), by norm_num⟩
  | 13 => ⟨((805031375/140737488355328), (433610381/70368744177664)), (353/140737488355328), by norm_num⟩
  | 14 => ⟨((-159430065/140737488355328), (-171746179/140737488355328)), (141/281474976710656), by norm_num⟩
  | 15 => ⟨((943005867/4503599627370496), (1015853907/4503599627370496)), (419/4503599627370496), by norm_num⟩
  | 16 => ⟨((-326820929/9007199254740992), (-44008517/1125899906842624)), (73/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-3020785882473/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444568524112793/158456325028528675187087900672), (-893268572619/158456325028528675187087900672)), (34707/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29518517506443/618970019642690137449562112), (-4018860698069/39614081257132168796771975168)), (19527/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888925099192875/2475880078570760549798248448), (-1067249143891/618970019642690137449562112)), (83009/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770591012815381/154742504910672534362390528), (-4267823568273/154742504910672534362390528)), (83031/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548990873913127/9671406556917033397649408), (-999959647459/2417851639229258349412352)), (155731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258296094914807/604462909807314587353088), (-3498613114547/604462909807314587353088)), (136311/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29484233145013/1180591620717411303424), (-5682911466385/75557863725914323419136)), (110797/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296938027294797/4722366482869645213696), (-4260141362509/4722366482869645213696)), (166273/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620620207081427/590295810358705651712), (-2927188573779/295147905179352825856)), (114375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822438315599603/73786976294838206464), (-914124757799/9223372036854775808)), (286125/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455372273295045/2305843009213693952), (-8220288441809/9223372036854775808)), (161075/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592735150423389/1152921504606846976), (-8211751480541/1152921504606846976)), (161237/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193483645104625/144115188075855872), (-7175686729201/144115188075855872)), (141265/72057594037927936), by norm_num⟩
  | 4 => ⟨((186248281847175/4503599627370496), (-5372179560629/18014398509481984)), (424525/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487184224877855/9007199254740992), (-13396946176591/9007199254740992)), (16623/281474976710656), by norm_num⟩
  | 2 => ⟨((1111886401424909/2251799813685248), (-6673392511325/1125899906842624)), (133465/562949953421312), by norm_num⟩
  | 1 => ⟨((2209770599742441/2251799813685248), (-39790199645713/2251799813685248)), (1611225/2251799813685248), by norm_num⟩
  | 0 => ⟨((270973753101995/281474976710656), (-78583678153725/2251799813685248)), (3261187/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((270973753101995/281474976710656), (-78583678153725/2251799813685248)), (12440441140181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521043008430079/562949953421312), (-37825945401469/562949953421312)), (3253329/1125899906842624), by norm_num⟩
  | 2 => ⟨((1918856288002875/2251799813685248), (-280080945297717/2251799813685248)), (3229745/562949953421312), by norm_num⟩
  | 3 => ⟨((1600303941846319/2251799813685248), (-238669121370411/1125899906842624)), (25231397/2251799813685248), by norm_num⟩
  | 4 => ⟨((1036113820654259/2251799813685248), (-42404206338061/140737488355328)), (46559925/2251799813685248), by norm_num⟩
  | 5 => ⟨((272321707526041/2251799813685248), (-312181102236337/1125899906842624)), (70903967/2251799813685248), by norm_num⟩
  | 6 => ⟨((-560740875926197/9007199254740992), (-302029302255707/4503599627370496)), (225876027/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-987635957/16777216)), (3/33554432), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1009231319/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-87412291985935/1125899906842624), (700988374444277/18014398509481984)), (140781059/9007199254740992), by norm_num⟩
  | 1 => ⟨((944739045/4294967296), (-59188891/536870912)), (3/67108864), by norm_num⟩
  | 2 => ⟨((-1338323635/4294967296), (670779023/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((631959397/2147483648), (-633486693/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-447618949/2147483648), (224350369/2147483648)), (187/4294967296), by norm_num⟩
  | 5 => ⟨((63409999/536870912), (-508505967/8589934592)), (107/4294967296), by norm_num⟩
  | 6 => ⟨((-479077481/8589934592), (480235297/17179869184)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((775616407/34359738368), (-388745443/34359738368)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((-1098743377/137438953472), (137674847/34359738368)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((1383544177/549755813888), (-693443935/549755813888)), (19/34359738368), by norm_num⟩
  | 10 => ⟨((-783975165/1099511627776), (196467461/549755813888)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((807697781/4398046511104), (-6325389/68719476736)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((-762793377/17592186044416), (11947451/549755813888)), (173/17592186044416), by norm_num⟩
  | 13 => ⟨((83121399/8796093022208), (-666578267/140737488355328)), (19/8796093022208), by norm_num⟩
  | 14 => ⟨((-1076574431/562949953421312), (269794063/281474976710656)), (31/70368744177664), by norm_num⟩
  | 15 => ⟨((813377345/2251799813685248), (-407671541/2251799813685248)), (189/2251799813685248), by norm_num⟩
  | 16 => ⟨((-576117887/9007199254740992), (577510225/18014398509481984)), (135/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (871765945459/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889095630109353/316912650057057350374175801344), (2062122683671/316912650057057350374175801344)), (46303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944545911881811/19807040628566084398385987584), (4638771601415/39614081257132168796771975168)), (6513/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236103228562245/309485009821345068724781056), (2463732059501/1237940039285380274899124224)), (3461/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442622895354737/38685626227668133590597632), (1231519954029/38685626227668133590597632)), (55393/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774448743191255/4835703278458516698824704), (4616729338793/9671406556917033397649408)), (51949/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258214210396509/604462909807314587353088), (1009542014175/151115727451828646838272)), (90947/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471714384934961/18889465931478580854784), (819908427753/9444732965739290427392)), (9241/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296837712195565/4722366482869645213696), (1229260037585/1180591620717411303424)), (13869/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202560227650343/73786976294838206464), (6757014771671/590295810358705651712)), (152655/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822264655489835/73786976294838206464), (4220198961141/36893488147419103232)), (190963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821292795525197/9223372036854775808), (9487379909673/9223372036854775808)), (215033/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398134423265405/288230376151711744), (9477301584637/1152921504606846976)), (215283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193309569132711/144115188075855872), (8281309527345/144115188075855872)), (188653/144115188075855872), by norm_num⟩
  | 4 => ⟨((372430637242035/9007199254740992), (12399327472941/36028797018963968)), (141771/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486850078680895/9007199254740992), (15459594210431/9007199254740992)), (355413/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111545527830321/2251799813685248), (3850086294555/562949953421312)), (178447/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104357322788103/1125899906842624), (22952740786465/1125899906842624)), (269527/562949953421312), by norm_num⟩
  | 0 => ⟨((1082773298565719/1125899906842624), (45316449419741/1125899906842624)), (273255/281474976710656), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082773298565719/1125899906842624), (45316449419741/1125899906842624)), (1042385102392101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1039474671226227/1125899906842624), (43580642576923/562949953421312)), (2190293/1125899906842624), by norm_num⟩
  | 2 => ⟨((1905871909164607/2251799813685248), (80470695199741/562949953421312)), (8766901/2251799813685248), by norm_num⟩
  | 3 => ⟨((783537503671965/1125899906842624), (136217115358169/562949953421312)), (8673287/1125899906842624), by norm_num⟩
  | 4 => ⟨((479359316325027/1125899906842624), (758370920018591/2251799813685248)), (32538403/2251799813685248), by norm_num⟩
  | 5 => ⟨((152773333655063/2251799813685248), (1291525697911643/4503599627370496)), (24811865/1125899906842624), by norm_num⟩
  | 6 => ⟨((-87412291985935/1125899906842624), (700988374444277/18014398509481984)), (140781059/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1009231319/16777216)), (1/16777216), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-2059183935/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((39910157329859/4503599627370496), (370149657385215/4503599627370496)), (58269355/4503599627370496), by norm_num⟩
  | 1 => ⟨((-27502821/1073741824), (-255076913/1073741824)), (163/4294967296), by norm_num⟩
  | 2 => ⟨((79493377/2147483648), (1474534211/4294967296)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((-153176941/4294967296), (-177581335/536870912)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((3458893/134217728), (1026552151/4294967296)), (21/536870912), by norm_num⟩
  | 5 => ⟨((-127967829/8589934592), (-593423469/4294967296)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((123291533/17179869184), (571738145/8589934592)), (191/17179869184), by norm_num⟩
  | 7 => ⟨((-203633351/68719476736), (-1888612329/68719476736)), (159/34359738368), by norm_num⟩
  | 8 => ⟨((73572011/68719476736), (1364697935/137438953472)), (29/17179869184), by norm_num⟩
  | 9 => ⟨((-94511317/274877906944), (-1753104165/549755813888)), (301/549755813888), by norm_num⟩
  | 10 => ⟨((109269137/1099511627776), (506712277/549755813888)), (11/68719476736), by norm_num⟩
  | 11 => ⟨((-114846701/4398046511104), (-266288519/1099511627776)), (187/4398046511104), by norm_num⟩
  | 12 => ⟨((110649887/17592186044416), (256557605/4398046511104)), (91/8796093022208), by norm_num⟩
  | 13 => ⟨((-98405941/70368744177664), (-1825346107/140737488355328)), (163/70368744177664), by norm_num⟩
  | 14 => ⟨((162531287/562949953421312), (1507408239/562949953421312)), (271/562949953421312), by norm_num⟩
  | 15 => ⟨((-62636779/1125899906842624), (-1161858721/2251799813685248)), (211/2251799813685248), by norm_num⟩
  | 16 => ⟨((181043577/18014398509481984), (1679101817/18014398509481984)), (307/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (1906228323231/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444530425807719/158456325028528675187087900672), (2254364642451/633825300114114700748351602688)), (46211/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889013944505385/39614081257132168796771975168), (2535610130377/39614081257132168796771975168)), (51995/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944371786754033/1237940039285380274899124224), (84168768151/77371252455336267181195264)), (110505/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885204939550779/77371252455336267181195264), (2692630052397/154742504910672534362390528)), (27631/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387205369311789/2417851639229258349412352), (2523522264207/9671406556917033397649408)), (25909/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629074144354793/302231454903657293676544), (2207263882383/604462909807314587353088)), (45351/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943375757651201/37778931862957161709568), (1792635267251/37778931862957161709568)), (73713/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296759153863041/4722366482869645213696), (671902986599/1180591620717411303424)), (110603/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810187680788315/295147905179352825856), (3693288613281/590295810358705651712)), (152131/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455533478684023/18446744073709551616), (4613346212421/73786976294838206464)), (190243/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455287228924063/2305843009213693952), (648191155427/1152921504606846976)), (214133/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796198904749877/576460752303423488), (2589963978613/576460752303423488)), (214269/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193191655649709/144115188075855872), (2263071378275/72057594037927936)), (187639/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489554620136515/36028797018963968), (6776643806105/36028797018963968)), (140883/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486655752478891/9007199254740992), (4224423658785/4503599627370496)), (352747/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111374453977789/2251799813685248), (4207996148639/1125899906842624)), (176779/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104158407027379/1125899906842624), (3135533574365/281474976710656)), (1064743/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082603642517783/1125899906842624), (12379273862543/562949953421312)), (1072919/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082603642517783/1125899906842624), (12379273862543/562949953421312)), (4092861179832076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040427887051113/1125899906842624), (23806462535195/562949953421312)), (4221015/2251799813685248), by norm_num⟩
  | 2 => ⟨((1918861864993255/2251799813685248), (175993673065409/2251799813685248)), (4079081/1125899906842624), by norm_num⟩
  | 3 => ⟨((1621395055536085/2251799813685248), (299944556059465/2251799813685248)), (7589561/1125899906842624), by norm_num⟩
  | 4 => ⟨((1127522603908539/2251799813685248), (431946585281813/2251799813685248)), (25903057/2251799813685248), by norm_num⟩
  | 5 => ⟨((240858304365171/1125899906842624), (432569125928907/2251799813685248)), (35877985/2251799813685248), by norm_num⟩
  | 6 => ⟨((39910157329859/4503599627370496), (370149657385215/4503599627370496)), (58269355/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-2059183935/33554432)), (1/16777216), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1048851489/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((675602174518211/9007199254740992), (220467971757503/9007199254740992)), (117230749/18014398509481984), by norm_num⟩
  | 1 => ⟨((-948557557/4294967296), (-154770491/2147483648)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((698242461/2147483648), (455712267/4294967296)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((-685310773/2147483648), (-447272321/4294967296)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((252231969/1073741824), (164620757/2147483648)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((-594145313/4294967296), (-387772619/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((1166283079/17179869184), (190295469/8589934592)), (57/8589934592), by norm_num⟩
  | 7 => ⟨((-30661155/1073741824), (-80044771/8589934592)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((1444478399/137438953472), (7365217/2147483648)), (147/137438953472), by norm_num⟩
  | 9 => ⟨((-472575389/137438953472), (-308429255/274877906944)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((1113175517/1099511627776), (11351889/34359738368)), (117/1099511627776), by norm_num⟩
  | 11 => ⟨((-1191882685/4398046511104), (-48618101/549755813888)), (127/4398046511104), by norm_num⟩
  | 12 => ⟨((292452153/4398046511104), (190870709/8796093022208)), (63/8796093022208), by norm_num⟩
  | 13 => ⟨((-1059824639/70368744177664), (-345850557/70368744177664)), (29/17592186044416), by norm_num⟩
  | 14 => ⟨((891596851/281474976710656), (290953103/281474976710656)), (99/281474976710656), by norm_num⟩
  | 15 => ⟨((-700067339/1125899906842624), (-114225821/562949953421312)), (157/2251799813685248), by norm_num⟩
  | 16 => ⟨((257663195/2251799813685248), (21020685/562949953421312)), (59/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (102721560503/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778052465090069/633825300114114700748351602688), (485889369589/633825300114114700748351602688)), (11531/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472234053137707/9903520314283042199192993792), (273252852909/19807040628566084398385987584)), (103783/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236082649479699/309485009821345068724781056), (580511969597/2475880078570760549798248448)), (1723/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((110645483767945/9671406556917033397649408), (145085729013/38685626227668133590597632)), (110277/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744725709477/9671406556917033397649408), (543891933743/9671406556917033397649408)), (103389/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081384508157/604462909807314587353088), (475725970009/604462909807314587353088)), (45235/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886643270649733/75557863725914323419136), (386359178493/37778931862957161709568)), (147021/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324169596318759/1180591620717411303424), (579244632149/4722366482869645213696)), (110273/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132489080501/295147905179352825856), (198995927317/147573952589676412928)), (151637/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821996944118763/73786976294838206464), (994263689473/73786976294838206464)), (189563/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820996208316001/9223372036854775808), (1117563104653/9223372036854775808)), (106641/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398061707332713/288230376151711744), (1116334992735/1152921504606846976)), (3333/18014398509481984), by norm_num⟩
  | 5 => ⟨((1193061486318361/144115188075855872), (60963331649/9007199254740992)), (93341/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489363230805135/36028797018963968), (730182431359/18014398509481984)), (280091/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486423252117951/9007199254740992), (910322414195/4503599627370496)), (175117/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222304009020067/4503599627370496), (1813448248083/2251799813685248)), (350415/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207699346634471/2251799813685248), (5404503507973/2251799813685248)), (1052163/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082084822393495/1125899906842624), (1333311111207/281474976710656)), (2108051/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1082084822393495/1125899906842624), (1333311111207/281474976710656)), (8041576394087981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519974782945655/562949953421312), (20502791883327/2251799813685248)), (2036001/1125899906842624), by norm_num⟩
  | 2 => ⟨((240116817202545/281474976710656), (37875248748211/2251799813685248)), (3798225/1125899906842624), by norm_num⟩
  | 3 => ⟨((409511864791213/562949953421312), (32310098348543/1125899906842624)), (413003/70368744177664), by norm_num⟩
  | 4 => ⟨((594862760973149/1125899906842624), (94014528615811/2251799813685248)), (9993171/1125899906842624), by norm_num⟩
  | 5 => ⟨((312329736735681/1125899906842624), (198688148827807/4503599627370496)), (2848529/281474976710656), by norm_num⟩
  | 6 => ⟨((675602174518211/9007199254740992), (220467971757503/9007199254740992)), (117230749/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1048851489/16777216)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-533561449/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((972788279708057/18014398509481984), (-950154261918867/18014398509481984)), (154823371/18014398509481984), by norm_num⟩
  | 1 => ⟨((-694802581/4294967296), (169659125/1073741824)), (7/268435456), by norm_num⟩
  | 2 => ⟨((520360629/2147483648), (-1016506633/4294967296)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((-519620377/2147483648), (31720643/134217728)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((778321767/4294967296), (-47513277/268435456)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((-932657455/8589934592), (910957167/8589934592)), (159/8589934592), by norm_num⟩
  | 6 => ⟨((931330679/17179869184), (-454830631/8589934592)), (161/17179869184), by norm_num⟩
  | 7 => ⟨((-797147821/34359738368), (778600457/34359738368)), (35/8589934592), by norm_num⟩
  | 8 => ⟨((149252591/17179869184), (-583119629/68719476736)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((-794881429/274877906944), (776386797/274877906944)), (9/17179869184), by norm_num⟩
  | 10 => ⟨((238125195/274877906944), (-465169397/549755813888)), (175/1099511627776), by norm_num⟩
  | 11 => ⟨((-518806787/2199023255552), (1013471255/4398046511104)), (193/4398046511104), by norm_num⟩
  | 12 => ⟨((518068745/8796093022208), (-253007379/4398046511104)), (195/17592186044416), by norm_num⟩
  | 13 => ⟨((-477537003/35184372088832), (932852149/70368744177664)), (91/35184372088832), by norm_num⟩
  | 14 => ⟨((204367573/70368744177664), (-798450083/281474976710656)), (79/140737488355328), by norm_num⟩
  | 15 => ⟨((-653045903/1125899906842624), (318925691/562949953421312)), (1/8796093022208), by norm_num⟩
  | 16 => ⟨((61135959/562949953421312), (-477707993/4503599627370496)), (97/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-503868550129/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777983685212355/633825300114114700748351602688), (-595801119725/316912650057057350374175801344)), (46159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888858817275381/39614081257132168796771975168), (-335063336141/9903520314283042199192993792)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472144734523029/618970019642690137449562112), (-711822004677/1237940039285380274899124224)), (55183/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770245454166575/154742504910672534362390528), (-1423222145273/154742504910672534362390528)), (110375/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548667552357099/9671406556917033397649408), (-666911351163/4835703278458516698824704)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629006913874463/302231454903657293676544), (-583323499463/302231454903657293676544)), (45281/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886533434605341/75557863725914323419136), (-947481017855/37778931862957161709568)), (147183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648297979525761/2361183241434822606848), (-710243758337/2361183241434822606848)), (27601/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405037890580595/147573952589676412928), (-975989168861/295147905179352825856)), (75917/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821855054915647/73786976294838206464), (-2438186269887/73786976294838206464)), (94917/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820836419214253/9223372036854775808), (-342563136177/1152921504606846976)), (106811/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592086836192825/1152921504606846976), (-2737440279969/1152921504606846976)), (106847/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192921263672411/144115188075855872), (-2391816826555/144115188075855872)), (23383/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489152441757145/36028797018963968), (-3580849618073/36028797018963968)), (35095/4503599627370496), by norm_num⟩
  | 3 => ⟨((743079487201479/4503599627370496), (-2232027438003/4503599627370496)), (175619/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221773099235905/4503599627370496), (-8892188866437/4503599627370496)), (703339/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103448582630081/1125899906842624), (-13248832074247/2251799813685248)), (33037/70368744177664), by norm_num⟩
  | 0 => ⟨((2162542427775481/2251799813685248), (-13070978794187/1125899906842624)), (2123133/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162542427775481/2251799813685248), (-13070978794187/1125899906842624)), (8099109658248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076519556296627/2251799813685248), (-6276434086901/281474976710656)), (4127249/2251799813685248), by norm_num⟩
  | 2 => ⟨((1913763492430273/2251799813685248), (-723484501489/17592186044416)), (7796031/2251799813685248), by norm_num⟩
  | 3 => ⟨((811332075017873/1125899906842624), (-78704160062487/1125899906842624)), (6946319/1125899906842624), by norm_num⟩
  | 4 => ⟨((579150408645349/1125899906842624), (-28357409529905/281474976710656)), (21964567/2251799813685248), by norm_num⟩
  | 5 => ⟨((1145923935404365/4503599627370496), (-466775569446099/4503599627370496)), (54044667/4503599627370496), by norm_num⟩
  | 6 => ⟨((972788279708057/18014398509481984), (-950154261918867/18014398509481984)), (154823371/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-533561449/8388608)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-8472677/131072)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-154162372822919/9007199254740992), (-79175149735131/1125899906842624)), (449629181/18014398509481984), by norm_num⟩
  | 1 => ⟨((223803903/4294967296), (919534759/4294967296)), (41/536870912), by norm_num⟩
  | 2 => ⟨((-170344001/2147483648), (-1399772103/4294967296)), (501/4294967296), by norm_num⟩
  | 3 => ⟨((345744089/4294967296), (1420545859/4294967296)), (511/4294967296), by norm_num⟩
  | 4 => ⟨((-263156409/4294967296), (-135152617/536870912)), (391/4294967296), by norm_num⟩
  | 5 => ⟨((320474237/8589934592), (82295035/536870912)), (239/4294967296), by norm_num⟩
  | 6 => ⟨((-325230335/17179869184), (-1336261763/17179869184)), (487/17179869184), by norm_num⟩
  | 7 => ⟨((282906015/34359738368), (581182703/17179869184)), (425/34359738368), by norm_num⟩
  | 8 => ⟨((-53832107/17179869184), (-442355945/34359738368)), (325/68719476736), by norm_num⟩
  | 9 => ⟨((72841359/68719476736), (1197122311/274877906944)), (221/137438953472), by norm_num⟩
  | 10 => ⟨((-354827443/1099511627776), (-1457866295/1099511627776)), (135/274877906944), by norm_num⟩
  | 11 => ⟨((98207283/1099511627776), (1614002417/4398046511104)), (75/549755813888), by norm_num⟩
  | 12 => ⟨((-99664759/4398046511104), (-1637955525/17592186044416)), (611/17592186044416), by norm_num⟩
  | 13 => ⟨((373454271/70368744177664), (767198823/35184372088832)), (287/35184372088832), by norm_num⟩
  | 14 => ⟨((-324854259/281474976710656), (-1334716589/281474976710656)), (501/281474976710656), by norm_num⟩
  | 15 => ⟨((2060471/8796093022208), (541809947/562949953421312)), (409/1125899906842624), by norm_num⟩
  | 16 => ⟨((-100370403/2251799813685248), (-1649552541/9007199254740992)), (625/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-2357131138879/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777915466197575/633825300114114700748351602688), (-2787004180283/633825300114114700748351602688)), (184949/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888781900779781/39614081257132168796771975168), (-1567331638783/19807040628566084398385987584)), (208103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472124246351219/618970019642690137449562112), (-416210913435/309485009821345068724781056)), (221151/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770163244263889/154742504910672534362390528), (-1664341856767/77371252455336267181195264)), (55299/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548590207512745/9671406556917033397649408), (-3119575023991/9671406556917033397649408)), (51855/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628972939104713/302231454903657293676544), (-1364281297365/302231454903657293676544)), (90771/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886422505654227/75557863725914323419136), (-2215958585337/37778931862957161709568)), (295097/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648256157904423/2361183241434822606848), (-3322191325491/4722366482869645213696)), (55351/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405008957071609/147573952589676412928), (-1141294135315/147573952589676412928)), (19035/36893488147419103232), by norm_num⟩
  | 8 => ⟨((910854651155231/36893488147419103232), (-1425554676803/18446744073709551616)), (11903/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820670958506079/9223372036854775808), (-801144272493/1152921504606846976)), (214389/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591919518589837/1152921504606846976), (-3200929365811/576460752303423488)), (107279/288230376151711744), by norm_num⟩
  | 5 => ⟨((298193194447031/36028797018963968), (-5593428468599/144115188075855872)), (375857/144115188075855872), by norm_num⟩
  | 4 => ⟨((744462780999369/18014398509481984), (-8373770482093/36028797018963968)), (282273/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485868144309151/9007199254740992), (-5219307402795/4503599627370496)), (707017/9007199254740992), by norm_num⟩
  | 2 => ⟨((555292470593837/1125899906842624), (-20791646773347/4503599627370496)), (354511/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205938917174253/2251799813685248), (-30974253883189/2251799813685248)), (267141/281474976710656), by norm_num⟩
  | 0 => ⟨((2160415038487679/2251799813685248), (-30550038311405/1125899906842624)), (67417/35184372088832), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160415038487679/2251799813685248), (-30550038311405/1125899906842624)), (257175445690858353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((258885131063669/281474976710656), (-117240905329535/2251799813685248)), (1064165/281474976710656), by norm_num⟩
  | 2 => ⟨((1898761716573153/2251799813685248), (-107831706736263/1125899906842624)), (16546663/2251799813685248), by norm_num⟩
  | 3 => ⟨((98776135837675/140737488355328), (-363703230347951/2251799813685248)), (31074415/2251799813685248), by norm_num⟩
  | 4 => ⟨((1050467074684173/2251799813685248), (-127631948336139/562949953421312)), (53657023/2251799813685248), by norm_num⟩
  | 5 => ⟨((374297236413251/2251799813685248), (-952647094755615/4503599627370496)), (148784699/4503599627370496), by norm_num⟩
  | 6 => ⟨((-154162372822919/9007199254740992), (-79175149735131/1125899906842624)), (449629181/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-8472677/131072)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile018Terms2
