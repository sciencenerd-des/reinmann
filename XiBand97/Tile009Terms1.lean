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
namespace Reinmann.XiBand97.Tile009Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (12067/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (12067/640))
  have he : value ((69/80), (12067/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-1390092431/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1126976171370123/9007199254740992), (750138924260033/9007199254740992)), (244300935/9007199254740992), by norm_num⟩
  | 1 => ⟨((1180753585/4294967296), (-98241787/536870912)), (129/2147483648), by norm_num⟩
  | 2 => ⟨((-648595199/2147483648), (215859269/1073741824)), (9/134217728), by norm_num⟩
  | 3 => ⟨((950072875/4294967296), (-158097097/1073741824)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-130470217/1073741824), (347374827/4294967296)), (237/8589934592), by norm_num⟩
  | 5 => ⟨((114668947/2147483648), (-305304203/8589934592)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((-335937905/17179869184), (447214599/34359738368)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((421789155/68719476736), (-35093961/8589934592)), (99/68719476736), by norm_num⟩
  | 8 => ⟨((-463382749/274877906944), (616874509/549755813888)), (55/137438953472), by norm_num⟩
  | 9 => ⟨((905027525/2199023255552), (-602405259/2199023255552)), (217/2199023255552), by norm_num⟩
  | 10 => ⟨((-795419489/8796093022208), (33090491/549755813888)), (193/8796093022208), by norm_num⟩
  | 11 => ⟨((1271065637/70368744177664), (-846047885/70368744177664)), (311/70368744177664), by norm_num⟩
  | 12 => ⟨((-465469443/140737488355328), (309826201/140737488355328)), (115/140737488355328), by norm_num⟩
  | 13 => ⟨((1258758031/2251799813685248), (-837855685/2251799813685248)), (157/1125899906842624), by norm_num⟩
  | 14 => ⟨((-790221167/9007199254740992), (16437117/281474976710656)), (199/9007199254740992), by norm_num⟩
  | 15 => ⟨((926023131/72057594037927936), (-616380373/72057594037927936)), (59/18014398509481984), by norm_num⟩
  | 16 => ⟨((-127167549/72057594037927936), (169290763/144115188075855872)), (131/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (415909957673/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779037559307853/633825300114114700748351602688), (3938829073863/633825300114114700748351602688)), (23147/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236255470315795/4951760157141521099596496896), (2215213236467/19807040628566084398385987584)), (52093/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944918549115787/1237940039285380274899124224), (1176603959807/618970019642690137449562112)), (55363/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771502665129639/154742504910672534362390528), (4705389555305/154742504910672534362390528)), (13845/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774922589813205/4835703278458516698824704), (4410212408465/9671406556917033397649408)), (103871/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259043244153633/604462909807314587353088), (3857845700417/604462909807314587353088)), (45461/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888204348456977/75557863725914323419136), (6266955522173/75557863725914323419136)), (36953/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297847493783363/4722366482869645213696), (1174607167967/1180591620717411303424)), (27729/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810934871230113/295147905179352825856), (403589658925/36893488147419103232)), (152601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823998763756425/73786976294838206464), (4033718427659/36893488147419103232)), (190889/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823242575450217/9223372036854775808), (2267469535567/2305843009213693952)), (53735/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199310763316037/144115188075855872), (9062395182593/1152921504606846976)), (107589/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195012891439107/144115188075855872), (495073801029/9007199254740992)), (188549/144115188075855872), by norm_num⟩
  | 4 => ⟨((186534305996545/4503599627370496), (5932474854601/18014398509481984)), (141679/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490034542334451/9007199254740992), (14801768480677/9007199254740992)), (5549/140737488355328), by norm_num⟩
  | 2 => ⟨((557360925952547/1125899906842624), (7378839305541/1125899906842624)), (178273/1125899906842624), by norm_num⟩
  | 1 => ⟨((554550687642411/562949953421312), (11013213593463/562949953421312)), (269175/562949953421312), by norm_num⟩
  | 0 => ⟨((1092179167650607/1125899906842624), (21806649728489/562949953421312)), (1090873/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092179167650607/1125899906842624), (21806649728489/562949953421312)), (4161350254539107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132222367983431/140737488355328), (42307079705689/562949953421312)), (2200917/1125899906842624), by norm_num⟩
  | 2 => ⟨((987420579182831/1125899906842624), (158989401516861/1125899906842624)), (4466317/1125899906842624), by norm_num⟩
  | 3 => ⟨((843522381187849/1125899906842624), (557738413425961/2251799813685248)), (9095357/1125899906842624), by norm_num⟩
  | 4 => ⟨((562893707744731/1125899906842624), (835713426591055/2251799813685248)), (1133377/70368744177664), by norm_num⟩
  | 5 => ⟨((505356088966629/4503599627370496), (1671259856926685/4503599627370496)), (31592435/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1126976171370123/9007199254740992), (750138924260033/9007199254740992)), (244300935/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1390092431/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-1456749639/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((521121156491995/4503599627370496), (332388569639243/4503599627370496)), (61064731/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1144338423/4294967296), (-364948733/2147483648)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((658734149/2147483648), (105040689/536870912)), (81/2147483648), by norm_num⟩
  | 3 => ⟨((-63199643/268435456), (-322486833/2147483648)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((1164180447/8589934592), (371276687/4294967296)), (37/2147483648), by norm_num⟩
  | 5 => ⟨((-1072249817/17179869184), (-170979233/4294967296)), (139/17179869184), by norm_num⟩
  | 6 => ⟨((205745537/8589934592), (131231411/8589934592)), (109/34359738368), by norm_num⟩
  | 7 => ⟨((-541424693/68719476736), (-690677693/137438953472)), (73/68719476736), by norm_num⟩
  | 8 => ⟨((1246676427/549755813888), (49698255/34359738368)), (171/549755813888), by norm_num⟩
  | 9 => ⟨((-318953173/549755813888), (-101719521/274877906944)), (177/2199023255552), by norm_num⟩
  | 10 => ⟨((1175066915/8796093022208), (749497129/8796093022208)), (83/4398046511104), by norm_num⟩
  | 11 => ⟨((-983887841/35184372088832), (-627556697/35184372088832)), (141/35184372088832), by norm_num⟩
  | 12 => ⟨((755161825/140737488355328), (481667565/140737488355328)), (55/70368744177664), by norm_num⟩
  | 13 => ⟨((-1070045761/1125899906842624), (-682511111/1125899906842624)), (79/562949953421312), by norm_num⟩
  | 14 => ⟨((351981631/2251799813685248), (449011403/4503599627370496)), (53/2251799813685248), by norm_num⟩
  | 15 => ⟨((-432249417/18014398509481984), (-137851595/9007199254740992)), (33/9007199254740992), by norm_num⟩
  | 16 => ⟨((124411383/36028797018963968), (634830055/288230376151711744)), (77/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (739590031115/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444726332471011/158456325028528675187087900672), (218848597739/158456325028528675187087900672)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472473870149423/9903520314283042199192993792), (246161877487/9903520314283042199192993792)), (25957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889680162031835/2475880078570760549798248448), (522988028847/1237940039285380274899124224)), (27581/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771346418490747/154742504910672534362390528), (130717215989/19342813113834066795298816)), (110331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699430646313/9671406556917033397649408), (245031492335/2417851639229258349412352)), (103443/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629458222786851/302231454903657293676544), (857357156777/604462909807314587353088)), (11315/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471999917964347/18889465931478580854784), (1392731059087/75557863725914323419136)), (73555/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297695185050005/4722366482869645213696), (1044133442465/4722366482869645213696)), (110345/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50676945750339/18446744073709551616), (1435009684105/590295810358705651712)), (151745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911871165769359/36893488147419103232), (1792751992085/73786976294838206464)), (189711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822958093222079/9223372036854775808), (2015458037095/9223372036854775808)), (213467/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398551655356047/288230376151711744), (2013724520683/1152921504606846976)), (13345/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194773952889255/144115188075855872), (1760060708767/144115188075855872)), (186891/144115188075855872), by norm_num⟩
  | 4 => ⟨((372981808722341/9007199254740992), (82381233191/1125899906842624)), (280455/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489620055907309/9007199254740992), (1644225009953/4503599627370496)), (350779/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228673077662413/4503599627370496), (409784126341/281474976710656)), (702189/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108595914607353/1125899906842624), (9784087332093/2251799813685248)), (527435/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091455742756501/1125899906842624), (19366165374267/2251799813685248)), (1058063/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091455742756501/1125899906842624), (19366165374267/2251799813685248)), (4036190037253951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115964072945465/2251799813685248), (37547409471223/2251799813685248)), (517397/281474976710656), by norm_num⟩
  | 2 => ⟨((496924074115719/562949953421312), (70564860153581/2251799813685248)), (7917013/2251799813685248), by norm_num⟩
  | 3 => ⟨((1752357000610045/2251799813685248), (124577247351437/2251799813685248)), (14473117/2251799813685248), by norm_num⟩
  | 4 => ⟨((678398574433941/1125899906842624), (48473183581037/562949953421312)), (24127447/2251799813685248), by norm_num⟩
  | 5 => ⟨((800827897663367/2251799813685248), (233655858321315/2251799813685248)), (33230475/2251799813685248), by norm_num⟩
  | 6 => ⟨((521121156491995/4503599627370496), (332388569639243/4503599627370496)), (61064731/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1456749639/33554432)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-758524209/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((381362829799155/9007199254740992), (-268220552147475/2251799813685248)), (162048661/9007199254740992), by norm_num⟩
  | 1 => ⟨((-436052383/4294967296), (1226739491/4294967296)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((261401987/2147483648), (-1470796413/4294967296)), (57/1073741824), by norm_num⟩
  | 3 => ⟨((-417876393/4294967296), (1175605255/4294967296)), (185/4294967296), by norm_num⟩
  | 4 => ⟨((250505957/4294967296), (-704744571/4294967296)), (7/268435456), by norm_num⟩
  | 5 => ⟨((-60068705/2147483648), (337980735/4294967296)), (217/17179869184), by norm_num⟩
  | 6 => ⟨((192051285/17179869184), (-270147469/8589934592)), (175/34359738368), by norm_num⟩
  | 7 => ⟨((-263153639/68719476736), (1480652203/137438953472)), (121/68719476736), by norm_num⟩
  | 8 => ⟨((315507433/274877906944), (-443806115/137438953472)), (147/274877906944), by norm_num⟩
  | 9 => ⟨((-336246125/1099511627776), (236489019/274877906944)), (159/1099511627776), by norm_num⟩
  | 10 => ⟨((322513197/4398046511104), (-907321441/4398046511104)), (155/4398046511104), by norm_num⟩
  | 11 => ⟨((-562438451/35184372088832), (1582299487/35184372088832)), (273/35184372088832), by norm_num⟩
  | 12 => ⟨((56194521/17592186044416), (-1264729487/140737488355328)), (221/140737488355328), by norm_num⟩
  | 13 => ⟨((-331688803/562949953421312), (933135033/562949953421312)), (165/562949953421312), by norm_num⟩
  | 14 => ⟨((454488579/4503599627370496), (-1278605763/4503599627370496)), (229/4503599627370496), by norm_num⟩
  | 15 => ⟨((-72654401/4503599627370496), (817590057/18014398509481984)), (37/4503599627370496), by norm_num⟩
  | 16 => ⟨((348435289/144115188075855872), (-490123833/72057594037927936)), (45/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-400314991431/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778777082711347/633825300114114700748351602688), (-1895028042657/633825300114114700748351602688)), (92387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236218892814629/4951760157141521099596496896), (-1065759787873/19807040628566084398385987584)), (103947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472381680755879/618970019642690137449562112), (-1132130808441/1237940039285380274899124224)), (55229/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885596444901277/77371252455336267181195264), (-1131862055045/77371252455336267181195264)), (110473/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549555402289683/9671406556917033397649408), (-2121670411797/9671406556917033397649408)), (103585/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157348790704105/75557863725914323419136), (-1855890848399/604462909807314587353088)), (45327/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887794548762459/75557863725914323419136), (-3014752831339/75557863725914323419136)), (147343/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648770593493515/2361183241434822606848), (-2260128932021/4722366482869645213696)), (110535/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621450263922427/590295810358705651712), (-1553078748633/295147905179352825856)), (76015/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823476952874901/73786976294838206464), (-3880418444821/73786976294838206464)), (190103/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822659022647019/9223372036854775808), (-2181169971609/4611686018427387904)), (213957/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796953451386673/576460752303423488), (-1089607369187/288230376151711744)), (26759/144115188075855872), by norm_num⟩
  | 5 => ⟨((597255485951337/72057594037927936), (-3809230697855/144115188075855872)), (93721/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491531313862373/36028797018963968), (-2852533150181/18014398509481984)), (281421/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489122628664119/9007199254740992), (-7115991789329/9007199254740992)), (88057/2251799813685248), by norm_num⟩
  | 2 => ⟨((69614709005483/140737488355328), (-7093027038431/2251799813685248)), (705815/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215669557041935/2251799813685248), (-10582292475967/1125899906842624)), (531065/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179793082658631/2251799813685248), (-41873146347035/2251799813685248)), (2137939/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179793082658631/2251799813685248), (-41873146347035/2251799813685248)), (8155590065962981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1054655146064713/1125899906842624), (-40534151482605/1125899906842624)), (4218659/2251799813685248), by norm_num⟩
  | 2 => ⟨((986459322835357/1125899906842624), (-37969229051967/562949953421312)), (4103589/1125899906842624), by norm_num⟩
  | 3 => ⟨((429583189549371/562949953421312), (-133067246036887/1125899906842624)), (15488567/2251799813685248), by norm_num⟩
  | 4 => ⟨((639897002057845/1125899906842624), (-406170755532833/2251799813685248)), (27299545/2251799813685248), by norm_num⟩
  | 5 => ⟨((1308196227185795/4503599627370496), (-461688374267463/2251799813685248)), (10219841/562949953421312), by norm_num⟩
  | 6 => ⟨((381362829799155/9007199254740992), (-268220552147475/2251799813685248)), (162048661/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-758524209/16777216)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-786048445/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-508778232807749/4503599627370496), (-283536684644527/9007199254740992)), (11461919/562949953421312), by norm_num⟩
  | 1 => ⟨((150712301/536870912), (167980717/2147483648)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((-1498023995/4294967296), (-417416401/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((1240816595/4294967296), (172873465/2147483648)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((-12044193/67108864), (-429574423/8589934592)), (9/268435456), by norm_num⟩
  | 5 => ⟨((766174599/8589934592), (53372617/2147483648)), (9/536870912), by norm_num⟩
  | 6 => ⟨((-1269248237/34359738368), (-44208657/4294967296)), (241/34359738368), by norm_num⟩
  | 7 => ⟨((901132395/68719476736), (251095739/68719476736)), (173/68719476736), by norm_num⟩
  | 8 => ⟨((-279903735/68719476736), (-19498421/17179869184)), (217/274877906944), by norm_num⟩
  | 9 => ⟨((19320407/17179869184), (86136455/274877906944)), (121/549755813888), by norm_num⟩
  | 10 => ⟨((-153630105/549755813888), (-21404105/274877906944)), (243/4398046511104), by norm_num⟩
  | 11 => ⟨((1110564275/17592186044416), (19340801/1099511627776)), (111/8796093022208), by norm_num⟩
  | 12 => ⟨((-459941425/35184372088832), (-256320453/70368744177664)), (93/35184372088832), by norm_num⟩
  | 13 => ⟨((703330157/281474976710656), (391958399/562949953421312)), (287/562949953421312), by norm_num⟩
  | 14 => ⟨((-998691305/2251799813685248), (-278280009/2251799813685248)), (205/2251799813685248), by norm_num⟩
  | 15 => ⟨((661774577/9007199254740992), (368799917/18014398509481984)), (137/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1644448047/144115188075855872), (-458216683/144115188075855872)), (343/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1869144284845/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778652843116707/633825300114114700748351602688), (-2211784600321/316912650057057350374175801344)), (23159/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236201364541877/4951760157141521099596496896), (-4975557087167/39614081257132168796771975168)), (26061/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889377134099257/2475880078570760549798248448), (-2642685287145/1237940039285380274899124224)), (110791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442760656999057/38685626227668133590597632), (-2642033470707/77371252455336267181195264)), (27707/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549413817396423/9671406556917033397649408), (-4952427834137/9671406556917033397649408)), (25985/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258665724949441/604462909807314587353088), (-4331989640725/604462909807314587353088)), (45493/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943795367625069/37778931862957161709568), (-7036887272273/75557863725914323419136)), (36981/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297387157789715/4722366482869645213696), (-1318848623143/1180591620717411303424)), (111007/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621236576228973/590295810358705651712), (-1812494487723/147573952589676412928)), (76369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823207000750557/73786976294838206464), (-9056939689239/73786976294838206464)), (191077/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455587856062795/2305843009213693952), (-2545363001069/2305843009213693952)), (215175/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398398608959367/288230376151711744), (-1271493644225/144115188075855872)), (107721/576460752303423488), by norm_num⟩
  | 5 => ⟨((149279012371649/18014398509481984), (-555610608601/9007199254740992)), (188813/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491102107575617/36028797018963968), (-13313295427517/36028797018963968)), (141911/18014398509481984), by norm_num⟩
  | 3 => ⟨((744283561375833/4503599627370496), (-2075533577399/1125899906842624)), (355833/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113251483843743/2251799813685248), (-16548298607941/2251799813685248)), (357419/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106888600750567/1125899906842624), (-24682719691259/1125899906842624)), (540103/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087725617125657/1125899906842624), (-24403857070489/562949953421312)), (1096165/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087725617125657/1125899906842624), (-24403857070489/562949953421312)), (4181537632468795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131091229559535/140737488355328), (-47152860269229/562949953421312)), (553259/281474976710656), by norm_num⟩
  | 2 => ⟨((242237496947803/281474976710656), (-175683863686293/1125899906842624)), (4493435/1125899906842624), by norm_num⟩
  | 3 => ⟨((1612930693683349/2251799813685248), (-75596807735477/281474976710656)), (2284101/281474976710656), by norm_num⟩
  | 4 => ⟨((248222916985229/562949953421312), (-108297736592737/281474976710656)), (17996139/1125899906842624), by norm_num⟩
  | 5 => ⟨((208914024031749/4503599627370496), (-1528063653492333/4503599627370496)), (118872897/4503599627370496), by norm_num⟩
  | 6 => ⟨((-508778232807749/4503599627370496), (-283536684644527/9007199254740992)), (11461919/562949953421312), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-786048445/16777216)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-25355259/524288)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-322598828550573/9007199254740992), (931580742862787/9007199254740992)), (172041271/9007199254740992), by norm_num⟩
  | 1 => ⟨((49319843/536870912), (-569691045/2147483648)), (213/4294967296), by norm_num⟩
  | 2 => ⟨((-506011599/4294967296), (182653585/536870912)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((432631375/4294967296), (-1249325855/4294967296)), (119/2147483648), by norm_num⟩
  | 4 => ⟨((-2167339/33554432), (801114387/4294967296)), (77/2147483648), by norm_num⟩
  | 5 => ⟨((284626677/8589934592), (-821927133/8589934592)), (5/268435456), by norm_num⟩
  | 6 => ⟨((-60837751/4294967296), (1372527/33554432)), (69/8589934592), by norm_num⟩
  | 7 => ⟨((356676001/68719476736), (-1029986669/68719476736)), (51/17179869184), by norm_num⟩
  | 8 => ⟨((-114356985/68719476736), (1320931823/274877906944)), (33/34359738368), by norm_num⟩
  | 9 => ⟨((130364389/274877906944), (-1505832547/1099511627776)), (303/1099511627776), by norm_num⟩
  | 10 => ⟨((-535004889/4398046511104), (772476845/2199023255552)), (313/4398046511104), by norm_num⟩
  | 11 => ⟨((499003799/17592186044416), (-1440991991/17592186044416)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((-426639825/70368744177664), (1232023827/70368744177664)), (127/35184372088832), by norm_num⟩
  | 13 => ⟨((336710629/281474976710656), (-972331915/281474976710656)), (101/140737488355328), by norm_num⟩
  | 14 => ⟨((-493511835/2251799813685248), (1425132641/2251799813685248)), (299/2251799813685248), by norm_num⟩
  | 15 => ⟨((168777715/4503599627370496), (-974771481/9007199254740992)), (207/9007199254740992), by norm_num⟩
  | 16 => ⟨((-108226573/18014398509481984), (625059871/36028797018963968)), (67/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (2480386040607/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778552300374087/633825300114114700748351602688), (733685269515/158456325028528675187087900672)), (92489/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472374539768941/9903520314283042199192993792), (1650470016411/19807040628566084398385987584)), (104069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889257788599427/2475880078570760549798248448), (1753228300123/1237940039285380274899124224)), (55297/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770923798602677/154742504910672534362390528), (1752782810537/77371252455336267181195264)), (110619/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774651481430203/4835703278458516698824704), (3285521346501/9671406556917033397649408)), (103731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258569274865869/604462909807314587353088), (2873885027177/604462909807314587353088)), (45395/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887435029862965/75557863725914323419136), (4668289714443/75557863725914323419136)), (73791/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297271275680643/4722366482869645213696), (3499666091277/4722366482869645213696)), (110729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621078694310271/590295810358705651712), (2404760634247/295147905179352825856)), (152321/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113938239352769/4611686018427387904), (6008124071907/73786976294838206464)), (23813/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911067425840645/4611686018427387904), (6753948581033/9223372036854775808)), (214459/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593381600399937/1152921504606846976), (210858264125/36028797018963968)), (53659/288230376151711744), by norm_num⟩
  | 5 => ⟨((149256257909623/18014398509481984), (1474185775397/36028797018963968)), (94003/72057594037927936), by norm_num⟩
  | 4 => ⟨((745418711135657/18014398509481984), (8830553935647/36028797018963968)), (282409/36028797018963968), by norm_num⟩
  | 3 => ⟨((23253919691261/140737488355328), (5506373427915/4503599627370496)), (353711/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225914024130399/4503599627370496), (21949299685559/4503599627370496)), (709525/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213002038093043/2251799813685248), (16366981676287/1125899906842624)), (534781/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174329715896767/2251799813685248), (32355485910721/1125899906842624)), (2160299/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174329715896767/2251799813685248), (32355485910721/1125899906842624)), (8240886696822356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2097665243087139/2251799813685248), (31242339598929/562949953421312)), (2148059/1125899906842624), by norm_num⟩
  | 2 => ⟨((1947145614308527/2251799813685248), (232830536679523/2251799813685248)), (8480951/2251799813685248), by norm_num⟩
  | 3 => ⟨((414908772284945/562949953421312), (201330045245311/1125899906842624)), (4105221/562949953421312), by norm_num⟩
  | 4 => ⟨((1151191799944091/2251799813685248), (593541940196505/2251799813685248)), (30077905/2251799813685248), by norm_num⟩
  | 5 => ⟨((864153660172815/4503599627370496), (1213750192756043/4503599627370496)), (46609771/2251799813685248), by norm_num⟩
  | 6 => ⟨((-322598828550573/9007199254740992), (931580742862787/9007199254740992)), (172041271/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-25355259/524288)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-1669621601/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((101066293359445/1125899906842624), (448953670295609/9007199254740992)), (87937393/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1017455071/4294967296), (-564963567/4294967296)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((1342561131/4294967296), (745485621/4294967296)), (151/4294967296), by norm_num⟩
  | 3 => ⟨((-1181031931/4294967296), (-655793097/4294967296)), (135/4294967296), by norm_num⟩
  | 4 => ⟨((779202743/4294967296), (432668895/4294967296)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-205636071/2147483648), (-456735207/8589934592)), (49/4294967296), by norm_num⟩
  | 6 => ⟨((723580507/17179869184), (401783465/17179869184)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-1091183109/68719476736), (-605902627/68719476736)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((719923695/137438953472), (199876471/68719476736)), (91/137438953472), by norm_num⟩
  | 9 => ⟨((-422204423/274877906944), (-468875969/549755813888)), (109/549755813888), by norm_num⟩
  | 10 => ⟨((891377341/2199023255552), (494956225/2199023255552)), (117/2199023255552), by norm_num⟩
  | 11 => ⟨((-855416693/8796093022208), (-237494155/4398046511104)), (57/4398046511104), by norm_num⟩
  | 12 => ⟨((376248949/17592186044416), (104460115/8796093022208)), (51/17592186044416), by norm_num⟩
  | 13 => ⟨((-611041567/140737488355328), (-2650733/1099511627776)), (21/35184372088832), by norm_num⟩
  | 14 => ⟨((230367675/281474976710656), (255833101/562949953421312)), (129/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1296967469/9007199254740992), (-11252637/140737488355328)), (23/1125899906842624), by norm_num⟩
  | 16 => ⟨((213923219/9007199254740992), (237570833/18014398509481984)), (123/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (660269407349/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778458079037263/633825300114114700748351602688), (781134576297/633825300114114700748351602688)), (46139/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944696210906373/19807040628566084398385987584), (878602564691/39614081257132168796771975168)), (103817/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472286446100829/618970019642690137449562112), (933298542961/2475880078570760549798248448)), (110311/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885406089215781/77371252455336267181195264), (933054876801/154742504910672534362390528)), (55159/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96824920419439/604462909807314587353088), (218620035075/2417851639229258349412352)), (51715/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314619618924347/151115727451828646838272), (382455707879/302231454903657293676544)), (22627/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887288244571261/75557863725914323419136), (1242496186733/75557863725914323419136)), (9193/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297161854015123/4722366482869645213696), (465724047907/2361183241434822606848)), (13791/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810464661349879/295147905179352825856), (1280052456485/590295810358705651712)), (151719/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822826737822915/73786976294838206464), (1599033251353/73786976294838206464)), (47419/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910964425605285/4611686018427387904), (1797494095109/9223372036854775808)), (213423/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593178379661203/1152921504606846976), (897861446129/576460752303423488)), (213471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193875365389973/144115188075855872), (784633623037/72057594037927936)), (186841/144115188075855872), by norm_num⟩
  | 4 => ⟨((186322699829991/4503599627370496), (2349926088963/36028797018963968)), (17523/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487941932408023/9007199254740992), (1465232375841/4503599627370496)), (350649/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112664284201319/2251799813685248), (5840152848567/4503599627370496)), (350933/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106102156470299/1125899906842624), (8708468923581/2251799813685248)), (527115/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086526432373865/1125899906842624), (1075686288819/140737488355328)), (2114231/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086526432373865/1125899906842624), (1075686288819/140737488355328)), (8065151223189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096928202248439/2251799813685248), (16609101091717/1125899906842624)), (2056455/1125899906842624), by norm_num⟩
  | 2 => ⟨((976109068335467/1125899906842624), (30933560151795/1125899906842624)), (7781421/2251799813685248), by norm_num⟩
  | 3 => ⟨((211349166644019/281474976710656), (107272514711339/2251799813685248)), (13919929/2251799813685248), by norm_num⟩
  | 4 => ⟨((1264443973089899/2251799813685248), (161093940591071/2251799813685248)), (22230173/2251799813685248), by norm_num⟩
  | 5 => ⟨((698493397960669/2251799813685248), (180916847975327/2251799813685248)), (56292669/4503599627370496), by norm_num⟩
  | 6 => ⟨((101066293359445/1125899906842624), (448953670295609/9007199254740992)), (87937393/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1669621601/33554432)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-428317629/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((38179186766489/562949953421312), (-38838445637697/562949953421312)), (100025399/9007199254740992), by norm_num⟩
  | 1 => ⟨((-197202977/1073741824), (802432713/4294967296)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((534035561/2147483648), (-543257017/2147483648)), (91/2147483648), by norm_num⟩
  | 3 => ⟨((-120516259/536870912), (980778183/4294967296)), (167/4294967296), by norm_num⟩
  | 4 => ⟨((652728159/4294967296), (-663999139/4294967296)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((-707048249/8589934592), (719257201/8589934592)), (127/8589934592), by norm_num⟩
  | 6 => ⟨((319120359/8589934592), (-20289423/536870912)), (117/17179869184), by norm_num⟩
  | 7 => ⟨((-987650231/68719476736), (251176119/17179869184)), (183/68719476736), by norm_num⟩
  | 8 => ⟨((334325801/68719476736), (-680197539/137438953472)), (63/68719476736), by norm_num⟩
  | 9 => ⟨((-804774269/549755813888), (818670703/549755813888)), (153/549755813888), by norm_num⟩
  | 10 => ⟨((13621057/34359738368), (-886800545/2199023255552)), (21/274877906944), by norm_num⟩
  | 11 => ⟨((-429224799/4398046511104), (873272871/8796093022208)), (21/1099511627776), by norm_num⟩
  | 12 => ⟨((387454101/17592186044416), (-788288925/35184372088832)), (77/17592186044416), by norm_num⟩
  | 13 => ⟨((-645689327/140737488355328), (164209691/35184372088832)), (65/70368744177664), by norm_num⟩
  | 14 => ⟨((999176635/1125899906842624), (-127053739/140737488355328)), (51/281474976710656), by norm_num⟩
  | 15 => ⟨((-360776065/2251799813685248), (734011527/4503599627370496)), (149/4503599627370496), by norm_num⟩
  | 16 => ⟨((976999695/36028797018963968), (-62116877/2251799813685248)), (51/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-517109338695/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778365905608497/633825300114114700748351602688), (-1223416676207/633825300114114700748351602688)), (92321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644360481205/19807040628566084398385987584), (-1376064406093/39614081257132168796771975168)), (103869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118064724572329/154742504910672534362390528), (-1461720163823/2475880078570760549798248448)), (55185/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770701976983729/154742504910672534362390528), (-730664262393/77371252455336267181195264)), (110379/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774547701016865/4835703278458516698824704), (-684789759197/4835703278458516698824704)), (25873/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78649253487919/37778931862957161709568), (-598983132893/302231454903657293676544)), (45283/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887141292049047/75557863725914323419136), (-972957937203/37778931862957161709568)), (73595/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297051621995043/4722366482869645213696), (-729377676547/2361183241434822606848)), (55205/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620777725112969/590295810358705651712), (-1002340863511/295147905179352825856)), (151843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911318599076365/36893488147419103232), (-1252096476133/36893488147419103232)), (94923/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821715560634163/9223372036854775808), (-2814937478913/9223372036854775808)), (53409/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592965016395013/1152921504606846976), (-2812090710937/1152921504606846976)), (106855/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193688591263167/144115188075855872), (-2457380497741/144115188075855872)), (23385/18014398509481984), by norm_num⟩
  | 4 => ⟨((93143829761047/2251799813685248), (-3679682335661/36028797018963968)), (280787/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487591249939037/9007199254740992), (-4588444178939/9007199254740992)), (175639/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224626376604663/4503599627370496), (-9143495893723/4503599627370496)), (43965/281474976710656), by norm_num⟩
  | 1 => ⟨((1105574498748127/1125899906842624), (-13632055130017/2251799813685248)), (264345/562949953421312), by norm_num⟩
  | 0 => ⟨((2170934357830319/2251799813685248), (-26933104510503/2251799813685248)), (2123697/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170934357830319/2251799813685248), (-26933104510503/2251799813685248)), (8101261147505950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092650761071709/2251799813685248), (-6491474240909/281474976710656)), (4145667/2251799813685248), by norm_num⟩
  | 2 => ⟨((1943552117730673/2251799813685248), (-96522885760319/2251799813685248)), (7896551/2251799813685248), by norm_num⟩
  | 3 => ⟨((836681427887039/1125899906842624), (-83309918532201/1125899906842624)), (7154081/1125899906842624), by norm_num⟩
  | 4 => ⟨((615592260939881/1125899906842624), (-123818931276309/1125899906842624)), (11691435/1125899906842624), by norm_num⟩
  | 5 => ⟨((645923677187929/2251799813685248), (-541589712465955/4503599627370496)), (61424843/4503599627370496), by norm_num⟩
  | 6 => ⟨((38179186766489/562949953421312), (-38838445637697/562949953421312)), (100025399/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-428317629/8388608)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile009Terms1
