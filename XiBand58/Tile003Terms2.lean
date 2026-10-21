/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile003Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2501/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2501/160))
  have he : value ((15/16), (2501/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-727108225/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((133916052858479/2251799813685248), (803108993810731/18014398509481984)), (35129877/4503599627370496), by norm_num⟩
  | 1 => ⟨((-354093683/2147483648), (-265442245/2147483648)), (95/4294967296), by norm_num⟩
  | 2 => ⟨((122719519/536870912), (735962175/4294967296)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((-907335345/4294967296), (-170043369/1073741824)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((78614617/536870912), (471460327/4294967296)), (89/4294967296), by norm_num⟩
  | 5 => ⟨((-348745601/4294967296), (-261433117/4294967296)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((644618747/17179869184), (15100969/536870912)), (95/17179869184), by norm_num⟩
  | 7 => ⟨((-1021292953/68719476736), (-382800241/34359738368)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((707906331/137438953472), (66334227/17179869184)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-872325827/549755813888), (-326964497/274877906944)), (135/549755813888), by norm_num⟩
  | 10 => ⟨((241860075/549755813888), (362615231/1099511627776)), (19/274877906944), by norm_num⟩
  | 11 => ⟨((-975386933/8796093022208), (-182796891/2199023255552)), (155/8796093022208), by norm_num⟩
  | 12 => ⟨((901448937/35184372088832), (337880399/17592186044416)), (145/35184372088832), by norm_num⟩
  | 13 => ⟨((-384514947/70368744177664), (-288247195/70368744177664)), (125/140737488355328), by norm_num⟩
  | 14 => ⟨((76150129/70368744177664), (456680527/562949953421312)), (201/1125899906842624), by norm_num⟩
  | 15 => ⟨((-450417043/2251799813685248), (-337649941/2251799813685248)), (75/2251799813685248), by norm_num⟩
  | 16 => ⟨((624410607/18014398509481984), (468082209/18014398509481984)), (53/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (209482646819/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888980036299713/316912650057057350374175801344), (990788598569/633825300114114700748351602688)), (46149/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888832272008793/39614081257132168796771975168), (1114387166665/39614081257132168796771975168)), (51921/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888550758503333/2475880078570760549798248448), (1183722571829/2475880078570760549798248448)), (110339/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770217302403405/154742504910672534362390528), (295842431835/38685626227668133590597632)), (110347/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548641189624227/9671406556917033397649408), (1109034367981/9671406556917033397649408)), (103459/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257990789880675/604462909807314587353088), (970030484759/604462909807314587353088)), (11317/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471624013344545/18889465931478580854784), (1575597535381/75557863725914323419136)), (147137/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81035498217465/295147905179352825856), (590542123987/2361183241434822606848)), (110367/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620113157888949/590295810358705651712), (1622993900681/590295810358705651712)), (75889/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821807166937659/73786976294838206464), (2027248107343/73786976294838206464)), (189757/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820782706640155/9223372036854775808), (1139300677793/4611686018427387904)), (213525/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592033324997043/1152921504606846976), (2276038177387/1152921504606846976)), (213585/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596437333707271/72057594037927936), (124290852835/9007199254740992)), (46739/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489082998169365/36028797018963968), (1488615236953/18014398509481984)), (140285/18014398509481984), by norm_num⟩
  | 3 => ⟨((743036477974183/4503599627370496), (3711496998177/9007199254740992)), (43869/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110801704489773/2251799813685248), (7392956111113/4503599627370496)), (702627/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206648456633413/2251799813685248), (11014637514817/2251799813685248)), (527879/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162068079561279/2251799813685248), (21731870170639/2251799813685248)), (2118851/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2162068079561279/2251799813685248), (21731870170639/2251799813685248)), (8082775124556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2075702324012189/2251799813685248), (41731758320215/2251799813685248)), (4109733/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912602786483355/2251799813685248), (76936419662119/2251799813685248)), (7729009/2251799813685248), by norm_num⟩
  | 3 => ⟨((405467904384501/562949953421312), (32673599521043/562949953421312)), (13657669/2251799813685248), by norm_num⟩
  | 4 => ⟨((580288376924533/1125899906842624), (94133383232245/1125899906842624)), (10629705/1125899906842624), by norm_num⟩
  | 5 => ⟨((1164840691654093/4503599627370496), (194065237374213/2251799813685248)), (50938131/4503599627370496), by norm_num⟩
  | 6 => ⟨((133916052858479/2251799813685248), (803108993810731/18014398509481984)), (35129877/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-727108225/16777216)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-743006963/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((150851212123709/2251799813685248), (-189547422063247/9007199254740992)), (12948209/2251799813685248), by norm_num⟩
  | 1 => ⟨((-815188727/4294967296), (512150083/8589934592)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((577400895/2147483648), (-90689403/1073741824)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((-1090599947/4294967296), (171294951/2147483648)), (99/4294967296), by norm_num⟩
  | 4 => ⟨((772475581/4294967296), (-485315141/8589934592)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((-437717625/4294967296), (275000267/8589934592)), (83/8589934592), by norm_num⟩
  | 6 => ⟨((51672809/1073741824), (-259711475/17179869184)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((-1338515127/68719476736), (210233719/34359738368)), (131/68719476736), by norm_num⟩
  | 8 => ⟨((474037365/68719476736), (-297818489/137438953472)), (47/68719476736), by norm_num⟩
  | 9 => ⟨((-1193821323/549755813888), (46876851/68719476736)), (15/68719476736), by norm_num⟩
  | 10 => ⟨((1352940201/2199023255552), (-424998783/2199023255552)), (69/1099511627776), by norm_num⟩
  | 11 => ⟨((-1393879357/8796093022208), (218929495/4398046511104)), (9/549755813888), by norm_num⟩
  | 12 => ⟨((1316385865/35184372088832), (-206757989/17592186044416)), (69/17592186044416), by norm_num⟩
  | 13 => ⟨((-573784923/70368744177664), (180242921/70368744177664)), (61/70368744177664), by norm_num⟩
  | 14 => ⟨((232236443/140737488355328), (-145904757/281474976710656)), (101/562949953421312), by norm_num⟩
  | 15 => ⟨((-1403680831/4503599627370496), (440937925/4503599627370496)), (155/4503599627370496), by norm_num⟩
  | 16 => ⟨((994231815/18014398509481984), (-312317803/18014398509481984)), (7/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (-396474533831/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777872944935955/633825300114114700748351602688), (-58594586351/79228162514264337593543950336)), (92247/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888734298114673/39614081257132168796771975168), (-527230693721/39614081257132168796771975168)), (103781/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((115261640577/151115727451828646838272), (-560030926257/2475880078570760549798248448)), (55135/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885056664139093/77371252455336267181195264), (-559860367649/154742504910672534362390528)), (110275/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774271891538729/4835703278458516698824704), (-262343974679/4835703278458516698824704)), (103387/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257905628300909/604462909807314587353088), (-229460446389/302231454903657293676544)), (22617/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886357795365055/75557863725914323419136), (-186351783205/18889465931478580854784)), (147017/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296464391229689/4722366482869645213696), (-69844827665/590295810358705651712)), (55135/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202496364863313/73786976294838206464), (-47988203035/36893488147419103232)), (9477/36893488147419103232), by norm_num⟩
  | 8 => ⟨((227703705459335/9223372036854775808), (-479520925069/36893488147419103232)), (189557/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820583371204063/9223372036854775808), (-1077929972279/9223372036854775808)), (106637/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99489653847557/72057594037927936), (-1076691229999/1152921504606846976)), (26663/144115188075855872), by norm_num⟩
  | 5 => ⟨((596350595909307/72057594037927936), (-470356577863/72057594037927936)), (93337/72057594037927936), by norm_num⟩
  | 4 => ⟨((744411920939493/18014398509481984), (-352072792937/9007199254740992)), (70019/9007199254740992), by norm_num⟩
  | 3 => ⟨((92859428400997/562949953421312), (-1755512215063/9007199254740992)), (87553/2251799813685248), by norm_num⟩
  | 2 => ⟨((138810294567303/281474976710656), (-1748256008873/2251799813685248)), (700775/4503599627370496), by norm_num⟩
  | 1 => ⟨((137856505991125/140737488355328), (-651079560473/281474976710656)), (1052055/2251799813685248), by norm_num⟩
  | 0 => ⟨((540058395992427/562949953421312), (-10273640218265/2251799813685248)), (526935/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((540058395992427/562949953421312), (-10273640218265/2251799813685248)), (2010097505809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2072343891880057/2251799813685248), (-4927938641401/562949953421312)), (4063297/2251799813685248), by norm_num⟩
  | 2 => ⟨((1907017056687955/2251799813685248), (-9070418676653/562949953421312)), (7550089/2251799813685248), by norm_num⟩
  | 3 => ⟨((1614440889676449/2251799813685248), (-7681607850997/281474976710656)), (6363/1099511627776), by norm_num⟩
  | 4 => ⟨((1155805643154645/2251799813685248), (-22029492564551/562949953421312)), (4849295/562949953421312), by norm_num⟩
  | 5 => ⟨((589804608737453/2251799813685248), (-180917054293711/4503599627370496)), (42861023/4503599627370496), by norm_num⟩
  | 6 => ⟨((150851212123709/2251799813685248), (-189547422063247/9007199254740992)), (12948209/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-743006963/16777216)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-1515993383/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((436877465050977/18014398509481984), (-558261570616891/9007199254740992)), (170078343/18014398509481984), by norm_num⟩
  | 1 => ⟨((-75265067/1073741824), (48088535/268435456)), (237/8589934592), by norm_num⟩
  | 2 => ⟨((27193003/268435456), (-277987487/1073741824)), (173/4294967296), by norm_num⟩
  | 3 => ⟨((-419188735/4294967296), (535658121/2147483648)), (169/4294967296), by norm_num⟩
  | 4 => ⟨((75725705/1073741824), (-774125553/4294967296)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((-350200703/8589934592), (447502127/4294967296)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((337403407/17179869184), (-215574585/4294967296)), (141/17179869184), by norm_num⟩
  | 7 => ⟨((-278634651/34359738368), (1424207297/68719476736)), (235/68719476736), by norm_num⟩
  | 8 => ⟨((402678863/137438953472), (-1029122137/137438953472)), (43/34359738368), by norm_num⟩
  | 9 => ⟨((-517285161/549755813888), (1322020249/549755813888)), (223/549755813888), by norm_num⟩
  | 10 => ⟨((74757321/274877906944), (-1528451997/2199023255552)), (65/549755813888), by norm_num⟩
  | 11 => ⟨((-314293017/4398046511104), (803235361/4398046511104)), (69/2199023255552), by norm_num⟩
  | 12 => ⟨((302807887/17592186044416), (-386941467/8796093022208)), (135/17592186044416), by norm_num⟩
  | 13 => ⟨((-538601455/140737488355328), (688249039/70368744177664)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((111197031/140737488355328), (-568370167/281474976710656)), (101/281474976710656), by norm_num⟩
  | 15 => ⟨((-342827475/2251799813685248), (13690009/35184372088832)), (79/1125899906842624), by norm_num⟩
  | 16 => ⟨((247724713/9007199254740992), (-316553723/4503599627370496)), (115/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (-780151303879/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777788713751583/633825300114114700748351602688), (-230575194537/79228162514264337593543950336)), (46191/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944319733159979/19807040628566084398385987584), (-2074691281763/39614081257132168796771975168)), (51971/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944172931157859/1237940039285380274899124224), (-1101875170647/1237940039285380274899124224)), (27613/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885006180577669/77371252455336267181195264), (-2203065379385/154742504910672534362390528)), (110467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774224504698289/4835703278458516698824704), (-2064646303057/9671406556917033397649408)), (103579/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257822584451799/604462909807314587353088), (-1805838342299/604462909807314587353088)), (11331/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886222630228495/75557863725914323419136), (-1466562265455/37778931862957161709568)), (147333/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296362826120611/4722366482869645213696), (-2198651643227/4722366482869645213696)), (55263/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619830956585575/590295810358705651712), (-3021210669595/590295810358705651712)), (152017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910727113098381/36893488147419103232), (-943403133533/18446744073709551616)), (95043/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227548173644441/1152921504606846976), (-4241329080305/9223372036854775808)), (13371/576460752303423488), by norm_num⟩
  | 6 => ⟨((795817842443663/576460752303423488), (-1059088293639/288230376151711744)), (6689/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192526371167977/144115188075855872), (-1850609254679/72057594037927936)), (187419/144115188075855872), by norm_num⟩
  | 4 => ⟨((744279917996803/18014398509481984), (-1385166285457/9007199254740992)), (70345/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485417757151139/9007199254740992), (-1726584551015/2251799813685248)), (44021/1125899906842624), by norm_num⟩
  | 2 => ⟨((555072328331777/1125899906842624), (-859647616629/281474976710656)), (352835/2251799813685248), by norm_num⟩
  | 1 => ⟨((551167051979513/562949953421312), (-20486332886069/2251799813685248)), (265463/562949953421312), by norm_num⟩
  | 0 => ⟨((2158071995032077/2251799813685248), (-20197636381755/1125899906842624)), (1068585/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2158071995032077/2251799813685248), (-20197636381755/1125899906842624)), (4076328281882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32305012537815/35184372088832), (-19356939802731/562949953421312)), (2086553/1125899906842624), by norm_num⟩
  | 2 => ⟨((236957520857377/281474976710656), (-71091356292181/1125899906842624)), (7950173/2251799813685248), by norm_num⟩
  | 3 => ⟨((1586869100326507/2251799813685248), (-59847705605107/562949953421312)), (1798695/281474976710656), by norm_num⟩
  | 4 => ⟨((1092834967280933/2251799813685248), (-84350726181787/562949953421312)), (11670255/1125899906842624), by norm_num⟩
  | 5 => ⟨((239907548403551/1125899906842624), (-654988405464935/4503599627370496)), (59299201/4503599627370496), by norm_num⟩
  | 6 => ⟨((436877465050977/18014398509481984), (-558261570616891/9007199254740992)), (170078343/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-1515993383/33554432)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-1544351517/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-32397114497139/1125899906842624), (-1014993482046203/18014398509481984)), (204957597/18014398509481984), by norm_num⟩
  | 1 => ⟨((363889033/4294967296), (178133629/1073741824)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-267862263/2147483648), (-1049007201/4294967296)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((525802725/4294967296), (1029579231/4294967296)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-193524255/2147483648), (-757883305/4294967296)), (5/134217728), by norm_num⟩
  | 5 => ⟨((14245509/268435456), (446308229/4294967296)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((-223706837/8589934592), (-876084897/17179869184)), (189/17179869184), by norm_num⟩
  | 7 => ⟨((94098733/8589934592), (368511217/17179869184)), (161/34359738368), by norm_num⟩
  | 8 => ⟨((-554135955/137438953472), (-135632349/17179869184)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((725164225/549755813888), (1419950845/549755813888)), (315/549755813888), by norm_num⟩
  | 10 => ⟨((-213520181/549755813888), (-836191723/1099511627776)), (187/1099511627776), by norm_num⟩
  | 11 => ⟨((228617143/2199023255552), (111914341/549755813888)), (101/2199023255552), by norm_num⟩
  | 12 => ⟨((-448766151/17592186044416), (-878733195/17592186044416)), (25/2199023255552), by norm_num⟩
  | 13 => ⟨((406573707/70368744177664), (12439309/1099511627776)), (183/70368744177664), by norm_num⟩
  | 14 => ⟨((-342037563/281474976710656), (-1339493899/562949953421312)), (155/281474976710656), by norm_num⟩
  | 15 => ⟨((537124657/2251799813685248), (1051748813/2251799813685248)), (245/2251799813685248), by norm_num⟩
  | 16 => ⟨((-197691347/4503599627370496), (-387101275/4503599627370496)), (91/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (-166324346305/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27776674617785/9903520314283042199192993792), (-3145814965939/633825300114114700748351602688)), (92511/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888547567151003/39614081257132168796771975168), (-884548133485/9903520314283042199192993792)), (52047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236030998785895/309485009821345068724781056), (-3758270538929/2475880078570760549798248448)), (110623/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884957115827313/77371252455336267181195264), (-117408737215/4835703278458516698824704)), (110649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548356739672879/9671406556917033397649408), (-3520997171919/9671406556917033397649408)), (103761/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4913053028927/2361183241434822606848), (-769902018307/151115727451828646838272)), (90819/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886090479172659/75557863725914323419136), (-2500996658495/37778931862957161709568)), (9227/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162032908247971/590295810358705651712), (-937355614123/1180591620717411303424)), (55385/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619693336381239/590295810358705651712), (-2576044986963/295147905179352825856)), (76191/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910640557675993/36893488147419103232), (-1608766759849/18446744073709551616)), (47647/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820189149909987/9223372036854775808), (-7232518522731/9223372036854775808)), (214563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591437588413569/1152921504606846976), (-7223861997233/1152921504606846976)), (107377/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192350953827213/144115188075855872), (-6311152122721/144115188075855872)), (188125/144115188075855872), by norm_num⟩
  | 4 => ⟨((186036570029315/4503599627370496), (-9447302575065/36028797018963968)), (35327/4503599627370496), by norm_num⟩
  | 3 => ⟨((742538218267205/4503599627370496), (-5887598887763/4503599627370496)), (354023/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219585138434421/4503599627370496), (-5862215341379/1125899906842624)), (88789/562949953421312), by norm_num⟩
  | 1 => ⟨((2203558613652593/2251799813685248), (-17460177517377/1125899906842624)), (535575/1125899906842624), by norm_num⟩
  | 0 => ⟨((538910618826387/562949953421312), (-34417170137727/1125899906842624)), (541285/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((538910618826387/562949953421312), (-34417170137727/1125899906842624)), (2064838411571311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2061487120981319/2251799813685248), (-131789892472337/2251799813685248)), (2138869/1125899906842624), by norm_num⟩
  | 2 => ⟨((939772831601621/1125899906842624), (-241303125043433/2251799813685248)), (4166563/1125899906842624), by norm_num⟩
  | 3 => ⟨((771486142061659/1125899906842624), (-201412327790595/1125899906842624)), (15697045/2251799813685248), by norm_num⟩
  | 4 => ⟨((985210031968997/2251799813685248), (-552044879963007/2251799813685248)), (27127867/2251799813685248), by norm_num⟩
  | 5 => ⟨((295712457897937/2251799813685248), (-483062615540919/2251799813685248)), (18519607/1125899906842624), by norm_num⟩
  | 6 => ⟨((-32397114497139/1125899906842624), (-1014993482046203/18014398509481984)), (204957597/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-1544351517/33554432)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1571254733/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1038679048483147/18014398509481984), (-317719298348731/18014398509481984)), (95767867/9007199254740992), by norm_num⟩
  | 1 => ⟨((1483728575/8589934592), (113463635/2147483648)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-555606697/2147483648), (-339906673/4294967296)), (209/4294967296), by norm_num⟩
  | 3 => ⟨((1109632609/4294967296), (169711565/2147483648)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((-831040555/4294967296), (-127102603/2147483648)), (159/4294967296), by norm_num⟩
  | 5 => ⟨((995830005/8589934592), (38076537/1073741824)), (3/134217728), by norm_num⟩
  | 6 => ⟨((-497206681/8589934592), (-152089481/8589934592)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((212785443/8589934592), (65088481/8589934592)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((-637448219/68719476736), (-194987663/68719476736)), (63/34359738368), by norm_num⟩
  | 9 => ⟨((212180467/68719476736), (32451713/34359738368)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((-1017017397/1099511627776), (-311093261/1099511627776)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((553947607/2199023255552), (338891681/4398046511104)), (113/2199023255552), by norm_num⟩
  | 12 => ⟨((-553159575/8796093022208), (-169204791/8796093022208)), (57/4398046511104), by norm_num⟩
  | 13 => ⟨((509882459/35184372088832), (155966847/35184372088832)), (53/17592186044416), by norm_num⟩
  | 14 => ⟨((-872840765/281474976710656), (-266991381/281474976710656)), (183/281474976710656), by norm_num⟩
  | 15 => ⟨((1394558533/2251799813685248), (426578505/2251799813685248)), (147/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1044431001/9007199254740992), (-319478749/9007199254740992)), (111/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (-926398829283/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888814073454329/316912650057057350374175801344), (-547508494151/79228162514264337593543950336)), (11579/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888458410040629/39614081257132168796771975168), (-1231590266711/9903520314283042199192993792)), (104239/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888152921029305/2475880078570760549798248448), (-2616378456599/1237940039285380274899124224)), (55393/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884909390282523/77371252455336267181195264), (-2615533949693/77371252455336267181195264)), (55411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548266848950581/9671406556917033397649408), (-4902332089891/9671406556917033397649408)), (51967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((4912744203571/2361183241434822606848), (-4287747087343/604462909807314587353088)), (90981/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471490312376209/18889465931478580854784), (-6964227441499/75557863725914323419136)), (36979/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324041420271841/1180591620717411303424), (-5220230423417/4722366482869645213696)), (13875/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619558082006201/590295810358705651712), (-3586520682477/295147905179352825856)), (19091/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821110437565561/73786976294838206464), (-8959142511205/73786976294838206464)), (191063/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819994928601915/9223372036854775808), (-5034598970841/4611686018427387904)), (215159/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591240613149709/1152921504606846976), (-10056910977147/1152921504606846976)), (1683/9007199254740992), by norm_num⟩
  | 5 => ⟨((1192175511939079/144115188075855872), (-2196496924187/36028797018963968)), (188795/144115188075855872), by norm_num⟩
  | 4 => ⟨((186002905557877/4503599627370496), (-13151396296613/36028797018963968)), (283791/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484729078334893/9007199254740992), (-512220209875/281474976710656)), (355787/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218858497599661/4503599627370496), (-16318899798505/2251799813685248)), (89341/562949953421312), by norm_num⟩
  | 1 => ⟨((1101194797308159/1125899906842624), (-24298511145159/1125899906842624)), (540001/1125899906842624), by norm_num⟩
  | 0 => ⟨((2152992703849913/2251799813685248), (-95761681192185/2251799813685248)), (1095897/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2152992703849913/2251799813685248), (-95761681192185/2251799813685248)), (4180515293601607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((513612184254853/562949953421312), (-183119475951777/2251799813685248)), (1094415/562949953421312), by norm_num⟩
  | 2 => ⟨((929751136206703/1125899906842624), (-10441913336567/70368744177664)), (8699987/2251799813685248), by norm_num⟩
  | 3 => ⟨((1485966168638681/2251799813685248), (-551857555640543/2251799813685248)), (16950593/2251799813685248), by norm_num⟩
  | 4 => ⟨((845345434817253/2251799813685248), (-182085825881525/562949953421312)), (30679745/2251799813685248), by norm_num⟩
  | 5 => ⟨((163535795016985/4503599627370496), (-1093705902049723/4503599627370496)), (42881583/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1038679048483147/18014398509481984), (-317719298348731/18014398509481984)), (95767867/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1571254733/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1596845063/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-927075665495243/18014398509481984), (466036630180655/18014398509481984)), (187993051/18014398509481984), by norm_num⟩
  | 1 => ⟨((672937075/4294967296), (-676564683/8589934592)), (275/8589934592), by norm_num⟩
  | 2 => ⟨((-256096503/1073741824), (257477045/2147483648)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((1039588733/4294967296), (-522596427/4294967296)), (27/536870912), by norm_num⟩
  | 4 => ⟨((-395631403/2147483648), (397764137/4294967296)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((963606947/8589934592), (-15137523/268435456)), (51/2147483648), by norm_num⟩
  | 6 => ⟨((-977907657/17179869184), (491589637/17179869184)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((425323115/17179869184), (-427615909/34359738368)), (23/4294967296), by norm_num⟩
  | 8 => ⟨((-1294905767/137438953472), (650943115/137438953472)), (141/68719476736), by norm_num⟩
  | 9 => ⟨((876082147/274877906944), (-440402427/274877906944)), (193/274877906944), by norm_num⟩
  | 10 => ⟨((-533450351/549755813888), (134081507/274877906944)), (237/1099511627776), by norm_num⟩
  | 11 => ⟨((1181164773/4398046511104), (-296883023/2199023255552)), (33/549755813888), by norm_num⟩
  | 12 => ⟨((-599347109/8796093022208), (602578017/17592186044416)), (135/8796093022208), by norm_num⟩
  | 13 => ⟨((140363517/8796093022208), (-282240353/35184372088832)), (255/70368744177664), by norm_num⟩
  | 14 => ⟨((-488388431/140737488355328), (491021193/281474976710656)), (7/8796093022208), by norm_num⟩
  | 15 => ⟨((198254605/281474976710656), (-398646677/1125899906842624)), (23/140737488355328), by norm_num⟩
  | 16 => ⟨((-1207181187/9007199254740992), (606844377/9007199254740992)), (141/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (871379161017/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888779454342821/316912650057057350374175801344), (4119620350183/633825300114114700748351602688)), (46303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944190300939665/19807040628566084398385987584), (1158353979403/9903520314283042199192993792)), (6513/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888070361160493/2475880078570760549798248448), (4921569436273/2475880078570760549798248448)), (110751/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769736345808175/154742504910672534362390528), (4919955570463/154742504910672534362390528)), (55393/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548189699206135/9671406556917033397649408), (4610744147441/9671406556917033397649408)), (51949/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257595142825271/604462909807314587353088), (4032687527597/604462909807314587353088)), (90947/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942926008287571/37778931862957161709568), (3274952750639/37778931862957161709568)), (9241/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296083973753875/4722366482869645213696), (2454810066355/2361183241434822606848)), (13869/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619446087230475/590295810358705651712), (6746165452061/590295810358705651712)), (152655/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820970972593533/73786976294838206464), (8425867640129/73786976294838206464)), (47741/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909919378016541/4611686018427387904), (4734852002859/4611686018427387904)), (107517/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397771336437243/288230376151711744), (4728983902985/576460752303423488)), (215283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192040668890585/144115188075855872), (8262532574789/144115188075855872)), (94327/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487823005784665/36028797018963968), (6183727631953/18014398509481984)), (283543/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484482311912915/9007199254740992), (15413296306823/9007199254740992)), (44427/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109187753539851/2251799813685248), (30688838241857/4503599627370496)), (713799/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201691278021833/2251799813685248), (22844984787317/1125899906842624)), (1078141/2251799813685248), by norm_num⟩
  | 0 => ⟨((268962453921675/281474976710656), (90013371377843/2251799813685248)), (546549/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((268962453921675/281474976710656), (90013371377843/2251799813685248)), (2084918977977561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((513112763014869/562949953421312), (172023939992611/2251799813685248)), (4352807/2251799813685248), by norm_num⟩
  | 2 => ⟨((1857608771324889/2251799813685248), (78397447781875/562949953421312)), (1074997/281474976710656), by norm_num⟩
  | 3 => ⟨((744376069717617/1125899906842624), (517388040496399/2251799813685248)), (2073037/281474976710656), by norm_num⟩
  | 4 => ⟨((865393333981627/2251799813685248), (85516322046699/281474976710656)), (3693759/281474976710656), by norm_num⟩
  | 5 => ⟨((249463540465353/4503599627370496), (1051677927617893/4503599627370496)), (40668397/2251799813685248), by norm_num⟩
  | 6 => ⟨((-927075665495243/18014398509481984), (466036630180655/18014398509481984)), (187993051/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1596845063/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile003Terms2
