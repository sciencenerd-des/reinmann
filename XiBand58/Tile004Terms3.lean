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
namespace Reinmann.XiBand58.Tile004Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2599/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2599/160))
  have he : value ((15/16), (2599/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-842386043/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((991819461088563/18014398509481984), (54964878500531/18014398509481984)), (130866441/36028797018963968), by norm_num⟩
  | 1 => ⟨((-182733301/1073741824), (-2531689/268435456)), (49/4294967296), by norm_num⟩
  | 2 => ⟨((564836391/2147483648), (62604465/4294967296)), (77/4294967296), by norm_num⟩
  | 3 => ⟨((-1163955509/4294967296), (-64504353/4294967296)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((899458973/4294967296), (99692847/8589934592)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-278026587/2147483648), (-15407741/2147483648)), (5/536870912), by norm_num⟩
  | 6 => ⟨((572927989/8589934592), (63501309/17179869184)), (21/4294967296), by norm_num⟩
  | 7 => ⟨((-1011968421/34359738368), (-112162995/68719476736)), (151/68719476736), by norm_num⟩
  | 8 => ⟨((1564018675/137438953472), (86675145/137438953472)), (119/137438953472), by norm_num⟩
  | 9 => ⟨((-1074321805/274877906944), (-14884253/68719476736)), (83/274877906944), by norm_num⟩
  | 10 => ⟨((1328309723/1099511627776), (73612573/1099511627776)), (13/137438953472), by norm_num⟩
  | 11 => ⟨((-1493040635/4398046511104), (-20685417/1099511627776)), (119/4398046511104), by norm_num⟩
  | 12 => ⟨((769175331/8796093022208), (85252669/17592186044416)), (125/17592186044416), by norm_num⟩
  | 13 => ⟨((-1463109909/70368744177664), (-5067685/4398046511104)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((323038203/70368744177664), (17902205/70368744177664)), (109/281474976710656), by norm_num⟩
  | 15 => ⟨((-520065/549755813888), (-29512787/562949953421312)), (23/281474976710656), by norm_num⟩
  | 16 => ⟨((1646124025/9007199254740992), (45612639/4503599627370496)), (145/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (36057333017/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888750434880101/316912650057057350374175801344), (85228006441/633825300114114700748351602688)), (92209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236039477445325/4951760157141521099596496896), (748888513/309485009821345068724781056)), (12967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472000555001535/618970019642690137449562112), (101818754695/2475880078570760549798248448)), (27555/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769668980017491/154742504910672534362390528), (50892465461/77371252455336267181195264)), (110221/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387031841723013/2417851639229258349412352), (95387450881/9671406556917033397649408)), (103333/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257541424366721/604462909807314587353088), (41714057781/302231454903657293676544)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885766264227655/75557863725914323419136), (135503405881/75557863725914323419136)), (146929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296021005428527/4722366482869645213696), (25392180183/1180591620717411303424)), (110199/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809680844877413/295147905179352825856), (8722591091/36893488147419103232)), (151525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455217186539907/18446744073709551616), (43577161487/18446744073709551616)), (94705/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819728239107185/9223372036854775808), (195900561905/9223372036854775808)), (213091/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795490212552267/576460752303423488), (195655033625/1152921504606846976)), (213097/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191955140635137/144115188075855872), (170922350755/144115188075855872)), (186467/144115188075855872), by norm_num⟩
  | 4 => ⟨((371926805460993/9007199254740992), (255832956213/36028797018963968)), (279715/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484359368132955/9007199254740992), (318830027405/9007199254740992)), (349671/9007199254740992), by norm_num⟩
  | 2 => ⟨((554548641190291/1125899906842624), (634785845841/4503599627370496)), (349713/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100790393687761/1125899906842624), (945025672569/2251799813685248)), (1049361/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076056873483381/1125899906842624), (1861632680993/2251799813685248)), (2099685/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1076056873483381/1125899906842624), (1861632680993/2251799813685248)), (8009662636763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028419597083791/1125899906842624), (1779219120731/1125899906842624)), (4016939/2251799813685248), by norm_num⟩
  | 2 => ⟨((1878752623776783/2251799813685248), (1625174493883/562949953421312)), (3675501/1125899906842624), by norm_num⟩
  | 3 => ⟨((1567487989306383/2251799813685248), (10847503675669/2251799813685248)), (6154411/1125899906842624), by norm_num⟩
  | 4 => ⟨((2182166383842853/4503599627370496), (3775498075413/562949953421312)), (17255043/2251799813685248), by norm_num⟩
  | 5 => ⟨((264285140776803/1125899906842624), (58539946099001/9007199254740992)), (67811617/9007199254740992), by norm_num⟩
  | 6 => ⟨((991819461088563/18014398509481984), (54964878500531/18014398509481984)), (130866441/36028797018963968), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-842386043/16777216)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-854500255/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((748769596916025/18014398509481984), (-589206509800439/18014398509481984)), (102078801/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1119500513/8589934592), (440467263/4294967296)), (77/4294967296), by norm_num⟩
  | 2 => ⟨((438773423/2147483648), (-345270639/2147483648)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((-229295255/1073741824), (360864697/2147483648)), (65/2147483648), by norm_num⟩
  | 4 => ⟨((359476973/2147483648), (-565744585/4294967296)), (103/4294967296), by norm_num⟩
  | 5 => ⟨((-112713797/1073741824), (709555549/8589934592)), (33/2147483648), by norm_num⟩
  | 6 => ⟨((942435889/17179869184), (-92700305/2147483648)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-844286365/34359738368), (664368617/34359738368)), (127/34359738368), by norm_num⟩
  | 8 => ⟨((661813753/68719476736), (-520780989/68719476736)), (101/68719476736), by norm_num⟩
  | 9 => ⟨((-922272531/274877906944), (362867951/137438953472)), (143/274877906944), by norm_num⟩
  | 10 => ⟨((578356037/549755813888), (-910216289/1099511627776)), (91/549755813888), by norm_num⟩
  | 11 => ⟨((-659429821/2199023255552), (259452537/1099511627776)), (53/1099511627776), by norm_num⟩
  | 12 => ⟨((172303199/2199023255552), (-271170643/4398046511104)), (7/549755813888), by norm_num⟩
  | 13 => ⟨((-83116259/4398046511104), (130808305/8796093022208)), (55/17592186044416), by norm_num⟩
  | 14 => ⟨((1191362511/281474976710656), (-937482705/281474976710656)), (199/281474976710656), by norm_num⟩
  | 15 => ⟨((-498068035/562949953421312), (783859093/1125899906842624)), (21/140737488355328), by norm_num⟩
  | 16 => ⟨((780844721/4503599627370496), (-614446413/4503599627370496)), (133/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-434226702451/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777436154955143/633825300114114700748351602688), (-1026302400351/633825300114114700748351602688)), (46151/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888243003165255/39614081257132168796771975168), (-1154299675659/39614081257132168796771975168)), (51923/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((117995302143229/154742504910672534362390528), (-306518977273/618970019642690137449562112)), (13793/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884795786886417/77371252455336267181195264), (-612831356977/77371252455336267181195264)), (110353/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548054776756345/9671406556917033397649408), (-1148619968221/9671406556917033397649408)), (12933/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257477886252683/604462909807314587353088), (-1004603864161/604462909807314587353088)), (90541/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885662974096439/75557863725914323419136), (-1631659352349/75557863725914323419136)), (147145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295943502297635/4722366482869645213696), (-1223025791061/4722366482869645213696)), (55187/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809627532676351/295147905179352825856), (-52515418897/18446744073709551616)), (37947/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820735379511369/73786976294838206464), (-2098867685191/73786976294838206464)), (47443/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819578083583443/9223372036854775808), (-1179411817631/4611686018427387904)), (26693/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1590830122632657/1152921504606846976), (-36809752895/18014398509481984)), (213607/1152921504606846976), by norm_num⟩
  | 5 => ⟨((297955865372215/36028797018963968), (-2057976845423/144115188075855872)), (186977/144115188075855872), by norm_num⟩
  | 4 => ⟨((743754688117563/18014398509481984), (-3080239275699/36028797018963968)), (280607/36028797018963968), by norm_num⟩
  | 3 => ⟨((742055746861705/4503599627370496), (-479819624263/1125899906842624)), (351009/9007199254740992), by norm_num⟩
  | 2 => ⟨((69303035384341/140737488355328), (-7642000952565/4503599627370496)), (702771/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100415247074843/1125899906842624), (-2843903504433/562949953421312)), (1056055/2251799813685248), by norm_num⟩
  | 0 => ⟨((2150596966989585/2251799813685248), (-22404039467545/2251799813685248)), (264973/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2150596966989585/2251799813685248), (-22404039467545/2251799813685248)), (1010791779638194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((256714947823885/281474976710656), (-42794265311145/2251799813685248)), (4091211/2251799813685248), by norm_num⟩
  | 2 => ⟨((234031281841327/281474976710656), (-39029855210913/1125899906842624)), (1904539/562949953421312), by norm_num⟩
  | 3 => ⟨((1553969263467055/2251799813685248), (-8112805578523/140737488355328)), (3299087/562949953421312), by norm_num⟩
  | 4 => ⟨((532456559404589/1125899906842624), (-179156963177843/2251799813685248)), (2466879/281474976710656), by norm_num⟩
  | 5 => ⟨((978721755335229/4503599627370496), (-338905082511505/4503599627370496)), (43612693/4503599627370496), by norm_num⟩
  | 6 => ⟨((748769596916025/18014398509481984), (-589206509800439/18014398509481984)), (102078801/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-854500255/16777216)), (1/16777216), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-433049405/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((386655369293747/36028797018963968), (-55930212664273/1125899906842624)), (278227535/36028797018963968), by norm_num⟩
  | 1 => ⟨((-146485755/4294967296), (1356118977/8589934592)), (213/8589934592), by norm_num⟩
  | 2 => ⟨((232769807/4294967296), (-1077454777/4294967296)), (171/4294967296), by norm_num⟩
  | 3 => ⟨((-7705781/134217728), (570701547/2147483648)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((195915095/4294967296), (-906860119/4294967296)), (147/4294967296), by norm_num⟩
  | 5 => ⟨((-249051487/8589934592), (576410055/4294967296)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((263833011/17179869184), (-1221241455/17179869184)), (101/8589934592), by norm_num⟩
  | 7 => ⟨((-14972777/2147483648), (138613253/4294967296)), (185/34359738368), by norm_num⟩
  | 8 => ⟨((190337165/68719476736), (-881040759/68719476736)), (37/17179869184), by norm_num⟩
  | 9 => ⟨((-268845225/274877906944), (311110551/68719476736)), (211/274877906944), by norm_num⟩
  | 10 => ⟨((341761839/1099511627776), (-1581961725/1099511627776)), (135/549755813888), by norm_num⟩
  | 11 => ⟨((-197479549/2199023255552), (914101731/2199023255552)), (79/1099511627776), by norm_num⟩
  | 12 => ⟨((52300053/2199023255552), (-242088709/2199023255552)), (169/8796093022208), by norm_num⟩
  | 13 => ⟨((-399549/68719476736), (946918091/35184372088832)), (167/35184372088832), by norm_num⟩
  | 14 => ⟨((92875939/70368744177664), (-429908095/70368744177664)), (153/140737488355328), by norm_num⟩
  | 15 => ⟨((-314842383/1125899906842624), (728677903/562949953421312)), (131/562949953421312), by norm_num⟩
  | 16 => ⟨((125073255/2251799813685248), (-36184025/140737488355328)), (105/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (-1768984987311/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777372955952581/633825300114114700748351602688), (-2090375612061/633825300114114700748351602688)), (92407/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((3687835597817/77371252455336267181195264), (-2351071000813/39614081257132168796771975168)), (103971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887849100489891/2475880078570760549798248448), (-1248627007495/1237940039285380274899124224)), (27621/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769515718490327/154742504910672534362390528), (-2496400682711/154742504910672534362390528)), (55251/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547983533486207/9671406556917033397649408), (-2339469358893/9671406556917033397649408)), (51807/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257415419595567/604462909807314587353088), (-2046129840493/604462909807314587353088)), (90681/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471390306149695/18889465931478580854784), (-3323263443609/75557863725914323419136)), (73695/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((20247921553967/73786976294838206464), (-622740786799/1180591620717411303424)), (110573/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202393688075725/73786976294838206464), (-855665960083/147573952589676412928)), (76043/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820602916843391/73786976294838206464), (-4274717078673/73786976294838206464)), (95091/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819428361103473/9223372036854775808), (-4804094106241/9223372036854775808)), (26757/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1590679525159527/1152921504606846976), (-4797898167407/1152921504606846976)), (214183/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595845353867683/72057594037927936), (-523900064819/18014398509481984)), (187553/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487308292161497/36028797018963968), (-3136452559453/18014398509481984)), (281617/36028797018963968), by norm_num⟩
  | 3 => ⟨((741928369569709/4503599627370496), (-488554397761/562949953421312)), (88131/2251799813685248), by norm_num⟩
  | 2 => ⟨((554294375124597/1125899906842624), (-7780591301583/2251799813685248)), (706561/4503599627370496), by norm_num⟩
  | 1 => ⟨((2200026004006773/2251799813685248), (-5790290946431/562949953421312)), (1063643/2251799813685248), by norm_num⟩
  | 0 => ⟨((2148889391313263/2251799813685248), (-45604580464725/2251799813685248)), (2142591/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2148889391313263/2251799813685248), (-45604580464725/2251799813685248)), (8173336037642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64054953540495/70368744177664), (-10880096729775/281474976710656)), (2088065/1125899906842624), by norm_num⟩
  | 2 => ⟨((1862480776945583/2251799813685248), (-39615547992857/562949953421312)), (7925707/2251799813685248), by norm_num⟩
  | 3 => ⟨((1529320838059537/2251799813685248), (-131065285921859/1125899906842624)), (1778289/281474976710656), by norm_num⟩
  | 4 => ⟨((1008131262482341/2251799813685248), (-356054515482871/2251799813685248)), (22635891/2251799813685248), by norm_num⟩
  | 5 => ⟨((197520627498115/1125899906842624), (-318811366822911/2251799813685248)), (107135/8796093022208), by norm_num⟩
  | 6 => ⟨((386655369293747/36028797018963968), (-55930212664273/1125899906842624)), (278227535/36028797018963968), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-433049405/8388608)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-219305955/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-383536998802061/18014398509481984), (-793302498085065/18014398509481984)), (79324515/9007199254740992), by norm_num⟩
  | 1 => ⟨((147170779/2147483648), (608811911/4294967296)), (245/8589934592), by norm_num⟩
  | 2 => ⟨((-473724463/4294967296), (-979844971/4294967296)), (199/4294967296), by norm_num⟩
  | 3 => ⟨((508286741/4294967296), (1051333097/4294967296)), (27/536870912), by norm_num⟩
  | 4 => ⟨((-51128497/536870912), (-846027673/4294967296)), (11/268435456), by norm_num⟩
  | 5 => ⟨((263322053/4294967296), (544651605/4294967296)), (229/8589934592), by norm_num⟩
  | 6 => ⟨((-565067327/17179869184), (-146097157/2147483648)), (31/2147483648), by norm_num⟩
  | 7 => ⟨((519680445/34359738368), (1074899673/34359738368)), (115/17179869184), by norm_num⟩
  | 8 => ⟨((-418196705/68719476736), (-864992143/68719476736)), (187/68719476736), by norm_num⟩
  | 9 => ⟨((299138503/137438953472), (154683461/34359738368)), (269/274877906944), by norm_num⟩
  | 10 => ⟨((-192577939/274877906944), (-796650965/549755813888)), (175/549755813888), by norm_num⟩
  | 11 => ⟨((450825071/2199023255552), (466240097/1099511627776)), (207/2199023255552), by norm_num⟩
  | 12 => ⟨((-483716641/8796093022208), (-1000512651/8796093022208)), (7/274877906944), by norm_num⟩
  | 13 => ⟨((479084247/35184372088832), (7741649/274877906944)), (7/1099511627776), by norm_num⟩
  | 14 => ⟨((-440603629/140737488355328), (-455669153/70368744177664)), (13/8796093022208), by norm_num⟩
  | 15 => ⟨((378199565/562949953421312), (782262625/562949953421312)), (181/562949953421312), by norm_num⟩
  | 16 => ⟨((-304344359/2251799813685248), (-629501563/2251799813685248)), (147/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (-1316374864331/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777311198558205/633825300114114700748351602688), (-3110873040007/633825300114114700748351602688)), (92507/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944051106646175/19807040628566084398385987584), (-1749410338963/19807040628566084398385987584)), (104091/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887774949909121/2475880078570760549798248448), (-3716352441933/2475880078570760549798248448)), (110619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442360339463979/38685626227668133590597632), (-928766360689/38685626227668133590597632)), (110645/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547913597430325/9671406556917033397649408), (-3481506953571/9671406556917033397649408)), (103757/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628677001417157/302231454903657293676544), (-1522476145047/302231454903657293676544)), (45407/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885461005304255/75557863725914323419136), (-618185869271/9444732965739290427392)), (18453/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1295791450585365/4722366482869645213696), (-3706876047007/4722366482869645213696)), (27691/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619045061253753/590295810358705651712), (-2546659160913/295147905179352825856)), (38093/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820471477644011/73786976294838206464), (-6361197746451/73786976294838206464)), (190575/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113704954869963/576460752303423488), (-7148860334493/9223372036854775808)), (53637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397632232141773/288230376151711744), (-446219479037/72057594037927936)), (214737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191557238892889/144115188075855872), (-389785595237/9007199254740992)), (47027/36028797018963968), by norm_num⟩
  | 4 => ⟨((1487104709616363/36028797018963968), (-9333883058173/36028797018963968)), (282587/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483596379447379/9007199254740992), (-726920820425/562949953421312)), (88495/2251799813685248), by norm_num⟩
  | 2 => ⟨((277079908130499/562949953421312), (-23151919434453/4503599627370496)), (710205/4503599627370496), by norm_num⟩
  | 1 => ⟨((2199175308173989/2251799813685248), (-34455113114189/2251799813685248)), (1070943/2251799813685248), by norm_num⟩
  | 0 => ⟨((2147017297520937/2251799813685248), (-33912874360183/1125899906842624)), (2164549/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2147017297520937/2251799813685248), (-33912874360183/1125899906842624)), (8257099160201262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1022533822873013/1125899906842624), (-129339255501235/2251799813685248)), (2129025/1125899906842624), by norm_num⟩
  | 2 => ⟨((924943018324149/1125899906842624), (-234929877108007/2251799813685248)), (513963/140737488355328), by norm_num⟩
  | 3 => ⟨((747598938628161/1125899906842624), (-96499141844753/562949953421312)), (15227191/2251799813685248), by norm_num⟩
  | 4 => ⟨((926646911258291/2251799813685248), (-256302200873171/1125899906842624)), (25442145/2251799813685248), by norm_num⟩
  | 5 => ⟨((264637745253007/2251799813685248), (-210943833767475/1125899906842624)), (32522999/2251799813685248), by norm_num⟩
  | 6 => ⟨((-383536998802061/18014398509481984), (-793302498085065/18014398509481984)), (79324515/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-219305955/4194304)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-887912441/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-752035629800419/18014398509481984), (-197372167434017/9007199254740992)), (154680925/18014398509481984), by norm_num⟩
  | 1 => ⟨((584174319/4294967296), (306633747/4294967296)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((-951648163/4294967296), (-499521175/4294967296)), (199/4294967296), by norm_num⟩
  | 3 => ⟨((1033520529/4294967296), (271248035/2147483648)), (109/2147483648), by norm_num⟩
  | 4 => ⟨((-420913707/2147483648), (-220938071/2147483648)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((1097101993/8589934592), (575870051/8589934592)), (59/2147483648), by norm_num⟩
  | 6 => ⟨((-1191488069/17179869184), (-625413407/17179869184)), (259/17179869184), by norm_num⟩
  | 7 => ⟨((277284511/8589934592), (145546947/8589934592)), (243/34359738368), by norm_num⟩
  | 8 => ⟨((-903419705/68719476736), (-118551501/17179869184)), (25/8589934592), by norm_num⟩
  | 9 => ⟨((1308190495/274877906944), (42916915/17179869184)), (291/274877906944), by norm_num⟩
  | 10 => ⟨((-852442185/549755813888), (-447447847/549755813888)), (191/549755813888), by norm_num⟩
  | 11 => ⟨((504970715/1099511627776), (530119375/2199023255552)), (57/549755813888), by norm_num⟩
  | 12 => ⟨((-274207223/2199023255552), (-143931675/2199023255552)), (125/4398046511104), by norm_num⟩
  | 13 => ⟨((1099561359/35184372088832), (577160975/35184372088832)), (63/8796093022208), by norm_num⟩
  | 14 => ⟨((-511782437/70368744177664), (-8394849/2199023255552)), (237/140737488355328), by norm_num⟩
  | 15 => ⟨((889299513/562949953421312), (466794299/562949953421312)), (13/35184372088832), by norm_num⟩
  | 16 => ⟨((-181088979/562949953421312), (-190107611/1125899906842624)), (171/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (-1731316242067/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777250813448707/633825300114114700748351602688), (-4091218865005/633825300114114700748351602688)), (23151/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472008523502245/9903520314283042199192993792), (-4601399240361/39614081257132168796771975168)), (104205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((235962789597555/309485009821345068724781056), (-1221865522001/618970019642690137449562112)), (110749/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110585527293873/9671406556917033397649408), (-4885747530369/154742504910672534362390528)), (55391/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547844928125773/9671406556917033397649408), (-2289283615795/4835703278458516698824704)), (51947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628646805906207/302231454903657293676544), (-4004425968123/604462909807314587353088)), (90943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885362298032231/75557863725914323419136), (-6503780550843/75557863725914323419136)), (73925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295716920478801/4722366482869645213696), (-304678234255/295147905179352825856)), (110947/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618941771782135/590295810358705651712), (-3349037779555/295147905179352825856)), (19081/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227542644039959/9223372036854775808), (-2091332765685/18446744073709551616)), (95477/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819130997246813/9223372036854775808), (-9401018420877/9223372036854775808)), (215021/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590378572820639/1152921504606846976), (-2347139207967/288230376151711744)), (215269/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191423351089175/144115188075855872), (-1025123086991/18014398509481984)), (5895/4503599627370496), by norm_num⟩
  | 4 => ⟨((1486899244648005/36028797018963968), (-767094615293/2251799813685248)), (2215/281474976710656), by norm_num⟩
  | 3 => ⟨((741665742216423/4503599627370496), (-1911631354415/1125899906842624)), (355381/9007199254740992), by norm_num⟩
  | 2 => ⟨((554021365159209/1125899906842624), (-15219976716273/2251799813685248)), (713713/4503599627370496), by norm_num⟩
  | 1 => ⟨((2198285182592113/2251799813685248), (-22647937315269/1125899906842624)), (538987/1125899906842624), by norm_num⟩
  | 0 => ⟨((2145003051204189/2251799813685248), (-44571702673379/1125899906842624)), (273215/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2145003051204189/2251799813685248), (-44571702673379/1125899906842624)), (1042232514501476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2039742394081429/2251799813685248), (-169831150443691/2251799813685248)), (4337171/2251799813685248), by norm_num⟩
  | 2 => ⟨((917423118485419/1125899906842624), (-1201857354595/8796093022208)), (132995/35184372088832), by norm_num⟩
  | 3 => ⟨((1453058345035353/2251799813685248), (-125352439934793/562949953421312)), (16197231/2251799813685248), by norm_num⟩
  | 4 => ⟨((206497797407577/562949953421312), (-323553466539639/1125899906842624)), (1757315/140737488355328), by norm_num⟩
  | 5 => ⟨((58511875901695/1125899906842624), (-237367736787141/1125899906842624)), (9196901/562949953421312), by norm_num⟩
  | 6 => ⟨((-752035629800419/18014398509481984), (-197372167434017/9007199254740992)), (154680925/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-887912441/16777216)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-224549405/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-406466261188477/9007199254740992), (212023766139573/36028797018963968)), (279177709/36028797018963968), by norm_num⟩
  | 1 => ⟨((1277586449/8589934592), (-166605889/8589934592)), (221/8589934592), by norm_num⟩
  | 2 => ⟨((-1052679129/4294967296), (68638229/2147483648)), (23/536870912), by norm_num⟩
  | 3 => ⟨((1156486227/4294967296), (-37703401/1073741824)), (51/1073741824), by norm_num⟩
  | 4 => ⟨((-952897485/4294967296), (124264259/4294967296)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((157029733/1073741824), (-81910945/4294967296)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((-1380118355/17179869184), (89988371/8589934592)), (125/8589934592), by norm_num⟩
  | 7 => ⟨((324903211/8589934592), (-21184785/4294967296)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((-1070827981/68719476736), (139643191/68719476736)), (197/68719476736), by norm_num⟩
  | 9 => ⟨((392141593/68719476736), (-102275817/137438953472)), (145/137438953472), by norm_num⟩
  | 10 => ⟨((-1033947775/549755813888), (134833763/549755813888)), (193/549755813888), by norm_num⟩
  | 11 => ⟨((1239172071/2199023255552), (-161596395/2199023255552)), (233/2199023255552), by norm_num⟩
  | 12 => ⟨((-1361369665/8796093022208), (177531785/8796093022208)), (129/4398046511104), by norm_num⟩
  | 13 => ⟨((345142487/8796093022208), (-180035631/35184372088832)), (33/4398046511104), by norm_num⟩
  | 14 => ⟨((-650019047/70368744177664), (84766867/70368744177664)), (251/140737488355328), by norm_num⟩
  | 15 => ⟨((1142590261/562949953421312), (-149001475/562949953421312)), (111/281474976710656), by norm_num⟩
  | 16 => ⟨((-29420243/70368744177664), (245542277/4503599627370496)), (23/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (245209941807/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444298452207503/158456325028528675187087900672), (4635311981293/633825300114114700748351602688)), (92657/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((471992461107675/9903520314283042199192993792), (5213319394447/39614081257132168796771975168)), (104269/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887633885525959/2475880078570760549798248448), (86521933079/38685626227668133590597632)), (27705/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884649909444019/77371252455336267181195264), (5535437651081/154742504910672534362390528)), (55429/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((773890200457261/4835703278458516698824704), (5187384532557/9671406556917033397649408)), (51985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257236952726693/604462909807314587353088), (4536873964223/604462909807314587353088)), (91015/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885269856686779/75557863725914323419136), (1842126937139/18889465931478580854784)), (18497/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((647823632964075/2361183241434822606848), (5522959045929/4722366482869645213696)), (111049/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809422735976599/295147905179352825856), (3705327813/288230376151711744)), (152801/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910109995966117/36893488147419103232), (9477308533291/73786976294838206464)), (47791/18446744073709551616), by norm_num⟩
  | 7 => ⟨((454748403564243/2305843009213693952), (10650526080033/9223372036854775808)), (53821/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1590239846854221/1152921504606846976), (5318115763263/576460752303423488)), (215565/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191300460463655/144115188075855872), (72583117549/1125899906842624)), (188937/144115188075855872), by norm_num⟩
  | 4 => ⟨((371677977870307/9007199254740992), (13903876066329/36028797018963968)), (284039/36028797018963968), by norm_num⟩
  | 3 => ⟨((741546051652693/4503599627370496), (2165475122185/1125899906842624)), (356161/9007199254740992), by norm_num⟩
  | 2 => ⟨((2215591175913475/4503599627370496), (17239935316575/2251799813685248)), (715665/4503599627370496), by norm_num⟩
  | 1 => ⟨((1098752686495201/1125899906842624), (12825470159689/562949953421312)), (33809/70368744177664), by norm_num⟩
  | 0 => ⟨((267911553754713/281474976710656), (50470236983885/1125899906842624)), (1098757/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((267911553754713/281474976710656), (50470236983885/1125899906842624)), (4191425327781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((63609027231183/70368744177664), (192152919122481/2251799813685248)), (1095065/562949953421312), by norm_num⟩
  | 2 => ⟨((455890014767449/562949953421312), (173694449259375/1125899906842624)), (8666535/2251799813685248), by norm_num⟩
  | 3 => ⟨((1423169245660357/2251799813685248), (562647280147249/2251799813685248)), (16710727/2251799813685248), by norm_num⟩
  | 4 => ⟨((11857450715305/35184372088832), (711202035272873/2251799813685248)), (29473703/2251799813685248), by norm_num⟩
  | 5 => ⟨((124497269531781/9007199254740992), (1917452000696517/9007199254740992)), (153934355/9007199254740992), by norm_num⟩
  | 6 => ⟨((-406466261188477/9007199254740992), (212023766139573/36028797018963968)), (279177709/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-224549405/4194304)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile004Terms3
