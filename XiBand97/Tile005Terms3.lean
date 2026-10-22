/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile005Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (2127/128)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (2127/128))
  have he : value ((69/80), (2127/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-3447008683/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((569304598757281/18014398509481984), (-557823079801863/9007199254740992)), (42454803/18014398509481984), by norm_num⟩
  | 1 => ⟨((-419555827/4294967296), (822188769/4294967296)), (127/17179869184), by norm_num⟩
  | 2 => ⟨((1296864873/8589934592), (-5082840779/17179869184)), (199/17179869184), by norm_num⟩
  | 3 => ⟨((-2672442919/17179869184), (5237092211/17179869184)), (207/17179869184), by norm_num⟩
  | 4 => ⟨((2065158629/17179869184), (-4047018589/17179869184)), (81/8589934592), by norm_num⟩
  | 5 => ⟨((-1276698599/17179869184), (5003802507/34359738368)), (101/17179869184), by norm_num⟩
  | 6 => ⟨((657721595/17179869184), (-2577827663/34359738368)), (105/34359738368), by norm_num⟩
  | 7 => ⟨((-1161740213/68719476736), (4553242711/137438953472)), (187/137438953472), by norm_num⟩
  | 8 => ⟨((1795494159/274877906944), (-1759283315/137438953472)), (73/137438953472), by norm_num⟩
  | 9 => ⟨((-2466643853/1099511627776), (4833795035/1099511627776)), (203/1099511627776), by norm_num⟩
  | 10 => ⟨((1524900173/2199023255552), (-2988293133/2199023255552)), (127/2199023255552), by norm_num⟩
  | 11 => ⟨((-1714011335/8796093022208), (1679443807/4398046511104)), (145/8796093022208), by norm_num⟩
  | 12 => ⟨((1766027267/35184372088832), (-865205351/8796093022208)), (151/35184372088832), by norm_num⟩
  | 13 => ⟨((-52489089/4398046511104), (822888145/35184372088832)), (145/140737488355328), by norm_num⟩
  | 14 => ⟨((741696011/281474976710656), (-2906951075/562949953421312)), (65/281474976710656), by norm_num⟩
  | 15 => ⟨((-2445454781/4503599627370496), (1198067891/1125899906842624)), (27/562949953421312), by norm_num⟩
  | 16 => ⟨((59054723/562949953421312), (-3703278713/18014398509481984)), (169/18014398509481984), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-178938063271/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777856300301209/633825300114114700748351602688), (-1692457644943/633825300114114700748351602688)), (5773/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888715499253201/39614081257132168796771975168), (-951788219789/19807040628566084398385987584)), (12991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888426646414247/2475880078570760549798248448), (-1011000046261/1237940039285380274899124224)), (27609/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885046572115059/77371252455336267181195264), (-505345444269/38685626227668133590597632)), (6903/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96782796401845/604462909807314587353088), (-1894388708471/9671406556917033397649408)), (12945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628944424871255/302231454903657293676544), (-207116712083/75557863725914323419136)), (11329/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235791288651283/9444732965739290427392), (-2691287067313/75557863725914323419136)), (36825/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296443583477243/4722366482869645213696), (-2017389487941/4722366482869645213696)), (27625/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619941994843055/590295810358705651712), (-1386081740703/295147905179352825856)), (18997/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821593019263505/73786976294838206464), (-1731292866317/36893488147419103232)), (47507/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113783845291629/576460752303423488), (-3891811559005/9223372036854775808)), (53467/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591791811809503/1152921504606846976), (-1943659816675/576460752303423488)), (13373/288230376151711744), by norm_num⟩
  | 5 => ⟨((596331486126231/72057594037927936), (-3396357872119/144115188075855872)), (46835/144115188075855872), by norm_num⟩
  | 4 => ⟨((5815487175397/140737488355328), (-79444682739/562949953421312)), (35155/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485673820293913/9007199254740992), (-6337976738913/9007199254740992)), (21997/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220801318730987/4503599627370496), (-1577913475595/562949953421312)), (88141/2251799813685248), by norm_num⟩
  | 1 => ⟨((275679486225199/281474976710656), (-18803864055327/2251799813685248)), (265191/2251799813685248), by norm_num⟩
  | 0 => ⟨((539901477747137/562949953421312), (-18543212934533/1125899906842624)), (533473/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539901477747137/562949953421312), (-18543212934533/1125899906842624)), (2035038002974700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070575838694271/2251799813685248), (-35568021649845/1125899906842624)), (260209/562949953421312), by norm_num⟩
  | 2 => ⟨((475422364490735/562949953421312), (-65411042145701/1125899906842624)), (989951/1125899906842624), by norm_num⟩
  | 3 => ⟨((1598414013054953/2251799813685248), (-55240918187693/562949953421312)), (3574185/2251799813685248), by norm_num⟩
  | 4 => ⟨((1112933040150445/2251799813685248), (-39212125868651/281474976710656)), (5775641/2251799813685248), by norm_num⟩
  | 5 => ⟨((1012713592709265/4503599627370496), (-155042096330361/1125899906842624)), (7318327/2251799813685248), by norm_num⟩
  | 6 => ⟨((569304598757281/18014398509481984), (-557823079801863/9007199254740992)), (42454803/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-3447008683/67108864)), (1/67108864), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-218536221/4194304)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-19863554087281/1125899906842624), (-1162742599961547/18014398509481984)), (3270697/1125899906842624), by norm_num⟩
  | 1 => ⟨((928075/16777216), (434609973/2147483648)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((-1489906583/17179869184), (-2725434113/8589934592)), (125/8589934592), by norm_num⟩
  | 3 => ⟨((1520701/16777216), (5697055265/17179869184)), (33/2147483648), by norm_num⟩
  | 4 => ⟨((-1220646193/17179869184), (-2232885479/8589934592)), (209/17179869184), by norm_num⟩
  | 5 => ⟨((1530931631/34359738368), (5600959603/34359738368)), (33/4294967296), by norm_num⟩
  | 6 => ⟨((-800037879/34359738368), (-731740685/8589934592)), (139/34359738368), by norm_num⟩
  | 7 => ⟨((1433436653/137438953472), (5244271281/137438953472)), (251/137438953472), by norm_num⟩
  | 8 => ⟨((-280908271/68719476736), (-4110845567/274877906944)), (99/137438953472), by norm_num⟩
  | 9 => ⟨((782921119/549755813888), (2864340555/549755813888)), (139/549755813888), by norm_num⟩
  | 10 => ⟨((-15342779/34359738368), (-3592449297/2199023255552)), (11/137438953472), by norm_num⟩
  | 11 => ⟨((1119585625/8796093022208), (4096037815/8796093022208)), (101/4398046511104), by norm_num⟩
  | 12 => ⟨((-1170151417/35184372088832), (-1070258573/8796093022208)), (213/35184372088832), by norm_num⟩
  | 13 => ⟨((35278875/4398046511104), (2065101271/70368744177664)), (207/140737488355328), by norm_num⟩
  | 14 => ⟨((-1011352763/562949953421312), (-3700064623/562949953421312)), (187/562949953421312), by norm_num⟩
  | 15 => ⟨((845624197/2251799813685248), (6187483319/4503599627370496)), (315/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1325724889/18014398509481984), (-4850204539/18014398509481984)), (249/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-2393695888919/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111112156073697/39614081257132168796771975168), (-353733807627/79228162514264337593543950336)), (1445/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236080729457261/4951760157141521099596496896), (-3182856433555/39614081257132168796771975168)), (26015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888352446015067/2475880078570760549798248448), (-3380851785079/2475880078570760549798248448)), (13823/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442504684601901/38685626227668133590597632), (-844950595677/38685626227668133590597632)), (6913/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548454768900819/9671406556917033397649408), (-3167450134643/9671406556917033397649408)), (12965/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257827405051211/604462909807314587353088), (-2770404708325/604462909807314587353088)), (22695/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943115026785381/37778931862957161709568), (-70309680249/1180591620717411303424)), (18445/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324092008798155/1180591620717411303424), (-1686519242411/2361183241434822606848)), (27679/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619837537409855/590295810358705651712), (-2317481072355/295147905179352825856)), (19037/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821461581162625/73786976294838206464), (-723657135419/9223372036854775808)), (47617/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820392468067045/9223372036854775808), (-813350811533/1152921504606846976)), (53603/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795820636472711/576460752303423488), (-6499179284125/1152921504606846976)), (26823/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192529588214063/144115188075855872), (-5678211499807/144115188075855872)), (46989/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488561328292497/36028797018963968), (-8500202065329/36028797018963968)), (70579/36028797018963968), by norm_num⟩
  | 3 => ⟨((92838363478059/562949953421312), (-5297679228543/4503599627370496)), (88393/9007199254740992), by norm_num⟩
  | 2 => ⟨((277533014344159/562949953421312), (-21101263987153/4503599627370496)), (11081/281474976710656), by norm_num⟩
  | 1 => ⟨((2204587487353089/2251799813685248), (-31429065172061/2251799813685248)), (133611/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157741048568607/2251799813685248), (-61971603734607/2251799813685248)), (539579/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157741048568607/2251799813685248), (-61971603734607/2251799813685248)), (2058330544478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032952823944669/1125899906842624), (-59383019934151/1125899906842624)), (531891/1125899906842624), by norm_num⟩
  | 2 => ⟨((1889093669829063/2251799813685248), (-108961476526559/1125899906842624)), (2064141/2251799813685248), by norm_num⟩
  | 3 => ⟨((48866251044511/70368744177664), (-45705314102651/281474976710656)), (60357/35184372088832), by norm_num⟩
  | 4 => ⟨((1026523708591775/2251799813685248), (-507827133562471/2251799813685248)), (827431/281474976710656), by norm_num⟩
  | 5 => ⟨((706867921279595/4503599627370496), (-231502191846679/1125899906842624)), (4510417/1125899906842624), by norm_num⟩
  | 6 => ⟨((-19863554087281/1125899906842624), (-1162742599961547/18014398509481984)), (3270697/1125899906842624), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-218536221/4194304)), (1/67108864), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-367900379/134217728), (-886010085/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-480560260604385/9007199254740992), (-163243675392333/4503599627370496)), (53158795/18014398509481984), by norm_num⟩
  | 1 => ⟨((2912991289/17179869184), (989527107/8589934592)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((-2314410781/8589934592), (-3144770413/17179869184)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((38308969/134217728), (416427069/2147483648)), (139/8589934592), by norm_num⟩
  | 4 => ⟨((-3895934901/17179869184), (-2646855283/17179869184)), (223/17179869184), by norm_num⟩
  | 5 => ⟨((2476298167/17179869184), (841184857/8589934592)), (285/34359738368), by norm_num⟩
  | 6 => ⟨((-2623269625/34359738368), (-1782220505/34359738368)), (153/34359738368), by norm_num⟩
  | 7 => ⟨((4763938331/137438953472), (1618283629/68719476736)), (35/17179869184), by norm_num⟩
  | 8 => ⟨((-3785013115/274877906944), (-2571496243/274877906944)), (7/8589934592), by norm_num⟩
  | 9 => ⟨((2673105651/549755813888), (227009819/68719476736)), (5/17179869184), by norm_num⟩
  | 10 => ⟨((-3398109461/2199023255552), (-2308638159/2199023255552)), (205/2199023255552), by norm_num⟩
  | 11 => ⟨((1963522689/4398046511104), (1333995699/4398046511104)), (239/8796093022208), by norm_num⟩
  | 12 => ⟨((-4160120535/35184372088832), (-1413170047/17592186044416)), (255/35184372088832), by norm_num⟩
  | 13 => ⟨((4068026769/140737488355328), (690943151/35184372088832)), (63/35184372088832), by norm_num⟩
  | 14 => ⟨((-3693830873/562949953421312), (-2509548031/562949953421312)), (231/562949953421312), by norm_num⟩
  | 15 => ⟨((3130451561/2251799813685248), (2126794329/2251799813685248)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((-4974371787/18014398509481984), (-422441679/2251799813685248)), (317/18014398509481984), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395101303882903/2535301200456458802993406410752), (-3314930321323/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777734027520939/633825300114114700748351602688), (-1959366381429/316912650057057350374175801344)), (23147/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888577607879047/39614081257132168796771975168), (-2203757978005/19807040628566084398385987584)), (26047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888279684009067/2475880078570760549798248448), (-1170418714143/618970019642690137449562112)), (13841/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769945673030721/154742504910672534362390528), (-73128134113/2417851639229258349412352)), (13845/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387096487015919/2417851639229258349412352), (-4386122102083/9671406556917033397649408)), (1623/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314441716273343/151115727451828646838272), (-1918145711833/302231454903657293676544)), (22731/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943065536792937/37778931862957161709568), (-6231039533189/75557863725914323419136)), (36953/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324073318412705/1180591620717411303424), (-4670713497351/4722366482869645213696)), (27729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619733885916983/590295810358705651712), (-3209031584033/295147905179352825856)), (38151/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227666342183485/9223372036854775808), (-1002041351335/9223372036854775808)), (23861/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455060878363575/2305843009213693952), (-1126223368307/1152921504606846976)), (26867/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397872532359091/288230376151711744), (-8999064409773/1152921504606846976)), (26897/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192394882581379/144115188075855872), (-7862130852763/144115188075855872)), (47137/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488354378298997/36028797018963968), (-11769126127493/36028797018963968)), (35419/18014398509481984), by norm_num⟩
  | 3 => ⟨((371286652415661/2251799813685248), (-916834643817/562949953421312)), (44391/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109852156824079/2251799813685248), (-3651603251999/562949953421312)), (178269/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203684892922267/2251799813685248), (-1359546972975/70368744177664)), (269171/2251799813685248), by norm_num⟩
  | 0 => ⟨((134730484477505/140737488355328), (-42880940524355/1125899906842624)), (545447/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((134730484477505/140737488355328), (-42880940524355/1125899906842624)), (2080715188033293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060411655659977/2251799813685248), (-164202728333789/2251799813685248)), (1085881/2251799813685248), by norm_num⟩
  | 2 => ⟨((1873316459638387/2251799813685248), (-300493155114363/2251799813685248)), (268193/281474976710656), by norm_num⟩
  | 3 => ⟨((1518349189347353/2251799813685248), (-249986153326457/1125899906842624)), (4142469/2251799813685248), by norm_num⟩
  | 4 => ⟨((912786270289313/2251799813685248), (-84280643186949/281474976710656)), (3712957/1125899906842624), by norm_num⟩
  | 5 => ⟨((84059927686187/1125899906842624), (-546622046842057/2251799813685248)), (2616831/562949953421312), by norm_num⟩
  | 6 => ⟨((-480560260604385/9007199254740992), (-163243675392333/4503599627370496)), (53158795/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-367900379/134217728), (-886010085/16777216)), (1/67108864), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-372626047/134217728), (-3589563419/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-559009829562563/9007199254740992), (11427492390203/2251799813685248)), (46850559/18014398509481984), by norm_num⟩
  | 1 => ⟨((6864102273/34359738368), (-561274399/34359738368)), (145/17179869184), by norm_num⟩
  | 2 => ⟨((-5523673217/17179869184), (451668149/17179869184)), (59/4294967296), by norm_num⟩
  | 3 => ⟨((740834091/2147483648), (-484621229/17179869184)), (255/17179869184), by norm_num⟩
  | 4 => ⟨((-1192326473/4294967296), (194991945/8589934592)), (207/17179869184), by norm_num⟩
  | 5 => ⟨((6140721375/34359738368), (-251061943/17179869184)), (67/8589934592), by norm_num⟩
  | 6 => ⟨((-6588739861/68719476736), (269379073/34359738368)), (145/34359738368), by norm_num⟩
  | 7 => ⟨((94680069/2147483648), (-495484449/137438953472)), (67/34359738368), by norm_num⟩
  | 8 => ⟨((-4876214163/274877906944), (398725729/274877906944)), (109/137438953472), by norm_num⟩
  | 9 => ⟨((3487983975/549755813888), (-142605401/274877906944)), (157/549755813888), by norm_num⟩
  | 10 => ⟨((-2245477459/1099511627776), (183611631/1099511627776)), (51/549755813888), by norm_num⟩
  | 11 => ⟨((5256664079/8796093022208), (-214917469/4398046511104)), (241/8796093022208), by norm_num⟩
  | 12 => ⟨((-5640182975/35184372088832), (461195097/35184372088832)), (261/35184372088832), by norm_num⟩
  | 13 => ⟨((698271101/17592186044416), (-28548649/8796093022208)), (65/35184372088832), by norm_num⟩
  | 14 => ⟨((-2568740533/281474976710656), (420089399/562949953421312)), (241/562949953421312), by norm_num⟩
  | 15 => ⟨((1102460907/562949953421312), (-180295415/1125899906842624)), (209/2251799813685248), by norm_num⟩
  | 16 => ⟨((-7097369523/18014398509481984), (580348553/18014398509481984)), (169/9007199254740992), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351916683/10141204801825835211973625643008), (1992998849113/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777676138522531/633825300114114700748351602688), (2355879251225/316912650057057350374175801344)), (23167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888512298360191/39614081257132168796771975168), (662428719981/4951760157141521099596496896)), (13035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472052510494719/618970019642690137449562112), (5629046579649/2475880078570760549798248448)), (6927/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884937874669079/77371252455336267181195264), (5627249690347/154742504910672534362390528)), (13859/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548320095608771/9671406556917033397649408), (5273637877665/9671406556917033397649408)), (6499/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257708945509339/604462909807314587353088), (1153131245917/151115727451828646838272)), (22757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886036394877867/75557863725914323419136), (3745888231991/37778931862957161709568)), (36999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162027721976337/590295810358705651712), (1403925989315/1180591620717411303424)), (13883/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809817391646633/295147905179352825856), (7716511490159/590295810358705651712)), (19103/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821205671683275/73786976294838206464), (9638021008893/73786976294838206464)), (23899/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910050592546885/4611686018427387904), (10832304612547/9223372036854775808)), (53831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591345769578365/1152921504606846976), (10819227658939/1152921504606846976)), (26951/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192266289402241/144115188075855872), (9452125455429/144115188075855872)), (47245/144115188075855872), by norm_num⟩
  | 4 => ⟨((186019618715235/4503599627370496), (14148822773973/36028797018963968)), (17757/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484891920990975/9007199254740992), (8817355616631/4503599627370496)), (44533/4503599627370496), by norm_num⟩
  | 2 => ⟨((17337276460175/35184372088832), (17557879956443/2251799813685248)), (44745/1125899906842624), by norm_num⟩
  | 1 => ⟨((137676699095325/140737488355328), (3268156030629/140737488355328)), (67649/562949953421312), by norm_num⟩
  | 0 => ⟨((1076871195184183/1125899906842624), (51527252610741/1125899906842624)), (274869/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1076871195184183/1125899906842624), (51527252610741/1125899906842624)), (1048542027000045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1027619334742091/1125899906842624), (98566868628833/1125899906842624)), (550959/1125899906842624), by norm_num⟩
  | 2 => ⟨((929288707802275/1125899906842624), (359851597295249/2251799813685248)), (1102199/1125899906842624), by norm_num⟩
  | 3 => ⟨((184564410294871/281474976710656), (594024431157235/2251799813685248)), (4343461/2251799813685248), by norm_num⟩
  | 4 => ⟨((811454172401541/2251799813685248), (389504495634019/1125899906842624)), (499229/140737488355328), by norm_num⟩
  | 5 => ⟨((1432267233465/140737488355328), (280722154989539/1125899906842624)), (11283495/2251799813685248), by norm_num⟩
  | 6 => ⟨((-559009829562563/9007199254740992), (11427492390203/2251799813685248)), (46850559/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-372626047/134217728), (-3589563419/67108864)), (1/67108864), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-377166347/134217728), (-908325203/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-805686687192223/18014398509481984), (725863333838475/18014398509481984)), (6238097/2251799813685248), by norm_num⟩
  | 1 => ⟨((2503399855/17179869184), (-1127687843/8589934592)), (157/17179869184), by norm_num⟩
  | 2 => ⟨((-127442475/536870912), (3674115857/17179869184)), (129/8589934592), by norm_num⟩
  | 3 => ⟨((1107253031/4294967296), (-3990208051/17179869184)), (283/17179869184), by norm_num⟩
  | 4 => ⟨((-3607537267/17179869184), (3250120759/17179869184)), (29/2147483648), by norm_num⟩
  | 5 => ⟨((293842617/2147483648), (-2117841439/17179869184)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((-1276490151/17179869184), (2300043953/34359738368)), (21/4294967296), by norm_num⟩
  | 7 => ⟨((2376530367/68719476736), (-2141075783/68719476736)), (79/34359738368), by norm_num⟩
  | 8 => ⟨((-3871482681/274877906944), (1743957899/137438953472)), (259/274877906944), by norm_num⟩
  | 9 => ⟨((700759129/137438953472), (-315665733/68719476736)), (95/274877906944), by norm_num⟩
  | 10 => ⟨((-3653025427/2199023255552), (1645551091/1099511627776)), (125/1099511627776), by norm_num⟩
  | 11 => ⟨((2163983545/4398046511104), (-1949587023/4398046511104)), (149/4398046511104), by norm_num⟩
  | 12 => ⟨((-2350155765/17592186044416), (2117314243/17592186044416)), (41/4398046511104), by norm_num⟩
  | 13 => ⟨((2356010573/70368744177664), (-1061294493/35184372088832)), (83/35184372088832), by norm_num⟩
  | 14 => ⟨((-4386348509/562949953421312), (1975885665/281474976710656)), (311/562949953421312), by norm_num⟩
  | 15 => ⟨((476371563/281474976710656), (-429175083/281474976710656)), (17/140737488355328), by norm_num⟩
  | 16 => ⟨((-388016135/1125899906842624), (349573463/1125899906842624)), (7/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287337695/10141204801825835211973625643008), (3137036260169/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777628585773817/633825300114114700748351602688), (1854006479155/316912650057057350374175801344)), (11571/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944229531381215/19807040628566084398385987584), (4170492000895/39614081257132168796771975168)), (26041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888153828961187/2475880078570760549798248448), (1107469125911/618970019642690137449562112)), (27675/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884909964719561/77371252455336267181195264), (4428446832809/154742504910672534362390528)), (27683/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193533522725073/1208925819614629174706176), (259384398481/604462909807314587353088)), (25961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257663937890465/604462909807314587353088), (3629863605357/604462909807314587353088)), (5681/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885964038488085/75557863725914323419136), (5895683341339/75557863725914323419136)), (36941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648084095535311/2361183241434822606848), (1104818574563/1180591620717411303424)), (3465/590295810358705651712), by norm_num⟩
  | 9 => ⟨((50611319121765/18446744073709551616), (6072461038995/590295810358705651712)), (38135/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455279154049779/18446744073709551616), (1896129623699/18446744073709551616)), (23851/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227500409267235/1152921504606846976), (8524260125297/9223372036854775808)), (26855/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591250697708727/1152921504606846976), (8513865593391/1152921504606846976)), (26883/576460752303423488), by norm_num⟩
  | 5 => ⟨((596093143285669/72057594037927936), (3718975763077/72057594037927936)), (11777/36028797018963968), by norm_num⟩
  | 4 => ⟨((23250676458245/562949953421312), (11133597985159/36028797018963968)), (70789/36028797018963968), by norm_num⟩
  | 3 => ⟨((742380454627185/4503599627370496), (13876244119731/9007199254740992)), (22177/2251799813685248), by norm_num⟩
  | 2 => ⟨((2218942340232917/4503599627370496), (6907629894175/1125899906842624)), (89041/2251799813685248), by norm_num⟩
  | 1 => ⟨((550641340386241/562949953421312), (5142734564549/281474976710656)), (67199/562949953421312), by norm_num⟩
  | 0 => ⟨((2153541567720555/2251799813685248), (81074245091529/2251799813685248)), (272161/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153541567720555/2251799813685248), (81074245091529/2251799813685248)), (1038211826804732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1028325924564287/1125899906842624), (155073071607045/2251799813685248)), (1080337/2251799813685248), by norm_num⟩
  | 2 => ⟨((466934176988769/562949953421312), (141633957660171/1125899906842624)), (1061111/1125899906842624), by norm_num⟩
  | 3 => ⟨((1513544711070539/2251799813685248), (469908453153167/2251799813685248)), (4054455/2251799813685248), by norm_num⟩
  | 4 => ⟨((114908285001869/281474976710656), (631696876103151/2251799813685248)), (7142573/2251799813685248), by norm_num⟩
  | 5 => ⟨((396136057551331/4503599627370496), (515763109902787/2251799813685248)), (19678247/4503599627370496), by norm_num⟩
  | 6 => ⟨((-805686687192223/18014398509481984), (725863333838475/18014398509481984)), (6238097/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-377166347/134217728), (-908325203/16777216)), (1/67108864), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-1837693669/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-109581568702821/9007199254740992), (1026574143257755/18014398509481984)), (45127013/18014398509481984), by norm_num⟩
  | 1 => ⟨((1377727409/34359738368), (-6453363241/34359738368)), (143/17179869184), by norm_num⟩
  | 2 => ⟨((-283797799/4294967296), (664663515/2147483648)), (119/8589934592), by norm_num⟩
  | 3 => ⟨((623567499/8589934592), (-5841660043/17179869184)), (263/17179869184), by norm_num⟩
  | 4 => ⟨((-128448547/2147483648), (150415301/536870912)), (109/8589934592), by norm_num⟩
  | 5 => ⟨((1354705461/34359738368), (-3172763483/17179869184)), (289/34359738368), by norm_num⟩
  | 6 => ⟨((-1488296067/68719476736), (6971273903/68719476736)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((1401480299/137438953472), (-6564623295/137438953472)), (19/8589934592), by norm_num⟩
  | 8 => ⟨((-1154762609/274877906944), (5408981867/274877906944)), (63/68719476736), by norm_num⟩
  | 9 => ⟨((845757595/549755813888), (-495197829/68719476736)), (93/274877906944), by norm_num⟩
  | 10 => ⟨((-139373953/274877906944), (2611346017/1099511627776)), (247/2199023255552), by norm_num⟩
  | 11 => ⟨((83518875/549755813888), (-1564830995/2199023255552)), (149/4398046511104), by norm_num⟩
  | 12 => ⟨((-1468077799/35184372088832), (6876570243/35184372088832)), (165/17592186044416), by norm_num⟩
  | 13 => ⟨((93048941/8796093022208), (-3486777495/70368744177664)), (21/8796093022208), by norm_num⟩
  | 14 => ⟨((-21905295/8796093022208), (6566771321/562949953421312)), (319/562949953421312), by norm_num⟩
  | 15 => ⟨((1232149825/2251799813685248), (-721433567/281474976710656)), (141/1125899906842624), by norm_num⟩
  | 16 => ⟨((-253810301/2251799813685248), (4755454693/9007199254740992)), (117/4503599627370496), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1160059427073/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777581810417971/633825300114114700748351602688), (2742259679483/633825300114114700748351602688)), (11559/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472101658975723/9903520314283042199192993792), (1542141833915/19807040628566084398385987584)), (26013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472024596864165/618970019642690137449562112), (1638050529043/1237940039285380274899124224)), (27643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442441195597151/38685626227668133590597632), (818758101043/38685626227668133590597632)), (27649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548216794040501/9671406556917033397649408), (3069207863671/9671406556917033397649408)), (25927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628809642955135/302231454903657293676544), (671105587173/151115727451828646838272)), (5673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942946031992837/37778931862957161709568), (1090015023879/18889465931478580854784)), (36885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324028680355849/1180591620717411303424), (3268185654125/4722366482869645213696)), (13837/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619489520727225/590295810358705651712), (4490735643639/590295810358705651712)), (9517/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28453546790881/1152921504606846976), (1402223367765/18446744073709551616)), (47609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909952077429053/4611686018427387904), (3151893625385/4611686018427387904)), (53593/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795576852390689/576460752303423488), (6296023054953/1152921504606846976)), (53635/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596051901590757/72057594037927936), (5500296695715/144115188075855872)), (23489/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487924322305973/36028797018963968), (4116513082151/18014398509481984)), (70559/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484620477419985/9007199254740992), (5130431374471/4503599627370496)), (88363/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218686172160933/4503599627370496), (20430717520519/4503599627370496)), (44305/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202242324589771/2251799813685248), (15209717996857/1125899906842624)), (267071/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153137227120461/2251799813685248), (59937573073861/2251799813685248)), (67391/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153137227120461/2251799813685248), (59937573073861/2251799813685248)), (257076264501476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2057202144698957/2251799813685248), (57311408902453/1125899906842624)), (529857/1125899906842624), by norm_num⟩
  | 2 => ⟨((468396685192879/562949953421312), (209434520055121/2251799813685248)), (2044155/2251799813685248), by norm_num⟩
  | 3 => ⟨((1539419461684283/2251799813685248), (87128912936745/562949953421312)), (3781881/2251799813685248), by norm_num⟩
  | 4 => ⟨((249616895986427/562949953421312), (238259091123575/1125899906842624)), (6341547/2251799813685248), by norm_num⟩
  | 5 => ⟨((683780088708953/4503599627370496), (845169193536521/4503599627370496)), (16615495/4503599627370496), by norm_num⟩
  | 6 => ⟨((-109581568702821/9007199254740992), (1026574143257755/18014398509481984)), (45127013/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1837693669/33554432)), (1/67108864), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile005Terms3
