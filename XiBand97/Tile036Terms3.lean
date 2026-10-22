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
namespace Reinmann.XiBand97.Tile036Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33263/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33263/1280))
  have he : value ((69/80), (33263/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-673823753/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((267755380414605/18014398509481984), (1223552708047351/18014398509481984)), (378370277/18014398509481984), by norm_num⟩
  | 1 => ⟨((-197325527/4294967296), (-901711789/4294967296)), (35/536870912), by norm_num⟩
  | 2 => ⟨((304970791/4294967296), (696807355/2147483648)), (435/4294967296), by norm_num⟩
  | 3 => ⟨((-314225887/4294967296), (-1435907411/4294967296)), (225/2147483648), by norm_num⟩
  | 4 => ⟨((242821389/4294967296), (277403173/1073741824)), (175/2147483648), by norm_num⟩
  | 5 => ⟨((-300228489/8589934592), (-1371943975/8589934592)), (435/8589934592), by norm_num⟩
  | 6 => ⟨((77334917/4294967296), (1413579023/17179869184)), (451/17179869184), by norm_num⟩
  | 7 => ⟨((-136597435/17179869184), (-1248409363/34359738368)), (25/2147483648), by norm_num⟩
  | 8 => ⟨((211114235/68719476736), (964721585/68719476736)), (311/68719476736), by norm_num⟩
  | 9 => ⟨((-72507007/68719476736), (-662665639/137438953472)), (429/274877906944), by norm_num⟩
  | 10 => ⟨((358595579/1099511627776), (819331049/549755813888)), (133/274877906944), by norm_num⟩
  | 11 => ⟨((-201533483/2199023255552), (-230235187/549755813888)), (301/2199023255552), by norm_num⟩
  | 12 => ⟨((207649517/8796093022208), (948888983/8796093022208)), (39/1099511627776), by norm_num⟩
  | 13 => ⟨((-1542917/274877906944), (-902478809/35184372088832)), (149/17592186044416), by norm_num⟩
  | 14 => ⟨((43604315/35184372088832), (1594057321/281474976710656)), (33/17592186044416), by norm_num⟩
  | 15 => ⟨((-35942077/140737488355328), (-1313946361/1125899906842624)), (437/1125899906842624), by norm_num⟩
  | 16 => ⟨((55549243/1125899906842624), (253841499/1125899906842624)), (339/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (882752636151/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444463874954783/158456325028528675187087900672), (2087344386669/633825300114114700748351602688)), (184811/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236089319366309/4951760157141521099596496896), (586930168437/9903520314283042199192993792)), (207939/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888425584408491/2475880078570760549798248448), (1246887461189/1237940039285380274899124224)), (220967/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770092016305951/154742504910672534362390528), (2493012185379/154742504910672534362390528)), (221001/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548523615019511/9671406556917033397649408), (1168194408891/4835703278458516698824704)), (207225/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257887793342073/604462909807314587353088), (2043530449413/604462909807314587353088)), (90679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886328461602573/75557863725914323419136), (3319219390667/75557863725914323419136)), (36847/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296442083320793/4722366482869645213696), (1244043686805/2361183241434822606848)), (221143/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619939746401599/590295810358705651712), (854741210143/147573952589676412928)), (304169/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821589930569723/73786976294838206464), (2135237734091/36893488147419103232)), (190179/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910268834083343/4611686018427387904), (599980836309/1152921504606846976)), (428105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795893739624701/576460752303423488), (4794304681061/1152921504606846976)), (214179/576460752303423488), by norm_num⟩
  | 5 => ⟨((298164661796811/36028797018963968), (523598717481/18014398509481984)), (375099/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488757164878615/36028797018963968), (6270750634575/36028797018963968)), (563219/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485662525880817/9007199254740992), (7816723178017/9007199254740992)), (705025/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220773200082809/4503599627370496), (973029877661/281474976710656)), (1413061/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205380003447907/2251799813685248), (1449432149665/140737488355328)), (2127151/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159439997930279/2251799813685248), (11434578709363/562949953421312)), (535587/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159439997930279/2251799813685248), (11434578709363/562949953421312)), (2043102265478038699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((517484845110267/562949953421312), (43862312225827/1125899906842624)), (2097993/562949953421312), by norm_num⟩
  | 2 => ⟨((1899348868834835/2251799813685248), (80639785865203/1125899906842624)), (16082297/2251799813685248), by norm_num⟩
  | 3 => ⟨((49703505551427/70368744177664), (272072295477267/2251799813685248)), (29433913/2251799813685248), by norm_num⟩
  | 4 => ⟨((545276191593143/1125899906842624), (48043158246869/281474976710656)), (12173185/562949953421312), by norm_num⟩
  | 5 => ⟨((925111735657619/4503599627370496), (744557563648397/4503599627370496)), (127572281/4503599627370496), by norm_num⟩
  | 6 => ⟨((267755380414605/18014398509481984), (1223552708047351/18014398509481984)), (378370277/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-673823753/8388608)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-683513899/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1181319116161421/18014398509481984), (119857268748587/9007199254740992)), (180870935/18014398509481984), by norm_num⟩
  | 1 => ⟨((-13798547/67108864), (-89600509/2147483648)), (273/8589934592), by norm_num⟩
  | 2 => ⟨((692244229/2147483648), (140470939/2147483648)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-1447018517/4294967296), (-18351909/268435456)), (57/1073741824), by norm_num⟩
  | 4 => ⟨((1134279547/4294967296), (115084609/2147483648)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-1422610783/8589934592), (-288677701/8589934592)), (57/2147483648), by norm_num⟩
  | 6 => ⟨((1486862627/17179869184), (150857877/8589934592)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((-1332014047/34359738368), (-270293715/34359738368)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((1044130585/68719476736), (211876095/68719476736)), (43/17179869184), by norm_num⟩
  | 9 => ⟨((-1455051293/274877906944), (-295260565/274877906944)), (121/137438953472), by norm_num⟩
  | 10 => ⟨((456230491/274877906944), (185157559/549755813888)), (77/274877906944), by norm_num⟩
  | 11 => ⟨((-520184751/1099511627776), (-211112893/2199023255552)), (177/2199023255552), by norm_num⟩
  | 12 => ⟨((543678759/4398046511104), (27580969/1099511627776)), (187/8796093022208), by norm_num⟩
  | 13 => ⟨((-1049047141/35184372088832), (-212873769/35184372088832)), (91/17592186044416), by norm_num⟩
  | 14 => ⟨((939794641/140737488355328), (190704135/140737488355328)), (165/140737488355328), by norm_num⟩
  | 15 => ⟨((-49112011/35184372088832), (-79726895/281474976710656)), (139/562949953421312), by norm_num⟩
  | 16 => ⟨((1231923411/4503599627370496), (124991609/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (4074786931/158456325028528675187087900672)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888899370892387/316912650057057350374175801344), (308306343491/633825300114114700748351602688)), (46115/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944325421248753/19807040628566084398385987584), (346763991785/39614081257132168796771975168)), (207523/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236044759596419/309485009821345068724781056), (368335169411/2475880078570760549798248448)), (110249/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885012359305037/77371252455336267181195264), (5753452525/2417851639229258349412352)), (220503/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774230373159769/4835703278458516698824704), (172542927867/4835703278458516698824704)), (206727/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628916502962515/302231454903657293676544), (9432152635/18889465931478580854784)), (45223/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943119924595435/37778931862957161709568), (490244732671/75557863725914323419136)), (36745/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296375988597795/4722366482869645213696), (367484865237/4722366482869645213696)), (3445/73786976294838206464), by norm_num⟩
  | 9 => ⟨((809924728918261/295147905179352825856), (252484525873/295147905179352825856)), (303173/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821477956030973/73786976294838206464), (630727749401/73786976294838206464)), (378989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820412913098547/9223372036854775808), (354452225829/4611686018427387904)), (213197/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99479015078589/72057594037927936), (708075071371/1152921504606846976)), (426433/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149069064518473/18014398509481984), (309316971487/72057594037927936)), (373173/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488601361482651/36028797018963968), (926090691377/36028797018963968)), (559849/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485473684439019/9007199254740992), (1154365308309/9007199254740992)), (699969/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220413155008475/4503599627370496), (2299015718363/4503599627370496)), (1400415/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204883679738567/2251799813685248), (1712169233859/1125899906842624)), (2101841/2251799813685248), by norm_num⟩
  | 0 => ⟨((539655058547721/562949953421312), (3376273429643/1125899906842624)), (4208685/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539655058547721/562949953421312), (3376273429643/1125899906842624)), (16054859169966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((517319045220035/562949953421312), (12946252321535/2251799813685248)), (4047151/1125899906842624), by norm_num⟩
  | 2 => ⟨((1901472893499057/2251799813685248), (5948435424367/562949953421312)), (7484741/1125899906842624), by norm_num⟩
  | 3 => ⟨((802698579286989/1125899906842624), (20091996898521/1125899906842624)), (1599845/140737488355328), by norm_num⟩
  | 4 => ⟨((571917021163753/1125899906842624), (28648758681771/1125899906842624)), (2338285/140737488355328), by norm_num⟩
  | 5 => ⟨((1159137950860207/4503599627370496), (116420386044905/4503599627370496)), (9978109/562949953421312), by norm_num⟩
  | 6 => ⟨((1181319116161421/18014398509481984), (119857268748587/9007199254740992)), (180870935/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-683513899/8388608)), (1/8388608), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1385583143/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((358502571934153/9007199254740992), (-914348019738647/18014398509481984)), (143028423/9007199254740992), by norm_num⟩
  | 1 => ⟨((-543279873/4294967296), (692807967/4294967296)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((863286341/4294967296), (-550445253/2147483648)), (351/4294967296), by norm_num⟩
  | 3 => ⟨((-914523487/4294967296), (1166229763/4294967296)), (187/2147483648), by norm_num⟩
  | 4 => ⟨((363300609/2147483648), (-926585241/4294967296)), (299/4294967296), by norm_num⟩
  | 5 => ⟨((-923671113/8589934592), (588947555/4294967296)), (383/8589934592), by norm_num⟩
  | 6 => ⟨((244623043/4294967296), (-77987793/1073741824)), (205/8589934592), by norm_num⟩
  | 7 => ⟨((-888485941/34359738368), (141628231/4294967296)), (187/17179869184), by norm_num⟩
  | 8 => ⟨((705914037/68719476736), (-225051071/17179869184)), (299/68719476736), by norm_num⟩
  | 9 => ⟨((-31158789/8589934592), (317877519/68719476736)), (213/137438953472), by norm_num⟩
  | 10 => ⟨((79219447/68719476736), (-808185493/549755813888)), (273/549755813888), by norm_num⟩
  | 11 => ⟨((-732403395/2199023255552), (233496091/549755813888)), (317/2199023255552), by norm_num⟩
  | 12 => ⟨((775872471/8796093022208), (-123677191/1099511627776)), (169/4398046511104), by norm_num⟩
  | 13 => ⟨((-379348381/17592186044416), (60469657/2199023255552)), (333/35184372088832), by norm_num⟩
  | 14 => ⟨((688908329/140737488355328), (-878518057/140737488355328)), (19/8796093022208), by norm_num⟩
  | 15 => ⟨((-291918367/281474976710656), (186131845/140737488355328)), (259/562949953421312), by norm_num⟩
  | 16 => ⟨((231933071/1125899906842624), (-591537023/2251799813685248)), (207/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-294970563439/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777741222116859/633825300114114700748351602688), (-1394793493709/633825300114114700748351602688)), (184675/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586093683739/39614081257132168796771975168), (-49024135237/1237940039285380274899124224)), (207777/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888289227185175/2475880078570760549798248448), (-1666354756109/2475880078570760549798248448)), (13799/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769955808396401/154742504910672534362390528), (-52057217209/4835703278458516698824704)), (220807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548396078641069/9671406556917033397649408), (-48786256177/302231454903657293676544)), (207031/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628888178712417/302231454903657293676544), (-341364776799/151115727451828646838272)), (181177/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471536918750555/18889465931478580854784), (-2217828962913/75557863725914323419136)), (147229/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648153376389679/2361183241434822606848), (-1662460433395/4722366482869645213696)), (55221/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101234630497383/36893488147419103232), (-2284403257297/590295810358705651712)), (303781/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910679244119085/36893488147419103232), (-2853286072271/73786976294838206464)), (379825/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910139080700945/4611686018427387904), (-801724984353/2305843009213693952)), (427439/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795764526365909/576460752303423488), (-3203095598521/1152921504606846976)), (427609/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596216868206659/72057594037927936), (-1399217321655/72057594037927936)), (374349/144115188075855872), by norm_num⟩
  | 4 => ⟨((372105554116721/9007199254740992), (-4189118622689/36028797018963968)), (561907/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485248055471225/9007199254740992), (-1305374468885/2251799813685248)), (703057/9007199254740992), by norm_num⟩
  | 2 => ⟨((554989210237107/1125899906842624), (-10398426037745/4503599627370496)), (1408139/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102093348560005/1125899906842624), (-1935834213267/281474976710656)), (529325/562949953421312), by norm_num⟩
  | 0 => ⟨((2157176990661893/2251799813685248), (-15266114616981/1125899906842624)), (4255113/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157176990661893/2251799813685248), (-15266114616981/1125899906842624)), (16231967934615325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033058161685553/1125899906842624), (-29249235201475/1125899906842624)), (8268009/2251799813685248), by norm_num⟩
  | 2 => ⟨((1894224595249595/2251799813685248), (-107349369031141/2251799813685248)), (1950255/281474976710656), by norm_num⟩
  | 3 => ⟨((397078251414785/562949953421312), (-180605588354255/2251799813685248)), (27736603/2251799813685248), by norm_num⟩
  | 4 => ⟨((276458836423597/562949953421312), (-254781267086365/2251799813685248)), (43577403/2251799813685248), by norm_num⟩
  | 5 => ⟨((128559198589883/562949953421312), (-125120416500881/1125899906842624)), (105323999/4503599627370496), by norm_num⟩
  | 6 => ⟨((358502571934153/9007199254740992), (-914348019738647/18014398509481984)), (143028423/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1385583143/16777216)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-87711307/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-432503135664169/18014398509481984), (-517510043948295/9007199254740992)), (399183747/18014398509481984), by norm_num⟩
  | 1 => ⟨((41490015/536870912), (397157805/2147483648)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((-534204825/4294967296), (-1278401657/4294967296)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((286589833/2147483648), (1371672063/4294967296)), (67/536870912), by norm_num⟩
  | 4 => ⟨((-461248543/4294967296), (-1103810511/4294967296)), (433/4294967296), by norm_num⟩
  | 5 => ⟨((296940357/4294967296), (355302897/2147483648)), (559/8589934592), by norm_num⟩
  | 6 => ⟨((-39825589/1073741824), (-190612651/2147483648)), (301/8589934592), by norm_num⟩
  | 7 => ⟨((586028003/34359738368), (350604831/8589934592)), (555/34359738368), by norm_num⟩
  | 8 => ⟨((-471587843/68719476736), (-1128553415/68719476736)), (7/1073741824), by norm_num⟩
  | 9 => ⟨((337329491/137438953472), (403630367/68719476736)), (323/137438953472), by norm_num⟩
  | 10 => ⟨((-217164349/274877906944), (-1039388825/549755813888)), (209/274877906944), by norm_num⟩
  | 11 => ⟨((508381871/2199023255552), (304151233/549755813888)), (123/549755813888), by norm_num⟩
  | 12 => ⟨((-545472705/8796093022208), (-1305366735/8796093022208)), (265/4398046511104), by norm_num⟩
  | 13 => ⟨((540248893/35184372088832), (646432835/17592186044416)), (527/35184372088832), by norm_num⟩
  | 14 => ⟨((-248427729/70368744177664), (-1189021157/140737488355328)), (487/140737488355328), by norm_num⟩
  | 15 => ⟨((426484273/562949953421312), (1020616389/562949953421312)), (105/140737488355328), by norm_num⟩
  | 16 => ⟨((-343199979/2251799813685248), (-821309355/2251799813685248)), (85/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1280865689503/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888841564978395/316912650057057350374175801344), (-3028165222285/633825300114114700748351602688)), (46249/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888520543823233/39614081257132168796771975168), (-3405864743305/39614081257132168796771975168)), (6505/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((236027414348953/309485009821345068724781056), (-1808853055627/1237940039285380274899124224)), (221215/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884942798754685/77371252455336267181195264), (-904138312093/38685626227668133590597632)), (13829/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548329939065401/9671406556917033397649408), (-3389294187557/9671406556917033397649408)), (207489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257718168742621/604462909807314587353088), (-1482204209737/302231454903657293676544)), (90803/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117878282845367/4722366482869645213696), (-150464679021/2361183241434822606848)), (295209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296234872582297/4722366482869645213696), (-3609146124229/4722366482869645213696)), (110747/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619654412045285/590295810358705651712), (-1239829458401/147573952589676412928)), (304697/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910616317288189/36893488147419103232), (-774282944911/9223372036854775808)), (95271/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113758428048757/576460752303423488), (-1740459222613/2305843009213693952)), (107253/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591383586372845/1152921504606846976), (-3476729072917/576460752303423488)), (429379/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192304037707873/144115188075855872), (-6074861155679/144115188075855872)), (47015/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488222855369055/36028797018963968), (-9093490677069/36028797018963968)), (35313/2251799813685248), by norm_num⟩
  | 3 => ⟨((742495236108979/4503599627370496), (-2833506323727/2251799813685248)), (707711/9007199254740992), by norm_num⟩
  | 2 => ⟨((277427086501481/562949953421312), (-22569791253561/4503599627370496)), (1419785/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203314586457711/2251799813685248), (-16804964365983/1125899906842624)), (1070311/1125899906842624), by norm_num⟩
  | 0 => ⟨((67349644182975/70368744177664), (-33123076330969/1125899906842624)), (2162617/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((67349644182975/70368744177664), (-33123076330969/1125899906842624)), (8249729160789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030386755595767/1125899906842624), (-126807856596331/2251799813685248)), (8533819/2251799813685248), by norm_num⟩
  | 2 => ⟨((469702857934143/562949953421312), (-116050401237497/1125899906842624)), (4145223/562949953421312), by norm_num⟩
  | 3 => ⟨((192960181916973/281474976710656), (-387311197340923/2251799813685248)), (31086963/2251799813685248), by norm_num⟩
  | 4 => ⟨((495812829007113/1125899906842624), (-531028654630355/2251799813685248)), (53316195/2251799813685248), by norm_num⟩
  | 5 => ⟨((311453091580925/2251799813685248), (-935396896068559/4503599627370496)), (144208443/4503599627370496), by norm_num⟩
  | 6 => ⟨((-432503135664169/18014398509481984), (-517510043948295/9007199254740992)), (399183747/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-87711307/1048576)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1420480547/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-535655238735531/9007199254740992), (-21029195019321/2251799813685248)), (185137583/9007199254740992), by norm_num⟩
  | 1 => ⟨((1664368133/8589934592), (130682273/4294967296)), (577/8589934592), by norm_num⟩
  | 2 => ⟨((-1355668013/4294967296), (-212887731/4294967296)), (59/536870912), by norm_num⟩
  | 3 => ⟨((1472299087/4294967296), (115601463/2147483648)), (515/4294967296), by norm_num⟩
  | 4 => ⟨((-299805785/1073741824), (-188320363/4294967296)), (421/4294967296), by norm_num⟩
  | 5 => ⟨((1562873905/8589934592), (245426369/8589934592)), (551/8589934592), by norm_num⟩
  | 6 => ⟨((-1697331353/17179869184), (-133270467/8589934592)), (601/17179869184), by norm_num⟩
  | 7 => ⟨((790009915/17179869184), (62029721/8589934592)), (561/34359738368), by norm_num⟩
  | 8 => ⟨((-1286964285/68719476736), (-202098819/68719476736)), (459/68719476736), by norm_num⟩
  | 9 => ⟨((116473719/17179869184), (146323881/137438953472)), (167/68719476736), by norm_num⟩
  | 10 => ⟨((-607172193/274877906944), (-47673733/137438953472)), (437/549755813888), by norm_num⟩
  | 11 => ⟨((719354771/1099511627776), (225928181/2199023255552)), (519/2199023255552), by norm_num⟩
  | 12 => ⟨((-390621215/2199023255552), (-245365275/8796093022208)), (283/4398046511104), by norm_num⟩
  | 13 => ⟨((1566377389/35184372088832), (245976539/35184372088832)), (285/17592186044416), by norm_num⟩
  | 14 => ⟨((-1458116785/140737488355328), (-228975803/140737488355328)), (533/140737488355328), by norm_num⟩
  | 15 => ⟨((158356175/70368744177664), (24867509/70368744177664)), (465/562949953421312), by norm_num⟩
  | 16 => ⟨((-1031879411/2251799813685248), (-81020745/1125899906842624)), (95/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1944688095189/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444406155682063/158456325028528675187087900672), (-2298643706691/316912650057057350374175801344)), (92653/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888454389270665/39614081257132168796771975168), (-5170668967471/39614081257132168796771975168)), (13033/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888148573196249/2475880078570760549798248448), (-1373064584013/618970019642690137449562112)), (55407/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769814347592453/154742504910672534362390528), (-5490484102099/154742504910672534362390528)), (27713/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774131301328623/4835703278458516698824704), (-2572722116223/4835703278458516698824704)), (207929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257658710315051/604462909807314587353088), (-140636864475/18889465931478580854784)), (182019/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885954895972077/75557863725914323419136), (-7309585595277/75557863725914323419136)), (295931/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648080384078157/2361183241434822606848), (-1369775119199/1180591620717411303424)), (222081/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619551086935323/590295810358705651712), (-941093283795/73786976294838206464)), (38197/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821101334660309/73786976294838206464), (-2350852877023/18446744073709551616)), (382295/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113749012195149/576460752303423488), (-10568502615939/9223372036854775808)), (215263/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591229265287885/1152921504606846976), (-10555593201433/1152921504606846976)), (431083/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192164893448767/144115188075855872), (-9221634367769/144115188075855872)), (377825/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488005943669103/36028797018963968), (-431358303555/1125899906842624)), (283997/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484705061086695/9007199254740992), (-17203682392017/9007199254740992)), (712195/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109401667804635/2251799813685248), (-8563929381067/1125899906842624)), (357753/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101144597173249/1125899906842624), (-1593922364389/70368744177664)), (540781/562949953421312), by norm_num⟩
  | 0 => ⟨((1076361119413577/1125899906842624), (-25126284569759/562949953421312)), (2196493/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076361119413577/1125899906842624), (-25126284569759/562949953421312)), (8378955845359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((256689766926527/281474976710656), (-192165968728445/2251799813685248)), (8791543/2251799813685248), by norm_num⟩
  | 2 => ⟨((1856296881954443/2251799813685248), (-175244841657171/1125899906842624)), (17535333/2251799813685248), by norm_num⟩
  | 3 => ⟨((1475706266448995/2251799813685248), (-577860342948367/2251799813685248)), (4296201/281474976710656), by norm_num⟩
  | 4 => ⟨((409402824726885/1125899906842624), (-757396038527665/2251799813685248)), (31343941/1125899906842624), by norm_num⟩
  | 5 => ⟨((42985140957801/2251799813685248), (-1101625733249203/4503599627370496)), (175519595/4503599627370496), by norm_num⟩
  | 6 => ⟨((-535655238735531/9007199254740992), (-21029195019321/2251799813685248)), (185137583/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1420480547/16777216)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-359233689/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-712298995400505/18014398509481984), (24095292054137/562949953421312)), (193146719/9007199254740992), by norm_num⟩
  | 1 => ⟨((139929133/1073741824), (-75735237/536870912)), (305/4294967296), by norm_num⟩
  | 2 => ⟨((-461183595/2147483648), (998443945/4294967296)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((506661965/2147483648), (-1096902787/4294967296)), (557/4294967296), by norm_num⟩
  | 4 => ⟨((-834937591/4294967296), (903803161/4294967296)), (461/4294967296), by norm_num⟩
  | 5 => ⟨((550363619/4294967296), (-148939389/1073741824)), (153/2147483648), by norm_num⟩
  | 6 => ⟨((-604636235/8589934592), (163626643/2147483648)), (169/4294967296), by norm_num⟩
  | 7 => ⟨((284683199/8589934592), (-616327683/17179869184)), (5/268435456), by norm_num⟩
  | 8 => ⟨((-469134691/34359738368), (507828875/34359738368)), (265/34359738368), by norm_num⟩
  | 9 => ⟨((343598091/68719476736), (-743876057/137438953472)), (195/68719476736), by norm_num⟩
  | 10 => ⟨((-226488651/137438953472), (980677653/549755813888)), (129/137438953472), by norm_num⟩
  | 11 => ⟨((542887015/1099511627776), (-146916071/274877906944)), (155/549755813888), by norm_num⟩
  | 12 => ⟨((-298211173/2199023255552), (161403801/1099511627776)), (171/2199023255552), by norm_num⟩
  | 13 => ⟨((604834079/17592186044416), (-20460023/549755813888)), (349/17592186044416), by norm_num⟩
  | 14 => ⟨((-284776351/35184372088832), (308264677/35184372088832)), (165/35184372088832), by norm_num⟩
  | 15 => ⟨((250287039/140737488355328), (-1083722759/562949953421312)), (291/281474976710656), by norm_num⟩
  | 16 => ⟨((-412452625/1125899906842624), (892943355/2251799813685248)), (241/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1508820678521/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777579019144627/633825300114114700748351602688), (891673739663/158456325028528675187087900672)), (185103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888403344511809/39614081257132168796771975168), (4011539014619/39614081257132168796771975168)), (104143/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944047342994117/1237940039285380274899124224), (4261023434109/2475880078570760549798248448)), (221357/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884880425645341/77371252455336267181195264), (4259632574543/154742504910672534362390528)), (221415/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548212864867799/9671406556917033397649408), (3991928252441/9671406556917033397649408)), (25955/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257615604355429/604462909807314587353088), (1745730249607/302231454903657293676544)), (45437/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117867851584477/4722366482869645213696), (354428478587/4722366482869645213696)), (295457/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296109493862393/4722366482869645213696), (531340155613/590295810358705651712)), (433/9223372036854775808), by norm_num⟩
  | 9 => ⟨((809740843041031/295147905179352825856), (730101331199/73786976294838206464)), (304999/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821016232852075/73786976294838206464), (7295120650129/73786976294838206464)), (381499/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227486339868321/1152921504606846976), (8198914707071/9223372036854775808)), (107383/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591138611760035/1152921504606846976), (4094402125241/576460752303423488)), (429965/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192088738096769/144115188075855872), (1788460652931/36028797018963968)), (188353/72057594037927936), by norm_num⟩
  | 4 => ⟨((743949010581237/18014398509481984), (10708074569853/36028797018963968)), (283017/18014398509481984), by norm_num⟩
  | 3 => ⟨((742290575479145/4503599627370496), (13345460740555/9007199254740992)), (709251/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218588293243533/4503599627370496), (26572319290765/4503599627370496)), (711821/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101023936935667/1125899906842624), (39563005295569/2251799813685248)), (1049/1099511627776), by norm_num⟩
  | 0 => ⟨((1076280189231039/1125899906842624), (38975147700713/1125899906842624)), (4348513/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076280189231039/1125899906842624), (38975147700713/1125899906842624)), (16588260659224700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054996144083725/2251799813685248), (74514935275671/1125899906842624)), (8614803/2251799813685248), by norm_num⟩
  | 2 => ⟨((1865529619619023/2251799813685248), (136004900380151/1125899906842624)), (16864067/2251799813685248), by norm_num⟩
  | 3 => ⟨((756330871257979/1125899906842624), (450699335758931/2251799813685248)), (32016709/2251799813685248), by norm_num⟩
  | 4 => ⟨((925932955205987/2251799813685248), (302760324624125/1125899906842624)), (55831217/2251799813685248), by norm_num⟩
  | 5 => ⟨((435826113749789/4503599627370496), (124494087082967/562949953421312)), (75941849/2251799813685248), by norm_num⟩
  | 6 => ⟨((-712298995400505/18014398509481984), (24095292054137/562949953421312)), (193146719/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-359233689/4194304)), (1/8388608), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile036Terms3
