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
namespace Reinmann.XiBand97.Tile040Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6939/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6939/256))
  have he : value ((69/80), (6939/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-351416215/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-317644756328293/9007199254740992), (-539717844854939/9007199254740992)), (113252447/4503599627370496), by norm_num⟩
  | 1 => ⟨((234092099/2147483648), (397751515/2147483648)), (21/268435456), by norm_num⟩
  | 2 => ⟨((-90448577/536870912), (-1229466819/4294967296)), (521/4294967296), by norm_num⟩
  | 3 => ⟨((372773855/2147483648), (316694511/1073741824)), (539/4294967296), by norm_num⟩
  | 4 => ⟨((-288064953/2147483648), (-489458089/2147483648)), (419/4294967296), by norm_num⟩
  | 5 => ⟨((712336799/8589934592), (605174293/4294967296)), (65/1073741824), by norm_num⟩
  | 6 => ⟨((-733954429/17179869184), (-1247079621/17179869184)), (269/8589934592), by norm_num⟩
  | 7 => ⟨((324097757/17179869184), (550682293/17179869184)), (477/34359738368), by norm_num⟩
  | 8 => ⟨((-500899963/68719476736), (-851091173/68719476736)), (185/34359738368), by norm_num⟩
  | 9 => ⟨((688134689/274877906944), (1169226199/274877906944)), (255/137438953472), by norm_num⟩
  | 10 => ⟨((-425410707/549755813888), (-180706391/137438953472)), (317/549755813888), by norm_num⟩
  | 11 => ⟨((239084101/1099511627776), (812467093/2199023255552)), (179/1099511627776), by norm_num⟩
  | 12 => ⟨((-123169851/2199023255552), (-837123425/8796093022208)), (371/8796093022208), by norm_num⟩
  | 13 => ⟨((468582447/35184372088832), (398089853/17592186044416)), (355/35184372088832), by norm_num⟩
  | 14 => ⟨((-413830925/140737488355328), (-351575039/70368744177664)), (315/140737488355328), by norm_num⟩
  | 15 => ⟨((170555861/281474976710656), (1159182263/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | 16 => ⟨((-527195407/4503599627370496), (-895770397/4503599627370496)), (101/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-1369530497601/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777852212068427/633825300114114700748351602688), (-202398276671/39614081257132168796771975168)), (92519/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888710676405873/39614081257132168796771975168), (-3642321723175/39614081257132168796771975168)), (208209/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944210611279593/1237940039285380274899124224), (-3868913731211/2475880078570760549798248448)), (221269/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770087383733019/154742504910672534362390528), (-1933864703705/77371252455336267181195264)), (221323/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548518984573831/9671406556917033397649408), (-3624738383375/9671406556917033397649408)), (207547/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628941727279201/302231454903657293676544), (-3170388608131/604462909807314587353088)), (181661/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886320873247093/75557863725914323419136), (-1287381173207/18889465931478580854784)), (295305/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648217961006577/2361183241434822606848), (-965020574491/1180591620717411303424)), (55393/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619930511839703/590295810358705651712), (-5304265500719/590295810358705651712)), (304813/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821577245062001/73786976294838206464), (-6625313582073/73786976294838206464)), (381245/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910260914643959/4611686018427387904), (-7446582814831/9223372036854775808)), (214607/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795884842621089/576460752303423488), (-464873243005/72057594037927936)), (214803/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192640884054241/144115188075855872), (-3249274399881/72057594037927936)), (376347/144115188075855872), by norm_num⟩
  | 4 => ⟨((372181537188231/9007199254740992), (-9728496701159/36028797018963968)), (141351/9007199254740992), by norm_num⟩
  | 3 => ⟨((742808070065963/4503599627370496), (-6063429769501/4503599627370496)), (354153/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220657719016045/4503599627370496), (-12076337467789/2251799813685248)), (177659/562949953421312), by norm_num⟩
  | 1 => ⟨((2205150486307029/2251799813685248), (-35977240377299/2251799813685248)), (2143595/2251799813685248), by norm_num⟩
  | 0 => ⟨((539689659272387/562949953421312), (-35476206450825/1125899906842624)), (4334151/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539689659272387/562949953421312), (-35476206450825/1125899906842624)), (16533473977095793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((516831534048929/562949953421312), (-136041519537305/2251799813685248)), (1072909/281474976710656), by norm_num⟩
  | 2 => ⟨((236218270408533/281474976710656), (-249793242932173/2251799813685248)), (16797323/2251799813685248), by norm_num⟩
  | 3 => ⟨((779097652475203/1125899906842624), (-419260912602059/2251799813685248)), (3989979/281474976710656), by norm_num⟩
  | 4 => ⟨((1000174563407431/2251799813685248), (-290119211128537/1125899906842624)), (56061885/2251799813685248), by norm_num⟩
  | 5 => ⟨((589459619447889/4503599627370496), (-1030890414194349/4503599627370496)), (78693437/2251799813685248), by norm_num⟩
  | 6 => ⟨((-317644756328293/9007199254740992), (-539717844854939/9007199254740992)), (113252447/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-351416215/4194304)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-712939745/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1188817762073515/18014398509481984), (199224100636209/18014398509481984)), (102998911/4503599627370496), by norm_num⟩
  | 1 => ⟨((111089087/536870912), (-297863967/8589934592)), (309/4294967296), by norm_num⟩
  | 2 => ⟨((-1393276759/4294967296), (116743843/2147483648)), (487/4294967296), by norm_num⟩
  | 3 => ⟨((1456203739/4294967296), (-30504137/536870912)), (511/4294967296), by norm_num⟩
  | 4 => ⟨((-71342475/268435456), (95645545/2147483648)), (201/2147483648), by norm_num⟩
  | 5 => ⟨((1431641073/8589934592), (-119958421/4294967296)), (253/4294967296), by norm_num⟩
  | 6 => ⟨((-46759399/536870912), (250752623/17179869184)), (531/17179869184), by norm_num⟩
  | 7 => ⟨((670234629/17179869184), (-112319057/17179869184)), (477/34359738368), by norm_num⟩
  | 8 => ⟨((-1050758401/68719476736), (176087877/68719476736)), (375/68719476736), by norm_num⟩
  | 9 => ⟨((732143753/137438953472), (-245387787/274877906944)), (525/274877906944), by norm_num⟩
  | 10 => ⟨((-918253001/549755813888), (307764795/1099511627776)), (661/1099511627776), by norm_num⟩
  | 11 => ⟨((1046973445/2199023255552), (-43863397/549755813888)), (189/1099511627776), by norm_num⟩
  | 12 => ⟨((-1094259727/8796093022208), (183377903/8796093022208)), (397/8796093022208), by norm_num⟩
  | 13 => ⟨((1055706167/35184372088832), (-22114629/4398046511104)), (385/35184372088832), by norm_num⟩
  | 14 => ⟨((-472880083/70368744177664), (79246047/70368744177664)), (347/140737488355328), by norm_num⟩
  | 15 => ⟨((790780141/562949953421312), (-265040557/1125899906842624)), (583/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1239743279/4503599627370496), (207758283/4503599627370496)), (459/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (3875991055339/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777787529861135/633825300114114700748351602688), (2291133273329/316912650057057350374175801344)), (92651/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888637617169591/39614081257132168796771975168), (644227335951/4951760157141521099596496896)), (52131/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944171601727653/1237940039285380274899124224), (5474418994589/2475880078570760549798248448)), (27703/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885004461129389/77371252455336267181195264), (684089597993/19342813113834066795298816)), (55425/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548444957329939/9671406556917033397649408), (5128863837203/9671406556917033397649408)), (51981/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((19653409555713/9444732965739290427392), (4485948216315/604462909807314587353088)), (91007/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471553493672715/18889465931478580854784), (1821569400181/18889465931478580854784)), (295923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296354980210419/4722366482869645213696), (170679517433/147573952589676412928)), (222075/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809908985432883/295147905179352825856), (7505084867065/590295810358705651712)), (9549/18446744073709551616), by norm_num⟩
  | 8 => ⟨((910717351516017/36893488147419103232), (9374138768693/73786976294838206464)), (191141/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910179454587303/4611686018427387904), (5267994026161/4611686018427387904)), (430511/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591603572451725/1152921504606846976), (10523599096055/1152921504606846976)), (215533/576460752303423488), by norm_num⟩
  | 5 => ⟨((596245977110717/72057594037927936), (9194223493107/144115188075855872)), (377807/144115188075855872), by norm_num⟩
  | 4 => ⟨((23257744034821/562949953421312), (13763513471937/36028797018963968)), (283981/18014398509481984), by norm_num⟩
  | 3 => ⟨((742657774444459/4503599627370496), (1072235658145/562949953421312)), (356073/4503599627370496), by norm_num⟩
  | 2 => ⟨((555004872433353/1125899906842624), (8541486115759/1125899906842624)), (178861/562949953421312), by norm_num⟩
  | 1 => ⟨((551025338444695/562949953421312), (12721465431921/562949953421312)), (1081435/1125899906842624), by norm_num⟩
  | 0 => ⟨((269537270750823/281474976710656), (50162564786985/1125899906842624)), (2196097/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269537270750823/281474976710656), (50162564786985/1125899906842624)), (8377445225242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030188523176561/1125899906842624), (48035107648109/562949953421312)), (1100401/281474976710656), by norm_num⟩
  | 2 => ⟨((1868832034932741/2251799813685248), (351613611887789/2251799813685248)), (4403007/562949953421312), by norm_num⟩
  | 3 => ⟨((748046301063637/1125899906842624), (583628063046067/2251799813685248)), (8683399/562949953421312), by norm_num⟩
  | 4 => ⟨((421367687001307/1125899906842624), (775523314470919/2251799813685248)), (64158615/2251799813685248), by norm_num⟩
  | 5 => ⟨((96604057471131/4503599627370496), (145119678600291/562949953421312)), (184430673/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1188817762073515/18014398509481984), (199224100636209/18014398509481984)), (102998911/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-712939745/8388608)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1445233657/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-18048501551987/1125899906842624), (1125494151480105/18014398509481984)), (201248503/9007199254740992), by norm_num⟩
  | 1 => ⟨((109403819/2147483648), (-1705589771/8589934592)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-173845613/2147483648), (677557013/2147483648)), (61/536870912), by norm_num⟩
  | 3 => ⟨((46040893/536870912), (-1435541773/4294967296)), (519/4294967296), by norm_num⟩
  | 4 => ⟨((-292640873/4294967296), (1140557257/4294967296)), (207/2147483648), by norm_num⟩
  | 5 => ⟨((372011379/8589934592), (-1449900943/8589934592)), (33/536870912), by norm_num⟩
  | 6 => ⟨((-394090729/17179869184), (1535954415/17179869184)), (561/17179869184), by norm_num⟩
  | 7 => ⟨((357840443/34359738368), (-174333779/4294967296)), (511/34359738368), by norm_num⟩
  | 8 => ⟨((-35538631/8589934592), (277021067/17179869184)), (51/8589934592), by norm_num⟩
  | 9 => ⟨((401577537/274877906944), (-1565133979/274877906944)), (579/274877906944), by norm_num⟩
  | 10 => ⟨((-127623503/274877906944), (994816007/549755813888)), (185/274877906944), by norm_num⟩
  | 11 => ⟨((147488859/1099511627776), (-574832513/1099511627776)), (429/2199023255552), by norm_num⟩
  | 12 => ⟨((-156242511/4398046511104), (1217899113/8796093022208)), (57/1099511627776), by norm_num⟩
  | 13 => ⟨((305567453/35184372088832), (-148867267/4398046511104)), (7/549755813888), by norm_num⟩
  | 14 => ⟨((-277459947/140737488355328), (16896721/2199023255552)), (51/17592186044416), by norm_num⟩
  | 15 => ⟨((235142039/562949953421312), (-114557203/70368744177664)), (87/140737488355328), by norm_num⟩
  | 16 => ⟨((-373647029/4503599627370496), (1456275831/4503599627370496)), (555/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (593325134039/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222217255385221/79228162514264337593543950336), (701397138551/158456325028528675187087900672)), (184953/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888582344108755/39614081257132168796771975168), (1577768256337/19807040628566084398385987584)), (52027/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888285010384769/2475880078570760549798248448), (3351819870039/2475880078570760549798248448)), (221155/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769951329925641/154742504910672534362390528), (3350765421281/154742504910672534362390528)), (110601/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548391602283553/9671406556917033397649408), (3140222631785/9671406556917033397649408)), (103713/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314443040770961/151115727451828646838272), (2746575303371/604462909807314587353088)), (181547/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943070169695643/37778931862957161709568), (4461086765025/75557863725914323419136)), (147553/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162037599599773/590295810358705651712), (3343980191789/4722366482869645213696)), (221411/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809872580667831/295147905179352825856), (4594992876093/590295810358705651712)), (304571/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821346226064677/73786976294838206464), (5739274404309/73786976294838206464)), (23807/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910131425782887/4611686018427387904), (3225273552667/4611686018427387904)), (214399/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591511853723247/1152921504606846976), (1610721000235/288230376151711744)), (429137/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596208284028829/72057594037927936), (2814456505639/72057594037927936)), (375879/144115188075855872), by norm_num⟩
  | 4 => ⟨((744196120347149/18014398509481984), (8426174768165/36028797018963968)), (70573/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485203229214377/9007199254740992), (5251343297097/4503599627370496)), (707075/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219845254876715/4503599627370496), (10457756498985/2251799813685248)), (88637/281474976710656), by norm_num⟩
  | 1 => ⟨((1101982479176869/1125899906842624), (31149441285587/2251799813685248)), (2137429/2251799813685248), by norm_num⟩
  | 0 => ⟨((539129726006147/562949953421312), (61408490029361/2251799813685248)), (4315619/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539129726006147/562949953421312), (61408490029361/2251799813685248)), (16462780007369231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515898743810053/562949953421312), (58810098842309/1125899906842624)), (8501405/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884976490866067/2251799813685248), (6736845773701/70368744177664)), (16469843/2251799813685248), by norm_num⟩
  | 3 => ⟨((1557270773646927/2251799813685248), (180460743678407/1125899906842624)), (15363631/1125899906842624), by norm_num⟩
  | 4 => ⟨((509554163845359/1125899906842624), (499202886887269/2251799813685248)), (6543743/281474976710656), by norm_num⟩
  | 5 => ⟨((701108736659951/4503599627370496), (451853505042677/2251799813685248)), (141191075/4503599627370496), by norm_num⟩
  | 6 => ⟨((-18048501551987/1125899906842624), (1125494151480105/18014398509481984)), (201248503/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1445233657/16777216)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-365949409/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((846691095116597/18014398509481984), (91978235720387/2251799813685248)), (123633287/9007199254740992), by norm_num⟩
  | 1 => ⟨((-649784445/4294967296), (-564702071/4294967296)), (191/4294967296), by norm_num⟩
  | 2 => ⟨((1045787721/4294967296), (454426461/2147483648)), (155/2147483648), by norm_num⟩
  | 3 => ⟨((-561043469/2147483648), (-487580783/2147483648)), (335/4294967296), by norm_num⟩
  | 4 => ⟨((451482315/2147483648), (392365499/2147483648)), (17/268435456), by norm_num⟩
  | 5 => ⟨((-145326551/1073741824), (-63148791/536870912)), (177/4294967296), by norm_num⟩
  | 6 => ⟨((77964687/1073741824), (542048311/8589934592)), (3/134217728), by norm_num⟩
  | 7 => ⟨((-573619763/17179869184), (-62313793/2147483648)), (89/8589934592), by norm_num⟩
  | 8 => ⟨((461602697/34359738368), (100290181/8589934592)), (289/68719476736), by norm_num⟩
  | 9 => ⟨((-660374117/137438953472), (-35869071/8589934592)), (209/137438953472), by norm_num⟩
  | 10 => ⟨((53141557/34359738368), (738931747/549755813888)), (271/549755813888), by norm_num⟩
  | 11 => ⟨((-995235335/2199023255552), (-108114979/274877906944)), (319/2199023255552), by norm_num⟩
  | 12 => ⟨((66740395/549755813888), (928023179/8796093022208)), (43/1099511627776), by norm_num⟩
  | 13 => ⟨((-1057619909/35184372088832), (-14361497/549755813888)), (343/35184372088832), by norm_num⟩
  | 14 => ⟨((121583827/17592186044416), (211327431/35184372088832)), (159/70368744177664), by norm_num⟩
  | 15 => ⟨((-834908249/562949953421312), (-181396469/140737488355328)), (275/562949953421312), by norm_num⟩
  | 16 => ⟨((671866495/2251799813685248), (583892709/2251799813685248)), (223/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (465980780169/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777687398661255/633825300114114700748351602688), (137706357927/79228162514264337593543950336)), (184617/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888525578189705/39614081257132168796771975168), (1239061474917/39614081257132168796771975168)), (207709/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944112488227169/1237940039285380274899124224), (1316130196151/2475880078570760549798248448)), (220707/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884945805234909/77371252455336267181195264), (1315711219831/154742504910672534362390528)), (220725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774167974576023/4835703278458516698824704), (1233034290893/9671406556917033397649408)), (206949/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257723800146999/604462909807314587353088), (1078460234661/604462909807314587353088)), (45275/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886062374383355/75557863725914323419136), (109479023701/4722366482869645213696)), (73581/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648121434531913/2361183241434822606848), (1313019411197/4722366482869645213696)), (220775/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619666396773501/590295810358705651712), (112763631123/36893488147419103232)), (303617/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821249097351315/73786976294838206464), (2253498679137/73786976294838206464)), (379599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820155402933745/9223372036854775808), (2532749188469/9223372036854775808)), (427157/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591406676402287/1152921504606846976), (2529706672549/1152921504606846976)), (106823/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192327086055181/144115188075855872), (2210075336557/144115188075855872)), (23377/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488263096355749/36028797018963968), (413536131757/4503599627370496)), (561353/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485050646864439/9007199254740992), (4123446473275/9007199254740992)), (702225/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219566476545925/4503599627370496), (4105628221627/2251799813685248)), (703029/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203612206603273/2251799813685248), (12228170393593/2251799813685248)), (2113137/2251799813685248), by norm_num⟩
  | 0 => ⟨((539017945196977/562949953421312), (6025934178953/562949953421312)), (4242615/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((539017945196977/562949953421312), (6025934178953/562949953421312)), (16184291848189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064155306141247/2251799813685248), (23079043806941/1125899906842624)), (1026917/281474976710656), by norm_num⟩
  | 2 => ⟨((1891201221768177/2251799813685248), (21155846290261/562949953421312)), (15398291/2251799813685248), by norm_num⟩
  | 3 => ⟨((792583985975999/1125899906842624), (142143940535111/2251799813685248)), (6755557/562949953421312), by norm_num⟩
  | 4 => ⟨((1106915714409045/2251799813685248), (50031539343311/562949953421312)), (20728227/1125899906842624), by norm_num⟩
  | 5 => ⟨((32896239064459/140737488355328), (393503520365253/4503599627370496)), (96252469/4503599627370496), by norm_num⟩
  | 6 => ⟨((846691095116597/18014398509481984), (91978235720387/2251799813685248)), (123633287/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-365949409/4194304)), (1/8388608), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-92602089/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((509783795480175/9007199254740992), (-46180792368975/2251799813685248)), (46093837/4503599627370496), by norm_num⟩
  | 1 => ⟨((-791990671/4294967296), (143491249/2147483648)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((161273879/536870912), (-233754171/2147483648)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((-700594489/2147483648), (31733069/268435456)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((35665695/134217728), (-413557609/4294967296)), (107/2147483648), by norm_num⟩
  | 5 => ⟨((-1487389151/8589934592), (269482123/4294967296)), (281/8589934592), by norm_num⟩
  | 6 => ⟨((807676241/8589934592), (-292666257/8589934592)), (77/4294967296), by norm_num⟩
  | 7 => ⟨((-1503706951/34359738368), (68109637/4294967296)), (289/34359738368), by norm_num⟩
  | 8 => ⟨((1224805603/68719476736), (-443815545/68719476736)), (237/68719476736), by norm_num⟩
  | 9 => ⟨((-221696383/34359738368), (40166497/17179869184)), (173/137438953472), by norm_num⟩
  | 10 => ⟨((1155693149/549755813888), (-418772239/549755813888)), (227/549755813888), by norm_num⟩
  | 11 => ⟨((-1369221763/2199023255552), (248072797/1099511627776)), (271/2199023255552), by norm_num⟩
  | 12 => ⟨((1487018895/8796093022208), (-538830081/8796093022208)), (297/8796093022208), by norm_num⟩
  | 13 => ⟨((-372680855/8796093022208), (540172437/35184372088832)), (75/8796093022208), by norm_num⟩
  | 14 => ⟨((1387691661/140737488355328), (-502838271/140737488355328)), (141/70368744177664), by norm_num⟩
  | 15 => ⟨((-1205662239/562949953421312), (436878835/562949953421312)), (247/562949953421312), by norm_num⟩
  | 16 => ⟨((30688781/70368744177664), (-355848355/2251799813685248)), (203/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-113209856221/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817904913409/316912650057057350374175801344), (-535261411187/633825300114114700748351602688)), (92253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888467581849749/39614081257132168796771975168), (-75252991047/4951760157141521099596496896)), (207577/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118010213093783/154742504910672534362390528), (-319733597827/1237940039285380274899124224)), (110279/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769830104380315/154742504910672534362390528), (-639261178081/154742504910672534362390528)), (220567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548278351815617/9671406556917033397649408), (-149772138561/2417851639229258349412352)), (206791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673467048463/604462909807314587353088), (-130995947493/151115727451828646838272)), (180951/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471495176014727/18889465931478580854784), (-425531914525/37778931862957161709568)), (18379/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296181722051527/4722366482869645213696), (-637939494151/4722366482869645213696)), (55141/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404895622809829/147573952589676412928), (-438292429603/295147905179352825856)), (303301/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910572236243233/36893488147419103232), (-136857360967/9223372036854775808)), (94791/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910019026413189/4611686018427387904), (-1230518180309/9223372036854775808)), (426613/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591289766505053/1152921504606846976), (-1229022374427/1152921504606846976)), (426679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596112641967441/72057594037927936), (-268428559939/36028797018963968)), (93355/36028797018963968), by norm_num⟩
  | 4 => ⟨((186013922283729/4503599627370496), (-1607216783641/36028797018963968)), (70035/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484862716474037/9007199254740992), (-1001582084767/4503599627370496)), (87577/1125899906842624), by norm_num⟩
  | 2 => ⟨((554798935177887/1125899906842624), (-3988812568913/4503599627370496)), (1402037/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203068822151995/2251799813685248), (-5939620145141/2251799813685248)), (2105091/2251799813685248), by norm_num⟩
  | 0 => ⟨((538758833470265/562949953421312), (-11705985034607/2251799813685248)), (4218465/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538758833470265/562949953421312), (-11705985034607/2251799813685248)), (16092166909224700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062368169659755/2251799813685248), (-22405909454425/2251799813685248)), (4059119/1125899906842624), by norm_num⟩
  | 2 => ⟨((944324716744493/1125899906842624), (-41042044848081/2251799813685248)), (15032147/2251799813685248), by norm_num⟩
  | 3 => ⟨((395829173124635/562949953421312), (-68846292890219/2251799813685248)), (25763753/2251799813685248), by norm_num⟩
  | 4 => ⟨((555589338246907/1125899906842624), (-96816319183659/2251799813685248)), (9451533/562949953421312), by norm_num⟩
  | 5 => ⟨((1088324676098893/4503599627370496), (-23887609537865/562949953421312)), (81125541/4503599627370496), by norm_num⟩
  | 6 => ⟨((509783795480175/9007199254740992), (-46180792368975/2251799813685248)), (46093837/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-92602089/1048576)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-46837375/524288)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((208737640814723/18014398509481984), (-257186161868939/4503599627370496)), (159900809/18014398509481984), by norm_num⟩
  | 1 => ⟨((-328047377/8589934592), (808375963/4294967296)), (253/8589934592), by norm_num⟩
  | 2 => ⟨((67574415/1073741824), (-666068825/2147483648)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-296952331/4294967296), (182937849/536870912)), (233/4294967296), by norm_num⟩
  | 4 => ⟨((122338305/2147483648), (-602933307/2147483648)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((-322565677/8589934592), (1589735857/8589934592)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((354374617/17179869184), (-436625837/4294967296)), (143/8589934592), by norm_num⟩
  | 7 => ⟨((-166851561/17179869184), (1644625749/34359738368)), (271/34359738368), by norm_num⟩
  | 8 => ⟨((274957763/68719476736), (-42347017/2147483648)), (225/68719476736), by norm_num⟩
  | 9 => ⟨((-100690659/68719476736), (496244835/68719476736)), (167/137438953472), by norm_num⟩
  | 10 => ⟨((265487989/549755813888), (-1308433617/549755813888)), (111/274877906944), by norm_num⟩
  | 11 => ⟨((-318183673/2199023255552), (784069773/1099511627776)), (67/549755813888), by norm_num⟩
  | 12 => ⟨((349560493/8796093022208), (-53836793/274877906944)), (297/8796093022208), by norm_num⟩
  | 13 => ⟨((-88622643/8796093022208), (1747074827/35184372088832)), (303/35184372088832), by norm_num⟩
  | 14 => ⟨((333812313/140737488355328), (-411290973/35184372088832)), (287/140737488355328), by norm_num⟩
  | 15 => ⟨((-293384247/562949953421312), (1445917815/562949953421312)), (127/281474976710656), by norm_num⟩
  | 16 => ⟨((120868327/1125899906842624), (-595688655/1125899906842624)), (211/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-223171385349/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888791728150677/316912650057057350374175801344), (-1055107828745/316912650057057350374175801344)), (92409/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944204288341161/19807040628566084398385987584), (-1186705580413/19807040628566084398385987584)), (103973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888100570044999/2475880078570760549798248448), (-2521018307211/2475880078570760549798248448)), (110487/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221220887547459/19342813113834066795298816), (-2520196282351/154742504910672534362390528)), (13813/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548219110897155/9671406556917033397649408), (-2361810963567/9671406556917033397649408)), (103617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157202682094837/75557863725914323419136), (-1032855968075/302231454903657293676544)), (90683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885895860562453/75557863725914323419136), (-1677573250811/37778931862957161709568)), (147395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648058901943029/2361183241434822606848), (-1257464871333/2361183241434822606848)), (6911/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619494140476259/590295810358705651712), (-863926499269/147573952589676412928)), (38023/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455258335091589/18446744073709551616), (-4316151639653/73786976294838206464)), (190189/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819912077447947/9223372036854775808), (-4850888868699/9223372036854775808)), (214065/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591162604514131/1152921504606846976), (-2422459191521/576460752303423488)), (214193/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596056343231045/72057594037927936), (-4232595952155/144115188075855872)), (187563/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487939831095069/36028797018963968), (-3167750769909/18014398509481984)), (140817/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484643666863275/9007199254740992), (-7895991635067/9007199254740992)), (352549/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218743888412121/4503599627370496), (-7861016269413/2251799813685248)), (706623/4503599627370496), by norm_num⟩
  | 1 => ⟨((550589246987719/562949953421312), (-23408888065399/2251799813685248)), (1063765/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076738695971821/1125899906842624), (-5765676816277/281474976710656)), (2142937/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076738695971821/1125899906842624), (-5765676816277/281474976710656)), (8174655922896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058503289491223/2251799813685248), (-88222795633229/2251799813685248)), (130829/70368744177664), by norm_num⟩
  | 2 => ⟨((939171525255321/1125899906842624), (-161299342788291/2251799813685248)), (7982353/2251799813685248), by norm_num⟩
  | 3 => ⟨((1555269307748159/2251799813685248), (-8409259388229/70368744177664)), (14460563/2251799813685248), by norm_num⟩
  | 4 => ⟨((130254129744429/281474976710656), (-371717960303091/2251799813685248)), (23431351/2251799813685248), by norm_num⟩
  | 5 => ⟨((841689926803767/4503599627370496), (-344029156662297/2251799813685248)), (7355471/562949953421312), by norm_num⟩
  | 6 => ⟨((208737640814723/18014398509481984), (-257186161868939/4503599627370496)), (159900809/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-46837375/524288)), (1/16777216), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile040Terms3
