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
namespace Reinmann.XiBand97.Tile007Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11351/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11351/640))
  have he : value ((69/80), (11351/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-326902693/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((25010456050257/562949953421312), (-323327410597071/2251799813685248)), (195458165/9007199254740992), by norm_num⟩
  | 1 => ⟨((-419262609/4294967296), (677512105/2147483648)), (13/268435456), by norm_num⟩
  | 2 => ⟨((460607055/4294967296), (-1488646249/4294967296)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((-337352381/4294967296), (1090296709/4294967296)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((370619471/8589934592), (-1197813363/8589934592)), (191/8589934592), by norm_num⟩
  | 5 => ⟨((-81433421/4294967296), (4112289/67108864)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((238570019/34359738368), (-1542079567/68719476736)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((-149769117/68719476736), (484042161/68719476736)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((329076385/549755813888), (-1063549333/549755813888)), (89/274877906944), by norm_num⟩
  | 9 => ⟨((-160678827/1099511627776), (1038602993/2199023255552)), (11/137438953472), by norm_num⟩
  | 10 => ⟨((141218987/4398046511104), (-912817609/8796093022208)), (157/8796093022208), by norm_num⟩
  | 11 => ⟨((-451330661/70368744177664), (729332831/35184372088832)), (127/35184372088832), by norm_num⟩
  | 12 => ⟨((165279137/140737488355328), (-1068338681/281474976710656)), (47/70368744177664), by norm_num⟩
  | 13 => ⟨((-223480235/1125899906842624), (1444541543/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | 14 => ⟨((280592151/9007199254740992), (-226713013/2251799813685248)), (163/9007199254740992), by norm_num⟩
  | 15 => ⟨((-20550799/4503599627370496), (265674349/18014398509481984)), (193/72057594037927936), by norm_num⟩
  | 16 => ⟨((361237765/576460752303423488), (-1167492419/576460752303423488)), (107/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1655262416339/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779043804945909/633825300114114700748351602688), (-15308573167/4951760157141521099596496896)), (92393/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945025572272669/19807040628566084398385987584), (-551016518249/9903520314283042199192993792)), (51977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889845400915531/2475880078570760549798248448), (-1170683633409/1237940039285380274899124224)), (55233/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771511484167755/154742504910672534362390528), (-2340857848741/154742504910672534362390528)), (55241/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774926997890531/4835703278458516698824704), (-2194013110077/9671406556917033397649408)), (103595/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259051506235681/604462909807314587353088), (-1919220498467/604462909807314587353088)), (90663/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944109400488179/37778931862957161709568), (-3117719305153/75557863725914323419136)), (73679/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324464807678923/1180591620717411303424), (-2337402543763/4722366482869645213696)), (110547/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621887337817853/590295810358705651712), (-3212487826343/590295810358705651712)), (152047/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114001433816463/4611686018427387904), (-4013449822417/73786976294838206464)), (190127/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455818193157741/2305843009213693952), (-2256081402167/4611686018427387904)), (53497/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797260022376361/576460752303423488), (-4508455045447/1152921504606846976)), (107053/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195046787687047/144115188075855872), (-1970365219061/72057594037927936)), (46869/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492333672037295/36028797018963968), (-1475692238257/9007199254740992)), (35185/4503599627370496), by norm_num⟩
  | 3 => ⟨((745061594944661/4503599627370496), (-3681954563859/4503599627370496)), (352317/9007199254740992), by norm_num⟩
  | 2 => ⟨((278708082959753/562949953421312), (-14684240655375/4503599627370496)), (706037/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218642696766709/2251799813685248), (-5479422917869/562949953421312)), (531285/1125899906842624), by norm_num⟩
  | 0 => ⟨((546417082711793/562949953421312), (-43402351200379/2251799813685248)), (2139247/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546417082711793/562949953421312), (-43402351200379/2251799813685248)), (8160579689986418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120642456472829/2251799813685248), (-84255397772437/2251799813685248)), (4235309/2251799813685248), by norm_num⟩
  | 2 => ⟨((1993971857024467/2251799813685248), (-79347894345377/1125899906842624)), (8294187/2251799813685248), by norm_num⟩
  | 3 => ⟨((438620186089247/562949953421312), (-140525340909321/1125899906842624)), (991131/140737488355328), by norm_num⟩
  | 4 => ⟨((1331918218636087/2251799813685248), (-437959010780995/2251799813685248)), (7167523/562949953421312), by norm_num⟩
  | 5 => ⟨((351318540039549/1125899906842624), (-129524299169469/562949953421312)), (45068433/2251799813685248), by norm_num⟩
  | 6 => ⟨((25010456050257/562949953421312), (-323327410597071/2251799813685248)), (195458165/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-326902693/8388608)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1370312849/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1236199940464001/9007199254740992), (-2718653769075/9007199254740992)), (198722351/9007199254740992), by norm_num⟩
  | 1 => ⟨((678647889/2147483648), (373121/536870912)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((-1562644513/4294967296), (-3436571/4294967296)), (1/16777216), by norm_num⟩
  | 3 => ⟨((1199373987/4294967296), (1318833/2147483648)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-345207583/2147483648), (-3036725/8589934592)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((158973967/2147483648), (2796927/17179869184)), (107/8589934592), by norm_num⟩
  | 6 => ⟨((-976136231/34359738368), (-2146721/34359738368)), (331/68719476736), by norm_num⟩
  | 7 => ⟨((160545481/17179869184), (22067/1073741824)), (55/34359738368), by norm_num⟩
  | 8 => ⟨((-1478678525/549755813888), (-3251913/549755813888)), (1/2147483648), by norm_num⟩
  | 9 => ⟨((756618473/1099511627776), (1663957/1099511627776)), (33/274877906944), by norm_num⟩
  | 10 => ⟨((-696871367/4398046511104), (-1532561/4398046511104)), (245/8796093022208), by norm_num⟩
  | 11 => ⟨((1166985907/35184372088832), (1283219/17592186044416)), (207/35184372088832), by norm_num⟩
  | 12 => ⟨((-1791389569/281474976710656), (-984907/70368744177664)), (5/4398046511104), by norm_num⟩
  | 13 => ⟨((1269177513/1125899906842624), (1395589/562949953421312)), (229/1125899906842624), by norm_num⟩
  | 14 => ⟨((-834968349/4503599627370496), (-229533/562949953421312)), (19/562949953421312), by norm_num⟩
  | 15 => ⟨((512689513/18014398509481984), (4510031/72057594037927936)), (47/9007199254740992), by norm_num⟩
  | 16 => ⟨((-590255615/144115188075855872), (-2596183/288230376151711744)), (109/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-2044705245003/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444723300647777/158456325028528675187087900672), (-1210078169885/158456325028528675187087900672)), (92677/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889881149997557/39614081257132168796771975168), (-2722184040321/19807040628566084398385987584)), (26073/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944832022180359/1237940039285380274899124224), (-722933118713/309485009821345068724781056)), (55423/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771329298682323/154742504910672534362390528), (-2891070844239/77371252455336267181195264)), (55443/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774841158353097/4835703278458516698824704), (-5419351944249/9671406556917033397649408)), (51999/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258900407488459/604462909807314587353088), (-592565893489/75557863725914323419136)), (2845/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1887971617672179/75557863725914323419136), (-7700720916235/75557863725914323419136)), (37005/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297672402706017/4722366482869645213696), (-2886617316605/2361183241434822606848)), (27771/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621628110930529/590295810358705651712), (-3967225313557/295147905179352825856)), (76427/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823695404248191/73786976294838206464), (-2478110849687/18446744073709551616)), (191237/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822899483878461/9223372036854775808), (-1392971558801/1152921504606846976)), (215375/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594140754308627/1152921504606846976), (-5567058010913/576460752303423488)), (53917/288230376151711744), by norm_num⟩
  | 5 => ⟨((597354085606507/72057594037927936), (-1216436260337/18014398509481984)), (189039/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491812309041177/36028797018963968), (-14575517468337/36028797018963968)), (35527/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489448050922151/9007199254740992), (-9090701401949/4503599627370496)), (44553/1125899906842624), by norm_num⟩
  | 2 => ⟨((1114122203363993/2251799813685248), (-4531108951611/562949953421312)), (358159/2251799813685248), by norm_num⟩
  | 1 => ⟨((277042313127305/281474976710656), (-27044321816387/1125899906842624)), (270793/562949953421312), by norm_num⟩
  | 0 => ⟨((1090185776417637/1125899906842624), (-26759920511585/562949953421312)), (1100623/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090185776417637/1125899906842624), (-26759920511585/562949953421312)), (4198543552878951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053060442153413/1125899906842624), (-103644327679563/1125899906842624)), (2236059/1125899906842624), by norm_num⟩
  | 2 => ⟨((975392343043951/1125899906842624), (-1514673685545/8796093022208)), (4594477/1125899906842624), by norm_num⟩
  | 3 => ⟨((405809365721035/562949953421312), (-167961060821057/562949953421312)), (4771461/562949953421312), by norm_num⟩
  | 4 => ⟨((484839984532833/1125899906842624), (-968614295368657/2251799813685248)), (9726347/562949953421312), by norm_num⟩
  | 5 => ⟨((458652941109/1125899906842624), (-1668435842762579/4503599627370496)), (4186101/140737488355328), by norm_num⟩
  | 6 => ⟨((-1236199940464001/9007199254740992), (-2718653769075/9007199254740992)), (198722351/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1370312849/33554432)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1427033777/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((133392588231949/9007199254740992), (282701284360577/2251799813685248)), (88212345/4503599627370496), by norm_num⟩
  | 1 => ⟨((-38130457/1073741824), (-646484445/2147483648)), (203/4294967296), by norm_num⟩
  | 2 => ⟨((182865685/4294967296), (1550201995/4294967296)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((-73082127/2147483648), (-309768503/1073741824)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((175243287/8589934592), (742792429/4294967296)), (239/8589934592), by norm_num⟩
  | 5 => ⟨((-42021505/4294967296), (-1424910763/17179869184)), (29/2147483648), by norm_num⟩
  | 6 => ⟨((134350891/34359738368), (35591529/1073741824)), (187/34359738368), by norm_num⟩
  | 7 => ⟨((-184091067/137438953472), (-1560589881/137438953472)), (259/137438953472), by norm_num⟩
  | 8 => ⟨((110357775/274877906944), (1871065549/549755813888)), (313/549755813888), by norm_num⟩
  | 9 => ⟨((-7350733/68719476736), (-997026497/1099511627776)), (169/1099511627776), by norm_num⟩
  | 10 => ⟨((225616485/8796093022208), (1912612099/8796093022208)), (327/8796093022208), by norm_num⟩
  | 11 => ⟨((-196728983/35184372088832), (-1667724913/35184372088832)), (287/35184372088832), by norm_num⟩
  | 12 => ⟨((78622583/70368744177664), (1333009895/140737488355328)), (231/140737488355328), by norm_num⟩
  | 13 => ⟨((-58008837/281474976710656), (-983513269/562949953421312)), (43/140737488355328), by norm_num⟩
  | 14 => ⟨((79485209/2251799813685248), (1347635325/4503599627370496)), (119/2251799813685248), by norm_num⟩
  | 15 => ⟨((-203303687/36028797018963968), (-1723460467/36028797018963968)), (307/36028797018963968), by norm_num⟩
  | 16 => ⟨((60937619/72057594037927936), (1033169427/144115188075855872)), (93/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1893185122465/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889388158967165/316912650057057350374175801344), (2240509957039/633825300114114700748351602688)), (92421/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472437559744553/9903520314283042199192993792), (2520115095191/39614081257132168796771975168)), (25997/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889525706815887/2475880078570760549798248448), (2677057097695/2475880078570760549798248448)), (110503/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221398976302987/19342813113834066795298816), (2676421438705/154742504910672534362390528)), (55261/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549554323295557/9671406556917033397649408), (19597421015/75557863725914323419136)), (103633/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157348664310533/75557863725914323419136), (2194236145939/604462909807314587353088)), (22675/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887792780068951/75557863725914323419136), (3564368524915/75557863725914323419136)), (147423/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648769875344335/2361183241434822606848), (1336084880069/2361183241434822606848)), (13825/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621448110813129/590295810358705651712), (3672435941331/590295810358705651712)), (76063/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911736997261467/36893488147419103232), (573481263625/9223372036854775808)), (47559/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822655327964715/9223372036854775808), (2578814136685/4611686018427387904)), (53531/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796951375365629/576460752303423488), (5153002810129/1152921504606846976)), (214259/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298626706362329/36028797018963968), (140739953119/4503599627370496)), (187629/144115188075855872), by norm_num⟩
  | 4 => ⟨((745762035064053/18014398509481984), (1686282885235/9007199254740992)), (70437/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489111788142155/9007199254740992), (8413264883775/9007199254740992)), (22045/562949953421312), by norm_num⟩
  | 2 => ⟨((2227643674474251/4503599627370496), (2096523289605/562949953421312)), (176761/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107807895877205/1125899906842624), (25022788447483/2251799813685248)), (1064591/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179633092506377/2251799813685248), (49505814229267/2251799813685248)), (2145337/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179633092506377/2251799813685248), (49505814229267/2251799813685248)), (8183811196334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2108690818539221/2251799813685248), (95838458027927/2251799813685248)), (530937/281474976710656), by norm_num⟩
  | 2 => ⟨((1970597888491827/2251799813685248), (44873810557721/562949953421312)), (8316663/2251799813685248), by norm_num⟩
  | 3 => ⟨((1710204198765963/2251799813685248), (314160204814681/2251799813685248)), (3970513/562949953421312), by norm_num⟩
  | 4 => ⟨((1255041300746175/2251799813685248), (7456231484449/35184372088832)), (3569485/281474976710656), by norm_num⟩
  | 5 => ⟨((598370223386591/2251799813685248), (66491725625237/281474976710656)), (10983579/562949953421312), by norm_num⟩
  | 6 => ⟨((133392588231949/9007199254740992), (282701284360577/2251799813685248)), (88212345/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1427033777/33554432)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-184851991/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1052059911300677/9007199254740992), (-47392392029579/4503599627370496)), (35526587/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1246581397/4294967296), (112310095/4294967296)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((1548819201/4294967296), (-139540051/4294967296)), (109/4294967296), by norm_num⟩
  | 3 => ⟨((-1282890377/4294967296), (57790667/2147483648)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((796965707/4294967296), (-143604413/8589934592)), (29/2147483648), by norm_num⟩
  | 5 => ⟨((-396077077/4294967296), (8921089/1073741824)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((1312286083/34359738368), (-118229725/34359738368)), (25/8589934592), by norm_num⟩
  | 7 => ⟨((-465844059/34359738368), (167879903/137438953472)), (9/8589934592), by norm_num⟩
  | 8 => ⟨((144697375/34359738368), (-6518217/17179869184)), (91/274877906944), by norm_num⟩
  | 9 => ⟨((-319608417/274877906944), (57589905/549755813888)), (103/1099511627776), by norm_num⟩
  | 10 => ⟨((1270715329/4398046511104), (-57242215/2199023255552)), (13/549755813888), by norm_num⟩
  | 11 => ⟨((-287055361/4398046511104), (12931051/2199023255552)), (3/549755813888), by norm_num⟩
  | 12 => ⟨((951074367/70368744177664), (-171373091/140737488355328)), (161/140737488355328), by norm_num⟩
  | 13 => ⟨((-727178775/281474976710656), (131029579/562949953421312)), (125/562949953421312), by norm_num⟩
  | 14 => ⟨((516277535/1125899906842624), (-46513753/1125899906842624)), (91/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1368428245/18014398509481984), (123287823/18014398509481984)), (61/9007199254740992), by norm_num⟩
  | 16 => ⟨((850104111/72057594037927936), (-76589683/72057594037927936)), (77/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-117042116211/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778663309696847/633825300114114700748351602688), (-8656098419/39614081257132168796771975168)), (46107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889623279679275/39614081257132168796771975168), (-155780687659/39614081257132168796771975168)), (51871/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472347759736721/618970019642690137449562112), (-82740402951/1237940039285380274899124224)), (110227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771057397043203/154742504910672534362390528), (-165440125363/154742504910672534362390528)), (27557/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193678572623083/1208925819614629174706176), (-2422764197/151115727451828646838272)), (25835/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314669890003825/151115727451828646838272), (-135631602037/604462909807314587353088)), (11303/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887614935023175/75557863725914323419136), (-220320400271/75557863725914323419136)), (146941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324351702310469/1180591620717411303424), (-82584750053/2361183241434822606848)), (861/36893488147419103232), by norm_num⟩
  | 9 => ⟨((405316508601187/147573952589676412928), (-113496537923/295147905179352825856)), (151539/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823247474879249/73786976294838206464), (-141784487709/36893488147419103232)), (47357/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822401970645559/9223372036854775808), (-159389134683/4611686018427387904)), (106557/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99603202310015/72057594037927936), (-79620626015/288230376151711744)), (213123/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74643051293787/9007199254740992), (-69584956375/36028797018963968)), (186493/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491201192146653/36028797018963968), (-416845932065/36028797018963968)), (279759/36028797018963968), by norm_num⟩
  | 3 => ⟨((372178848293365/2251799813685248), (-519897832237/9007199254740992)), (43717/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113436199165243/2251799813685248), (-1036325212443/4503599627370496)), (349791/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107256167495089/1125899906842624), (-1545840657097/2251799813685248)), (1049657/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088819027383487/1125899906842624), (-23884890049/17592186044416)), (1050245/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088819027383487/1125899906842624), (-23884890049/17592186044416)), (4006366734031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131619663798331/140737488355328), (-5913153188957/2251799813685248)), (508541/281474976710656), by norm_num⟩
  | 2 => ⟨((1969465224063649/2251799813685248), (-5530063409641/1125899906842624)), (3815441/1125899906842624), by norm_num⟩
  | 3 => ⟨((1722475914074737/2251799813685248), (-19346777641535/2251799813685248)), (13423179/2251799813685248), by norm_num⟩
  | 4 => ⟨((658706195535983/1125899906842624), (-14798988036137/1125899906842624)), (20766321/2251799813685248), by norm_num⟩
  | 5 => ⟨((1540722543291633/4503599627370496), (-17316255286677/1125899906842624)), (24844527/2251799813685248), by norm_num⟩
  | 6 => ⟨((1052059911300677/9007199254740992), (-47392392029579/4503599627370496)), (35526587/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-184851991/4194304)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1526450889/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((15101733509237/2251799813685248), (-984003905975591/9007199254740992)), (311898933/18014398509481984), by norm_num⟩
  | 1 => ⟨((-9235187/536870912), (1203498929/4294967296)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((23687787/1073741824), (-1543456903/4294967296)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((-10126329/536870912), (1319629597/4294967296)), (27/536870912), by norm_num⟩
  | 4 => ⟨((25973521/2147483648), (-211548943/1073741824)), (279/8589934592), by norm_num⟩
  | 5 => ⟨((-53296613/8589934592), (868179721/8589934592)), (289/17179869184), by norm_num⟩
  | 6 => ⟨((91135409/34359738368), (-371139503/8589934592)), (249/34359738368), by norm_num⟩
  | 7 => ⟨((-66787917/68719476736), (1087947463/68719476736)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((21413453/68719476736), (-1395265073/274877906944)), (119/137438953472), by norm_num⟩
  | 9 => ⟨((-48821709/549755813888), (1590570779/1099511627776)), (273/1099511627776), by norm_num⟩
  | 10 => ⟨((100180169/4398046511104), (-1631893399/4398046511104)), (141/2199023255552), by norm_num⟩
  | 11 => ⟨((-93438931/17592186044416), (380520357/4398046511104)), (265/17592186044416), by norm_num⟩
  | 12 => ⟨((79888709/70368744177664), (-1301353927/70368744177664)), (229/70368744177664), by norm_num⟩
  | 13 => ⟨((-31524691/140737488355328), (1027048283/281474976710656)), (183/281474976710656), by norm_num⟩
  | 14 => ⟨((92410555/2251799813685248), (-1505329619/2251799813685248)), (271/2251799813685248), by norm_num⟩
  | 15 => ⟨((-15801893/2251799813685248), (1029625131/9007199254740992)), (187/9007199254740992), by norm_num⟩
  | 16 => ⟨((81062111/72057594037927936), (-1320468159/72057594037927936)), (121/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-983135952101/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778554014245969/633825300114114700748351602688), (-581612986187/158456325028528675187087900672)), (46215/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944750091595291/19807040628566084398385987584), (-2616750701001/39614081257132168796771975168)), (51999/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889260065072689/2475880078570760549798248448), (-694917481677/618970019642690137449562112)), (110515/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885463108267909/77371252455336267181195264), (-86842624795/4835703278458516698824704)), (55267/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549305379871747/9671406556917033397649408), (-2604528904527/9671406556917033397649408)), (51823/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((19665180309921/9444732965739290427392), (-1139106596859/302231454903657293676544)), (90711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235929873950191/9444732965739290427392), (-1850345728619/37778931862957161709568)), (147443/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648637246379543/2361183241434822606848), (-43348277285/73786976294838206464)), (110615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621083516719883/590295810358705651712), (-476581560853/73786976294838206464)), (152151/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823018455247605/73786976294838206464), (-37209557963/576460752303423488)), (95135/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911071562938045/4611686018427387904), (-669258102319/1152921504606846976)), (107083/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593390898140273/1152921504606846976), (-2674464752139/576460752303423488)), (107153/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194059347619809/144115188075855872), (-4674541715767/144115188075855872)), (187677/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490853639763977/36028797018963968), (-875035428957/4503599627370496)), (281831/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488275126357857/9007199254740992), (-4365104946415/4503599627370496)), (352845/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225974479413677/4503599627370496), (-17400112847951/4503599627370496)), (353679/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213122320296145/2251799813685248), (-25949843116523/2251799813685248)), (1065221/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174687432328061/2251799813685248), (-51301023188377/2251799813685248)), (2147245/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174687432328061/2251799813685248), (-51301023188377/2251799813685248)), (8191089638716887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099046995483107/2251799813685248), (-99088462229465/2251799813685248)), (4245265/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952295998597213/2251799813685248), (-184733418721983/2251799813685248)), (8288187/2251799813685248), by norm_num⟩
  | 3 => ⟨((209684116189489/281474976710656), (-320325378824747/2251799813685248)), (15731505/2251799813685248), by norm_num⟩
  | 4 => ⟨((1204062219235293/2251799813685248), (-238625631083985/1125899906842624)), (27914005/2251799813685248), by norm_num⟩
  | 5 => ⟨((1085351418116519/4503599627370496), (-1020766074082521/4503599627370496)), (20842081/1125899906842624), by norm_num⟩
  | 6 => ⟨((15101733509237/2251799813685248), (-984003905975591/9007199254740992)), (311898933/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1526450889/33554432)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1570553973/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-878523061683997/9007199254740992), (-288925509396477/9007199254740992)), (40588489/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105533945/4294967296), (181792017/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-729391865/2147483648), (-479759555/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((641635649/2147483648), (422037657/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((-846656631/4294967296), (-278445393/4294967296)), (81/2147483648), by norm_num⟩
  | 5 => ⟨((893750155/8589934592), (146966671/4294967296)), (173/8589934592), by norm_num⟩
  | 6 => ⟨((-786219299/17179869184), (-64642245/4294967296)), (307/34359738368), by norm_num⟩
  | 7 => ⟨((1185644459/68719476736), (97482623/17179869184)), (117/34359738368), by norm_num⟩
  | 8 => ⟨((-782245925/137438953472), (-514524461/274877906944)), (39/34359738368), by norm_num⟩
  | 9 => ⟨((917507485/549755813888), (301746567/549755813888)), (185/549755813888), by norm_num⟩
  | 10 => ⟨((-968541941/2199023255552), (-79632649/549755813888)), (197/2199023255552), by norm_num⟩
  | 11 => ⟨((929468257/8796093022208), (305680183/8796093022208)), (191/8796093022208), by norm_num⟩
  | 12 => ⟨((-817640005/35184372088832), (-268902509/35184372088832)), (85/17592186044416), by norm_num⟩
  | 13 => ⟨((663938107/140737488355328), (436707161/281474976710656)), (139/140737488355328), by norm_num⟩
  | 14 => ⟨((-31288763/35184372088832), (-329284353/1125899906842624)), (53/281474976710656), by norm_num⟩
  | 15 => ⟨((352310781/2251799813685248), (463466819/9007199254740992)), (301/9007199254740992), by norm_num⟩
  | 16 => ⟨((-929768349/36028797018963968), (-76444719/9007199254740992)), (201/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-3678391216635/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889224131032893/316912650057057350374175801344), (-4351736628233/633825300114114700748351602688)), (92629/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889380829623753/39614081257132168796771975168), (-1223677049883/9903520314283042199192993792)), (104235/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889132747068265/2475880078570760549798248448), (-5199417173197/2475880078570760549798248448)), (110781/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770798331095249/154742504910672534362390528), (-5198055723329/154742504910672534362390528)), (55409/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774592442404517/4835703278458516698824704), (-2435865474547/4835703278458516698824704)), (51965/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314616376171565/151115727451828646838272), (-4261318568439/604462909807314587353088)), (90977/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943632778420653/37778931862957161709568), (-3460965997717/37778931862957161709568)), (36977/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648571715524051/2361183241434822606848), (-5189077747667/4722366482869645213696)), (55497/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810450853581755/295147905179352825856), (-1782782434779/147573952589676412928)), (76359/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911394398589273/36893488147419103232), (-8908135881621/73786976294838206464)), (95525/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821881471451039/9223372036854775808), (-5006856821097/4611686018427387904)), (107571/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796562570347235/576460752303423488), (-10003794381853/1152921504606846976)), (215405/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596911102713037/72057594037927936), (-1092770935377/18014398509481984)), (188775/144115188075855872), by norm_num⟩
  | 4 => ⟨((372622186562921/9007199254740992), (-3272740615357/9007199254740992)), (70939/9007199254740992), by norm_num⟩
  | 3 => ⟨((743901504201785/4503599627370496), (-16324734790085/9007199254740992)), (177867/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112491248539473/2251799813685248), (-1016647288031/140737488355328)), (357295/2251799813685248), by norm_num⟩
  | 1 => ⟨((276439484627659/281474976710656), (-3031731250483/140737488355328)), (33741/70368744177664), by norm_num⟩
  | 0 => ⟨((271375753168929/281474976710656), (-23963264502717/562949953421312)), (1095427/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271375753168929/281474976710656), (-23963264502717/562949953421312)), (4178722385886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1044515441557745/1125899906842624), (-92413883874245/1125899906842624)), (2205507/1125899906842624), by norm_num⟩
  | 2 => ⟨((480714215864641/562949953421312), (-171467691105273/1125899906842624)), (2227113/562949953421312), by norm_num⟩
  | 3 => ⟨((1589738936481761/2251799813685248), (-146419688241991/562949953421312)), (17927617/2251799813685248), by norm_num⟩
  | 4 => ⟨((970001982953073/2251799813685248), (-826961892619997/2251799813685248)), (34639009/2251799813685248), by norm_num⟩
  | 5 => ⟨((228295493698069/4503599627370496), (-1424912944379783/4503599627370496)), (110569419/4503599627370496), by norm_num⟩
  | 6 => ⟨((-878523061683997/9007199254740992), (-288925509396477/9007199254740992)), (40588489/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1570553973/33554432)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-402903241/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-537612947266215/9007199254740992), (5357618381989/70368744177664)), (158499717/9007199254740992), by norm_num⟩
  | 1 => ⟨((694219041/4294967296), (-885540743/4294967296)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-939990007/4294967296), (1199044393/4294967296)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((26516043/134217728), (-541178735/2147483648)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-574454205/4294967296), (732769591/4294967296)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((311130165/4294967296), (-793750735/8589934592)), (193/8589934592), by norm_num⟩
  | 6 => ⟨((-561704071/17179869184), (179126403/4294967296)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((869213041/68719476736), (-1108761809/68719476736)), (275/68719476736), by norm_num⟩
  | 8 => ⟨((-294234069/68719476736), (187661415/34359738368)), (47/34359738368), by norm_num⟩
  | 9 => ⟨((354133613/274877906944), (-451730251/274877906944)), (229/549755813888), by norm_num⟩
  | 10 => ⟨((-767209281/2199023255552), (489323279/1099511627776)), (251/2199023255552), by norm_num⟩
  | 11 => ⟨((188876477/2199023255552), (-963717821/8796093022208)), (249/8796093022208), by norm_num⟩
  | 12 => ⟨((-340991321/17592186044416), (54370755/2199023255552)), (227/35184372088832), by norm_num⟩
  | 13 => ⟨((4439527/1099511627776), (-724867613/140737488355328)), (191/140737488355328), by norm_num⟩
  | 14 => ⟨((-879357219/1125899906842624), (1121701649/1125899906842624)), (149/562949953421312), by norm_num⟩
  | 15 => ⟨((158756233/1125899906842624), (-810033167/4503599627370496)), (217/4503599627370496), by norm_num⟩
  | 16 => ⟨((-859839697/36028797018963968), (137100655/4503599627370496)), (37/4503599627370496), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (2912214139731/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889180174662877/316912650057057350374175801344), (861242264601/158456325028528675187087900672)), (23135/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889282160897469/39614081257132168796771975168), (1937395718245/19807040628566084398385987584)), (104129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889028215316885/2475880078570760549798248448), (4115983822935/2475880078570760549798248448)), (55331/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885347070416275/77371252455336267181195264), (4114879242071/154742504910672534362390528)), (110691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774543784517941/4835703278458516698824704), (3856525965127/9671406556917033397649408)), (51901/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258380715720311/604462909807314587353088), (1686643612181/302231454903657293676544)), (45429/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58972764174783/2361183241434822606848), (5479393073219/75557863725914323419136)), (36925/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324260299255783/1180591620717411303424), (256726354455/295147905179352825856)), (110825/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620762098627545/590295810358705651712), (5644856017199/590295810358705651712)), (9529/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455653932388407/18446744073709551616), (3525693322461/36893488147419103232)), (190701/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455422187898019/2305843009213693952), (3963187030571/4611686018427387904)), (214705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592934892910813/1152921504606846976), (7918334760047/1152921504606846976)), (107457/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193658513588649/144115188075855872), (1729876597257/36028797018963968)), (188283/144115188075855872), by norm_num⟩
  | 4 => ⟨((745124371589685/18014398509481984), (1295150718421/4503599627370496)), (141447/18014398509481984), by norm_num⟩
  | 3 => ⟨((743756327981223/4503599627370496), (3229989049249/2251799813685248)), (44305/1125899906842624), by norm_num⟩
  | 2 => ⟨((556107652355921/1125899906842624), (1609089518019/281474976710656)), (711353/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210759610194375/2251799813685248), (4797819117909/281474976710656)), (536613/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169776887759077/2251799813685248), (75826350784169/2251799813685248)), (271417/281474976710656), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169776887759077/2251799813685248), (75826350784169/2251799813685248)), (1035373688817882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2088188336548767/2251799813685248), (36532169159687/562949953421312)), (4330723/2251799813685248), by norm_num⟩
  | 2 => ⟨((1926981658134481/2251799813685248), (135511245865567/1125899906842624)), (1074275/281474976710656), by norm_num⟩
  | 3 => ⟨((101024886227723/140737488355328), (463855949657521/2251799813685248)), (16777769/2251799813685248), by norm_num⟩
  | 4 => ⟨((1064739733324043/2251799813685248), (332967392610353/1125899906842624)), (30999225/2251799813685248), by norm_num⟩
  | 5 => ⟨((153255533053455/1125899906842624), (1259520888700469/4503599627370496)), (23825195/1125899906842624), by norm_num⟩
  | 6 => ⟨((-537612947266215/9007199254740992), (5357618381989/70368744177664)), (158499717/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-402903241/8388608)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile007Terms1
