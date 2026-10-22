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
namespace Reinmann.XiBand97.Tile010Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (24671/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (24671/1280))
  have he : value ((69/80), (24671/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1793131449/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-205943556425061/2251799813685248), (3338114856061/1125899906842624)), (33681823/2251799813685248), by norm_num⟩
  | 1 => ⟨((1089089931/4294967296), (-35305861/4294967296)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((-754899615/2147483648), (12236079/1073741824)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((1395350773/4294967296), (-45234153/4294967296)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((-1934366909/8589934592), (62707851/8589934592)), (327/8589934592), by norm_num⟩
  | 5 => ⟨((1072640775/8589934592), (-4346577/1073741824)), (183/8589934592), by norm_num⟩
  | 6 => ⟨((-247832643/4294967296), (32136721/17179869184)), (85/8589934592), by norm_num⟩
  | 7 => ⟨((785300561/34359738368), (-50915377/68719476736)), (17/4294967296), by norm_num⟩
  | 8 => ⟨((-272164435/34359738368), (17645925/68719476736)), (95/68719476736), by norm_num⟩
  | 9 => ⟨((335377797/137438953472), (-43488793/549755813888)), (59/137438953472), by norm_num⟩
  | 10 => ⟨((-371945879/549755813888), (48230615/2199023255552)), (33/274877906944), by norm_num⟩
  | 11 => ⟨((750002145/4398046511104), (-48626785/8796093022208)), (67/2199023255552), by norm_num⟩
  | 12 => ⟨((-693149163/17592186044416), (11235173/8796093022208)), (249/35184372088832), by norm_num⟩
  | 13 => ⟨((1182656955/140737488355328), (-19169547/70368744177664)), (107/70368744177664), by norm_num⟩
  | 14 => ⟨((-936863239/562949953421312), (60742023/1125899906842624)), (171/562949953421312), by norm_num⟩
  | 15 => ⟨((692676387/2251799813685248), (-44910039/4503599627370496)), (255/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1920506739/36028797018963968), (31129267/18014398509481984)), (89/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (2025031108723/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778268640272541/633825300114114700748351602688), (2395266289469/316912650057057350374175801344)), (181/1237940039285380274899124224), by norm_num⟩
  | 16 => ⟨((944589339712919/19807040628566084398385987584), (5388195807087/39614081257132168796771975168)), (52143/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888917855371895/2475880078570760549798248448), (715444732329/309485009821345068724781056)), (110839/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221322914884987/19342813113834066795298816), (5721982740263/154742504910672534362390528)), (110879/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387245795838603/2417851639229258349412352), (2681342764151/4835703278458516698824704)), (103991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157286111048799/75557863725914323419136), (2345338426185/302231454903657293676544)), (45517/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943489158304881/37778931862957161709568), (7619213688737/75557863725914323419136)), (148009/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648463896161153/2361183241434822606848), (5711666745591/4722366482869645213696)), (27769/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620604865683033/590295810358705651712), (7849084775129/590295810358705651712)), (76421/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822417239141475/73786976294838206464), (9804672608757/73786976294838206464)), (47805/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227682846817477/1152921504606846976), (1377633818291/1152921504606846976)), (107677/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592705578960991/1152921504606846976), (2752398275803/288230376151711744)), (53911/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193454119866373/144115188075855872), (9620489045273/144115188075855872)), (189015/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489934689516085/36028797018963968), (14404941772873/36028797018963968)), (284175/36028797018963968), by norm_num⟩
  | 3 => ⟨((743553542275073/4503599627370496), (17961082275761/9007199254740992)), (356363/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111790338696435/2251799813685248), (8946760757601/1125899906842624)), (89521/562949953421312), by norm_num⟩
  | 1 => ⟨((1104694260229637/1125899906842624), (13335833627897/562949953421312)), (541439/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083327306937177/1125899906842624), (26335302282207/562949953421312)), (550101/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083327306937177/1125899906842624), (26335302282207/562949953421312)), (2098468782665061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((259975121734829/281474976710656), (101358040534051/1125899906842624)), (555035/281474976710656), by norm_num⟩
  | 2 => ⟨((118918160913553/140737488355328), (187232053339725/1125899906842624)), (1125213/281474976710656), by norm_num⟩
  | 3 => ⟨((1545434027658633/2251799813685248), (9887775685881/35184372088832)), (4551531/562949953421312), by norm_num⟩
  | 4 => ⟨((882808565547061/2251799813685248), (868618883647297/2251799813685248)), (35222955/2251799813685248), by norm_num⟩
  | 5 => ⟨((22073186278411/4503599627370496), (1362153395731553/4503599627370496)), (109584255/4503599627370496), by norm_num⟩
  | 6 => ⟨((-205943556425061/2251799813685248), (3338114856061/1125899906842624)), (33681823/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1793131449/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-916169771/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-565574655614429/18014398509481984), (1458623549903291/18014398509481984)), (137870395/9007199254740992), by norm_num⟩
  | 1 => ⟨((95510105/1073741824), (-492643321/2147483648)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((-33825063/268435456), (1395763631/4294967296)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((511112639/4294967296), (-659082691/2147483648)), (255/4294967296), by norm_num⟩
  | 4 => ⟨((-362022787/4294967296), (466830469/2147483648)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((102568779/2147483648), (-1058104251/8589934592)), (105/4294967296), by norm_num⟩
  | 6 => ⟨((-96866411/4294967296), (999278361/17179869184)), (25/2147483648), by norm_num⟩
  | 7 => ⟨((313649381/34359738368), (-101113171/4294967296)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((-222158903/68719476736), (1145900741/137438953472)), (117/68719476736), by norm_num⟩
  | 9 => ⟨((4370997/4294967296), (-1442925009/549755813888)), (297/549755813888), by norm_num⟩
  | 10 => ⟨((-79257389/274877906944), (408811439/549755813888)), (85/549755813888), by norm_num⟩
  | 11 => ⟨((326622679/4398046511104), (-421181827/2199023255552)), (177/4398046511104), by norm_num⟩
  | 12 => ⟨((-308463911/17592186044416), (397765991/8796093022208)), (169/17592186044416), by norm_num⟩
  | 13 => ⟨((537811735/140737488355328), (-1387022663/140737488355328)), (297/140737488355328), by norm_num⟩
  | 14 => ⟨((-435352967/562949953421312), (1122780319/562949953421312)), (121/281474976710656), by norm_num⟩
  | 15 => ⟨((328919423/2251799813685248), (-424143491/1125899906842624)), (23/281474976710656), by norm_num⟩
  | 16 => ⟨((-465949449/18014398509481984), (1201688999/18014398509481984)), (263/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (2527970627911/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889097792598799/316912650057057350374175801344), (2989899756135/633825300114114700748351602688)), (92495/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889096928713011/39614081257132168796771975168), (3362917249063/39614081257132168796771975168)), (26019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944415784866759/1237940039285380274899124224), (3572208313697/2475880078570760549798248448)), (55301/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770497679196477/154742504910672534362390528), (3571205956311/154742504910672534362390528)), (110627/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548903581589977/9671406556917033397649408), (836735223657/2417851639229258349412352)), (103739/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258219921923771/604462909807314587353088), (2927508947963/604462909807314587353088)), (45399/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943433764727609/37778931862957161709568), (4755207165919/75557863725914323419136)), (147595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296845823725329/4722366482869645213696), (3564660612333/4722366482869645213696)), (27685/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620493979552477/590295810358705651712), (4898574515173/590295810358705651712)), (152337/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911140679346881/36893488147419103232), (3059484936651/36893488147419103232)), (95263/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910656826377295/4611686018427387904), (6878003746671/9223372036854775808)), (107243/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796280563763797/576460752303423488), (3435356529973/576460752303423488)), (214667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596666483119337/72057594037927936), (6003680169971/144115188075855872)), (188037/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489763409943507/36028797018963968), (4494576694549/18014398509481984)), (8827/1125899906842624), by norm_num⟩
  | 3 => ⟨((1486911202473637/9007199254740992), (5603923072085/4503599627370496)), (176897/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223243279420307/4503599627370496), (11165045508297/2251799813685248)), (709735/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209017340422837/2251799813685248), (16640890884371/1125899906842624)), (267497/562949953421312), by norm_num⟩
  | 0 => ⟨((541611487437317/562949953421312), (32857014146861/1125899906842624)), (2161605/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541611487437317/562949953421312), (32857014146861/1125899906842624)), (8245868691451262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520602418915319/562949953421312), (126446311588995/2251799813685248)), (4285505/2251799813685248), by norm_num⟩
  | 2 => ⟨((479665350502727/562949953421312), (116934472196119/1125899906842624)), (4203777/1125899906842624), by norm_num⟩
  | 3 => ⟨((805259612860559/1125899906842624), (99634815228105/562949953421312)), (16073823/2251799813685248), by norm_num⟩
  | 4 => ⟨((1081329973974801/2251799813685248), (35630117850801/140737488355328)), (28682169/2251799813685248), by norm_num⟩
  | 5 => ⟨((749872303196213/4503599627370496), (547514594136455/2251799813685248)), (84139051/4503599627370496), by norm_num⟩
  | 6 => ⟨((-565574655614429/18014398509481984), (1458623549903291/18014398509481984)), (137870395/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-916169771/16777216)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-467326479/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((995069465090703/18014398509481984), (1107923369178525/18014398509481984)), (175911283/18014398509481984), by norm_num⟩
  | 1 => ⟨((-342860303/2147483648), (-763490299/4294967296)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((990993737/4294967296), (1103385399/4294967296)), (45/1073741824), by norm_num⟩
  | 3 => ⟨((-954780103/4294967296), (-1063064665/4294967296)), (11/268435456), by norm_num⟩
  | 4 => ⟨((689917361/4294967296), (768163021/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((-398823531/4294967296), (-888110681/8589934592)), (151/8589934592), by norm_num⟩
  | 6 => ⟨((768498847/17179869184), (855656677/17179869184)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((-79330263/4294967296), (-706618827/34359738368)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((917175807/137438953472), (1021195551/137438953472)), (45/34359738368), by norm_num⟩
  | 9 => ⟨((-73638307/34359738368), (-81989855/34359738368)), (117/274877906944), by norm_num⟩
  | 10 => ⟨((681094665/1099511627776), (189584929/274877906944)), (137/1099511627776), by norm_num⟩
  | 11 => ⟨((-715860649/4398046511104), (-398524309/2199023255552)), (73/2199023255552), by norm_num⟩
  | 12 => ⟨((344850567/8796093022208), (23997571/549755813888)), (143/17592186044416), by norm_num⟩
  | 13 => ⟨((-613382363/70368744177664), (-682947953/70368744177664)), (129/70368744177664), by norm_num⟩
  | 14 => ⟨((506543731/281474976710656), (1127984843/562949953421312)), (27/70368744177664), by norm_num⟩
  | 15 => ⟨((-390426585/1125899906842624), (-434706071/1125899906842624)), (169/2251799813685248), by norm_num⟩
  | 16 => ⟨((141059747/2251799813685248), (628231075/9007199254740992)), (31/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (273226120175/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111132720746159/39614081257132168796771975168), (646251340629/316912650057057350374175801344)), (11541/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889016102739681/39614081257132168796771975168), (1453751628391/39614081257132168796771975168)), (103877/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888746000746963/2475880078570760549798248448), (1544218439703/2475880078570760549798248448)), (110379/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770412457058921/154742504910672534362390528), (12060756951/1208925819614629174706176)), (55195/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548824054098219/9671406556917033397649408), (361705464829/2417851639229258349412352)), (51751/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629075351666283/302231454903657293676544), (1265500345707/604462909807314587353088)), (5661/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471688934636019/18889465931478580854784), (1027779754131/37778931862957161709568)), (73603/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296762583046463/4722366482869645213696), (770450653943/2361183241434822606848)), (110423/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620380501503635/590295810358705651712), (1058745771575/295147905179352825856)), (75931/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911070487943729/36893488147419103232), (1322497071527/36893488147419103232)), (189873/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910578866385851/4611686018427387904), (1486524477421/4611686018427387904)), (106835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592407715848499/1152921504606846976), (2969840412203/1152921504606846976)), (53437/288230376151711744), by norm_num⟩
  | 5 => ⟨((596600772971529/72057594037927936), (2595005251847/144115188075855872)), (93559/72057594037927936), by norm_num⟩
  | 4 => ⟨((744785946041489/18014398509481984), (1942654449765/18014398509481984)), (280855/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486681588408937/9007199254740992), (4844063160891/9007199254740992)), (351379/9007199254740992), by norm_num⟩
  | 2 => ⟨((555703311616103/1125899906842624), (9650508223633/4503599627370496)), (703693/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104222369853841/1125899906842624), (14382068959931/2251799813685248)), (1057891/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165587323206701/2251799813685248), (28391468425273/2251799813685248)), (1062623/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165587323206701/2251799813685248), (28391468425273/2251799813685248)), (4053585056785201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1041158798943225/1125899906842624), (54608943242047/2251799813685248)), (2070675/1125899906842624), by norm_num⟩
  | 2 => ⟨((962133582090981/1125899906842624), (100997577869763/2251799813685248)), (7860167/2251799813685248), by norm_num⟩
  | 3 => ⟨((819922709374883/1125899906842624), (172614209820573/2251799813685248)), (7069421/1125899906842624), by norm_num⟩
  | 4 => ⟨((1180965250907657/2251799813685248), (62852083800941/562949953421312)), (22760533/2251799813685248), by norm_num⟩
  | 5 => ⟨((1182585383256069/4503599627370496), (527408352838047/4503599627370496)), (14478013/1125899906842624), by norm_num⟩
  | 6 => ⟨((995069465090703/18014398509481984), (1107923369178525/18014398509481984)), (175911283/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-467326479/8388608)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1904273105/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1392117480484561/18014398509481984), (-143341044076429/9007199254740992)), (106627747/18014398509481984), by norm_num⟩
  | 1 => ⟨((-977278941/4294967296), (100626697/2147483648)), (77/4294967296), by norm_num⟩
  | 2 => ⟨((89923069/268435456), (-296289169/4294967296)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((-1412122611/4294967296), (290801793/4294967296)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((1039477215/4294967296), (-107031017/2147483648)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-306067723/2147483648), (252117039/8589934592)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((600798489/8589934592), (-123723873/8589934592)), (13/2147483648), by norm_num⟩
  | 7 => ⟨((-1010865423/34359738368), (52042485/8589934592)), (45/17179869184), by norm_num⟩
  | 8 => ⟨((1488215777/137438953472), (-306471843/137438953472)), (67/68719476736), by norm_num⟩
  | 9 => ⟨((-486884505/137438953472), (200530587/274877906944)), (45/137438953472), by norm_num⟩
  | 10 => ⟨((286720343/274877906944), (-236180031/1099511627776)), (27/274877906944), by norm_num⟩
  | 11 => ⟨((-1227971715/4398046511104), (31609895/549755813888)), (117/4398046511104), by norm_num⟩
  | 12 => ⟨((1205229261/17592186044416), (-31024469/2199023255552)), (29/4398046511104), by norm_num⟩
  | 13 => ⟨((-1091915081/70368744177664), (224860691/70368744177664)), (107/70368744177664), by norm_num⟩
  | 14 => ⟨((459296761/140737488355328), (-189168167/281474976710656)), (23/70368744177664), by norm_num⟩
  | 15 => ⟨((-360632343/562949953421312), (297063533/2251799813685248)), (73/1125899906842624), by norm_num⟩
  | 16 => ⟨((132732491/1125899906842624), (-218671361/9007199254740992)), (109/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-264551600793/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778052539189969/633825300114114700748351602688), (-156421409857/316912650057057350374175801344)), (92231/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888936299993143/39614081257132168796771975168), (-351871030403/39614081257132168796771975168)), (51881/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59020665443077/77371252455336267181195264), (-93441543087/618970019642690137449562112)), (55125/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442581961183427/38685626227668133590597632), (-11676791511/4835703278458516698824704)), (110253/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774372415055217/4835703278458516698824704), (-350188143359/9671406556917033397649408)), (103365/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081482335597/604462909807314587353088), (-38287384233/75557863725914323419136)), (90447/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886643441750895/75557863725914323419136), (-497519442861/75557863725914323419136)), (146981/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648339262101993/2361183241434822606848), (-93237551493/1180591620717411303424)), (110241/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620265186395743/590295810358705651712), (-512498997375/590295810358705651712)), (37897/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821997230183893/73786976294838206464), (-160040698369/18446744073709551616)), (23687/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820996565511347/9223372036854775808), (-719549901043/9223372036854775808)), (213199/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796123615322705/576460752303423488), (-701913283/1125899906842624)), (213219/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149132735871389/18014398509481984), (-628025936073/144115188075855872)), (186589/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489363930460995/36028797018963968), (-470132548411/18014398509481984)), (34991/4503599627370496), by norm_num⟩
  | 3 => ⟨((371606074658837/2251799813685248), (-586116887541/4503599627370496)), (87497/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222306614960443/4503599627370496), (-1167600486011/2251799813685248)), (87527/562949953421312), by norm_num⟩
  | 1 => ⟨((1103852263786293/1125899906842624), (-3479726488263/2251799813685248)), (525467/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164185033702271/2251799813685248), (-6867699889905/2251799813685248)), (526091/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164185033702271/2251799813685248), (-6867699889905/2251799813685248)), (2006877901317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2079958292177829/2251799813685248), (-1650121519169/281474976710656)), (253613/140737488355328), by norm_num⟩
  | 2 => ⟨((480288279317955/562949953421312), (-3048391705193/281474976710656)), (7543867/2251799813685248), by norm_num⟩
  | 3 => ⟨((1638793353338377/2251799813685248), (-41612418237215/2251799813685248)), (1629463/281474976710656), by norm_num⟩
  | 4 => ⟨((1191896386740551/2251799813685248), (-60568576308637/2251799813685248)), (19455791/2251799813685248), by norm_num⟩
  | 5 => ⟨((1258503030045267/4503599627370496), (-64118903299967/2251799813685248)), (21642863/2251799813685248), by norm_num⟩
  | 6 => ⟨((1392117480484561/18014398509481984), (-143341044076429/9007199254740992)), (106627747/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1904273105/33554432)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1937446297/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((125801001227465/4503599627370496), (-315821932426191/4503599627370496)), (192006537/18014398509481984), by norm_num⟩
  | 1 => ⟨((-359407539/4294967296), (902288395/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((269172191/2147483648), (-1351507233/4294967296)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-537578547/4294967296), (337396153/1073741824)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((402610351/4294967296), (-1010748545/4294967296)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-482445129/8589934592), (1211172815/8589934592)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((240879407/8589934592), (-604724915/8589934592)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((-206174347/17179869184), (258799135/8589934592)), (171/34359738368), by norm_num⟩
  | 8 => ⟨((308821573/68719476736), (-775292921/68719476736)), (65/34359738368), by norm_num⟩
  | 9 => ⟨((-411176335/274877906944), (1032253345/274877906944)), (175/274877906944), by norm_num⟩
  | 10 => ⟨((492709687/1099511627776), (-154617733/137438953472)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((-67092105/549755813888), (673735757/2199023255552)), (233/4398046511104), by norm_num⟩
  | 12 => ⟨((535973291/17592186044416), (-672777317/8796093022208)), (235/17592186044416), by norm_num⟩
  | 13 => ⟨((-494040765/70368744177664), (1240283521/70368744177664)), (109/35184372088832), by norm_num⟩
  | 14 => ⟨((26428819/17592186044416), (-1061587821/281474976710656)), (47/70368744177664), by norm_num⟩
  | 15 => ⟨((-168903821/562949953421312), (424031053/562949953421312)), (19/140737488355328), by norm_num⟩
  | 16 => ⟨((126497657/2251799813685248), (-1270283511/9007199254740992)), (115/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1552363189621/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888991319956713/316912650057057350374175801344), (-917798626605/316912650057057350374175801344)), (92381/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472214395973897/9903520314283042199192993792), (-2064584831107/39614081257132168796771975168)), (25985/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888577550996473/2475880078570760549798248448), (-2193043315821/2475880078570760549798248448)), (55225/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885121990480063/77371252455336267181195264), (-1096196639609/77371252455336267181195264)), (55233/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774333039902863/4835703278458516698824704), (-2054678288963/9671406556917033397649408)), (51789/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314503111981921/151115727451828646838272), (-1797153377885/604462909807314587353088)), (90647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471632755327181/18889465931478580854784), (-2919080860855/75557863725914323419136)), (73665/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296593999550835/4722366482869645213696), (-1094089772747/2361183241434822606848)), (110525/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620148625349613/590295810358705651712), (-3006909972511/590295810358705651712)), (76007/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910925510138577/36893488147419103232), (-1877942048563/36893488147419103232)), (95041/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113801961341205/576460752303423488), (-2110793475625/4611686018427387904)), (213931/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24876268380179/18014398509481984), (-4216863460023/1152921504606846976)), (214043/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192915613314011/144115188075855872), (-3684448236031/144115188075855872)), (187413/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489142574975233/36028797018963968), (-5516074340787/36028797018963968)), (140685/18014398509481984), by norm_num⟩
  | 3 => ⟨((743072108414915/4503599627370496), (-1719145906989/2251799813685248)), (352153/9007199254740992), by norm_num⟩
  | 2 => ⟨((555434088498563/1125899906842624), (-13697787979485/4503599627370496)), (352815/2251799813685248), by norm_num⟩
  | 1 => ⟨((34481626862855/35184372088832), (-20408752668329/2251799813685248)), (1061769/2251799813685248), by norm_num⟩
  | 0 => ⟨((67572671891743/70368744177664), (-40268891322313/2251799813685248)), (1068455/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((67572671891743/70368744177664), (-40268891322313/2251799813685248)), (4075832371238326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2075686283590879/2251799813685248), (-38668823958217/1125899906842624)), (4180431/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910690466334439/2251799813685248), (-142578122628587/2251799813685248)), (7994111/2251799813685248), by norm_num⟩
  | 3 => ⟨((403056425689499/562949953421312), (-241959927306737/2251799813685248)), (3644653/562949953421312), by norm_num⟩
  | 4 => ⟨((1128309494818339/2251799813685248), (-173236542374057/1125899906842624)), (12004377/1125899906842624), by norm_num⟩
  | 5 => ⟨((512052053044317/2251799813685248), (-694429174111193/4503599627370496)), (31448349/2251799813685248), by norm_num⟩
  | 6 => ⟨((125801001227465/4503599627370496), (-315821932426191/4503599627370496)), (192006537/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1937446297/33554432)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1969000627/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-694017692473701/18014398509481984), (-1103717356273195/18014398509481984)), (236335625/18014398509481984), by norm_num⟩
  | 1 => ⟨((251883559/2147483648), (801156105/4294967296)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((-766865147/4294967296), (-1219568869/4294967296)), (265/4294967296), by norm_num⟩
  | 3 => ⟨((778246049/4294967296), (618834131/2147483648)), (271/4294967296), by norm_num⟩
  | 4 => ⟨((-296173445/2147483648), (-942027199/4294967296)), (13/268435456), by norm_num⟩
  | 5 => ⟨((721365359/8589934592), (573604589/4294967296)), (255/8589934592), by norm_num⟩
  | 6 => ⟨((-732071007/17179869184), (-1164234695/17179869184)), (261/17179869184), by norm_num⟩
  | 7 => ⟨((19900059/1073741824), (1012725329/34359738368)), (229/34359738368), by norm_num⟩
  | 8 => ⟨((-484689409/68719476736), (-770816247/68719476736)), (11/4294967296), by norm_num⟩
  | 9 => ⟨((327921729/137438953472), (1043007715/274877906944)), (15/17179869184), by norm_num⟩
  | 10 => ⟨((-399346025/549755813888), (-1270184157/1099511627776)), (295/1099511627776), by norm_num⟩
  | 11 => ⟨((110528903/549755813888), (87888731/274877906944)), (165/2199023255552), by norm_num⟩
  | 12 => ⟨((-448676967/8796093022208), (-356772285/4398046511104)), (169/8796093022208), by norm_num⟩
  | 13 => ⟨((420309875/35184372088832), (167107881/8796093022208)), (5/1099511627776), by norm_num⟩
  | 14 => ⟨((-731224483/281474976710656), (-581444221/140737488355328)), (35/35184372088832), by norm_num⟩
  | 15 => ⟨((593661159/1125899906842624), (944117321/1125899906842624)), (229/1125899906842624), by norm_num⟩
  | 16 => ⟨((-28240855/281474976710656), (-44912287/281474976710656)), (11/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-2777329175761/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444478462195537/158456325028528675187087900672), (-820958568615/158456325028528675187087900672)), (23131/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888779992539321/39614081257132168796771975168), (-28855203523/309485009821345068724781056)), (52055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888494839357065/2475880078570760549798248448), (-1961627889055/1237940039285380274899124224)), (110641/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770160965001817/154742504910672534362390528), (-980518195787/38685626227668133590597632)), (27667/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774293964639265/4835703278458516698824704), (-1837843348639/4835703278458516698824704)), (25945/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628971871728451/302231454903657293676544), (-3214969767591/604462909807314587353088)), (90837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886418772021147/75557863725914323419136), (-2610985821483/37778931862957161709568)), (147663/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296509284278883/4722366482869645213696), (-3914419725395/4722366482869645213696)), (110795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810015642286229/295147905179352825856), (-2689491502769/295147905179352825856)), (38105/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821703060520261/73786976294838206464), (-6718715676663/73786976294838206464)), (11915/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1820663164987999/9223372036854775808), (-1887916794589/2305843009213693952)), (214629/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591910762862369/1152921504606846976), (-235720774021/36028797018963968)), (53707/288230376151711744), by norm_num⟩
  | 5 => ⟨((596382018510627/72057594037927936), (-6590514320285/144115188075855872)), (188199/144115188075855872), by norm_num⟩
  | 4 => ⟨((372227574818683/9007199254740992), (-9866462655119/36028797018963968)), (141373/18014398509481984), by norm_num⟩
  | 3 => ⟨((742922658672989/4503599627370496), (-12299346055759/9007199254740992)), (177109/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221113049371169/4503599627370496), (-6124431952505/1125899906842624)), (177699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102912976111763/1125899906842624), (-18247496801261/1125899906842624)), (1072117/2251799813685248), by norm_num⟩
  | 0 => ⟨((540019908404325/562949953421312), (-71988462055433/2251799813685248)), (1084015/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540019908404325/562949953421312), (-71988462055433/2251799813685248)), (4135189060691451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069793973946307/2251799813685248), (-138112464346361/2251799813685248)), (2149033/1125899906842624), by norm_num⟩
  | 2 => ⟨((473507016016297/562949953421312), (-126949271730835/1125899906842624)), (2107143/562949953421312), by norm_num⟩
  | 3 => ⟨((195559004384203/281474976710656), (-427116978888689/2251799813685248)), (8039771/1125899906842624), by norm_num⟩
  | 4 => ⟨((1005925935825227/2251799813685248), (-593491983714931/2251799813685248)), (7110721/562949953421312), by norm_num⟩
  | 5 => ⟨((585890672539313/4503599627370496), (-66281311453055/281474976710656)), (80810131/4503599627370496), by norm_num⟩
  | 6 => ⟨((-694017692473701/18014398509481984), (-1103717356273195/18014398509481984)), (236335625/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1969000627/33554432)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile010Terms2
