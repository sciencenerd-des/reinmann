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
namespace Reinmann.XiBand97.Tile012Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25387/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25387/1280))
  have he : value ((69/80), (25387/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-922585791/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((20648992249079/18014398509481984), (824142301061239/9007199254740992)), (265482331/18014398509481984), by norm_num⟩
  | 1 => ⟨((-13649741/4294967296), (-544788277/2147483648)), (177/4294967296), by norm_num⟩
  | 2 => ⟨((18922559/4294967296), (1510473833/4294967296)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((-8744079/2147483648), (-697987119/2147483648)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((24243735/8589934592), (1935231215/8589934592)), (321/8589934592), by norm_num⟩
  | 5 => ⟨((-13443581/8589934592), (-67070003/536870912)), (45/2147483648), by norm_num⟩
  | 6 => ⟨((12424507/17179869184), (1983547029/34359738368)), (335/34359738368), by norm_num⟩
  | 7 => ⟨((-19684599/68719476736), (-392825723/17179869184)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((3411081/34359738368), (1089144169/137438953472)), (187/137438953472), by norm_num⟩
  | 9 => ⟨((-16813377/549755813888), (-335527649/137438953472)), (233/549755813888), by norm_num⟩
  | 10 => ⟨((2330829/274877906944), (1488448281/2199023255552)), (65/549755813888), by norm_num⟩
  | 11 => ⟨((-18799797/8796093022208), (-375168629/2199023255552)), (33/1099511627776), by norm_num⟩
  | 12 => ⟨((8687351/17592186044416), (693458873/17592186044416)), (123/17592186044416), by norm_num⟩
  | 13 => ⟨((-463201/4398046511104), (-1183185385/140737488355328)), (53/35184372088832), by norm_num⟩
  | 14 => ⟨((23483719/1125899906842624), (1874563689/1125899906842624)), (169/562949953421312), by norm_num⟩
  | 15 => ⟨((-4340713/1125899906842624), (-346492943/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | 16 => ⟨((3008753/4503599627370496), (480341213/9007199254740992)), (11/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1014909948819/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778277848662619/633825300114114700748351602688), (300116326211/79228162514264337593543950336)), (92437/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889189549875711/39614081257132168796771975168), (1350241456461/19807040628566084398385987584)), (104007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888930080791017/2475880078570760549798248448), (1434281483455/1237940039285380274899124224)), (110525/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770596303824069/154742504910672534362390528), (1433887800699/77371252455336267181195264)), (6909/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548996162740941/9671406556917033397649408), (1343851656753/4835703278458516698824704)), (12957/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629150525437291/302231454903657293676544), (2350904382413/604462909807314587353088)), (90721/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886999589579807/75557863725914323419136), (3818652718307/75557863725914323419136)), (36865/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81059066621787/295147905179352825856), (1431309563427/2361183241434822606848)), (55315/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620630757472843/590295810358705651712), (983468889447/147573952589676412928)), (38043/147573952589676412928), by norm_num⟩
  | 8 => ⟨((56951650314471/2305843009213693952), (2457003947351/36893488147419103232)), (190299/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910753596393077/4611686018427387904), (1380918616833/2305843009213693952)), (214203/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592755487101535/1152921504606846976), (1379487241157/288230376151711744)), (53587/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193503950092985/144115188075855872), (1205442760989/36028797018963968)), (93859/72057594037927936), by norm_num⟩
  | 4 => ⟨((5820397333191/140737488355328), (3609902588059/18014398509481984)), (17619/2251799813685248), by norm_num⟩
  | 3 => ⟨((743618638233187/4503599627370496), (4501152609005/4503599627370496)), (176477/4503599627370496), by norm_num⟩
  | 2 => ⟨((555976233796409/1125899906842624), (17937411183423/4503599627370496)), (707633/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105016689315661/1125899906842624), (6684664608531/562949953421312)), (1065775/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084285480696945/1125899906842624), (52810714470899/2251799813685248)), (2148929/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084285480696945/1125899906842624), (52810714470899/2251799813685248)), (8197513588912200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043589890734141/1125899906842624), (101717551583441/2251799813685248)), (2119901/1125899906842624), by norm_num⟩
  | 2 => ⟨((964999853330063/1125899906842624), (188562780576809/2251799813685248)), (8242733/2251799813685248), by norm_num⟩
  | 3 => ⟨((409599348382063/562949953421312), (161615659166729/1125899906842624)), (7755017/1125899906842624), by norm_num⟩
  | 4 => ⟨((572845667338969/1125899906842624), (470362726069807/2251799813685248)), (27022765/2251799813685248), by norm_num⟩
  | 5 => ⟨((969329097238165/4503599627370496), (478630912160645/2251799813685248)), (77573947/4503599627370496), by norm_num⟩
  | 6 => ⟨((20648992249079/18014398509481984), (824142301061239/9007199254740992)), (265482331/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-922585791/16777216)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-942758785/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((733208029121259/9007199254740992), (136262911208067/4503599627370496)), (24954211/2251799813685248), by norm_num⟩
  | 1 => ⟨((-990550409/4294967296), (-368177317/4294967296)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((701610159/2147483648), (130390611/1073741824)), (197/4294967296), by norm_num⟩
  | 3 => ⟨((-662603755/2147483648), (-123141473/1073741824)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((234662225/1073741824), (348886065/4294967296)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((-265939259/2147483648), (-197693731/4294967296)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((251154219/4294967296), (186702839/8589934592)), (37/4294967296), by norm_num⟩
  | 7 => ⟨((-101653355/4294967296), (-151133993/17179869184)), (61/17179869184), by norm_num⟩
  | 8 => ⟨((1152022567/137438953472), (214097423/68719476736)), (175/137438953472), by norm_num⟩
  | 9 => ⟨((-1450633649/549755813888), (-269592745/274877906944)), (223/549755813888), by norm_num⟩
  | 10 => ⟨((410995461/549755813888), (305525505/1099511627776)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((-1654031/8589934592), (-314770523/4398046511104)), (67/2199023255552), by norm_num⟩
  | 12 => ⟨((99972751/2199023255552), (148635341/8796093022208)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((-1394432651/140737488355328), (-259148081/70368744177664)), (225/140737488355328), by norm_num⟩
  | 14 => ⟨((1128778627/562949953421312), (419555315/562949953421312)), (23/70368744177664), by norm_num⟩
  | 15 => ⟨((-852818845/2251799813685248), (-316983925/2251799813685248)), (141/2251799813685248), by norm_num⟩
  | 16 => ⟨((604054433/9007199254740992), (449041543/18014398509481984)), (101/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (231777127155/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444550053783431/158456325028528675187087900672), (274129124883/316912650057057350374175801344)), (138381/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102393615889/39614081257132168796771975168), (77082514727/4951760157141521099596496896)), (38921/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((14756544654833/19342813113834066795298816), (327519064937/1237940039285380274899124224)), (165421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770504206969029/154742504910672534362390528), (654854563533/154742504910672534362390528)), (41357/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548910106615797/9671406556917033397649408), (613731186391/9671406556917033397649408)), (19387/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314556509054593/151115727451828646838272), (16775621955/18889465931478580854784)), (33929/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886878223639481/75557863725914323419136), (871967104153/75557863725914323419136)), (27569/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296854507286309/4722366482869645213696), (326827959033/2361183241434822606848)), (82713/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620506995338613/590295810358705651712), (898258169755/590295810358705651712)), (227481/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822299239883895/73786976294838206464), (1122045201955/73786976294838206464)), (71095/18446744073709551616), by norm_num⟩
  | 7 => ⟨((28458374702951/144115188075855872), (1261232694845/9223372036854775808)), (319967/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49768319214085/36028797018963968), (1259898875655/1152921504606846976)), (160009/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193358013685687/144115188075855872), (550456430761/72057594037927936)), (280073/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489807153390301/36028797018963968), (824188353125/18014398509481984)), (3283/281474976710656), by norm_num⟩
  | 3 => ⟨((1486976638811865/9007199254740992), (2055244466977/9007199254740992)), (525481/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111703122938513/2251799813685248), (4094852036775/4503599627370496)), (1051571/4503599627370496), by norm_num⟩
  | 1 => ⟨((552335351562387/562949953421312), (762916705079/281474976710656)), (394723/562949953421312), by norm_num⟩
  | 0 => ⟨((2167408854244401/2251799813685248), (12051773420081/2251799813685248)), (1582003/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167408854244401/2251799813685248), (12051773420081/2251799813685248)), (6034862522605514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086116122607987/2251799813685248), (5800053863865/562949953421312)), (3062363/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932384131379107/2251799813685248), (42986364254473/2251799813685248)), (2868591/562949953421312), by norm_num⟩
  | 3 => ⟨((414364165612243/562949953421312), (73777577958923/2251799813685248)), (2516445/281474976710656), by norm_num⟩
  | 4 => ⟨((1217568027239491/2251799813685248), (108609244377935/2251799813685248)), (3869399/281474976710656), by norm_num⟩
  | 5 => ⟨((1306222626055415/4503599627370496), (234903906845599/4503599627370496)), (72923131/4503599627370496), by norm_num⟩
  | 6 => ⟨((733208029121259/9007199254740992), (136262911208067/4503599627370496)), (24954211/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-942758785/16777216)), (3/33554432), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1923556779/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((530494357178063/9007199254740992), (-1044969081043369/18014398509481984)), (42432495/4503599627370496), by norm_num⟩
  | 1 => ⟨((-731146769/4294967296), (360053673/2147483648)), (119/4294967296), by norm_num⟩
  | 2 => ⟨((528321493/2147483648), (-130086121/536870912)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-1018030349/4294967296), (501329667/2147483648)), (85/2147483648), by norm_num⟩
  | 4 => ⟨((735621543/4294967296), (-181128639/1073741824)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((-850487893/8589934592), (837646565/8589934592)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((819408729/17179869184), (-403518329/8589934592)), (9/1073741824), by norm_num⟩
  | 7 => ⟨((-42292783/2147483648), (333233709/17179869184)), (121/34359738368), by norm_num⟩
  | 8 => ⟨((977934925/137438953472), (-963169301/137438953472)), (89/68719476736), by norm_num⟩
  | 9 => ⟨((-628132331/274877906944), (618648299/274877906944)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((181553595/274877906944), (-715249429/1099511627776)), (17/137438953472), by norm_num⟩
  | 11 => ⟨((-763283467/4398046511104), (375879409/2199023255552)), (145/4398046511104), by norm_num⟩
  | 12 => ⟨((45961937/1099511627776), (-362143743/8796093022208)), (71/8796093022208), by norm_num⟩
  | 13 => ⟨((-654016417/70368744177664), (1258089/137438953472)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((270050083/140737488355328), (-1063890627/562949953421312)), (107/281474976710656), by norm_num⟩
  | 15 => ⟨((-208145369/562949953421312), (820010513/2251799813685248)), (167/2251799813685248), by norm_num⟩
  | 16 => ⟨((75202187/1125899906842624), (-592533807/9007199254740992)), (61/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-1013160262039/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778123657847323/633825300114114700748351602688), (-599097349473/316912650057057350374175801344)), (92319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944508125668387/19807040628566084398385987584), (-673839073447/19807040628566084398385987584)), (51933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888746167865539/2475880078570760549798248448), (-1431544027629/2475880078570760549798248448)), (110367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885206317277341/77371252455336267181195264), (-1431134709555/154742504910672534362390528)), (13797/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548824231517837/9671406556917033397649408), (-167656756263/1208925819614629174706176)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258150869582595/604462909807314587353088), (-1173162734193/604462909807314587353088)), (90563/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886756029319991/75557863725914323419136), (-476393756753/18889465931478580854784)), (9199/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162095352393807/590295810358705651712), (-714234519647/2361183241434822606848)), (55203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405095213848699/147573952589676412928), (-1962988271557/590295810358705651712)), (37959/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911070731028907/36893488147419103232), (-1226000804297/36893488147419103232)), (189837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910579169920141/4611686018427387904), (-1378059984039/4611686018427387904)), (26703/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796204198957829/576460752303423488), (-688286430185/288230376151711744)), (213697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298300556726371/36028797018963968), (-601415168229/36028797018963968)), (187067/144115188075855872), by norm_num⟩
  | 4 => ⟨((186196635160715/4503599627370496), (-3601817818879/36028797018963968)), (280765/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486683367260395/9007199254740992), (-4490617720895/9007199254740992)), (351245/9007199254740992), by norm_num⟩
  | 2 => ⟨((277852209538155/562949953421312), (-4473182858273/2251799813685248)), (351679/2251799813685248), by norm_num⟩
  | 1 => ⟨((2208453547711329/2251799813685248), (-13332702174387/2251799813685248)), (264305/562949953421312), by norm_num⟩
  | 0 => ⟨((1082806745060747/1125899906842624), (-1644998713795/140737488355328)), (1061615/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082806745060747/1125899906842624), (-1644998713795/140737488355328)), (4049739841941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082418258843917/2251799813685248), (-6328149392635/281474976710656)), (1033391/562949953421312), by norm_num⟩
  | 2 => ⟨((1924639511933649/2251799813685248), (-93634283188601/2251799813685248)), (3915567/1125899906842624), by norm_num⟩
  | 3 => ⟨((820559147720157/1125899906842624), (-40015155876897/562949953421312)), (1754749/281474976710656), by norm_num⟩
  | 4 => ⟨((592337258449601/1125899906842624), (-7290790682787/70368744177664)), (22457535/2251799813685248), by norm_num⟩
  | 5 => ⟨((1198172536404679/4503599627370496), (-245484384605103/2251799813685248)), (56566897/4503599627370496), by norm_num⟩
  | 6 => ⟨((530494357178063/9007199254740992), (-1044969081043369/18014398509481984)), (42432495/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1923556779/33554432)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1959538783/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-391894168854375/18014398509481984), (-683117240954351/9007199254740992)), (246796883/18014398509481984), by norm_num⟩
  | 1 => ⟨((275113217/4294967296), (959108845/4294967296)), (175/4294967296), by norm_num⟩
  | 2 => ⟨((-12657095/134217728), (-706009367/2147483648)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((397525801/4294967296), (1385867667/4294967296)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-36577827/536870912), (-1020150695/4294967296)), (3/67108864), by norm_num⟩
  | 5 => ⟨((344643775/8589934592), (300377147/2147483648)), (57/2147483648), by norm_num⟩
  | 6 => ⟨((-338260855/17179869184), (-73703515/1073741824)), (225/17179869184), by norm_num⟩
  | 7 => ⟨((4446377/536870912), (248017717/8589934592)), (191/34359738368), by norm_num⟩
  | 8 => ⟨((-52368343/17179869184), (-1460546067/137438953472)), (283/137438953472), by norm_num⟩
  | 9 => ⟨((137062569/137438953472), (955664171/274877906944)), (187/274877906944), by norm_num⟩
  | 10 => ⟨((-322857897/1099511627776), (-562778967/549755813888)), (111/549755813888), by norm_num⟩
  | 11 => ⟨((345685591/4398046511104), (1205140601/4398046511104)), (15/274877906944), by norm_num⟩
  | 12 => ⟨((-21205211/1099511627776), (-1182820987/17592186044416)), (237/17592186044416), by norm_num⟩
  | 13 => ⟨((19211523/4398046511104), (535806803/35184372088832)), (217/70368744177664), by norm_num⟩
  | 14 => ⟨((-129296359/140737488355328), (-901514535/281474976710656)), (23/35184372088832), by norm_num⟩
  | 15 => ⟨((406085589/2251799813685248), (707854543/1125899906842624)), (291/2251799813685248), by norm_num⟩
  | 16 => ⟨((-298923559/9007199254740992), (-521058627/4503599627370496)), (27/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-75312885213/316912650057057350374175801344)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778048237306549/633825300114114700748351602688), (-2849935701041/633825300114114700748351602688)), (92481/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472232805878333/9903520314283042199192993792), (-3205467144937/39614081257132168796771975168)), (104059/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944327792497277/1237940039285380274899124224), (-1702463070759/1237940039285380274899124224)), (13823/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770321781083717/154742504910672534362390528), (-3403933454687/154742504910672534362390528)), (110607/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548738769111515/9671406556917033397649408), (-3190133221969/9671406556917033397649408)), (103719/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258075802964545/604462909807314587353088), (-174394534845/37778931862957161709568)), (22695/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943316754239717/37778931862957161709568), (-2266141220749/37778931862957161709568)), (147563/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324167614673471/1180591620717411303424), (-3397484106909/4722366482869645213696)), (55357/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405063274337981/147573952589676412928), (-4668734608075/590295810358705651712)), (76149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910990311360707/36893488147419103232), (-5831711848175/73786976294838206464)), (23809/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820975828621607/9223372036854775808), (-3277448155585/4611686018427387904)), (214419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24878498944741/18014398509481984), (-6547678357409/1152921504606846976)), (3353/18014398509481984), by norm_num⟩
  | 5 => ⟨((1193038627262239/144115188075855872), (-1430276804705/36028797018963968)), (93981/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489323312395979/36028797018963968), (-4282730128607/18014398509481984)), (70583/9007199254740992), by norm_num⟩
  | 3 => ⟨((743181772020937/4503599627370496), (-10678524034571/9007199254740992)), (88399/2251799813685248), by norm_num⟩
  | 2 => ⟨((555538832670581/1125899906842624), (-21272342805165/4503599627370496)), (354621/2251799813685248), by norm_num⟩
  | 1 => ⟨((551850939853109/562949953421312), (-31697445000807/2251799813685248)), (534501/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163291687782225/2251799813685248), (-31277383901993/1125899906842624)), (2158649/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163291687782225/2251799813685248), (-31277383901993/1125899906842624)), (8234592446334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((259565581664659/281474976710656), (-60096021146765/1125899906842624)), (4267539/2251799813685248), by norm_num⟩
  | 2 => ⟨((238559644749821/281474976710656), (-221673114491121/2251799813685248)), (8326295/2251799813685248), by norm_num⟩
  | 3 => ⟨((1595677409278061/2251799813685248), (-187875526491113/1125899906842624)), (3938241/562949953421312), by norm_num⟩
  | 4 => ⟨((1068033457524417/2251799813685248), (-266265883455655/1125899906842624)), (27583129/2251799813685248), by norm_num⟩
  | 5 => ⟨((380631252570875/2251799813685248), (-1010323814398137/4503599627370496)), (4901479/281474976710656), by norm_num⟩
  | 6 => ⟨((-391894168854375/18014398509481984), (-683117240954351/9007199254740992)), (246796883/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1959538783/33554432)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1993674725/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-654524037191887/9007199254740992), (-92026931361173/4503599627370496)), (237849805/18014398509481984), by norm_num⟩
  | 1 => ⟨((467486091/2147483648), (262916611/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-700231585/2147483648), (-3076671/33554432)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((699235453/2147483648), (196626829/2147483648)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-1047361107/4294967296), (-294520669/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((313761347/2147483648), (352922029/8589934592)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((-1253259991/17179869184), (-352419971/17179869184)), (241/17179869184), by norm_num⟩
  | 7 => ⟨((536347343/17179869184), (301644537/34359738368)), (209/34359738368), by norm_num⟩
  | 8 => ⟨((-1606753045/137438953472), (-451823137/137438953472)), (79/34359738368), by norm_num⟩
  | 9 => ⟨((534822439/137438953472), (300786923/274877906944)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((-1281747873/1099511627776), (-360430837/1099511627776)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((698140631/2199023255552), (98159481/1099511627776)), (281/4398046511104), by norm_num⟩
  | 12 => ⟨((-1394294947/17592186044416), (-392079367/17592186044416)), (283/17592186044416), by norm_num⟩
  | 13 => ⟨((80325661/4398046511104), (180702279/35184372088832)), (131/35184372088832), by norm_num⟩
  | 14 => ⟨((-1100041943/281474976710656), (-309334657/281474976710656)), (113/140737488355328), by norm_num⟩
  | 15 => ⟨((109847705/140737488355328), (61778921/281474976710656)), (91/562949953421312), by norm_num⟩
  | 16 => ⟨((-329074315/2251799813685248), (-370146215/9007199254740992)), (275/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1867599345625/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222246748376997/79228162514264337593543950336), (-4416698684749/633825300114114700748351602688)), (92635/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944423687040209/19807040628566084398385987584), (-2483824982557/19807040628566084398385987584)), (104243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472141517199303/618970019642690137449562112), (-2638367197337/1237940039285380274899124224)), (55395/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885115892976897/77371252455336267181195264), (-2637583382657/77371252455336267181195264)), (110827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774326945115627/4835703278458516698824704), (-308987726779/604462909807314587353088)), (103939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258001025970647/604462909807314587353088), (-4324163401319/604462909807314587353088)), (45493/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886511044416751/75557863725914323419136), (-7023645012771/75557863725914323419136)), (36981/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648288889566303/2361183241434822606848), (-1316251061453/1180591620717411303424)), (111007/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50628884800705/18446744073709551616), (-904368391767/73786976294838206464)), (152737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910908811172329/36893488147419103232), (-9037036435779/73786976294838206464)), (191077/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910394840022815/4611686018427387904), (-5078765349673/4611686018427387904)), (215175/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398008581358697/288230376151711744), (-5073059541787/576460752303423488)), (107721/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192868841320967/144115188075855872), (-4432513222245/72057594037927936)), (188813/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489060901277365/36028797018963968), (-13271909958293/36028797018963968)), (141911/18014398509481984), by norm_num⟩
  | 3 => ⟨((743011030127685/4503599627370496), (-16545093542453/9007199254740992)), (355833/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110716099364769/2251799813685248), (-8239009472313/1125899906842624)), (178711/1125899906842624), by norm_num⟩
  | 1 => ⟨((275777438286521/281474976710656), (-24549749240473/1125899906842624)), (270057/562949953421312), by norm_num⟩
  | 0 => ⟨((540132518358819/562949953421312), (-48432828890597/1125899906842624)), (274055/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540132518358819/562949953421312), (-48432828890597/1125899906842624)), (1045436860204601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((517198200107411/562949953421312), (-23234876991225/281474976710656)), (1098945/562949953421312), by norm_num⟩
  | 2 => ⟨((942657650281675/1125899906842624), (-341544721310887/2251799813685248)), (4401387/1125899906842624), by norm_num⟩
  | 3 => ⟨((1526672559874129/2251799813685248), (-571915394077803/2251799813685248)), (17410559/2251799813685248), by norm_num⟩
  | 4 => ⟨((889795742460045/2251799813685248), (-193873259381623/562949953421312)), (8112975/562949953421312), by norm_num⟩
  | 5 => ⟨((42265527088849/1125899906842624), (-612870112969049/2251799813685248)), (11999687/562949953421312), by norm_num⟩
  | 6 => ⟨((-654524037191887/9007199254740992), (-92026931361173/4503599627370496)), (237849805/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1993674725/33554432)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1013072411/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1002576690307259/18014398509481984), (833482177408583/18014398509481984)), (119573209/9007199254740992), by norm_num⟩
  | 1 => ⟨((363870529/2147483648), (-605000303/4294967296)), (175/4294967296), by norm_num⟩
  | 2 => ⟨((-553905995/2147483648), (920968499/4294967296)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((281063205/1073741824), (-233659105/1073741824)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((-427851617/2147483648), (177845097/1073741824)), (105/2147483648), by norm_num⟩
  | 5 => ⟨((1042083079/8589934592), (-866325421/8589934592)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((-1057548439/17179869184), (439591197/8589934592)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((919922843/34359738368), (-382384361/17179869184)), (29/4294967296), by norm_num⟩
  | 8 => ⟨((-350090717/34359738368), (145522221/17179869184)), (179/68719476736), by norm_num⟩
  | 9 => ⟨((947430261/274877906944), (-787636741/274877906944)), (245/274877906944), by norm_num⟩
  | 10 => ⟨((-1153789075/1099511627776), (239797773/274877906944)), (301/1099511627776), by norm_num⟩
  | 11 => ⟨((638679405/2199023255552), (-265479891/1099511627776)), (21/274877906944), by norm_num⟩
  | 12 => ⟨((-324078963/4398046511104), (538839657/8796093022208)), (43/2199023255552), by norm_num⟩
  | 13 => ⟨((607178877/35184372088832), (-504772131/35184372088832)), (163/35184372088832), by norm_num⟩
  | 14 => ⟨((-1056325551/281474976710656), (878165759/281474976710656)), (143/140737488355328), by norm_num⟩
  | 15 => ⟨((857601825/1125899906842624), (-356479381/562949953421312)), (117/562949953421312), by norm_num⟩
  | 16 => ⟨((-81593375/562949953421312), (542654737/4503599627370496)), (45/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (797208712749/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888956004098097/316912650057057350374175801344), (3770386769665/633825300114114700748351602688)), (23143/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944388910501627/19807040628566084398385987584), (4240707636021/39614081257132168796771975168)), (104167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472123099302463/618970019642690137449562112), (4504543601427/2475880078570760549798248448)), (110705/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885079185632315/77371252455336267181195264), (2251592340965/77371252455336267181195264)), (110737/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193573167089451/1208925819614629174706176), (527536525195/1208925819614629174706176)), (12981/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257941314176317/604462909807314587353088), (230707044011/37778931862957161709568)), (90901/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886414523273309/75557863725914323419136), (2997839280323/37778931862957161709568)), (147775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648252917253715/2361183241434822606848), (4494393398899/4722366482869645213696)), (55443/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202503264250147/73786976294838206464), (6175948805225/590295810358705651712)), (38139/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821695957619851/73786976294838206464), (241068002303/2305843009213693952)), (47707/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820654296307301/9223372036854775808), (8670533446731/9223372036854775808)), (214863/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795950399628983/576460752303423488), (4330324028541/576460752303423488)), (53773/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192754090474485/144115188075855872), (1891739213521/36028797018963968)), (188463/144115188075855872), by norm_num⟩
  | 4 => ⟨((744446465572537/18014398509481984), (2832060512519/9007199254740992)), (35401/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485819341674735/9007199254740992), (7060762748743/4503599627370496)), (11091/281474976710656), by norm_num⟩
  | 2 => ⟨((2221048377434757/4503599627370496), (28126964044291/4503599627370496)), (356267/2251799813685248), by norm_num⟩
  | 1 => ⟨((275712175964923/281474976710656), (41901083036233/2251799813685248)), (67225/140737488355328), by norm_num⟩
  | 0 => ⟨((2159697980473621/2251799813685248), (20662458976849/562949953421312)), (1089257/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159697980473621/2251799813685248), (20662458976849/562949953421312)), (4155185703757857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2068329672638177/2251799813685248), (158538678803381/2251799813685248)), (1084685/562949953421312), by norm_num⟩
  | 2 => ⟨((1888646182574595/2251799813685248), (72810702718115/562949953421312)), (4290703/1125899906842624), by norm_num⟩
  | 3 => ⟨((193298822951865/281474976710656), (488546645766311/2251799813685248)), (8307361/1125899906842624), by norm_num⟩
  | 4 => ⟨((955966866557469/2251799813685248), (335502262713695/1125899906842624)), (30029239/2251799813685248), by norm_num⟩
  | 5 => ⟨((411782232145147/4503599627370496), (569729235894115/2251799813685248)), (86786957/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1002576690307259/18014398509481984), (833482177408583/18014398509481984)), (119573209/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1013072411/16777216)), (1/16777216), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile012Terms2
