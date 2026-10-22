/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile053Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨53,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77087/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77087/2560))
  have he : value ((69/80), (77087/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-5602818047/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-192944286101097/9007199254740992), (-1602609921599511/18014398509481984)), (8845023/4503599627370496), by norm_num⟩
  | 1 => ⟨((4081383909/68719476736), (8475071325/34359738368)), (47/8589934592), by norm_num⟩
  | 2 => ⟨((-5657999499/68719476736), (-2937235897/8589934592)), (131/17179869184), by norm_num⟩
  | 3 => ⟨((5229101867/68719476736), (10858329497/34359738368)), (243/34359738368), by norm_num⟩
  | 4 => ⟨((-28316697/536870912), (-15052840953/68719476736)), (169/34359738368), by norm_num⟩
  | 5 => ⟨((4019740403/137438953472), (8347067413/68719476736)), (377/137438953472), by norm_num⟩
  | 6 => ⟨((-3715028969/274877906944), (-15428656649/274877906944)), (175/137438953472), by norm_num⟩
  | 7 => ⟨((2942927835/549755813888), (24444182529/1099511627776)), (557/1099511627776), by norm_num⟩
  | 8 => ⟨((-4079764263/2199023255552), (-16943416201/2199023255552)), (97/549755813888), by norm_num⟩
  | 9 => ⟨((1256834265/2199023255552), (10439361039/4398046511104)), (15/274877906944), by norm_num⟩
  | 10 => ⟨((-2787747607/17592186044416), (-5788810937/8796093022208)), (535/35184372088832), by norm_num⟩
  | 11 => ⟨((2810646391/70368744177664), (2918180349/17592186044416)), (271/70368744177664), by norm_num⟩
  | 12 => ⟨((-5195177657/562949953421312), (-21575770467/562949953421312)), (503/562949953421312), by norm_num⟩
  | 13 => ⟨((2216013997/1125899906842624), (4601595221/562949953421312)), (27/140737488355328), by norm_num⟩
  | 14 => ⟨((-3510911667/9007199254740992), (-14580949731/9007199254740992)), (43/1125899906842624), by norm_num⟩
  | 15 => ⟨((5191634183/72057594037927936), (21561054285/72057594037927936)), (255/36028797018963968), by norm_num⟩
  | 16 => ⟨((-3598566597/288230376151711744), (-3736245997/72057594037927936)), (355/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-1176965550551/5070602400912917605986812821504)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889138391744593/316912650057057350374175801344), (-348037357919/79228162514264337593543950336)), (1445/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889188292444151/39614081257132168796771975168), (-3131680258241/39614081257132168796771975168)), (813/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472232166654261/618970019642690137449562112), (-831649534013/618970019642690137449562112)), (6911/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770594801813661/154742504910672534362390528), (-3325684772239/154742504910672534362390528)), (6913/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548994661348469/9671406556917033397649408), (-3116859313025/9671406556917033397649408)), (12965/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258299643975535/604462909807314587353088), (-2726282061961/604462909807314587353088)), (11347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886997128818867/75557863725914323419136), (-1107097648695/18889465931478580854784)), (4611/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648471533905115/2361183241434822606848), (-1659851548907/2361183241434822606848)), (13839/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620627762416635/590295810358705651712), (-1140502386475/147573952589676412928)), (4759/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911224347677369/36893488147419103232), (-5698640868359/73786976294838206464)), (23807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821502054638057/9223372036854775808), (-6405651928883/9223372036854775808)), (26799/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592749713880167/1152921504606846976), (-3199504306773/576460752303423488)), (6705/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193498185856281/144115188075855872), (-5591666357721/144115188075855872)), (5873/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490011650071753/36028797018963968), (-4186293020577/18014398509481984)), (35285/36028797018963968), by norm_num⟩
  | 3 => ⟨((185902776992455/1125899906842624), (-5219838169037/4503599627370496)), (44189/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111933712325437/2251799813685248), (-20801353461787/4503599627370496)), (44313/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104979389335739/1125899906842624), (-3875953037139/281474976710656)), (133565/2251799813685248), by norm_num⟩
  | 0 => ⟨((135521828647457/140737488355328), (-3827573190817/140737488355328)), (134823/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135521828647457/140737488355328), (-3827573190817/140737488355328)), (514308933738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086325789994093/2251799813685248), (-7371450551851/140737488355328)), (266987/1125899906842624), by norm_num⟩
  | 2 => ⟨((481708528786201/562949953421312), (-54638062593401/562949953421312)), (1045407/2251799813685248), by norm_num⟩
  | 3 => ⟨((813776739581605/1125899906842624), (-374024306603297/2251799813685248)), (1992009/2251799813685248), by norm_num⟩
  | 4 => ⟨((1114235879387501/2251799813685248), (-270336891318747/1125899906842624)), (55333/35184372088832), by norm_num⟩
  | 5 => ⟨((210763285864535/1125899906842624), (-66884068023893/281474976710656)), (162663/70368744177664), by norm_num⟩
  | 6 => ⟨((-192944286101097/9007199254740992), (-1602609921599511/18014398509481984)), (8845023/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-5602818047/67108864)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-22901310573/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-689797307387709/9007199254740992), (92210366231371/2251799813685248)), (17650273/9007199254740992), by norm_num⟩
  | 1 => ⟨((3727613327/17179869184), (-996595917/8589934592)), (383/68719476736), by norm_num⟩
  | 2 => ⟨((-21122247639/68719476736), (11294275403/68719476736)), (545/68719476736), by norm_num⟩
  | 3 => ⟨((19947944623/68719476736), (-1333295491/8589934592)), (517/68719476736), by norm_num⟩
  | 4 => ⟨((-14129195723/68719476736), (7555021153/68719476736)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((8006205173/68719476736), (-4280997349/68719476736)), (419/137438953472), by norm_num⟩
  | 6 => ⟨((-7561095777/137438953472), (8085985877/274877906944)), (199/137438953472), by norm_num⟩
  | 7 => ⟨((12241255687/549755813888), (-3272760441/274877906944)), (81/137438953472), by norm_num⟩
  | 8 => ⟨((-67738455/8589934592), (9272428553/2199023255552)), (231/1099511627776), by norm_num⟩
  | 9 => ⟨((10917973027/4398046511104), (-5837948513/4398046511104)), (73/1099511627776), by norm_num⟩
  | 10 => ⟨((-3093294687/4398046511104), (1654015363/4398046511104)), (333/17592186044416), by norm_num⟩
  | 11 => ⟨((6373791843/35184372088832), (-213008109/2199023255552)), (345/70368744177664), by norm_num⟩
  | 12 => ⟨((-12038874735/281474976710656), (6437305779/281474976710656)), (41/35184372088832), by norm_num⟩
  | 13 => ⟨((20989969567/2251799813685248), (-11223545005/2251799813685248)), (287/1125899906842624), by norm_num⟩
  | 14 => ⟨((-8495580267/4503599627370496), (1135667767/1125899906842624)), (233/4503599627370496), by norm_num⟩
  | 15 => ⟨((3209305517/9007199254740992), (-1716047505/9007199254740992)), (177/18014398509481984), by norm_num⟩
  | 16 => ⟨((-568290451/9007199254740992), (9723857381/288230376151711744)), (63/36028797018963968), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (3452655808643/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889095719624777/316912650057057350374175801344), (2041775059903/316912650057057350374175801344)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889092035080093/39614081257132168796771975168), (4592999822407/39614081257132168796771975168)), (6513/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888826066151369/2475880078570760549798248448), (4878843801093/2475880078570760549798248448)), (3461/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770491833829753/154742504910672534362390528), (609684153193/19342813113834066795298816)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774448869342783/4835703278458516698824704), (4571175246321/9671406556917033397649408)), (12987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78638402926021/37778931862957161709568), (1999161406499/302231454903657293676544)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943428976623173/37778931862957161709568), (1623636563547/18889465931478580854784)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296838047956011/4722366482869645213696), (4868523210633/4722366482869645213696)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202560290558779/73786976294838206464), (3345171439911/295147905179352825856)), (9541/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911132673438583/36893488147419103232), (8357116414715/73786976294838206464)), (23869/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910646829426295/4611686018427387904), (4696884232945/4611686018427387904)), (26877/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796269331530057/576460752303423488), (9383790472417/1152921504606846976)), (6727/288230376151711744), by norm_num⟩
  | 5 => ⟨((596655268788871/72057594037927936), (8199600199125/144115188075855872)), (5895/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489724240257771/36028797018963968), (12276989324227/36028797018963968)), (35439/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486852608650423/9007199254740992), (15307066868227/9007199254740992)), (11105/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111548678130573/2251799813685248), (15248411077799/2251799813685248)), (11151/562949953421312), by norm_num⟩
  | 1 => ⟨((1104363587001665/1125899906842624), (11363161747103/562949953421312)), (16841/281474976710656), by norm_num⟩
  | 0 => ⟨((1082791909909259/1125899906842624), (44869554489997/1125899906842624)), (136573/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082791909909259/1125899906842624), (44869554489997/1125899906842624)), (520984653953170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519773132643313/562949953421312), (86303214535735/1125899906842624)), (136787/562949953421312), by norm_num⟩
  | 2 => ⟨((953200356718905/1125899906842624), (318735915360171/2251799813685248)), (136781/281474976710656), by norm_num⟩
  | 3 => ⟨((1568865524806153/2251799813685248), (269845646468207/1125899906842624)), (270323/281474976710656), by norm_num⟩
  | 4 => ⟨((481852856116551/1125899906842624), (47001461807361/140737488355328)), (4050033/2251799813685248), by norm_num⟩
  | 5 => ⟨((80644273994531/1125899906842624), (643688867214959/2251799813685248)), (12343477/4503599627370496), by norm_num⟩
  | 6 => ⟨((-689797307387709/9007199254740992), (92210366231371/2251799813685248)), (17650273/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-22901310573/268435456)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-5840832763/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((55687128124423/1125899906842624), (1193225475427343/18014398509481984)), (361199/281474976710656), by norm_num⟩
  | 1 => ⟨((-4912002637/34359738368), (-13156376705/68719476736)), (1/268435456), by norm_num⟩
  | 2 => ⟨((14197513697/68719476736), (2376676229/8589934592)), (93/17179869184), by norm_num⟩
  | 3 => ⟨((-13678697541/68719476736), (-1144912975/4294967296)), (45/8589934592), by norm_num⟩
  | 4 => ⟨((1235516283/8589934592), (13236896513/68719476736)), (131/34359738368), by norm_num⟩
  | 5 => ⟨((-11427524387/137438953472), (-15303820737/137438953472)), (305/137438953472), by norm_num⟩
  | 6 => ⟨((5504965625/137438953472), (7372288541/137438953472)), (37/34359738368), by norm_num⟩
  | 7 => ⟨((-9092226955/549755813888), (-12176374051/549755813888)), (247/549755813888), by norm_num⟩
  | 8 => ⟨((3284989501/549755813888), (17597123835/2199023255552)), (359/2199023255552), by norm_num⟩
  | 9 => ⟨((-8439858559/4398046511104), (-11302717723/4398046511104)), (29/549755813888), by norm_num⟩
  | 10 => ⟨((1219716441/2199023255552), (6533811219/8796093022208)), (135/8796093022208), by norm_num⟩
  | 11 => ⟨((-10255807865/70368744177664), (-13734649759/70368744177664)), (143/35184372088832), by norm_num⟩
  | 12 => ⟨((9881032469/281474976710656), (13232747923/281474976710656)), (277/281474976710656), by norm_num⟩
  | 13 => ⟨((-8787648365/1125899906842624), (-5884240135/562949953421312)), (31/140737488355328), by norm_num⟩
  | 14 => ⟨((14514040373/9007199254740992), (19437304575/9007199254740992)), (103/2251799813685248), by norm_num⟩
  | 15 => ⟨((-5593462985/18014398509481984), (-3745402413/9007199254740992)), (5/562949953421312), by norm_num⟩
  | 16 => ⟨((1010449215/18014398509481984), (10825605357/144115188075855872)), (233/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (605326104261/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778123328592127/633825300114114700748351602688), (1431754790303/633825300114114700748351602688)), (1443/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889015862750961/39614081257132168796771975168), (201297031091/4951760157141521099596496896)), (12987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888745730845549/2475880078570760549798248448), (213823721551/309485009821345068724781056)), (13801/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885206085199027/77371252455336267181195264), (1710100623497/154742504910672534362390528)), (6901/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548823767560333/9671406556917033397649408), (200337475341/1208925819614629174706176)), (12941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314537608708475/151115727451828646838272), (350460752045/151115727451828646838272)), (11325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471688817233119/18889465931478580854784), (1138510808165/37778931862957161709568)), (18405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296762201731633/4722366482869645213696), (1706915050599/4722366482869645213696)), (13807/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202547491244891/73786976294838206464), (2345625902621/590295810358705651712)), (4747/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911070095354133/36893488147419103232), (2929960419377/73786976294838206464)), (11871/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821156752338473/9223372036854775808), (3293358929883/9223372036854775808)), (13359/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592406614290547/1152921504606846976), (3289804351595/1152921504606846976)), (26729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193200446169473/144115188075855872), (2874584850575/144115188075855872)), (2925/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489569971487379/36028797018963968), (2151950852345/18014398509481984)), (8781/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486678715515291/9007199254740992), (670743451203/1125899906842624)), (10987/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222806092154885/4503599627370496), (10690217352249/4503599627370496)), (11003/562949953421312), by norm_num⟩
  | 1 => ⟨((138026907160309/140737488355328), (3982879456703/562949953421312)), (132361/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165545063084543/2251799813685248), (31450113880067/2251799813685248)), (266029/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165545063084543/2251799813685248), (31450113880067/2251799813685248)), (1014820107466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082155030874397/2251799813685248), (30245423430853/1125899906842624)), (259555/1125899906842624), by norm_num⟩
  | 2 => ⟨((1923665862176411/2251799813685248), (111867245347023/2251799813685248)), (493947/1125899906842624), by norm_num⟩
  | 3 => ⟨((1637790378304419/2251799813685248), (191131733524391/2251799813685248)), (1786031/2251799813685248), by norm_num⟩
  | 4 => ⟨((1174982770504981/2251799813685248), (34753723693869/281474976710656)), (1450623/1125899906842624), by norm_num⟩
  | 5 => ⟨((144693584570123/562949953421312), (145075157402583/1125899906842624)), (1872079/1125899906842624), by norm_num⟩
  | 6 => ⟨((55687128124423/1125899906842624), (1193225475427343/18014398509481984)), (361199/281474976710656), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-5840832763/67108864)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-11900182467/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((544152863575663/9007199254740992), (-914203658019663/18014398509481984)), (4825995/4503599627370496), by norm_num⟩
  | 1 => ⟨((-6112002953/34359738368), (10268466513/68719476736)), (109/34359738368), by norm_num⟩
  | 2 => ⟨((17996419735/68719476736), (-944839783/4294967296)), (81/17179869184), by norm_num⟩
  | 3 => ⟨((-8831559959/34359738368), (14837456459/68719476736)), (5/1073741824), by norm_num⟩
  | 4 => ⟨((13001994695/68719476736), (-10921996287/68719476736)), (237/68719476736), by norm_num⟩
  | 5 => ⟨((-15313431995/137438953472), (12863660639/137438953472)), (281/137438953472), by norm_num⟩
  | 6 => ⟨((1878727753/34359738368), (-12625421267/274877906944)), (139/137438953472), by norm_num⟩
  | 7 => ⟨((-12644112519/549755813888), (5310683215/274877906944)), (59/137438953472), by norm_num⟩
  | 8 => ⟨((18614908879/2199023255552), (-1954622833/274877906944)), (175/1099511627776), by norm_num⟩
  | 9 => ⟨((-12180102955/4398046511104), (10231586949/4398046511104)), (231/4398046511104), by norm_num⟩
  | 10 => ⟨((3586356991/4398046511104), (-3012628343/4398046511104)), (137/8796093022208), by norm_num⟩
  | 11 => ⟨((-3839930661/17592186044416), (3225636481/17592186044416)), (37/8796093022208), by norm_num⟩
  | 12 => ⟨((7537627677/140737488355328), (-12663586383/281474976710656)), (73/70368744177664), by norm_num⟩
  | 13 => ⟨((-13657898303/1125899906842624), (1434121437/140737488355328)), (133/562949953421312), by norm_num⟩
  | 14 => ⟨((5744978305/2251799813685248), (-4825923497/2251799813685248)), (113/2251799813685248), by norm_num⟩
  | 15 => ⟨((-9021726963/18014398509481984), (15156946405/36028797018963968)), (357/36028797018963968), by norm_num⟩
  | 16 => ⟨((13281962265/144115188075855872), (-5578587975/72057594037927936)), (265/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-910101267469/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778051970692319/633825300114114700748351602688), (-1076231048633/633825300114114700748351602688)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888935629132221/39614081257132168796771975168), (-1210494161361/39614081257132168796771975168)), (6491/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944330269851997/1237940039285380274899124224), (-642908501275/1237940039285380274899124224)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110645440213527/9671406556917033397649408), (-10042519565/1208925819614629174706176)), (3449/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548744029143695/9671406556917033397649408), (-602352296987/4835703278458516698824704)), (12935/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258080731801479/604462909807314587353088), (-526859467665/302231454903657293676544)), (11319/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943321064530031/37778931862957161709568), (-855774079511/37778931862957161709568)), (18395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296677458339523/4722366482869645213696), (-80188094181/295147905179352825856)), (13799/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810131794408733/295147905179352825856), (-220384984477/73786976294838206464)), (593/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821995035491777/73786976294838206464), (-275282966133/9223372036854775808)), (23725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820993825109959/9223372036854775808), (-1237683849827/4611686018427387904)), (3337/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592244151763819/1152921504606846976), (-618161705697/288230376151711744)), (26705/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193058813169347/144115188075855872), (-2160508921875/144115188075855872)), (1461/9007199254740992), by norm_num⟩
  | 4 => ⟨((1489358562716841/36028797018963968), (-3234659119255/36028797018963968)), (17541/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486416269786027/9007199254740992), (-2016331762097/4503599627370496)), (43885/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111143311147323/2251799813685248), (-8033434084761/4503599627370496)), (43933/2251799813685248), by norm_num⟩
  | 1 => ⟨((551916194928937/562949953421312), (-1496340806685/281474976710656)), (66023/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164066971275329/2251799813685248), (-23625594016737/2251799813685248)), (132541/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164066971275329/2251799813685248), (-23625594016737/2251799813685248)), (505603794578170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079504429751525/2251799813685248), (-45410224636893/2251799813685248)), (515071/2251799813685248), by norm_num⟩
  | 2 => ⟨((1919476393321525/2251799813685248), (-83871366108595/2251799813685248)), (15189/35184372088832), by norm_num⟩
  | 3 => ⟨((25516777707913/35184372088832), (-71493525464683/1125899906842624)), (1729681/2251799813685248), by norm_num⟩
  | 4 => ⟨((146909409766573/281474976710656), (-103698562090661/1125899906842624)), (2728501/2251799813685248), by norm_num⟩
  | 5 => ⟨((594306120880601/2251799813685248), (-432984693088125/4503599627370496)), (3350763/2251799813685248), by norm_num⟩
  | 6 => ⟨((544152863575663/9007199254740992), (-914203658019663/18014398509481984)), (4825995/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-11900182467/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-24214976727/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-847013716537865/18014398509481984), (-1063803523378985/18014398509481984)), (31053023/18014398509481984), by norm_num⟩
  | 1 => ⟨((4839756635/34359738368), (3039236591/17179869184)), (357/68719476736), by norm_num⟩
  | 2 => ⟨((-3624653787/17179869184), (-18209478285/68719476736)), (537/68719476736), by norm_num⟩
  | 3 => ⟨((7238994887/34359738368), (2272946741/8589934592)), (539/68719476736), by norm_num⟩
  | 4 => ⟨((-5421522653/34359738368), (-1702284977/8589934592)), (203/34359738368), by norm_num⟩
  | 5 => ⟨((12993144307/137438953472), (8159344071/68719476736)), (61/17179869184), by norm_num⟩
  | 6 => ⟨((-6487330289/137438953472), (-2036934197/34359738368)), (245/137438953472), by norm_num⟩
  | 7 => ⟨((11105316981/549755813888), (13947678887/549755813888)), (421/549755813888), by norm_num⟩
  | 8 => ⟨((-4158569561/549755813888), (-5222938973/549755813888)), (317/1099511627776), by norm_num⟩
  | 9 => ⟨((692108947/274877906944), (6954011931/2199023255552)), (53/549755813888), by norm_num⟩
  | 10 => ⟨((-3317396975/4398046511104), (-8332943189/8796093022208)), (255/8796093022208), by norm_num⟩
  | 11 => ⟨((451728781/2199023255552), (2269387895/8796093022208)), (279/35184372088832), by norm_num⟩
  | 12 => ⟨((-14434757207/281474976710656), (-18129276155/281474976710656)), (35/17592186044416), by norm_num⟩
  | 13 => ⟨((3326359079/281474976710656), (16710910053/1125899906842624)), (519/1125899906842624), by norm_num⟩
  | 14 => ⟨((-5694217855/2251799813685248), (-14303260733/4503599627370496)), (223/2251799813685248), by norm_num⟩
  | 15 => ⟨((142152935/281474976710656), (2856582653/4503599627370496)), (179/9007199254740992), by norm_num⟩
  | 16 => ⟨((-13627268325/144115188075855872), (-17115113691/144115188075855872)), (269/72057594037927936), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-2922049167637/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777978045378489/633825300114114700748351602688), (-1727593601083/316912650057057350374175801344)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236106520333083/4951760157141521099596496896), (-3886205755881/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888571454137763/2475880078570760549798248448), (-2064002174877/1237940039285380274899124224)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442559376402649/38685626227668133590597632), (-2063389647627/77371252455336267181195264)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548659607337947/9671406556917033397649408), (-3867554355701/9671406556917033397649408)), (12977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258006383049699/604462909807314587353088), (-3382809262503/604462909807314587353088)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886520413890413/75557863725914323419136), (-5494626977861/75557863725914323419136)), (18463/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648292693378041/2361183241434822606848), (-2059418921321/2361183241434822606848)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620135716183239/590295810358705651712), (-5659938630279/590295810358705651712)), (19059/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821833286453313/73786976294838206464), (-7069731212367/73786976294838206464)), (23839/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820809238578419/9223372036854775808), (-7946313431671/9223372036854775808)), (3355/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592056299104907/1152921504606846976), (-7937403083609/1152921504606846976)), (13433/576460752303423488), by norm_num⟩
  | 5 => ⟨((596445388964603/72057594037927936), (-6935213699527/144115188075855872)), (11769/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489099207054545/36028797018963968), (-10382817896749/36028797018963968)), (35365/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486079352601015/9007199254740992), (-6471787359903/4503599627370496)), (44309/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221574848615507/4503599627370496), (-25782534274999/4503599627370496)), (88927/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206503067691803/2251799813685248), (-38413059973851/2251799813685248)), (16771/281474976710656), by norm_num⟩
  | 0 => ⟨((2161372097669979/2251799813685248), (-75787926702101/2251799813685248)), (271463/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161372097669979/2251799813685248), (-75787926702101/2251799813685248)), (1035549172408293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072025011458099/2251799813685248), (-4546527324461/70368744177664)), (539397/2251799813685248), by norm_num⟩
  | 2 => ⟨((948601338710281/1125899906842624), (-267747234703417/2251799813685248)), (1062369/2251799813685248), by norm_num⟩
  | 3 => ⟨((48956525188221/70368744177664), (-225584338121043/1125899906842624)), (1021395/1125899906842624), by norm_num⟩
  | 4 => ⟨((499758007574291/1125899906842624), (-39235549320761/140737488355328)), (915245/562949953421312), by norm_num⟩
  | 5 => ⟨((268646710179797/2251799813685248), (-1114601670600811/4503599627370496)), (10582571/4503599627370496), by norm_num⟩
  | 6 => ⟨((-847013716537865/18014398509481984), (-1063803523378985/18014398509481984)), (31053023/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-24214976727/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-6152338831/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1097089754207111/18014398509481984), (352223865563217/9007199254740992)), (14858543/9007199254740992), by norm_num⟩
  | 1 => ⟨((12741525165/68719476736), (-8181407637/68719476736)), (347/68719476736), by norm_num⟩
  | 2 => ⟨((-4848982407/17179869184), (6227119781/34359738368)), (531/68719476736), by norm_num⟩
  | 3 => ⟨((2460472623/8589934592), (-12639070597/68719476736)), (541/68719476736), by norm_num⟩
  | 4 => ⟨((-1872741027/8589934592), (4809991753/34359738368)), (207/34359738368), by norm_num⟩
  | 5 => ⟨((9122563323/68719476736), (-5857651127/68719476736)), (253/68719476736), by norm_num⟩
  | 6 => ⟨((-18515899151/274877906944), (11889166859/274877906944)), (515/274877906944), by norm_num⟩
  | 7 => ⟨((8053152917/274877906944), (-5170976467/274877906944)), (225/274877906944), by norm_num⟩
  | 8 => ⟨((-12259002375/1099511627776), (7871576939/1099511627776)), (43/137438953472), by norm_num⟩
  | 9 => ⟨((1036744661/274877906944), (-2662799179/1099511627776)), (117/1099511627776), by norm_num⟩
  | 10 => ⟨((-20200911249/17592186044416), (3242780739/4398046511104)), (143/4398046511104), by norm_num⟩
  | 11 => ⟨((11182205011/35184372088832), (-7180159069/35184372088832)), (159/17592186044416), by norm_num⟩
  | 12 => ⟨((-2837039505/35184372088832), (222373/4294967296)), (81/35184372088832), by norm_num⟩
  | 13 => ⟨((5315341803/281474976710656), (-6826023957/562949953421312)), (305/562949953421312), by norm_num⟩
  | 14 => ⟨((-9247244219/2251799813685248), (11875418913/4503599627370496)), (533/4503599627370496), by norm_num⟩
  | 15 => ⟨((3753792335/4503599627370496), (-9641327823/18014398509481984)), (435/18014398509481984), by norm_num⟩
  | 16 => ⟨((-5714252495/36028797018963968), (3669154861/36028797018963968)), (333/72057594037927936), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (3348737055409/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777911224473589/633825300114114700748351602688), (3959450544985/633825300114114700748351602688)), (11575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888776896362523/39614081257132168796771975168), (4453353400581/39614081257132168796771975168)), (13025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944245678672579/1237940039285380274899124224), (2365209456473/1237940039285380274899124224)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770157266854053/154742504910672534362390528), (4728991562867/154742504910672534362390528)), (6923/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548584232806113/9671406556917033397649408), (2215956724011/4835703278458516698824704)), (12985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257940279793257/604462909807314587353088), (969102148445/151115727451828646838272)), (11367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235801589270811/9444732965739290427392), (3148161537001/37778931862957161709568)), (9239/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324126091401137/1180591620717411303424), (4719757522363/4722366482869645213696)), (6933/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405005978097333/147573952589676412928), (6485630688783/590295810358705651712)), (19077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821692933232879/73786976294838206464), (506311735833/4611686018427387904)), (23863/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820650520063839/9223372036854775808), (4552648499407/4611686018427387904)), (13435/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591896556808605/1152921504606846976), (4547456079103/576460752303423488)), (26901/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298187463824337/36028797018963968), (3973188073235/72057594037927936)), (23571/144115188075855872), by norm_num⟩
  | 4 => ⟨((744442767962499/18014398509481984), (11896247616859/36028797018963968)), (35425/36028797018963968), by norm_num⟩
  | 3 => ⟨((742904140734615/4503599627370496), (14829567064427/9007199254740992)), (22199/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110510420431553/2251799813685248), (29537153105729/4503599627370496)), (1393/70368744177664), by norm_num⟩
  | 1 => ⟨((275705334429979/281474976710656), (44001639099337/2251799813685248)), (33655/562949953421312), by norm_num⟩
  | 0 => ⟨((2159535481284769/2251799813685248), (86792086171121/2251799813685248)), (272825/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159535481284769/2251799813685248), (86792086171121/2251799813685248)), (1040744790084075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033853142807995/1125899906842624), (166471804857747/2251799813685248)), (544325/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886356147623793/2251799813685248), (305724154687505/2251799813685248)), (270033/562949953421312), by norm_num⟩
  | 3 => ⟨((1538712382806423/2251799813685248), (512216614609307/2251799813685248)), (2102973/2251799813685248), by norm_num⟩
  | 4 => ⟨((233731915679769/562949953421312), (700021416458553/2251799813685248)), (1915379/1125899906842624), by norm_num⟩
  | 5 => ⟨((170556791364225/2251799813685248), (145321396414853/562949953421312)), (11125491/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1097089754207111/18014398509481984), (352223865563217/9007199254740992)), (14858543/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-6152338831/67108864)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile053Terms2
