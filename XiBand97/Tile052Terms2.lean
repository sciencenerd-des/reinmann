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
namespace Reinmann.XiBand97.Tile052Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨52,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76729/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76729/2560))
  have he : value ((69/80), (76729/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-320962607/134217728), (-11153595961/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((62170541374707/4503599627370496), (-407386926914105/4503599627370496)), (31715683/18014398509481984), by norm_num⟩
  | 1 => ⟨((-164388029/4294967296), (8617526239/34359738368)), (169/34359738368), by norm_num⟩
  | 2 => ⟨((1823121581/34359738368), (-93331469/268435456)), (471/68719476736), by norm_num⟩
  | 3 => ⟨((-3369844223/68719476736), (22081687755/68719476736)), (219/34359738368), by norm_num⟩
  | 4 => ⟨((1167899011/34359738368), (-7652929805/34359738368)), (305/68719476736), by norm_num⟩
  | 5 => ⟨((-2590482901/137438953472), (2121842687/17179869184)), (85/34359738368), by norm_num⟩
  | 6 => ⟨((2394114559/274877906944), (-15687992279/274877906944)), (79/68719476736), by norm_num⟩
  | 7 => ⟨((-474135359/137438953472), (12427528705/549755813888)), (503/1099511627776), by norm_num⟩
  | 8 => ⟨((1314582349/1099511627776), (-17228212967/2199023255552)), (351/2199023255552), by norm_num⟩
  | 9 => ⟨((-404977355/1099511627776), (5307416553/2199023255552)), (435/8796093022208), by norm_num⟩
  | 10 => ⟨((3593074071/35184372088832), (-23544453247/35184372088832)), (121/8796093022208), by norm_num⟩
  | 11 => ⟨((-113205871/4398046511104), (23737849289/140737488355328)), (245/70368744177664), by norm_num⟩
  | 12 => ⟨((3347982093/562949953421312), (-21938431077/562949953421312)), (455/562949953421312), by norm_num⟩
  | 13 => ⟨((-714044415/562949953421312), (18715768181/2251799813685248)), (195/1125899906842624), by norm_num⟩
  | 14 => ⟨((1131286567/4503599627370496), (-14826036511/9007199254740992)), (155/4503599627370496), by norm_num⟩
  | 15 => ⟨((-418212317/9007199254740992), (10961733767/36028797018963968)), (115/18014398509481984), by norm_num⟩
  | 16 => ⟨((2319061507/288230376151711744), (-7598094855/144115188075855872)), (321/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-1848870521149/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889139187422783/316912650057057350374175801344), (-273362296379/79228162514264337593543950336)), (11553/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889190171030919/39614081257132168796771975168), (-1229873826943/19807040628566084398385987584)), (6499/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236116347421801/309485009821345068724781056), (-653211062957/618970019642690137449562112)), (13813/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770597045796299/154742504910672534362390528), (-1306063591727/77371252455336267181195264)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774498452203367/4835703278458516698824704), (-9562920295/37778931862957161709568)), (6477/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258301745860919/604462909807314587353088), (-1070666392029/302231454903657293676544)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887000805155723/75557863725914323419136), (-434779851075/9444732965739290427392)), (4607/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648473026497495/2361183241434822606848), (-2607431099705/4722366482869645213696)), (27/9223372036854775808), by norm_num⟩
  | 9 => ⟨((810316118488789/295147905179352825856), (-895797713311/147573952589676412928)), (19015/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911227421326675/36893488147419103232), (-4475950130963/73786976294838206464)), (11889/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821509730933653/9223372036854775808), (-314454323687/576460752303423488)), (26763/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592758338959993/1152921504606846976), (-2513027736825/576460752303423488)), (6695/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193506797510685/144115188075855872), (-1097984891967/36028797018963968)), (23451/144115188075855872), by norm_num⟩
  | 4 => ⟨((186253336287785/4503599627370496), (-6576207509877/36028797018963968)), (35213/36028797018963968), by norm_num⟩
  | 3 => ⟨((371811179015565/2251799813685248), (-8199817347471/9007199254740992)), (22041/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223923464653537/4503599627370496), (-8169226544079/2251799813685248)), (11045/562949953421312), by norm_num⟩
  | 1 => ⟨((69064694677213/70368744177664), (-3044403802017/281474976710656)), (16629/281474976710656), by norm_num⟩
  | 0 => ⟨((542170119909623/562949953421312), (-12025921207677/562949953421312)), (67011/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((542170119909623/562949953421312), (-12025921207677/562949953421312)), (255626680614280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2087601672982385/2251799813685248), (-46328062404583/1125899906842624)), (527753/2251799813685248), by norm_num⟩
  | 2 => ⟨((1931564058732161/2251799813685248), (-42949883908001/562949953421312)), (255493/562949953421312), by norm_num⟩
  | 3 => ⟨((1643762740385351/2251799813685248), (-294734732916217/2251799813685248)), (954605/1125899906842624), by norm_num⟩
  | 4 => ⟨((580666045000725/1125899906842624), (-53787415884033/281474976710656)), (821787/562949953421312), by norm_num⟩
  | 5 => ⟨((516713211057637/2251799813685248), (-887681780232885/4503599627370496)), (2323443/1125899906842624), by norm_num⟩
  | 6 => ⟨((62170541374707/4503599627370496), (-407386926914105/4503599627370496)), (31715683/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-11153595961/134217728)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-22794954519/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-194675932866163/2251799813685248), (148119548079061/18014398509481984)), (32628237/18014398509481984), by norm_num⟩
  | 1 => ⟨((1052014257/4294967296), (-1600854035/68719476736)), (177/34359738368), by norm_num⟩
  | 2 => ⟨((-23844646649/68719476736), (2267780507/68719476736)), (503/68719476736), by norm_num⟩
  | 3 => ⟨((22518990357/68719476736), (-1070850999/34359738368)), (477/68719476736), by norm_num⟩
  | 4 => ⟨((-7975137997/34359738368), (758487335/34359738368)), (339/68719476736), by norm_num⟩
  | 5 => ⟨((18076213915/137438953472), (-1719165151/137438953472)), (193/68719476736), by norm_num⟩
  | 6 => ⟨((-17071256825/274877906944), (101474201/17179869184)), (183/137438953472), by norm_num⟩
  | 7 => ⟨((27638007221/1099511627776), (-2628553695/1099511627776)), (595/1099511627776), by norm_num⟩
  | 8 => ⟨((-4894023179/549755813888), (1861813351/2199023255552)), (423/2199023255552), by norm_num⟩
  | 9 => ⟨((1540645753/549755813888), (-2344406413/8796093022208)), (535/8796093022208), by norm_num⟩
  | 10 => ⟨((-13967929939/17592186044416), (2656881413/35184372088832)), (19/1099511627776), by norm_num⟩
  | 11 => ⟨((899411943/4398046511104), (-2737277045/140737488355328)), (629/140737488355328), by norm_num⟩
  | 12 => ⟨((-27181076467/562949953421312), (2585096617/562949953421312)), (149/140737488355328), by norm_num⟩
  | 13 => ⟨((23695319555/2251799813685248), (-2253578533/2251799813685248)), (261/1125899906842624), by norm_num⟩
  | 14 => ⟨((-2397639127/1125899906842624), (456062055/2251799813685248)), (53/1125899906842624), by norm_num⟩
  | 15 => ⟨((28983565521/72057594037927936), (-2756525013/72057594037927936)), (643/72057594037927936), by norm_num⟩
  | 16 => ⟨((-5132289037/72057594037927936), (1952455863/288230376151711744)), (229/144115188075855872), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (1984379946169/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889094283873723/316912650057057350374175801344), (4693960484931/633825300114114700748351602688)), (181/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889088645728771/39614081257132168796771975168), (2639777173327/19807040628566084398385987584)), (13035/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888822254362515/2475880078570760549798248448), (5608124853397/2475880078570760549798248448)), (6927/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885243892661509/77371252455336267181195264), (5606548150505/154742504910672534362390528)), (13859/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193611711485917/1208925819614629174706176), (5254463951015/9671406556917033397649408)), (6499/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258210654757781/604462909807314587353088), (1148995340325/151115727451828646838272)), (11379/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886851320772325/75557863725914323419136), (466583161053/4722366482869645213696)), (18499/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648416331235673/2361183241434822606848), (5596251921665/4722366482869645213696)), (13883/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620474252191679/590295810358705651712), (7690385498647/590295810358705651712)), (19103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911127128577947/36893488147419103232), (9606292939589/73786976294838206464)), (23899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910639905592879/4611686018427387904), (10797886187727/9223372036854775808)), (13457/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592523104338709/1152921504606846976), (10786400354189/1152921504606846976)), (13475/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193295003716901/144115188075855872), (2356296709933/36028797018963968)), (23621/144115188075855872), by norm_num⟩
  | 4 => ⟨((46553034746401/1125899906842624), (440999174405/1125899906842624)), (4439/4503599627370496), by norm_num⟩
  | 3 => ⟨((371703006931523/2251799813685248), (549839092519/281474976710656)), (44529/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111498147039189/2251799813685248), (17527268488007/2251799813685248)), (11185/562949953421312), by norm_num⟩
  | 1 => ⟨((1104263108819645/1125899906842624), (6530566975653/281474976710656)), (33819/562949953421312), by norm_num⟩
  | 0 => ⟨((270623346752633/281474976710656), (51571931935303/1125899906842624)), (68699/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270623346752633/281474976710656), (51571931935303/1125899906842624)), (262065889598655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1038398050885897/1125899906842624), (99167385903561/1125899906842624)), (138395/562949953421312), by norm_num⟩
  | 2 => ⟨((948962101482817/1125899906842624), (182920736750893/1125899906842624)), (139829/281474976710656), by norm_num⟩
  | 3 => ⟨((770112040020261/1125899906842624), (616697259488009/2251799813685248)), (1124577/1125899906842624), by norm_num⟩
  | 4 => ⟨((442307236809081/1125899906842624), (421819010458093/1125899906842624)), (4308775/2251799813685248), by norm_num⟩
  | 5 => ⟨((62898714325285/4503599627370496), (331421292097751/1125899906842624)), (13227911/4503599627370496), by norm_num⟩
  | 6 => ⟨((-194675932866163/2251799813685248), (148119548079061/18014398509481984)), (32628237/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-22794954519/268435456)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-23254829327/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((43739878949851/2251799813685248), (45233920050095/562949953421312)), (13905153/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1929084943/34359738368), (-3989954987/17179869184)), (309/68719476736), by norm_num⟩
  | 2 => ⟨((2787886319/34359738368), (5766226605/17179869184)), (449/68719476736), by norm_num⟩
  | 3 => ⟨((-5372018587/68719476736), (-5555512843/17179869184)), (435/68719476736), by norm_num⟩
  | 4 => ⟨((1940891351/34359738368), (8028748711/34359738368)), (79/17179869184), by norm_num⟩
  | 5 => ⟨((-4487918037/137438953472), (-4641213705/34359738368)), (367/137438953472), by norm_num⟩
  | 6 => ⟨((2161958591/137438953472), (4471611005/68719476736)), (355/274877906944), by norm_num⟩
  | 7 => ⟨((-3570779459/549755813888), (-1846374023/68719476736)), (295/549755813888), by norm_num⟩
  | 8 => ⟨((5160440051/2199023255552), (10673414661/1099511627776)), (107/549755813888), by norm_num⟩
  | 9 => ⟨((-828643899/1099511627776), (-27422343375/8796093022208)), (69/1099511627776), by norm_num⟩
  | 10 => ⟨((3832142277/17592186044416), (15852153365/17592186044416)), (321/17592186044416), by norm_num⟩
  | 11 => ⟨((-1006937801/17592186044416), (-8330657525/35184372088832)), (339/70368744177664), by norm_num⟩
  | 12 => ⟨((3880566109/281474976710656), (16052464823/281474976710656)), (329/281474976710656), by norm_num⟩
  | 13 => ⟨((-3451162673/1125899906842624), (-14276181837/1125899906842624)), (147/562949953421312), by norm_num⟩
  | 14 => ⟨((712510223/1125899906842624), (11789563655/4503599627370496)), (487/9007199254740992), by norm_num⟩
  | 15 => ⟨((-1098357027/9007199254740992), (-9086992487/18014398509481984)), (377/36028797018963968), by norm_num⟩
  | 16 => ⟨((3174660131/144115188075855872), (26264786449/288230376151711744)), (547/288230376151711744), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (1737168389355/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778122165007817/633825300114114700748351602688), (128401820601/39614081257132168796771975168)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889014489492891/39614081257132168796771975168), (72210377079/1237940039285380274899124224)), (12997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472186046605729/618970019642690137449562112), (306816059365/309485009821345068724781056)), (13811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770410530075067/154742504910672534362390528), (613456592865/38685626227668133590597632)), (13813/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548822127941237/9671406556917033397649408), (287464561969/1208925819614629174706176)), (1619/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258148898438531/604462909807314587353088), (2011506495933/604462909807314587353088)), (11335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29480509089607/1180591620717411303424), (1633650487579/37778931862957161709568)), (18423/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648380009891797/2361183241434822606848), (153078368793/295147905179352825856)), (6911/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620376659485439/590295810358705651712), (3365739791047/590295810358705651712)), (9505/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822135697782381/73786976294838206464), (2102100135417/36893488147419103232)), (5943/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821151142138745/9223372036854775808), (4725638684391/9223372036854775808)), (6689/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398100077749653/288230376151711744), (590066914363/144115188075855872)), (26771/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193194153092533/144115188075855872), (4124733849167/144115188075855872)), (11721/72057594037927936), by norm_num⟩
  | 4 => ⟨((372389745387381/9007199254740992), (385978031275/2251799813685248)), (17599/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486662276409851/9007199254740992), (7699556961491/9007199254740992)), (44059/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222765154281675/4503599627370496), (7669626964837/2251799813685248)), (88301/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104174558418137/1125899906842624), (22859758244273/2251799813685248)), (33229/562949953421312), by norm_num⟩
  | 0 => ⟨((541325812111871/562949953421312), (45126180601513/2251799813685248)), (267695/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541325812111871/562949953421312), (45126180601513/2251799813685248)), (1021175393111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2081224874910935/2251799813685248), (86785570238209/2251799813685248)), (525555/2251799813685248), by norm_num⟩
  | 2 => ⟨((1920226308958591/2251799813685248), (2506610024587/35184372088832)), (1011999/2251799813685248), by norm_num⟩
  | 3 => ⟨((101627970631985/140737488355328), (4275032341915/35184372088832)), (1870163/2251799813685248), by norm_num⟩
  | 4 => ⟨((1140941775518615/2251799813685248), (49392708808105/281474976710656)), (49303/35184372088832), by norm_num⟩
  | 5 => ⟨((508753570554277/2251799813685248), (12513147159597/70368744177664)), (4304953/2251799813685248), by norm_num⟩
  | 6 => ⟨((43739878949851/2251799813685248), (45233920050095/562949953421312)), (13905153/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-23254829327/268435456)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-681712945/268435456), (-11844916789/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((681614269956197/9007199254740992), (-402225847075071/18014398509481984)), (7157393/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7655989171/34359738368), (2258929181/34359738368)), (163/68719476736), by norm_num⟩
  | 2 => ⟨((22542592939/68719476736), (-1662819783/17179869184)), (121/34359738368), by norm_num⟩
  | 3 => ⟨((-22125096447/68719476736), (6528095179/68719476736)), (239/68719476736), by norm_num⟩
  | 4 => ⟨((16286499099/68719476736), (-1201348619/17179869184)), (177/68719476736), by norm_num⟩
  | 5 => ⟨((-2397730139/17179869184), (2829838161/68719476736)), (105/68719476736), by norm_num⟩
  | 6 => ⟨((18826586887/274877906944), (-5554857191/274877906944)), (13/17179869184), by norm_num⟩
  | 7 => ⟨((-3959552591/137438953472), (4673125153/549755813888)), (177/549755813888), by norm_num⟩
  | 8 => ⟨((11658660989/1099511627776), (-6879865927/2199023255552)), (263/2199023255552), by norm_num⟩
  | 9 => ⟨((-15256984827/4398046511104), (4501632313/4398046511104)), (87/2199023255552), by norm_num⟩
  | 10 => ⟨((4492326083/4398046511104), (-5301912661/17592186044416)), (207/17592186044416), by norm_num⟩
  | 11 => ⟨((-4809956373/17592186044416), (5676784837/70368744177664)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((18883497377/281474976710656), (-2785824425/140737488355328)), (111/140737488355328), by norm_num⟩
  | 13 => ⟨((-8554047037/562949953421312), (5047809247/1125899906842624)), (203/1125899906842624), by norm_num⟩
  | 14 => ⟨((1799062109/562949953421312), (-2123280901/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 15 => ⟨((-5650377173/9007199254740992), (1667165613/9007199254740992)), (137/18014398509481984), by norm_num⟩
  | 16 => ⟨((16637190795/144115188075855872), (-613608427/18014398509481984)), (203/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-93434021491/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778052486937095/633825300114114700748351602688), (-441957828305/633825300114114700748351602688)), (2883/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888936238331943/39614081257132168796771975168), (-62136695355/4951760157141521099596496896)), (12973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888661224832393/2475880078570760549798248448), (-528025161589/2475880078570760549798248448)), (1723/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442581942770639/38685626227668133590597632), (-527871393867/154742504910672534362390528)), (13785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744756491887/9671406556917033397649408), (-123679029167/2417851639229258349412352)), (3231/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258081413352779/604462909807314587353088), (-13522292439/18889465931478580854784)), (2827/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886643321099963/75557863725914323419136), (-175713318789/18889465931478580854784)), (18377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296678426239661/4722366482869645213696), (-263436208481/2361183241434822606848)), (1723/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810132519781001/295147905179352825856), (-362007552185/295147905179352825856)), (9477/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455499257117585/18446744073709551616), (-904367671179/73786976294838206464)), (11847/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227624539205387/1152921504606846976), (-508259509803/4611686018427387904)), (26659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398061736917283/288230376151711744), (-1015401958747/1152921504606846976)), (13331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193061604463129/144115188075855872), (-55451354471/9007199254740992)), (23333/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489363437123013/36028797018963968), (-1328326544421/36028797018963968)), (35007/36028797018963968), by norm_num⟩
  | 3 => ⟨((743211780362151/4503599627370496), (-414008000867/2251799813685248)), (10943/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222304777493561/4503599627370496), (-412371553367/562949953421312)), (43793/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103850437238885/1125899906842624), (-614482332105/281474976710656)), (65741/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164174182994599/2251799813685248), (-9702088284563/2251799813685248)), (131695/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164174182994599/2251799813685248), (-9702088284563/2251799813685248)), (502376560691451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079916578444977/2251799813685248), (-18649090260135/2251799813685248)), (63569/281474976710656), by norm_num⟩
  | 2 => ⟨((480249749381959/562949953421312), (-4306394352779/281474976710656)), (947891/2251799813685248), by norm_num⟩
  | 3 => ⟨((102391713619875/140737488355328), (-29390105405895/1125899906842624)), (1646287/2251799813685248), by norm_num⟩
  | 4 => ⟨((595182796254397/1125899906842624), (-85529542729385/2251799813685248)), (1240709/1125899906842624), by norm_num⟩
  | 5 => ⟨((1252025097952471/4503599627370496), (-180853420786901/4503599627370496)), (5623999/4503599627370496), by norm_num⟩
  | 6 => ⟨((681614269956197/9007199254740992), (-402225847075071/18014398509481984)), (7157393/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-11844916789/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-693588655/268435456), (-24102519871/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-341024714652319/18014398509481984), (-1316363291934681/18014398509481984)), (29381161/18014398509481984), by norm_num⟩
  | 1 => ⟨((974291557/17179869184), (15043151845/68719476736)), (169/34359738368), by norm_num⟩
  | 2 => ⟨((-2918716661/34359738368), (-22532627739/68719476736)), (127/17179869184), by norm_num⟩
  | 3 => ⟨((1457282283/17179869184), (22500573375/68719476736)), (255/34359738368), by norm_num⟩
  | 4 => ⟨((-4365627567/68719476736), (-8425711729/34359738368)), (3/536870912), by norm_num⟩
  | 5 => ⟨((5231300559/137438953472), (20192941243/137438953472)), (231/68719476736), by norm_num⟩
  | 6 => ⟨((-5223858639/274877906944), (-5041053815/68719476736)), (463/274877906944), by norm_num⟩
  | 7 => ⟨((4471223405/549755813888), (4314756459/137438953472)), (199/274877906944), by norm_num⟩
  | 8 => ⟨((-418580883/137438953472), (-12925855177/1099511627776)), (599/2199023255552), by norm_num⟩
  | 9 => ⟨((1114627787/1099511627776), (8604978115/2199023255552)), (401/4398046511104), by norm_num⟩
  | 10 => ⟨((-5342602295/17592186044416), (-10311284261/8796093022208)), (241/8796093022208), by norm_num⟩
  | 11 => ⟨((5820002225/70368744177664), (2808167913/8796093022208)), (527/70368744177664), by norm_num⟩
  | 12 => ⟨((-5811722833/281474976710656), (-22433384657/281474976710656)), (529/281474976710656), by norm_num⟩
  | 13 => ⟨((2678517793/562949953421312), (20678281361/1125899906842624)), (245/562949953421312), by norm_num⟩
  | 14 => ⟨((-1146303171/1125899906842624), (-2212378387/562949953421312)), (211/2251799813685248), by norm_num⟩
  | 15 => ⟨((1831475949/9007199254740992), (14139079115/18014398509481984)), (339/18014398509481984), by norm_num⟩
  | 16 => ⟨((-5486611609/144115188075855872), (-5294611953/36028797018963968)), (255/72057594037927936), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-2376340292229/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777980213032583/633825300114114700748351602688), (-2809911844277/633825300114114700748351602688)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888854720345231/39614081257132168796771975168), (-1580219578111/19807040628566084398385987584)), (13007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29508973915131/38685626227668133590597632), (-839270301949/618970019642690137449562112)), (13823/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221280070076045/19342813113834066795298816), (-3356085505147/154742504910672534362390528)), (6913/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548662660975353/9671406556917033397649408), (-1572636288159/4835703278458516698824704)), (12965/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258009244389991/604462909807314587353088), (-1375528156201/302231454903657293676544)), (2837/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943262709173867/37778931862957161709568), (-1117121276873/18889465931478580854784)), (18445/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648294725085711/2361183241434822606848), (-1674815469893/2361183241434822606848)), (13839/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620141806573229/590295810358705651712), (-4602928158293/590295810358705651712)), (4759/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821841653053807/73786976294838206464), (-44917510603/576460752303423488)), (93/288230376151711744), by norm_num⟩
  | 7 => ⟨((1820819685309895/9223372036854775808), (-1615581265797/2305843009213693952)), (26801/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592068035854381/1152921504606846976), (-6455086142901/1152921504606846976)), (13411/576460752303423488), by norm_num⟩
  | 5 => ⟨((298225623730611/36028797018963968), (-1410016434857/36028797018963968)), (11747/72057594037927936), by norm_num⟩
  | 4 => ⟨((744559833702277/18014398509481984), (-8443852191867/36028797018963968)), (4411/4503599627370496), by norm_num⟩
  | 3 => ⟨((743054977253999/4503599627370496), (-10526435375057/9007199254740992)), (44193/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110825521965687/2251799813685248), (-10483968169033/2251799813685248)), (88639/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206654532810983/2251799813685248), (-15620142678697/1125899906842624)), (133591/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161821885325577/2251799813685248), (-61638385341405/2251799813685248)), (8429/70368744177664), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161821885325577/2251799813685248), (-61638385341405/2251799813685248)), (32154083520388581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((259219011440611/281474976710656), (-118350849482579/2251799813685248)), (133167/562949953421312), by norm_num⟩
  | 2 => ⟨((1903562113949863/2251799813685248), (-1703014962719/17592186044416)), (518547/1125899906842624), by norm_num⟩
  | 3 => ⟨((397019180023713/562949953421312), (-368549395093581/2251799813685248)), (1954211/2251799813685248), by norm_num⟩
  | 4 => ⟨((1059667470341531/2251799813685248), (-519837252846461/2251799813685248)), (1698047/1125899906842624), by norm_num⟩
  | 5 => ⟨((189329525002849/1125899906842624), (-978514383677087/4503599627370496)), (148885/70368744177664), by norm_num⟩
  | 6 => ⟨((-341024714652319/18014398509481984), (-1316363291934681/18014398509481984)), (29381161/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-24102519871/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-352442413/134217728), (-24495066933/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-645046403349457/9007199254740992), (23556144626681/2251799813685248)), (13831409/9007199254740992), by norm_num⟩
  | 1 => ⟨((29966098761/137438953472), (-4377271171/137438953472)), (645/137438953472), by norm_num⟩
  | 2 => ⟨((-5702028753/17179869184), (1665837537/34359738368)), (493/68719476736), by norm_num⟩
  | 3 => ⟨((5786651493/17179869184), (-3381119839/68719476736)), (251/34359738368), by norm_num⟩
  | 4 => ⟨((-8808795155/34359738368), (643368451/17179869184)), (3/536870912), by norm_num⟩
  | 5 => ⟨((21454859599/137438953472), (-391749937/17179869184)), (469/137438953472), by norm_num⟩
  | 6 => ⟨((-21773267149/274877906944), (3180510595/274877906944)), (239/137438953472), by norm_num⟩
  | 7 => ⟨((18939771537/549755813888), (-2766610249/549755813888)), (209/274877906944), by norm_num⟩
  | 8 => ⟨((-28831279705/2199023255552), (2105751745/1099511627776)), (319/1099511627776), by norm_num⟩
  | 9 => ⟨((2438263277/549755813888), (-2849337083/4398046511104)), (217/2199023255552), by norm_num⟩
  | 10 => ⟨((-23754711219/17592186044416), (3469948273/17592186044416)), (265/8796093022208), by norm_num⟩
  | 11 => ⟨((26298818657/70368744177664), (-960394125/17592186044416)), (589/70368744177664), by norm_num⟩
  | 12 => ⟨((-208508707/2199023255552), (3898588617/281474976710656)), (75/35184372088832), by norm_num⟩
  | 13 => ⟨((6250431379/281474976710656), (-3652104775/1125899906842624)), (141/281474976710656), by norm_num⟩
  | 14 => ⟨((-5437022451/1125899906842624), (1588416419/2251799813685248)), (493/4503599627370496), by norm_num⟩
  | 15 => ⟨((17656679303/18014398509481984), (-2579183695/18014398509481984)), (201/9007199254740992), by norm_num⟩
  | 16 => ⟨((-26878078157/144115188075855872), (3926191315/144115188075855872)), (307/72057594037927936), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (487916706193/1267650600228229401496703205376)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777908209216737/633825300114114700748351602688), (576898704281/79228162514264337593543950336)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888773338941589/39614081257132168796771975168), (324430045311/2475880078570760549798248448)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888487356622249/2475880078570760549798248448), (1378457626623/618970019642690137449562112)), (13853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770153017798249/154742504910672534362390528), (5512165474515/154742504910672534362390528)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387144996419029/2417851639229258349412352), (5165886442913/9671406556917033397649408)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257936300154365/604462909807314587353088), (564797800637/75557863725914323419136)), (11377/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886405753887833/75557863725914323419136), (7339056943811/75557863725914323419136)), (18497/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162062339276289/590295810358705651712), (1375348380781/1180591620717411303424)), (13881/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620015442000981/590295810358705651712), (3779853370811/295147905179352825856)), (4775/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455420324333773/18446744073709551616), (2360643147171/18446744073709551616)), (23895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820635991510077/9223372036854775808), (10613190696719/9223372036854775808)), (26909/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591880234605931/1152921504606846976), (10601069149619/1152921504606846976)), (26945/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298183390273417/36028797018963968), (4631154738089/72057594037927936)), (369/2251799813685248), by norm_num⟩
  | 4 => ⟨((744428541996849/18014398509481984), (13866238951339/36028797018963968)), (17751/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485765729241011/9007199254740992), (8642607412509/4503599627370496)), (11129/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110457449657911/2251799813685248), (17213959853963/2251799813685248)), (44723/2251799813685248), by norm_num⟩
  | 1 => ⟨((275679013268035/281474976710656), (25643225834937/1125899906842624)), (67605/1125899906842624), by norm_num⟩
  | 0 => ⟨((539727579870989/562949953421312), (25289070731561/562949953421312)), (137299/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((539727579870989/562949953421312), (25289070731561/562949953421312)), (523754124168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129081777877595/140737488355328), (24245865658535/281474976710656)), (275607/1125899906842624), by norm_num⟩
  | 2 => ⟨((938777013724225/1125899906842624), (355805632964919/2251799813685248)), (1106089/2251799813685248), by norm_num⟩
  | 3 => ⟨((754643342823675/1125899906842624), (593342529919497/2251799813685248)), (2194063/2251799813685248), by norm_num⟩
  | 4 => ⟨((213816846634917/562949953421312), (795385073747045/2251799813685248)), (4097435/2251799813685248), by norm_num⟩
  | 5 => ⟨((43895947738371/2251799813685248), (302099196021775/1125899906842624)), (6007143/2251799813685248), by norm_num⟩
  | 6 => ⟨((-645046403349457/9007199254740992), (23556144626681/2251799813685248)), (13831409/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-24495066933/268435456)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile052Terms2
