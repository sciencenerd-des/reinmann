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
namespace Reinmann.XiBand97.Tile003Terms2
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
  | 0 => ⟨((69/80), (9919/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9919/640))
  have he : value ((69/80), (9919/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1441860553/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((218656500366799/4503599627370496), (349311632717879/4503599627370496)), (53317843/4503599627370496), by norm_num⟩
  | 1 => ⟨((-289079927/2147483648), (-923631185/4294967296)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((801499745/4294967296), (5001659/16777216)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((-740743051/4294967296), (-591681849/2147483648)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((513443957/4294967296), (820245211/4294967296)), (33/1073741824), by norm_num⟩
  | 5 => ⟨((-284713785/4294967296), (-909681049/8589934592)), (37/2147483648), by norm_num⟩
  | 6 => ⟨((131565705/4294967296), (420361903/8589934592)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((-208444337/17179869184), (-665994669/34359738368)), (7/2147483648), by norm_num⟩
  | 8 => ⟨((288965209/68719476736), (461632327/68719476736)), (157/137438953472), by norm_num⟩
  | 9 => ⟨((-712161493/549755813888), (-568851815/274877906944)), (195/549755813888), by norm_num⟩
  | 10 => ⟨((394906185/1099511627776), (630876851/1099511627776)), (219/2199023255552), by norm_num⟩
  | 11 => ⟨((-796299953/8796093022208), (-1272117849/8796093022208)), (223/8796093022208), by norm_num⟩
  | 12 => ⟨((735937423/35184372088832), (587843267/17592186044416)), (13/2199023255552), by norm_num⟩
  | 13 => ⟨((-627831323/140737488355328), (-501491573/70368744177664)), (179/140737488355328), by norm_num⟩
  | 14 => ⟨((497348013/562949953421312), (24829105/17592186044416)), (143/562949953421312), by norm_num⟩
  | 15 => ⟨((-367717731/2251799813685248), (-587442317/2251799813685248)), (107/2251799813685248), by norm_num⟩
  | 16 => ⟨((509765017/18014398509481984), (203591993/4503599627370496)), (75/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (658798520223/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889139818008773/316912650057057350374175801344), (779246244783/316912650057057350374175801344)), (46177/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944595829918801/19807040628566084398385987584), (876469848807/19807040628566084398385987584)), (25977/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472233113442029/618970019642690137449562112), (1862044165663/2475880078570760549798248448)), (55207/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((55331213255915/4835703278458516698824704), (930766664949/77371252455336267181195264)), (110427/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548998682068385/9671406556917033397649408), (872322460225/4835703278458516698824704)), (103539/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629151705820959/302231454903657293676544), (190752742389/75557863725914323419136)), (45305/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943501859359725/37778931862957161709568), (2478769160437/75557863725914323419136)), (147267/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296948418810211/4722366482869645213696), (1858187886981/4722366482869645213696)), (110473/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620635783154989/590295810358705651712), (2553564582355/590295810358705651712)), (1187/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1822459714513647/73786976294838206464), (797447886533/18446744073709551616)), (189975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821515814563385/9223372036854775808), (3585542112733/9223372036854775808)), (213797/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398191293633123/288230376151711744), (3581828948911/1152921504606846976)), (53473/288230376151711744), by norm_num⟩
  | 5 => ⟨((596756811228421/72057594037927936), (1564963953527/72057594037927936)), (93631/72057594037927936), by norm_num⟩
  | 4 => ⟨((745019305041661/18014398509481984), (2343279607375/18014398509481984)), (140553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487262548071815/9007199254740992), (2921822149961/4503599627370496)), (87939/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223967878257661/4503599627370496), (45483335517/17592186044416)), (704635/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105079279609253/1125899906842624), (17357096245393/2251799813685248)), (264943/562949953421312), by norm_num⟩
  | 0 => ⟨((2168942991204927/2251799813685248), (34282460045515/2251799813685248)), (532721/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168942991204927/2251799813685248), (34282460045515/2251799813685248)), (2032169344188499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2088613021213971/2251799813685248), (66042017576413/2251799813685248)), (4169837/2251799813685248), by norm_num⟩
  | 2 => ⟨((241914422066613/281474976710656), (122511971995943/2251799813685248)), (7979893/2251799813685248), by norm_num⟩
  | 3 => ⟨((1656646563646885/2251799813685248), (210586484439827/2251799813685248)), (7292497/1125899906842624), by norm_num⟩
  | 4 => ⟨((1199099117516725/2251799813685248), (309856474520947/2251799813685248)), (12094141/1125899906842624), by norm_num⟩
  | 5 => ⟨((297945592381685/1125899906842624), (330001470731843/2251799813685248)), (64835327/4503599627370496), by norm_num⟩
  | 6 => ⟨((218656500366799/4503599627370496), (349311632717879/4503599627370496)), (53317843/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1441860553/33554432)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-736693929/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((780195601165505/9007199254740992), (112412842210857/18014398509481984)), (51975097/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1054029745/4294967296), (-75933829/4294967296)), (9/536870912), by norm_num⟩
  | 2 => ⟨((1493145569/4294967296), (107568369/4294967296)), (13/536870912), by norm_num⟩
  | 3 => ⟨((-1410133317/4294967296), (-50794023/2147483648)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((1997604265/8589934592), (4497197/268435456)), (9/536870912), by norm_num⟩
  | 5 => ⟨((-282981953/2147483648), (-81545719/8589934592)), (83/8589934592), by norm_num⟩
  | 6 => ⟨((1068997661/17179869184), (19253035/4294967296)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((-865342411/34359738368), (-62340521/34359738368)), (33/17179869184), by norm_num⟩
  | 8 => ⟨((1225849833/137438953472), (44155999/68719476736)), (95/137438953472), by norm_num⟩
  | 9 => ⟨((-385899345/137438953472), (-6950187/34359738368)), (61/274877906944), by norm_num⟩
  | 10 => ⟨((874668139/1099511627776), (7876545/137438953472)), (35/549755813888), by norm_num⟩
  | 11 => ⟨((-450567535/2199023255552), (-16229769/1099511627776)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((1702071937/35184372088832), (7663733/2199023255552)), (141/35184372088832), by norm_num⟩
  | 13 => ⟨((-741897373/70368744177664), (-106894723/140737488355328)), (125/140737488355328), by norm_num⟩
  | 14 => ⟨((1201116307/562949953421312), (86530159/562949953421312)), (103/562949953421312), by norm_num⟩
  | 15 => ⟨((-1814943333/4503599627370496), (-130751147/4503599627370496)), (79/2251799813685248), by norm_num⟩
  | 16 => ⟨((642765209/9007199254740992), (46305737/9007199254740992)), (57/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (1463752935/158456325028528675187087900672)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444550092412739/158456325028528675187087900672), (110798111215/633825300114114700748351602688)), (92211/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944551287999447/19807040628566084398385987584), (31155382657/9903520314283042199192993792)), (103739/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888837920935627/2475880078570760549798248448), (66188693561/1237940039285380274899124224)), (110223/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442626106206095/38685626227668133590597632), (132340291591/154742504910672534362390528)), (6889/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548910324379561/9671406556917033397649408), (124029624077/9671406556917033397649408)), (103337/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258226240274639/604462909807314587353088), (3390204323/18889465931478580854784)), (90421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943439290271765/37778931862957161709568), (176216817343/75557863725914323419136)), (146935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648427398544349/2361183241434822606848), (33024516659/1180591620717411303424)), (110203/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620507429723663/590295810358705651712), (90765009817/295147905179352825856)), (151531/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911149918323077/36893488147419103232), (226755406733/73786976294838206464)), (189419/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910668363083333/4611686018427387904), (254883982591/9223372036854775808)), (213101/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796293526055659/576460752303423488), (127307225173/576460752303423488)), (213109/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193358849617587/144115188075855872), (111242402577/72057594037927936)), (11655/9007199254740992), by norm_num⟩
  | 4 => ⟨((744904306643299/18014398509481984), (166561245397/18014398509481984)), (34967/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486978822699843/9007199254740992), (51918377141/1125899906842624)), (349701/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223411684805875/4503599627370496), (413767180001/2251799813685248)), (87437/562949953421312), by norm_num⟩
  | 1 => ⟨((1104676110979745/1125899906842624), (1233432424289/2251799813685248)), (524745/1125899906842624), by norm_num⟩
  | 0 => ⟨((270930124026109/281474976710656), (608892037729/562949953421312)), (525005/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270930124026109/281474976710656), (608892037729/562949953421312)), (2002735140086936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((32597497775477/35184372088832), (4688649690377/2251799813685248)), (4047239/2251799813685248), by norm_num⟩
  | 2 => ⟨((1932842668197633/2251799813685248), (4343924270303/1125899906842624)), (939525/281474976710656), by norm_num⟩
  | 3 => ⟨((1659030824404919/2251799813685248), (7457254526831/1125899906842624)), (1620141/281474976710656), by norm_num⟩
  | 4 => ⟨((152775616254783/281474976710656), (21976758413881/2251799813685248)), (19270115/2251799813685248), by norm_num⟩
  | 5 => ⟨((165789816663981/562949953421312), (745517605419/70368744177664)), (1330909/140737488355328), by norm_num⟩
  | 6 => ⟨((780195601165505/9007199254740992), (112412842210857/18014398509481984)), (51975097/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-736693929/16777216)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-93944537/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1022520103274657/18014398509481984), (-1082640323804227/18014398509481984)), (43346659/4503599627370496), by norm_num⟩
  | 1 => ⟨((-22019917/134217728), (746067289/4294967296)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((254582985/1073741824), (-1078205911/4294967296)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-981119293/4294967296), (1038805305/4294967296)), (175/4294967296), by norm_num⟩
  | 4 => ⟨((354474937/2147483648), (-750633379/4294967296)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-409825739/4294967296), (27120119/268435456)), (75/4294967296), by norm_num⟩
  | 6 => ⟨((789699161/17179869184), (-836130411/17179869184)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((-326074879/17179869184), (172623409/8589934592)), (61/17179869184), by norm_num⟩
  | 8 => ⟨((942477621/137438953472), (-249472913/34359738368)), (179/137438953472), by norm_num⟩
  | 9 => ⟨((-605357933/274877906944), (640950633/274877906944)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((699883789/1099511627776), (-741034243/1099511627776)), (17/137438953472), by norm_num⟩
  | 11 => ⟨((-367804425/2199023255552), (778859799/4398046511104)), (145/4398046511104), by norm_num⟩
  | 12 => ⟨((354363841/8796093022208), (-375199061/8796093022208)), (71/8796093022208), by norm_num⟩
  | 13 => ⟨((-630303531/70368744177664), (667362935/70368744177664)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((1041035157/562949953421312), (-1102243989/562949953421312)), (107/281474976710656), by norm_num⟩
  | 15 => ⟨((-401197149/1125899906842624), (212392993/562949953421312)), (167/2251799813685248), by norm_num⟩
  | 16 => ⟨((579804455/9007199254740992), (-613894709/9007199254740992)), (123/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-1060259322111/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778123584634943/633825300114114700748351602688), (-313473876459/158456325028528675187087900672)), (23081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236127020616473/4951760157141521099596496896), (-1410327973793/39614081257132168796771975168)), (103873/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944373035345415/1237940039285380274899124224), (-1498092540475/2475880078570760549798248448)), (55187/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885206265672967/77371252455336267181195264), (-748832092891/77371252455336267181195264)), (6899/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548824128353363/9671406556917033397649408), (-10965665739/75557863725914323419136)), (12937/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258150772912919/604462909807314587353088), (-613849895721/302231454903657293676544)), (45285/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886755860242045/75557863725914323419136), (-997079932353/37778931862957161709568)), (147197/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296762681862681/4722366482869645213696), (-1494874538827/4722366482869645213696)), (6901/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620380649617121/590295810358705651712), (-64195063445/18446744073709551616)), (151851/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822141179363535/73786976294838206464), (-2565988156451/73786976294838206464)), (94929/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455289496711777/2305843009213693952), (-2884244028101/9223372036854775808)), (213651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49762750041029/36028797018963968), (-2881131404943/1152921504606846976)), (213727/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596600915472557/72057594037927936), (-2517492655235/144115188075855872)), (187097/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489572389797969/36028797018963968), (-1884627631369/18014398509481984)), (140409/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486682332908535/9007199254740992), (-4699372116989/9007199254740992)), (87831/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222815100477719/4503599627370496), (-9362251348133/4503599627370496)), (175889/1125899906842624), by norm_num⟩
  | 1 => ⟨((2208448426104731/2251799813685248), (-3488121729785/562949953421312)), (66101/140737488355328), by norm_num⟩
  | 0 => ⟨((2165598274790729/2251799813685248), (-13771729523955/1125899906842624)), (531105/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165598274790729/2251799813685248), (-13771729523955/1125899906842624)), (2026004793407249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2082359727158093/2251799813685248), (-52978126237877/2251799813685248)), (4138161/2251799813685248), by norm_num⟩
  | 2 => ⟨((240552874921099/281474976710656), (-48991706912661/1125899906842624)), (1962069/562949953421312), by norm_num⟩
  | 3 => ⟨((410094528459605/562949953421312), (-83738143140497/1125899906842624)), (14097527/2251799813685248), by norm_num⟩
  | 4 => ⟨((591258608716143/1125899906842624), (-15250269636129/140737488355328)), (11318181/1125899906842624), by norm_num⟩
  | 5 => ⟨((594550570636749/2251799813685248), (-128137190921559/1125899906842624)), (28680399/2251799813685248), by norm_num⟩
  | 6 => ⟨((1022520103274657/18014398509481984), (-1082640323804227/18014398509481984)), (43346659/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-93944537/2097152)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-765614889/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-14394712419415/2251799813685248), (-354164192449779/4503599627370496)), (117824253/9007199254740992), by norm_num⟩
  | 1 => ⟨((10105217/536870912), (497252871/2147483648)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((-119016779/4294967296), (-91508171/268435456)), (31/536870912), by norm_num⟩
  | 3 => ⟨((29203137/1073741824), (179626817/536870912)), (123/2147483648), by norm_num⟩
  | 4 => ⟨((-85986855/4294967296), (-1057800403/4294967296)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((101273219/8589934592), (1245851495/8589934592)), (217/8589934592), by norm_num⟩
  | 6 => ⟨((-99397605/17179869184), (-1222777901/17179869184)), (215/17179869184), by norm_num⟩
  | 7 => ⟨((20905013/8589934592), (1028684261/34359738368)), (183/34359738368), by norm_num⟩
  | 8 => ⟨((-61553535/68719476736), (-757224509/68719476736)), (17/8589934592), by norm_num⟩
  | 9 => ⟨((40275695/137438953472), (495466969/137438953472)), (179/274877906944), by norm_num⟩
  | 10 => ⟨((-94871461/1099511627776), (-1167097805/1099511627776)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((25394839/1099511627776), (1249617553/4398046511104)), (229/4398046511104), by norm_num⟩
  | 12 => ⟨((-12462259/2199023255552), (-1226474211/17592186044416)), (227/17592186044416), by norm_num⟩
  | 13 => ⟨((90324581/70368744177664), (1111162607/70368744177664)), (13/4398046511104), by norm_num⟩
  | 14 => ⟨((-75987205/281474976710656), (-934785855/281474976710656)), (11/17592186044416), by norm_num⟩
  | 15 => ⟨((59663917/1125899906842624), (1467957285/2251799813685248)), (279/2251799813685248), by norm_num⟩
  | 16 => ⟨((-87838381/9007199254740992), (-540288831/4503599627370496)), (207/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2151792448499/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778049120409737/633825300114114700748351602688), (-2544580395699/633825300114114700748351602688)), (92451/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888932265627929/39614081257132168796771975168), (-2862019979307/39614081257132168796771975168)), (13003/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888656756990233/2475880078570760549798248448), (-1520054134271/1237940039285380274899124224)), (6909/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770323025844831/154742504910672534362390528), (-3039222151669/154742504910672534362390528)), (110565/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774370006664039/4835703278458516698824704), (-2848329582581/9671406556917033397649408)), (103677/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258076968839241/604462909807314587353088), (-2491347554001/604462909807314587353088)), (90739/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943317773802027/37778931862957161709568), (-2023338234627/37778931862957161709568)), (73747/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296672114399401/4722366482869645213696), (-3033465210571/4722366482869645213696)), (110657/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620255579015741/590295810358705651712), (-4168510093013/590295810358705651712)), (152213/590295810358705651712), by norm_num⟩
  | 8 => ⟨((3558562562369/144115188075855872), (-5206883222089/73786976294838206464)), (190355/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910490042762801/4611686018427387904), (-731573166631/1152921504606846976)), (837/36028797018963968), by norm_num⟩
  | 6 => ⟨((199028589393443/144115188075855872), (-5846143464469/1152921504606846976)), (214427/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193043402039889/144115188075855872), (-5108136667315/144115188075855872)), (187797/144115188075855872), by norm_num⟩
  | 4 => ⟨((744665825246875/18014398509481984), (-1911936961969/9007199254740992)), (141021/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486376015728329/9007199254740992), (-9534431030801/9007199254740992)), (176581/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111093193042237/2251799813685248), (-18993285404685/4503599627370496)), (708153/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207465499959599/2251799813685248), (-14150815803825/1125899906842624)), (1066821/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163475066413353/2251799813685248), (-27926969090913/1125899906842624)), (1076045/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163475066413353/2251799813685248), (-27926969090913/1125899906842624)), (4104785923484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129826835409459/140737488355328), (-53663119555735/1125899906842624)), (4242115/2251799813685248), by norm_num⟩
  | 2 => ⟨((59721157459079/70368744177664), (-198011576632113/2251799813685248)), (8230871/2251799813685248), by norm_num⟩
  | 3 => ⟨((802248681559497/1125899906842624), (-5251568312111/35184372088832)), (15418455/2251799813685248), by norm_num⟩
  | 4 => ⟨((546551321581657/1125899906842624), (-239484947684939/1125899906842624)), (26575205/2251799813685248), by norm_num⟩
  | 5 => ⟨((857501827606903/4503599627370496), (-930035175316259/4503599627370496)), (9276613/562949953421312), by norm_num⟩
  | 6 => ⟨((-14394712419415/2251799813685248), (-354164192449779/4503599627370496)), (117824253/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-765614889/16777216)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-194738051/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-261164538931025/4503599627370496), (-870516798378477/18014398509481984)), (249265381/18014398509481984), by norm_num⟩
  | 1 => ⟨((373067397/2147483648), (621756379/4294967296)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((-558805021/2147483648), (-465653913/2147483648)), (17/268435456), by norm_num⟩
  | 3 => ⟨((1116020157/4294967296), (464991485/2147483648)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((-835824401/4294967296), (-696494999/4294967296)), (207/4294967296), by norm_num⟩
  | 5 => ⟨((1001562453/8589934592), (834605019/8589934592)), (125/4294967296), by norm_num⟩
  | 6 => ⟨((-1000137655/17179869184), (-416708865/8589934592)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((856041329/34359738368), (356670913/17179869184)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((-641117659/68719476736), (-534245283/68719476736)), (41/17179869184), by norm_num⟩
  | 9 => ⟨((426803747/137438953472), (711313705/274877906944)), (55/68719476736), by norm_num⟩
  | 10 => ⟨((-3995593/4294967296), (-852362169/1099511627776)), (133/549755813888), by norm_num⟩
  | 11 => ⟨((1114272759/4398046511104), (464263429/2199023255552)), (73/1099511627776), by norm_num⟩
  | 12 => ⟨((-556343811/8796093022208), (-927205959/17592186044416)), (147/8796093022208), by norm_num⟩
  | 13 => ⟨((1025635145/70368744177664), (427332433/35184372088832)), (273/70368744177664), by norm_num⟩
  | 14 => ⟨((-438932615/140737488355328), (-731527749/281474976710656)), (235/281474976710656), by norm_num⟩
  | 15 => ⟨((10957705/17592186044416), (584389677/1125899906842624)), (95/562949953421312), by norm_num⟩
  | 16 => ⟨((-1050443217/9007199254740992), (-218834377/2251799813685248)), (287/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-3187324321395/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777976830366993/633825300114114700748351602688), (-1884431365211/316912650057057350374175801344)), (23143/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944425364518101/19807040628566084398385987584), (-4239007945941/39614081257132168796771975168)), (104167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888569841847335/2475880078570760549798248448), (-2251378727615/1237940039285380274899124224)), (110705/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770235793230889/154742504910672534362390528), (-2250710379915/77371252455336267181195264)), (6921/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548657895721625/9671406556917033397649408), (-4218662119279/9671406556917033397649408)), (12981/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629002389610063/302231454903657293676544), (-922477489039/151115727451828646838272)), (90901/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235814701101165/9444732965739290427392), (-5993443252331/75557863725914323419136)), (147775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296583109146229/4722366482869645213696), (-4492755511269/4722366482869645213696)), (55443/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620132302424265/590295810358705651712), (-6173759341977/590295810358705651712)), (38139/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821828596847403/73786976294838206464), (-481970815561/4611686018427387904)), (190827/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820803383034875/9223372036854775808), (-2166922197767/2305843009213693952)), (107431/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398012430124477/288230376151711744), (-8657963985003/1152921504606846976)), (215091/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596442105204631/72057594037927936), (-3782394233217/72057594037927936)), (188461/144115188075855872), by norm_num⟩
  | 4 => ⟨((744543869403505/18014398509481984), (-5662674309261/18014398509481984)), (141603/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486062199971339/9007199254740992), (-14118534523457/9007199254740992)), (88727/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221532140765409/4503599627370496), (-14061424390121/2251799813685248)), (356263/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206418171685117/2251799813685248), (-10474884824345/562949953421312)), (1075583/2251799813685248), by norm_num⟩
  | 0 => ⟨((270139999726071/281474976710656), (-82665040661201/2251799813685248)), (272307/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((270139999726071/281474976710656), (-82665040661201/2251799813685248)), (1038768769384288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2071057163979523/2251799813685248), (-158672250887353/2251799813685248)), (2170703/1125899906842624), by norm_num⟩
  | 2 => ⟨((946820598206443/1125899906842624), (-291872572266713/2251799813685248)), (8597711/2251799813685248), by norm_num⟩
  | 3 => ⟨((1554617493542327/2251799813685248), (-245448962020609/1125899906842624)), (16689243/2251799813685248), by norm_num⟩
  | 4 => ⟨((483136814866081/1125899906842624), (-169455227684987/562949953421312)), (3790091/281474976710656), by norm_num⟩
  | 5 => ⟨((421212878336017/4503599627370496), (-1163443513492711/4503599627370496)), (88551645/4503599627370496), by norm_num⟩
  | 6 => ⟨((-261164538931025/4503599627370496), (-870516798378477/18014398509481984)), (249265381/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-194738051/4194304)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1583277307/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-325330757107475/4503599627370496), (80068318848123/18014398509481984)), (107969227/9007199254740992), by norm_num⟩
  | 1 => ⟨((1889184551/8589934592), (-3632453/268435456)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-1437916189/4294967296), (88472677/4294967296)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((729628017/2147483648), (-89785683/4294967296)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-1110684435/4294967296), (8542329/536870912)), (191/4294967296), by norm_num⟩
  | 5 => ⟨((676300737/4294967296), (-83223399/8589934592)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((-1372675179/17179869184), (42229251/8589934592)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((1194040109/34359738368), (-73467373/34359738368)), (211/34359738368), by norm_num⟩
  | 8 => ⟨((-227205119/17179869184), (111836533/137438953472)), (323/137438953472), by norm_num⟩
  | 9 => ⟨((1229744147/274877906944), (-75664185/274877906944)), (221/274877906944), by norm_num⟩
  | 10 => ⟨((-374398365/274877906944), (23036131/274877906944)), (271/1099511627776), by norm_num⟩
  | 11 => ⟨((414496081/1099511627776), (-102013117/4398046511104)), (151/2199023255552), by norm_num⟩
  | 12 => ⟨((-1682590159/17592186044416), (103527075/17592186044416)), (309/17592186044416), by norm_num⟩
  | 13 => ⟨((788105153/35184372088832), (-96981693/70368744177664)), (73/17592186044416), by norm_num⟩
  | 14 => ⟨((-685543949/140737488355328), (10545105/35184372088832)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((1113148765/1125899906842624), (-68490259/1125899906842624)), (105/562949953421312), by norm_num⟩
  | 16 => ⟨((-423625799/2251799813685248), (104260065/9007199254740992)), (321/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (2006114248277/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222238445377183/79228162514264337593543950336), (2371971887405/316912650057057350374175801344)), (23167/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888772576550575/39614081257132168796771975168), (666961687431/4951760157141521099596496896)), (104281/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888486499228141/2475880078570760549798248448), (5667652560075/2475880078570760549798248448)), (55417/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770152107183313/154742504910672534362390528), (5665940792309/154742504910672534362390528)), (110873/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548579075473305/9671406556917033397649408), (2655000570217/4835703278458516698824704)), (103985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39310482727409/18889465931478580854784), (4644433095529/604462909807314587353088)), (22757/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886404262228221/75557863725914323419136), (7543796169933/75557863725914323419136)), (147999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648248751528817/2361183241434822606848), (5654866425425/4722366482869645213696)), (27767/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620013626707943/590295810358705651712), (7770599489331/590295810358705651712)), (152829/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910839401819939/36893488147419103232), (4852994868185/36893488147419103232)), (191203/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910316438944325/4611686018427387904), (2727315394817/2305843009213693952)), (215333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795938368294191/576460752303423488), (10896798157789/1152921504606846976)), (215621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192730069080087/144115188075855872), (2380171898829/36028797018963968)), (188991/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488850986466603/36028797018963968), (14253036223911/36028797018963968)), (142067/18014398509481984), by norm_num⟩
  | 3 => ⟨((371439152477945/2251799813685248), (17767363240439/9007199254740992)), (356303/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110446097604713/2251799813685248), (17694084366423/2251799813685248)), (358009/2251799813685248), by norm_num⟩
  | 1 => ⟨((275673372496803/281474976710656), (26358347281385/1125899906842624)), (135323/281474976710656), by norm_num⟩
  | 0 => ⟨((1079388173432497/1125899906842624), (51988091072823/1125899906842624)), (274943/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079388173432497/1125899906842624), (51988091072823/1125899906842624)), (1048824311376476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1032397338580667/1125899906842624), (99680851419025/1125899906842624)), (2210243/1125899906842624), by norm_num⟩
  | 2 => ⟨((1875669384377017/2251799813685248), (91402659407841/562949953421312)), (8889487/2251799813685248), by norm_num⟩
  | 3 => ⟨((1503004166076869/2251799813685248), (304540694710069/1125899906842624)), (4423979/562949953421312), by norm_num⟩
  | 4 => ⟨((419229403260437/1125899906842624), (813084591458551/2251799813685248)), (16597963/1125899906842624), by norm_num⟩
  | 5 => ⟨((37220553186303/4503599627370496), (1211009845567277/4503599627370496)), (24346975/1125899906842624), by norm_num⟩
  | 6 => ⟨((-325330757107475/4503599627370496), (80068318848123/18014398509481984)), (107969227/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1583277307/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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

end Reinmann.XiBand97.Tile003Terms2
