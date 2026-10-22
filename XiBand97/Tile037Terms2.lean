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
namespace Reinmann.XiBand97.Tile037Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33621/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33621/1280))
  have he : value ((69/80), (33621/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1221816555/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-694207060967201/9007199254740992), (444290090056029/9007199254740992)), (299428535/9007199254740992), by norm_num⟩
  | 1 => ⟨((917792639/4294967296), (-293692039/2147483648)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-159041345/536870912), (814287235/4294967296)), (277/2147483648), by norm_num⟩
  | 3 => ⟨((1175883305/4294967296), (-376280601/2147483648)), (515/4294967296), by norm_num⟩
  | 4 => ⟨((-407530099/2147483648), (521635675/4294967296)), (359/4294967296), by norm_num⟩
  | 5 => ⟨((903930685/8589934592), (-144628119/2147483648)), (25/536870912), by norm_num⟩
  | 6 => ⟨((-835409341/17179869184), (33416191/1073741824)), (93/4294967296), by norm_num⟩
  | 7 => ⟨((661784719/34359738368), (-423539905/34359738368)), (297/34359738368), by norm_num⟩
  | 8 => ⟨((-114678553/17179869184), (293575491/68719476736)), (207/68719476736), by norm_num⟩
  | 9 => ⟨((282627967/137438953472), (-90440455/68719476736)), (513/549755813888), by norm_num⟩
  | 10 => ⟨((-626888891/1099511627776), (401206697/1099511627776)), (571/2199023255552), by norm_num⟩
  | 11 => ⟨((632038207/4398046511104), (-809004483/8796093022208)), (289/4398046511104), by norm_num⟩
  | 12 => ⟨((-584127335/17592186044416), (373839451/17592186044416)), (67/4398046511104), by norm_num⟩
  | 13 => ⟨((62290187/8796093022208), (-159462007/35184372088832)), (459/140737488355328), by norm_num⟩
  | 14 => ⟨((-789508891/562949953421312), (31580183/35184372088832)), (183/281474976710656), by norm_num⟩
  | 15 => ⟨((1167457839/4503599627370496), (-186792233/1125899906842624)), (17/140737488355328), by norm_num⟩
  | 16 => ⟨((-404610055/9007199254740992), (517898039/18014398509481984)), (379/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (104708888429/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778272520636455/633825300114114700748351602688), (3963287984369/633825300114114700748351602688)), (46295/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889183260172425/39614081257132168796771975168), (4457754548843/39614081257132168796771975168)), (104189/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944461503539711/1237940039285380274899124224), (2367603468911/1237940039285380274899124224)), (55365/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885294395380007/77371252455336267181195264), (4733905246161/154742504910672534362390528)), (221525/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387247163193645/2417851639229258349412352), (4436653434377/9671406556917033397649408)), (103875/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258294013571231/604462909807314587353088), (3880689373393/604462909807314587353088)), (90925/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886987280876495/75557863725914323419136), (6303529014641/75557863725914323419136)), (295637/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296935071290767/4722366482869645213696), (4725380194637/4722366482869645213696)), (110921/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810307888133379/295147905179352825856), (6493716001221/590295810358705651712)), (152609/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455608057103157/18446744073709551616), (4055812404581/36893488147419103232)), (381801/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56921296623949/288230376151711744), (9117991639595/9223372036854775808)), (429909/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398181652433383/288230376151711744), (2277128698305/288230376151711744)), (107597/288230376151711744), by norm_num⟩
  | 5 => ⟨((596737558873729/72057594037927936), (3979648616535/72057594037927936)), (188565/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489971361868159/36028797018963968), (5958830018475/18014398509481984)), (566775/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487161945363697/9007199254740992), (14859871262475/9007199254740992)), (710361/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111858656584909/2251799813685248), (14804158406801/2251799813685248)), (89151/281474976710656), by norm_num⟩
  | 1 => ⟨((276207530778023/281474976710656), (1379205033205/70368744177664)), (1076945/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083731041573683/1125899906842624), (10895171151009/281474976710656)), (272817/140737488355328), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083731041573683/1125899906842624), (10895171151009/281474976710656)), (1040714264452886537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2082909301747945/2251799813685248), (167793745896553/2251799813685248)), (2185273/562949953421312), by norm_num⟩
  | 2 => ⟨((957091387953327/1125899906842624), (77604401594447/562949953421312)), (8736835/1125899906842624), by norm_num⟩
  | 3 => ⟨((1584393331745377/2251799813685248), (527752095772745/2251799813685248)), (34525213/2251799813685248), by norm_num⟩
  | 4 => ⟨((991109396813657/2251799813685248), (742665397052797/2251799813685248)), (64767989/2251799813685248), by norm_num⟩
  | 5 => ⟨((191289626127019/2251799813685248), (653754964570095/2251799813685248)), (199472633/4503599627370496), by norm_num⟩
  | 6 => ⟨((-694207060967201/9007199254740992), (444290090056029/9007199254740992)), (299428535/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1221816555/16777216)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-624266221/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((435783653295165/9007199254740992), (649582159424179/9007199254740992)), (398681717/18014398509481984), by norm_num⟩
  | 1 => ⟨((-294367805/2147483648), (-877573415/4294967296)), (271/4294967296), by norm_num⟩
  | 2 => ⟨((834006793/4294967296), (1243176355/4294967296)), (193/2147483648), by norm_num⟩
  | 3 => ⟨((-787639725/4294967296), (-1174061279/4294967296)), (367/4294967296), by norm_num⟩
  | 4 => ⟨((557887845/4294967296), (831591521/4294967296)), (131/2147483648), by norm_num⟩
  | 5 => ⟨((-632246115/8589934592), (-471215239/4294967296)), (299/8589934592), by norm_num⟩
  | 6 => ⟨((597096043/17179869184), (890035535/17179869184)), (285/17179869184), by norm_num⟩
  | 7 => ⟨((-483342993/34359738368), (-180118611/8589934592)), (233/34359738368), by norm_num⟩
  | 8 => ⟨((684706909/137438953472), (127578613/17179869184)), (83/34359738368), by norm_num⟩
  | 9 => ⟨((-862187001/549755813888), (-1285181969/549755813888)), (105/137438953472), by norm_num⟩
  | 10 => ⟨((488551943/1099511627776), (728238941/1099511627776)), (15/68719476736), by norm_num⟩
  | 11 => ⟨((-503335231/4398046511104), (-750275013/4398046511104)), (249/4398046511104), by norm_num⟩
  | 12 => ⟨((475352031/17592186044416), (177140765/4398046511104)), (237/17592186044416), by norm_num⟩
  | 13 => ⟨((-414391913/70368744177664), (-308847741/35184372088832)), (415/140737488355328), by norm_num⟩
  | 14 => ⟨((670891827/562949953421312), (1000036047/562949953421312)), (169/281474976710656), by norm_num⟩
  | 15 => ⟨((-126718645/562949953421312), (-755550793/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | 16 => ⟨((89755239/2251799813685248), (535159147/9007199254740992)), (183/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1276417420125/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889099577420353/316912650057057350374175801344), (188706708615/79228162514264337593543950336)), (184697/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59034410690817/1237940039285380274899124224), (424500066091/9903520314283042199192993792)), (51951/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888836308306231/2475880078570760549798248448), (1803675660477/2475880078570760549798248448)), (110407/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221312839005351/19342813113834066795298816), (1803170053479/154742504910672534362390528)), (220839/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548908612314769/9671406556917033397649408), (1689934907687/9671406556917033397649408)), (207063/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258224635975533/604462909807314587353088), (1478156240561/604462909807314587353088)), (181207/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886875774543343/75557863725914323419136), (2400997838131/75557863725914323419136)), (147255/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648426259320705/2361183241434822606848), (1799868536279/4722366482869645213696)), (110463/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620504014550871/590295810358705651712), (2473390344131/590295810358705651712)), (75961/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822295144841443/73786976294838206464), (3089596077729/73786976294838206464)), (47489/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910665433747079/4611686018427387904), (6782915929/18014398509481984)), (427547/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592580469462933/1152921504606846976), (867294571427/288230376151711744)), (213865/576460752303423488), by norm_num⟩
  | 5 => ⟨((596676138703073/72057594037927936), (3031401968443/144115188075855872)), (187235/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489797135367593/36028797018963968), (2269428652297/18014398509481984)), (562119/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486961652638265/9007199254740992), (2829584819219/4503599627370496)), (703373/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223368923111591/4503599627370496), (5637622328741/2251799813685248)), (1408925/4503599627370496), by norm_num⟩
  | 1 => ⟨((552316796825873/562949953421312), (8402759623425/1125899906842624)), (2118859/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167188320155721/2251799813685248), (16591986434689/1125899906842624)), (266233/140737488355328), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167188320155721/2251799813685248), (16591986434689/1125899906842624)), (1015598297656011537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2085267087432277/2251799813685248), (15968541693141/562949953421312)), (4162443/1125899906842624), by norm_num⟩
  | 2 => ⟨((1929238509722443/2251799813685248), (118300656122717/2251799813685248)), (15890717/2251799813685248), by norm_num⟩
  | 3 => ⟨((1646667771984859/2251799813685248), (202709121947977/2251799813685248)), (28898543/2251799813685248), by norm_num⟩
  | 4 => ⟨((1185906378952177/2251799813685248), (296469140969331/2251799813685248)), (47468073/2251799813685248), by norm_num⟩
  | 5 => ⟨((585522736115061/2251799813685248), (624539789551907/4503599627370496)), (124994257/4503599627370496), by norm_num⟩
  | 6 => ⟨((435783653295165/9007199254740992), (649582159424179/9007199254740992)), (398681717/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-624266221/8388608)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-636860425/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1291260956414693/18014398509481984), (-741823727433977/18014398509481984)), (143574181/9007199254740992), by norm_num⟩
  | 1 => ⟨((-889831591/4294967296), (511204327/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((642986025/2147483648), (-738785275/4294967296)), (291/4294967296), by norm_num⟩
  | 3 => ⟨((-1238979099/4294967296), (711788031/4294967296)), (283/4294967296), by norm_num⟩
  | 4 => ⟨((895277549/4294967296), (-257166503/2147483648)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((-1035073977/8589934592), (297322719/4294967296)), (15/536870912), by norm_num⟩
  | 6 => ⟨((498624765/8589934592), (-143228865/4294967296)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((-205887277/8589934592), (473125333/34359738368)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((595090771/68719476736), (-341877025/68719476736)), (283/137438953472), by norm_num⟩
  | 9 => ⟨((-764459359/274877906944), (109794633/68719476736)), (23/34359738368), by norm_num⟩
  | 10 => ⟨((883828697/1099511627776), (-253877845/549755813888)), (215/1099511627776), by norm_num⟩
  | 11 => ⟨((-928943093/4398046511104), (533673711/4398046511104)), (57/1099511627776), by norm_num⟩
  | 12 => ⟨((27968655/549755813888), (-16067869/549755813888)), (111/8796093022208), by norm_num⟩
  | 13 => ⟨((-795961211/70368744177664), (457276207/70368744177664)), (199/70368744177664), by norm_num⟩
  | 14 => ⟨((657321087/281474976710656), (-377628067/281474976710656)), (331/562949953421312), by norm_num⟩
  | 15 => ⟨((-506640615/1125899906842624), (18191425/70368744177664)), (257/2251799813685248), by norm_num⟩
  | 16 => ⟨((732189863/9007199254740992), (-420639849/9007199254740992)), (47/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-169813379001/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444531020365199/158456325028528675187087900672), (-401653120721/316912650057057350374175801344)), (92279/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472254187821609/9903520314283042199192993792), (-903524716229/39614081257132168796771975168)), (207639/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944373365066737/1237940039285380274899124224), (-479875498427/1237940039285380274899124224)), (55157/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770413231739939/154742504910672534362390528), (-479738304591/77371252455336267181195264)), (220641/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387206207112589/2417851639229258349412352), (-899217893653/9671406556917033397649408)), (206865/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629075714469001/302231454903657293676544), (-196631088167/151115727451828646838272)), (90511/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58961156489181/2361183241434822606848), (-638778069593/37778931862957161709568)), (147093/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648381806770879/2361183241434822606848), (-957689673703/4722366482869645213696)), (220663/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620382046097653/590295810358705651712), (-1316047966437/590295810358705651712)), (303449/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822143097837073/73786976294838206464), (-821948906251/36893488147419103232)), (379369/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910580191204173/4611686018427387904), (-461947120027/2305843009213693952)), (106717/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796205346420345/576460752303423488), (-1845794866143/1152921504606846976)), (213483/576460752303423488), by norm_num⟩
  | 5 => ⟨((298301129531819/36028797018963968), (-6300119357/562949953421312)), (373707/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489577082599021/36028797018963968), (-150923317273/2251799813685248)), (280391/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486689352604249/9007199254740992), (-3010655077783/9007199254740992)), (701367/9007199254740992), by norm_num⟩
  | 2 => ⟨((555708145399191/1125899906842624), (-5997940444237/4503599627370496)), (1403909/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208483184633753/2251799813685248), (-8938710104403/2251799813685248)), (2108823/2251799813685248), by norm_num⟩
  | 0 => ⟨((33839086509987/35184372088832), (-8822977717489/1125899906842624)), (4229597/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((33839086509987/35184372088832), (-8822977717489/1125899906842624)), (16134632119185637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082756974023621/2251799813685248), (-8485628377963/562949953421312)), (8202045/2251799813685248), by norm_num⟩
  | 2 => ⟨((1925892564811583/2251799813685248), (-7848611397765/281474976710656)), (7709951/1125899906842624), by norm_num⟩
  | 3 => ⟨((1645403691670503/2251799813685248), (-53701336124771/1125899906842624)), (27236235/2251799813685248), by norm_num⟩
  | 4 => ⟨((1197183674220427/2251799813685248), (-39239889874015/562949953421312)), (21200751/1125899906842624), by norm_num⟩
  | 5 => ⟨((1251099176704717/4503599627370496), (-333794187208825/4503599627370496)), (101994339/4503599627370496), by norm_num⟩
  | 6 => ⟨((1291260956414693/18014398509481984), (-741823727433977/18014398509481984)), (143574181/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-636860425/8388608)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-40548345/524288)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-515048409460867/18014398509481984), (-1324727456894539/18014398509481984)), (250936191/18014398509481984), by norm_num⟩
  | 1 => ⟨((361568597/4294967296), (929970541/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-532308335/4294967296), (-1369120755/4294967296)), (33/536870912), by norm_num⟩
  | 3 => ⟨((522449803/4294967296), (1343764173/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-384580391/4294967296), (-494578951/2147483648)), (195/4294967296), by norm_num⟩
  | 5 => ⟨((226474699/4294967296), (1165006033/8589934592)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-444560621/17179869184), (-1143429725/17179869184)), (229/17179869184), by norm_num⟩
  | 7 => ⟨((373994749/34359738368), (480965579/17179869184)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((-275301179/68719476736), (-708086899/68719476736)), (9/4294967296), by norm_num⟩
  | 9 => ⟨((180135005/137438953472), (463315259/137438953472)), (95/137438953472), by norm_num⟩
  | 10 => ⟨((-53039653/137438953472), (-1091362807/1099511627776)), (113/549755813888), by norm_num⟩
  | 11 => ⟨((454318609/4398046511104), (1168527705/4398046511104)), (61/1099511627776), by norm_num⟩
  | 12 => ⟨((-222952237/8796093022208), (-573443087/8796093022208)), (241/17592186044416), by norm_num⟩
  | 13 => ⟨((403981081/70368744177664), (259764335/17592186044416)), (55/17592186044416), by norm_num⟩
  | 14 => ⟨((-339856469/281474976710656), (-874125981/281474976710656)), (93/140737488355328), by norm_num⟩
  | 15 => ⟨((266849769/1125899906842624), (1372698993/2251799813685248)), (295/2251799813685248), by norm_num⟩
  | 16 => ⟨((-392861431/9007199254740992), (-1010457105/9007199254740992)), (219/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2529159524423/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444511949029799/158456325028528675187087900672), (-1495416007229/316912650057057350374175801344)), (92495/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888930702885861/39614081257132168796771975168), (-1681969767037/19807040628566084398385987584)), (26019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944327499740275/1237940039285380274899124224), (-446657414927/309485009821345068724781056)), (110603/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442580289804271/38685626227668133590597632), (-3572217433055/154742504910672534362390528)), (110627/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548738147516997/9671406556917033397649408), (-52310112287/151115727451828646838272)), (103739/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258075220508685/604462909807314587353088), (-1464130010669/302231454903657293676544)), (90799/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943316244879701/37778931862957161709568), (-4756349113897/75557863725914323419136)), (36899/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648334815762591/2361183241434822606848), (-1782724210671/2361183241434822606848)), (27685/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620251857545605/590295810358705651712), (-2449773167745/295147905179352825856)), (152337/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821978919525073/73786976294838206464), (-3060008886027/36893488147419103232)), (190527/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113810856370643/576460752303423488), (-859869197691/1152921504606846976)), (214487/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199027692887591/144115188075855872), (-6871377186249/1152921504606846976)), (53667/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193036241851181/144115188075855872), (-6003940689747/144115188075855872)), (188039/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489319146805005/36028797018963968), (-8988905062223/36028797018963968)), (141233/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486357313380191/9007199254740992), (-1400802744759/1125899906842624)), (353797/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222139815921095/4503599627370496), (-2790489987419/562949953421312)), (709745/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207372914994819/2251799813685248), (-33264283069361/2251799813685248)), (133751/281474976710656), by norm_num⟩
  | 0 => ⟨((2163200076042813/2251799813685248), (-65646450102403/2251799813685248)), (2161677/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163200076042813/2251799813685248), (-65646450102403/2251799813685248)), (8246143349654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076172617196097/2251799813685248), (-31531756284555/562949953421312)), (2139643/1125899906842624), by norm_num⟩
  | 2 => ⟨((1907178730464609/2251799813685248), (-232579711827775/2251799813685248)), (4185217/1125899906842624), by norm_num⟩
  | 3 => ⟨((1591277060156807/2251799813685248), (-393970260446537/2251799813685248)), (248561/35184372088832), by norm_num⟩
  | 4 => ⟨((1055577898896311/2251799813685248), (-278406559065559/1125899906842624)), (14024837/1125899906842624), by norm_num⟩
  | 5 => ⟨((44642281655541/281474976710656), (-261017705811439/1125899906842624)), (10042421/562949953421312), by norm_num⟩
  | 6 => ⟨((-515048409460867/18014398509481984), (-1324727456894539/18014398509481984)), (250936191/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-40548345/524288)), (1/16777216), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-165018853/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-336273359306327/4503599627370496), (6237002400089/562949953421312)), (115398581/4503599627370496), by norm_num⟩
  | 1 => ⟨((960717159/4294967296), (-71275289/2147483648)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((-359756425/1073741824), (53380421/1073741824)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((1436978577/4294967296), (-213217933/4294967296)), (125/1073741824), by norm_num⟩
  | 4 => ⟨((-1076200775/4294967296), (159685961/4294967296)), (47/536870912), by norm_num⟩
  | 5 => ⟨((644801879/4294967296), (-191350555/8589934592)), (113/2147483648), by norm_num⟩
  | 6 => ⟨((-1287769199/17179869184), (23884793/2147483648)), (227/8589934592), by norm_num⟩
  | 7 => ⟨((1102231929/34359738368), (-81774223/17179869184)), (195/17179869184), by norm_num⟩
  | 8 => ⟨((-825497941/68719476736), (244973679/137438953472)), (293/68719476736), by norm_num⟩
  | 9 => ⟨((34346817/8589934592), (-163083457/274877906944)), (391/274877906944), by norm_num⟩
  | 10 => ⟨((-1317041513/1099511627776), (97710875/549755813888)), (235/549755813888), by norm_num⟩
  | 11 => ⟨((717364321/2199023255552), (-212884089/4398046511104)), (257/2199023255552), by norm_num⟩
  | 12 => ⟨((-89542977/1099511627776), (212581245/17592186044416)), (129/4398046511104), by norm_num⟩
  | 13 => ⟨((660299781/35184372088832), (-195949691/70368744177664)), (239/35184372088832), by norm_num⟩
  | 14 => ⟨((-70645763/17592186044416), (167717947/281474976710656)), (411/281474976710656), by norm_num⟩
  | 15 => ⟨((225744845/281474976710656), (-267966969/2251799813685248)), (659/2251799813685248), by norm_num⟩
  | 16 => ⟨((-338135559/2251799813685248), (50172331/2251799813685248)), (31/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (121887329273/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777973041373459/633825300114114700748351602688), (4612035086851/633825300114114700748351602688)), (46327/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888846258288237/39614081257132168796771975168), (5187350408241/39614081257132168796771975168)), (208531/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888564813957779/2475880078570760549798248448), (2755052079591/1237940039285380274899124224)), (221631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442557613303889/38685626227668133590597632), (5508466793257/154742504910672534362390528)), (55427/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774326279043819/4835703278458516698824704), (5162448302013/9671406556917033397649408)), (51983/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257999777717599/604462909807314587353088), (4515403379415/604462909807314587353088)), (182021/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886508861236671/75557863725914323419136), (7334271000373/75557863725914323419136)), (289/73786976294838206464), by norm_num⟩
  | 10 => ⟨((648288003241081/2361183241434822606848), (5497852113733/4722366482869645213696)), (111043/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202515207089609/73786976294838206464), (7554915281861/590295810358705651712)), (305583/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910906986230663/36893488147419103232), (589793753503/4611686018427387904)), (382303/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56899535085357/288230376151711744), (662921525135/576460752303423488)), (215269/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796014602690669/576460752303423488), (10594822809581/1152921504606846976)), (53887/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192863729916429/144115188075855872), (9257068291895/144115188075855872)), (188919/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489051975759177/36028797018963968), (13858824439177/36028797018963968)), (568015/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486008710806807/9007199254740992), (17276726112001/9007199254740992)), (712225/9007199254740992), by norm_num⟩
  | 2 => ⟨((555349740194965/1125899906842624), (8603316861543/1125899906842624)), (357771/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103076718245863/1125899906842624), (12817560096225/562949953421312)), (270407/281474976710656), by norm_num⟩
  | 0 => ⟨((135020868006525/140737488355328), (25286663707555/562949953421312)), (2196663/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135020868006525/140737488355328), (25286663707555/562949953421312)), (8379604343894576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517009975088293/562949953421312), (97038175760621/1125899906842624)), (2206107/562949953421312), by norm_num⟩
  | 2 => ⟨((1882548960822277/2251799813685248), (356477193240409/2251799813685248)), (8864857/1125899906842624), by norm_num⟩
  | 3 => ⟨((1517414905102255/2251799813685248), (18626371825247/70368744177664)), (35258281/2251799813685248), by norm_num⟩
  | 4 => ⟨((432382943981667/1125899906842624), (100413665775557/281474976710656)), (33092163/1125899906842624), by norm_num⟩
  | 5 => ⟨((91050871214155/4503599627370496), (38562181380565/140737488355328)), (196110571/4503599627370496), by norm_num⟩
  | 6 => ⟨((-336273359306327/4503599627370496), (6237002400089/562949953421312)), (115398581/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-165018853/2097152)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-83853221/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-92225257016679/9007199254740992), (645335274597425/9007199254740992)), (439745943/18014398509481984), by norm_num⟩
  | 1 => ⟨((267774453/8589934592), (-936859953/4294967296)), (641/8589934592), by norm_num⟩
  | 2 => ⟨((-203811333/4294967296), (713072787/2147483648)), (245/2147483648), by norm_num⟩
  | 3 => ⟨((206836059/4294967296), (-1447310733/4294967296)), (499/4294967296), by norm_num⟩
  | 4 => ⟨((-19678657/536870912), (275398125/1073741824)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((191718761/8589934592), (-670764617/4294967296)), (467/8589934592), by norm_num⟩
  | 6 => ⟨((-194564023/17179869184), (680719309/8589934592)), (119/4294967296), by norm_num⟩
  | 7 => ⟨((21155519/4294967296), (-592132917/17179869184)), (13/1073741824), by norm_num⟩
  | 8 => ⟨((-257633809/137438953472), (56336311/4294967296)), (635/137438953472), by norm_num⟩
  | 9 => ⟨((174304869/274877906944), (-1219677603/274877906944)), (431/274877906944), by norm_num⟩
  | 10 => ⟨((-106135017/549755813888), (371333583/274877906944)), (527/1099511627776), by norm_num⟩
  | 11 => ⟨((235003957/4398046511104), (-1644412255/4398046511104)), (585/4398046511104), by norm_num⟩
  | 12 => ⟨((-238491607/17592186044416), (1668816669/17592186044416)), (149/4398046511104), by norm_num⟩
  | 13 => ⟨((111706623/35184372088832), (-1563307629/70368744177664)), (35/4398046511104), by norm_num⟩
  | 14 => ⟨((-6073095/8796093022208), (679932165/140737488355328)), (489/281474976710656), by norm_num⟩
  | 15 => ⟨((157778551/1125899906842624), (-1104036657/1125899906842624)), (399/1125899906842624), by norm_num⟩
  | 16 => ⟨((-240180169/9007199254740992), (1680632187/9007199254740992)), (305/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (2231042604511/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777915899908675/633825300114114700748351602688), (164870044845/39614081257132168796771975168)), (23115/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888782412475143/39614081257132168796771975168), (1483491715335/19807040628566084398385987584)), (52017/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888497560868167/2475880078570760549798248448), (787893822829/618970019642690137449562112)), (221111/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885081927723889/77371252455336267181195264), (1575312744159/77371252455336267181195264)), (221155/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548590818420195/9671406556917033397649408), (1476351288969/4835703278458516698824704)), (207379/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257946450641577/604462909807314587353088), (1291303165079/302231454903657293676544)), (181503/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471605876705907/18889465931478580854784), (2097422660475/37778931862957161709568)), (295029/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296513128709121/4722366482869645213696), (1572240551419/2361183241434822606848)), (55337/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202504630834403/73786976294838206464), (4320977132869/590295810358705651712)), (304477/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821710976033607/73786976294838206464), (5397197568061/73786976294838206464)), (190391/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820673048319949/9223372036854775808), (3033159451087/4611686018427387904)), (214317/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795960933208131/576460752303423488), (378713443051/72057594037927936)), (214477/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192775121601927/144115188075855872), (5294230533697/144115188075855872)), (375695/144115188075855872), by norm_num⟩
  | 4 => ⟨((372232413664629/9007199254740992), (7925853242159/36028797018963968)), (564263/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485874265305069/9007199254740992), (9880255766849/9007199254740992)), (22081/281474976710656), by norm_num⟩
  | 2 => ⟨((555296280511077/1125899906842624), (9839766813615/2251799813685248)), (708491/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205969208677665/2251799813685248), (29317569840555/2251799813685248)), (1067499/1125899906842624), by norm_num⟩
  | 0 => ⟨((540126244552707/562949953421312), (57832490982667/2251799813685248)), (4308281/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540126244552707/562949953421312), (57832490982667/2251799813685248)), (16434787758834075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071426214494081/2251799813685248), (55487785331103/1125899906842624)), (4244259/1125899906842624), by norm_num⟩
  | 2 => ⟨((1900031680794657/2251799813685248), (204172417850875/2251799813685248)), (16453823/2251799813685248), by norm_num⟩
  | 3 => ⟨((396175760176953/562949953421312), (43069332795865/281474976710656)), (30750693/2251799813685248), by norm_num⟩
  | 4 => ⟨((531256330453767/1125899906842624), (484960357332397/2251799813685248)), (52692085/2251799813685248), by norm_num⟩
  | 5 => ⟨((793806448489003/4503599627370496), (915314969958405/4503599627370496)), (72421697/2251799813685248), by norm_num⟩
  | 6 => ⟨((-92225257016679/9007199254740992), (645335274597425/9007199254740992)), (439745943/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-83853221/1048576)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile037Terms2
