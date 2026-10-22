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
namespace Reinmann.XiBand97.Tile040Terms2
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
  | 0 => ⟨((-20060163/8388608), (-1260846655/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((799412351282635/9007199254740992), (100320760856745/4503599627370496)), (32004349/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1056881747/4294967296), (-66315701/1073741824)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((732574603/2147483648), (367732329/4294967296)), (15/268435456), by norm_num⟩
  | 3 => ⟨((-338521347/1073741824), (-84964209/1073741824)), (7/134217728), by norm_num⟩
  | 4 => ⟨((938580469/4294967296), (29446351/536870912)), (157/4294967296), by norm_num⟩
  | 5 => ⟨((-1040919049/8589934592), (-130628193/4294967296)), (11/536870912), by norm_num⟩
  | 6 => ⟨((30062921/536870912), (120726085/8589934592)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((-1524152973/68719476736), (-382541465/68719476736)), (131/34359738368), by norm_num⟩
  | 8 => ⟨((2063403/268435456), (132578769/68719476736)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((-650919013/274877906944), (-163371733/274877906944)), (57/137438953472), by norm_num⟩
  | 10 => ⟨((360946143/549755813888), (90592525/549755813888)), (255/2199023255552), by norm_num⟩
  | 11 => ⟨((-1455643935/8796093022208), (-365346637/8796093022208)), (259/8796093022208), by norm_num⟩
  | 12 => ⟨((1345300653/35184372088832), (337651989/35184372088832)), (121/17592186044416), by norm_num⟩
  | 13 => ⟨((-1147681667/140737488355328), (-288052337/140737488355328)), (209/140737488355328), by norm_num⟩
  | 14 => ⟨((14205577/8796093022208), (228185903/562949953421312)), (167/562949953421312), by norm_num⟩
  | 15 => ⟨((-168047883/562949953421312), (-168710843/2251799813685248)), (249/4503599627370496), by norm_num⟩
  | 16 => ⟨((465927665/9007199254740992), (116941445/9007199254740992)), (175/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (320320930605/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222285107576627/79228162514264337593543950336), (23680312971/39614081257132168796771975168)), (92237/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889193105465291/39614081257132168796771975168), (213078674843/19807040628566084398385987584)), (207539/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944467039800929/1237940039285380274899124224), (452681782193/2475880078570760549798248448)), (55129/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770600551005585/154742504910672534362390528), (452557636097/154742504910672534362390528)), (110261/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387250102043519/2417851639229258349412352), (212070463323/4835703278458516698824704)), (206747/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258305029111331/604462909807314587353088), (185495753839/302231454903657293676544)), (90455/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887006547782381/75557863725914323419136), (602614183913/75557863725914323419136)), (293991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648475358005219/2361183241434822606848), (225872306817/2361183241434822606848)), (220505/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810319613241785/295147905179352825856), (155199504823/147573952589676412928)), (75803/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822464445077031/73786976294838206464), (775471663475/73786976294838206464)), (189521/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821521721753069/9223372036854775808), (27240099175/288230376151711744)), (106615/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592771811859941/1152921504606846976), (217695257207/288230376151711744)), (213253/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193520249471679/144115188075855872), (190229936013/36028797018963968)), (373247/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490050184193171/36028797018963968), (1139355441245/36028797018963968)), (69997/4503599627370496), by norm_num⟩
  | 3 => ⟨((371819965749343/2251799813685248), (1420659043381/9007199254740992)), (700159/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224011004152029/4503599627370496), (2830740445381/4503599627370496)), (175111/562949953421312), by norm_num⟩
  | 1 => ⟨((2210244328415587/2251799813685248), (4219764770199/2251799813685248)), (525693/562949953421312), by norm_num⟩
  | 0 => ⟨((1084598948734949/1125899906842624), (2083683276089/562949953421312)), (4211411/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084598948734949/1125899906842624), (2083683276089/562949953421312)), (16065258034712981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089595186044193/2251799813685248), (8028993259553/1125899906842624)), (2036257/562949953421312), by norm_num⟩
  | 2 => ⟨((1938960184681101/2251799813685248), (3725319089641/281474976710656)), (15232797/2251799813685248), by norm_num⟩
  | 3 => ⟨((834594261618385/1125899906842624), (51324245405101/2251799813685248)), (13318131/1125899906842624), by norm_num⟩
  | 4 => ⟨((1236147250311491/2251799813685248), (76090104345267/2251799813685248)), (10175867/562949953421312), by norm_num⟩
  | 5 => ⟨((1352047647594455/4503599627370496), (167081589918745/4503599627370496)), (23719965/1125899906842624), by norm_num⟩
  | 6 => ⟨((799412351282635/9007199254740992), (100320760856745/4503599627370496)), (32004349/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1260846655/16777216)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-644207981/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((134991956298781/9007199254740992), (-770481372945553/9007199254740992)), (478243103/18014398509481984), by norm_num⟩
  | 1 => ⟨((-91185811/2147483648), (260226501/1073741824)), (325/4294967296), by norm_num⟩
  | 2 => ⟨((258348857/4294967296), (-737277195/2147483648)), (463/4294967296), by norm_num⟩
  | 3 => ⟨((-121992905/2147483648), (1392575725/4294967296)), (439/4294967296), by norm_num⟩
  | 4 => ⟨((172815963/4294967296), (-61647877/268435456)), (313/4294967296), by norm_num⟩
  | 5 => ⟨((-195849797/8589934592), (558917081/4294967296)), (89/2147483648), by norm_num⟩
  | 6 => ⟨((184961419/17179869184), (-1055687555/17179869184)), (169/8589934592), by norm_num⟩
  | 7 => ⟨((-299448663/68719476736), (1709136039/68719476736)), (549/68719476736), by norm_num⟩
  | 8 => ⟨((212100487/137438953472), (-605293379/68719476736)), (391/137438953472), by norm_num⟩
  | 9 => ⟨((-267078191/549755813888), (1524378025/549755813888)), (495/549755813888), by norm_num⟩
  | 10 => ⟨((151337899/1099511627776), (-1727555265/2199023255552)), (563/2199023255552), by norm_num⟩
  | 11 => ⟨((-311834585/8796093022208), (1779830047/8796093022208)), (291/4398046511104), by norm_num⟩
  | 12 => ⟨((294497969/35184372088832), (-1680879413/35184372088832)), (69/4398046511104), by norm_num⟩
  | 13 => ⟨((-128365473/70368744177664), (1465319995/140737488355328)), (483/140737488355328), by norm_num⟩
  | 14 => ⟨((51955253/140737488355328), (-593080595/281474976710656)), (393/562949953421312), by norm_num⟩
  | 15 => ⟨((-314027341/4503599627370496), (896172723/2251799813685248)), (149/1125899906842624), by norm_num⟩
  | 16 => ⟨((222426613/18014398509481984), (-1269524259/18014398509481984)), (53/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-910103531317/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889098946209345/316912650057057350374175801344), (-1076404249493/316912650057057350374175801344)), (23103/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889099652017831/39614081257132168796771975168), (-2421394307169/39614081257132168796771975168)), (103977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472208658120529/618970019642690137449562112), (-1286045040575/1237940039285380274899124224)), (220983/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770500932145639/154742504910672534362390528), (-1285684409329/77371252455336267181195264)), (221019/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548906833166365/9671406556917033397649408), (-2409892181499/9671406556917033397649408)), (207243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258222968819103/604462909807314587353088), (-1053944930077/302231454903657293676544)), (1417/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1886872858609167/75557863725914323419136), (-213992860039/4722366482869645213696)), (294805/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296850150934251/4722366482869645213696), (-160416192263/295147905179352825856)), (110583/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620500465594767/590295810358705651712), (-3527117601247/590295810358705651712)), (76051/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822290269256073/73786976294838206464), (-4405841058575/73786976294838206464)), (380407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910662389675325/4611686018427387904), (-4952372516945/9223372036854775808)), (214083/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592573629007257/1152921504606846976), (-2473564521187/576460752303423488)), (214213/576460752303423488), by norm_num⟩
  | 5 => ⟨((149168180977351/18014398509481984), (-4322845690645/144115188075855872)), (375167/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489785208005399/36028797018963968), (-6472500794189/36028797018963968)), (563337/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486943810331117/9007199254740992), (-2017517493451/2251799813685248)), (705203/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223324487492809/4503599627370496), (-8039310883221/2251799813685248)), (1413503/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104589412403623/1125899906842624), (-23964660677799/2251799813685248)), (266003/281474976710656), by norm_num⟩
  | 0 => ⟨((1083462882232787/1125899906842624), (-23659682848987/1125899906842624)), (4287269/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083462882232787/1125899906842624), (-23659682848987/1125899906842624)), (16354633339888762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084256388072815/2251799813685248), (-91071641507331/2251799813685248)), (526971/140737488355328), by norm_num⟩
  | 2 => ⟨((962747803109453/1125899906842624), (-21073881593551/281474976710656)), (8145199/1125899906842624), by norm_num⟩
  | 3 => ⟨((25528956632697/35184372088832), (-36040207631025/281474976710656)), (118355/8796093022208), by norm_num⟩
  | 4 => ⟨((1148568786282355/2251799813685248), (-13074965432421/70368744177664)), (51727287/2251799813685248), by norm_num⟩
  | 5 => ⟨((254052917027559/1125899906842624), (-213411470573981/1125899906842624)), (17997823/562949953421312), by norm_num⟩
  | 6 => ⟨((134991956298781/9007199254740992), (-770481372945553/9007199254740992)), (478243103/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-644207981/8388608)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1314408997/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1460975401053423/18014398509481984), (-288458277159277/18014398509481984)), (511004237/18014398509481984), by norm_num⟩
  | 1 => ⟨((1006784925/4294967296), (99390943/2147483648)), (177/2147483648), by norm_num⟩
  | 2 => ⟨((-1454991357/4294967296), (-287276775/4294967296)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((175227747/536870912), (69194723/1073741824)), (249/2147483648), by norm_num⟩
  | 4 => ⟨((-506473331/2147483648), (-199998473/4294967296)), (181/2147483648), by norm_num⟩
  | 5 => ⟨((585558485/4294967296), (231227975/8589934592)), (105/2147483648), by norm_num⟩
  | 6 => ⟨((-1128321139/17179869184), (-111389135/8589934592)), (407/17179869184), by norm_num⟩
  | 7 => ⟨((465895365/17179869184), (183974863/34359738368)), (169/17179869184), by norm_num⟩
  | 8 => ⟨((-1346610805/137438953472), (-132938937/68719476736)), (491/137438953472), by norm_num⟩
  | 9 => ⟨((864934631/274877906944), (42693661/68719476736)), (633/549755813888), by norm_num⟩
  | 10 => ⟨((-249998263/274877906944), (-197440883/1099511627776)), (23/68719476736), by norm_num⟩
  | 11 => ⟨((1051036973/4398046511104), (103759555/2199023255552)), (97/1099511627776), by norm_num⟩
  | 12 => ⟨((-1012629195/17592186044416), (-12495987/1099511627776)), (47/2199023255552), by norm_num⟩
  | 13 => ⟨((450288435/35184372088832), (22226491/8796093022208)), (21/4398046511104), by norm_num⟩
  | 14 => ⟨((-1487429687/562949953421312), (-293681471/562949953421312)), (279/281474976710656), by norm_num⟩
  | 15 => ⟨((35826873/70368744177664), (226359635/2251799813685248)), (27/140737488355328), by norm_num⟩
  | 16 => ⟨((-1656847711/18014398509481984), (-81782937/4503599627370496)), (627/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-1919175305351/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778113382139467/633825300114114700748351602688), (-4539352288609/633825300114114700748351602688)), (92647/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889004123985405/39614081257132168796771975168), (-5105639722925/39614081257132168796771975168)), (104257/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472183132253661/618970019642690137449562112), (-5423359772867/2475880078570760549798248448)), (55403/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885199074407577/77371252455336267181195264), (-2710902368745/77371252455336267181195264)), (221687/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774404876003689/4835703278458516698824704), (-5081290057437/9671406556917033397649408)), (207911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258137301656957/604462909807314587353088), (-277779831205/37778931862957161709568)), (91001/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886732298674445/75557863725914323419136), (-7219179861139/75557863725914323419136)), (147951/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296743550391981/4722366482869645213696), (-1352919232227/1180591620717411303424)), (111029/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202543996741015/73786976294838206464), (-1859164214699/147573952589676412928)), (152771/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911050892616063/36893488147419103232), (-9289225370929/73786976294838206464)), (191123/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821108796552543/9223372036854775808), (-652582112559/576460752303423488)), (215233/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796176367086467/576460752303423488), (-10429989403341/1152921504606846976)), (431015/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149143331704075/18014398509481984), (-9113509765505/144115188075855872)), (377757/144115188075855872), by norm_num⟩
  | 4 => ⟨((744738015671281/18014398509481984), (-6822412603857/18014398509481984)), (283937/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486538198237963/9007199254740992), (-17011563138741/9007199254740992)), (712013/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111228085673915/2251799813685248), (-16944962032489/2251799813685248)), (715275/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103867389279349/1125899906842624), (-25251296028037/1125899906842624)), (1081091/1125899906842624), by norm_num⟩
  | 0 => ⟨((270434787825263/281474976710656), (-24920071872869/562949953421312)), (2195035/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((270434787825263/281474976710656), (-24920071872869/562949953421312)), (8373394016746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129638028259929/140737488355328), (-95770564449959/1125899906842624)), (551527/140737488355328), by norm_num⟩
  | 2 => ⟨((1894330336570167/2251799813685248), (-352869936382181/2251799813685248)), (8879099/1125899906842624), by norm_num⟩
  | 3 => ⟨((1538311803294191/2251799813685248), (-593704841158483/2251799813685248)), (35443851/2251799813685248), by norm_num⟩
  | 4 => ⟨((55897446830633/140737488355328), (-811176161643165/2251799813685248)), (33558437/1125899906842624), by norm_num⟩
  | 5 => ⟨((31501806208217/1125899906842624), (-1288716372463505/4503599627370496)), (203339925/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1460975401053423/18014398509481984), (-288458277159277/18014398509481984)), (511004237/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1314408997/16777216)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1338996299/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-420322049734837/18014398509481984), (1357758105718809/18014398509481984)), (247800175/9007199254740992), by norm_num⟩
  | 1 => ⟨((73767461/1073741824), (-953158353/4294967296)), (175/2147483648), by norm_num⟩
  | 2 => ⟨((-434407575/4294967296), (21925911/67108864)), (517/4294967296), by norm_num⟩
  | 3 => ⟨((426362199/4294967296), (-1377269483/4294967296)), (255/2147483648), by norm_num⟩
  | 4 => ⟨((-313849369/4294967296), (63363843/268435456)), (189/2147483648), by norm_num⟩
  | 5 => ⟨((184822063/4294967296), (-1194054203/8589934592)), (447/8589934592), by norm_num⟩
  | 6 => ⟨((-362798191/17179869184), (1171939913/17179869184)), (55/2147483648), by norm_num⟩
  | 7 => ⟨((152605305/17179869184), (-985915875/34359738368)), (93/8589934592), by norm_num⟩
  | 8 => ⟨((-28083563/8589934592), (725742283/68719476736)), (275/68719476736), by norm_num⟩
  | 9 => ⟨((294010089/274877906944), (-237433763/68719476736)), (361/274877906944), by norm_num⟩
  | 10 => ⟨((-346277907/1099511627776), (1118574763/1099511627776)), (427/1099511627776), by norm_num⟩
  | 11 => ⟨((370761515/4398046511104), (-1197663685/4398046511104)), (459/4398046511104), by norm_num⟩
  | 12 => ⟨((-181947443/8796093022208), (587741273/8796093022208)), (113/4398046511104), by norm_num⟩
  | 13 => ⟨((164840967/35184372088832), (-266241279/17592186044416)), (411/70368744177664), by norm_num⟩
  | 14 => ⟨((-277350953/281474976710656), (895921371/281474976710656)), (87/70368744177664), by norm_num⟩
  | 15 => ⟨((217771455/1125899906842624), (-351731441/562949953421312)), (549/2251799813685248), by norm_num⟩
  | 16 => ⟨((-80151845/2251799813685248), (1035651765/9007199254740992)), (203/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (304649966451/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889024069254649/316912650057057350374175801344), (2882085891591/633825300114114700748351602688)), (184967/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944465553463333/19807040628566084398385987584), (3241627913409/39614081257132168796771975168)), (208125/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888655453877503/2475880078570760549798248448), (1721668489743/1237940039285380274899124224)), (221175/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885160820913019/77371252455336267181195264), (3442333067663/154742504910672534362390528)), (221223/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548738629914769/9671406556917033397649408), (3226120934767/9671406556917033397649408)), (207447/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258075672532309/604462909807314587353088), (2821789884305/604462909807314587353088)), (181567/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886633280352383/75557863725914323419136), (2291705374575/37778931862957161709568)), (73785/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324167568365467/1180591620717411303424), (3435810788043/4722366482869645213696)), (221439/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810126409857945/295147905179352825856), (4721402036321/590295810358705651712)), (304613/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227747530164513/9223372036854775808), (2948749256587/36893488147419103232)), (380969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820975352380893/9223372036854775808), (3314420429641/4611686018427387904)), (428869/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592223397401313/1152921504606846976), (1655385283733/288230376151711744)), (214609/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193038093084941/144115188075855872), (5785645214971/144115188075855872)), (375959/144115188075855872), by norm_num⟩
  | 4 => ⟨((744661189786823/18014398509481984), (8662083527663/36028797018963968)), (141181/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486362148777033/9007199254740992), (5399490966017/4503599627370496)), (176821/2251799813685248), by norm_num⟩
  | 2 => ⟨((555537964094519/1125899906842624), (5378074083957/1125899906842624)), (1418713/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103698426123953/1125899906842624), (16027487114013/1125899906842624)), (1069231/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163271172603177/2251799813685248), (63260249657695/2251799813685248)), (2159339/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163271172603177/2251799813685248), (63260249657695/2251799813685248)), (8237224583152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038222909206337/1125899906842624), (121546394687907/2251799813685248)), (4270217/1125899906842624), by norm_num⟩
  | 2 => ⟨((954093184622329/1125899906842624), (224162469024983/2251799813685248)), (16672715/2251799813685248), by norm_num⟩
  | 3 => ⟨((1594691670826147/2251799813685248), (379912783800851/2251799813685248)), (1973535/140737488355328), by norm_num⟩
  | 4 => ⟨((66577515770077/140737488355328), (269048673103885/1125899906842624)), (27689503/1125899906842624), by norm_num⟩
  | 5 => ⟨((375338889377711/2251799813685248), (31819155801735/140737488355328)), (157724935/4503599627370496), by norm_num⟩
  | 6 => ⟨((-420322049734837/18014398509481984), (1357758105718809/18014398509481984)), (247800175/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1338996299/16777216)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1362322145/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((602862573026531/9007199254740992), (314379162300585/9007199254740992)), (63745119/4503599627370496), by norm_num⟩
  | 1 => ⟨((-861174997/4294967296), (-224541617/2147483648)), (23/536870912), by norm_num⟩
  | 2 => ⟨((644962433/2147483648), (672666569/4294967296)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((-1288089851/4294967296), (-335854825/2147483648)), (279/4294967296), by norm_num⟩
  | 4 => ⟨((964693085/4294967296), (503065569/4294967296)), (211/4294967296), by norm_num⟩
  | 5 => ⟨((-288996221/2147483648), (-9419061/134217728)), (255/8589934592), by norm_num⟩
  | 6 => ⟨((144292551/2147483648), (601962347/17179869184)), (257/17179869184), by norm_num⟩
  | 7 => ⟨((-494013545/17179869184), (-515233723/34359738368)), (111/17179869184), by norm_num⟩
  | 8 => ⟨((46247885/4294967296), (385875573/68719476736)), (21/8589934592), by norm_num⟩
  | 9 => ⟨((-985218003/274877906944), (-32110553/17179869184)), (225/274877906944), by norm_num⟩
  | 10 => ⟨((1180579747/1099511627776), (4809731/8589934592)), (17/68719476736), by norm_num⟩
  | 11 => ⟨((-321518259/1099511627776), (-335328963/2199023255552)), (299/4398046511104), by norm_num⟩
  | 12 => ⟨((321060875/4398046511104), (669703865/17592186044416)), (301/17592186044416), by norm_num⟩
  | 13 => ⟨((-1183769139/70368744177664), (-154327191/17592186044416)), (35/8796093022208), by norm_num⟩
  | 14 => ⟨((1013215833/281474976710656), (264184541/140737488355328)), (241/281474976710656), by norm_num⟩
  | 15 => ⟨((-404709783/562949953421312), (-211046975/562949953421312)), (97/562949953421312), by norm_num⟩
  | 16 => ⟨((606201079/4503599627370496), (316120117/4503599627370496)), (293/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (156535321073/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777984152633567/633825300114114700748351602688), (370191469771/316912650057057350374175801344)), (92273/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888859368799793/39614081257132168796771975168), (416372569463/19807040628566084398385987584)), (25953/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888579558353423/2475880078570760549798248448), (110569828741/309485009821345068724781056)), (55153/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770246112933723/154742504910672534362390528), (884296543615/154742504910672534362390528)), (13789/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548668210831397/9671406556917033397649408), (828749651599/9671406556917033397649408)), (101/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((314503611189397/151115727451828646838272), (90609713677/75557863725914323419136)), (181005/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471633628437219/18889465931478580854784), (1177404845571/75557863725914323419136)), (294157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296596835273255/4722366482869645213696), (220649410149/1180591620717411303424)), (6895/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810076437818283/295147905179352825856), (606415626357/295147905179352825856)), (303415/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910928429534583/36893488147419103232), (757464580955/36893488147419103232)), (379321/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113802416995527/576460752303423488), (212846321291/1152921504606846976)), (53351/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398022341773371/288230376151711744), (850433359471/576460752303423488)), (426899/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192923790325687/144115188075855872), (743059694313/72057594037927936)), (46705/18014398509481984), by norm_num⟩
  | 4 => ⟨((93072303366283/2251799813685248), (2224908197775/36028797018963968)), (70083/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486165573520165/9007199254740992), (2773677135657/9007199254740992)), (701191/9007199254740992), by norm_num⟩
  | 2 => ⟨((555447382646059/1125899906842624), (5525043547153/4503599627370496)), (1403471/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206929829372139/2251799813685248), (8232010521331/2251799813685248)), (2107951/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162639432415533/2251799813685248), (16243128917911/2251799813685248)), (1056749/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162639432415533/2251799813685248), (16243128917911/2251799813685248)), (4031177522899436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2076892202840923/2251799813685248), (15599979576423/1125899906842624)), (4090119/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915138174610879/2251799813685248), (28776515345497/1125899906842624)), (957273/140737488355328), by norm_num⟩
  | 3 => ⟨((1627339097480883/2251799813685248), (97896807230379/2251799813685248)), (6708959/562949953421312), by norm_num⟩
  | 4 => ⟨((1171795439935505/2251799813685248), (4421776886991/70368744177664)), (41121017/2251799813685248), by norm_num⟩
  | 5 => ⟨((150222411349787/562949953421312), (147264756622811/2251799813685248)), (47965113/2251799813685248), by norm_num⟩
  | 6 => ⟨((602862573026531/9007199254740992), (314379162300585/9007199254740992)), (63745119/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1362322145/16777216)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-692254841/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((868479517148803/18014398509481984), (-486208748116245/9007199254740992)), (154581565/9007199254740992), by norm_num⟩
  | 1 => ⟨((-630403847/4294967296), (352924691/2147483648)), (113/2147483648), by norm_num⟩
  | 2 => ⟨((959639329/4294967296), (-1074487141/4294967296)), (173/2147483648), by norm_num⟩
  | 3 => ⟨((-973881157/4294967296), (1090433403/4294967296)), (177/2147483648), by norm_num⟩
  | 4 => ⟨((741250759/4294967296), (-829962241/4294967296)), (17/268435456), by norm_num⟩
  | 5 => ⟨((-902701827/8589934592), (505367733/4294967296)), (333/8589934592), by norm_num⟩
  | 6 => ⟨((28628083/536870912), (-512867801/8589934592)), (85/4294967296), by norm_num⟩
  | 7 => ⟨((-796880833/34359738368), (27882813/1073741824)), (149/17179869184), by norm_num⟩
  | 8 => ⟨((303265197/34359738368), (-679118799/68719476736)), (229/68719476736), by norm_num⟩
  | 9 => ⟨((-102588633/34359738368), (918929965/274877906944)), (39/34359738368), by norm_num⟩
  | 10 => ⟨((62466679/68719476736), (-1119081159/1099511627776)), (191/549755813888), by norm_num⟩
  | 11 => ⟨((-553254417/2199023255552), (309733427/1099511627776)), (213/2199023255552), by norm_num⟩
  | 12 => ⟨((280732581/4398046511104), (-314330123/4398046511104)), (109/4398046511104), by norm_num⟩
  | 13 => ⟨((-131491791/8796093022208), (588913915/35184372088832)), (103/17592186044416), by norm_num⟩
  | 14 => ⟨((915039333/281474976710656), (-512274751/140737488355328)), (45/35184372088832), by norm_num⟩
  | 15 => ⟨((-46430963/70368744177664), (831803719/1125899906842624)), (147/562949953421312), by norm_num⟩
  | 16 => ⟨((565440435/4503599627370496), (-79138909/562949953421312)), (113/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-1096536911773/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444479682532187/158456325028528675187087900672), (-162064220067/79228162514264337593543950336)), (11541/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472196437897101/9903520314283042199192993792), (-1458247382903/39614081257132168796771975168)), (103877/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888501316111605/2475880078570760549798248448), (-1548972996317/2475880078570760549798248448)), (110379/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770167843790339/154742504910672534362390528), (-1548506517913/154742504910672534362390528)), (220779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48393587654995/302231454903657293676544), (-1451229419345/9671406556917033397649408)), (51751/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628975093053917/302231454903657293676544), (-317332629233/151115727451828646838272)), (181151/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235803755007795/9444732965739290427392), (-1030867001177/37778931862957161709568)), (294413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296518433379811/4722366482869645213696), (-193186110501/590295810358705651712)), (13803/295147905179352825856), by norm_num⟩
  | 9 => ⟨((202505624676327/73786976294838206464), (-2123729196633/590295810358705651712)), (151863/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910860949056677/36893488147419103232), (-2652685971345/73786976294838206464)), (379749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227585835707769/1152921504606846976), (-745389453349/2305843009213693952)), (26709/576460752303423488), by norm_num⟩
  | 6 => ⟨((397984296867747/288230376151711744), (-744542272995/288230376151711744)), (427501/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192790416498221/144115188075855872), (-2602090669269/144115188075855872)), (374241/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488956361968427/36028797018963968), (-1947766988767/18014398509481984)), (280859/18014398509481984), by norm_num⟩
  | 3 => ⟨((742957104498517/4503599627370496), (-4856142106639/9007199254740992)), (351387/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221284571916419/4503599627370496), (-9672570602503/4503599627370496)), (351857/1125899906842624), by norm_num⟩
  | 1 => ⟨((2206166884727765/2251799813685248), (-14409964503847/2251799813685248)), (2115871/2251799813685248), by norm_num⟩
  | 0 => ⟨((270136489806831/281474976710656), (-7106677656609/562949953421312)), (531349/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((270136489806831/281474976710656), (-7106677656609/562949953421312)), (2026935578466319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2073679096052029/2251799813685248), (-54563229137585/2251799813685248)), (8266445/2251799813685248), by norm_num⟩
  | 2 => ⟨((1908325873957945/2251799813685248), (-6280899560213/140737488355328)), (7812861/1125899906842624), by norm_num⟩
  | 3 => ⟨((1612758157332315/2251799813685248), (-170331349273817/2251799813685248)), (13939635/1125899906842624), by norm_num⟩
  | 4 => ⟨((1142186836443175/2251799813685248), (-1906136866339/17592186044416)), (44152447/2251799813685248), by norm_num⟩
  | 5 => ⟨((1105837053852247/4503599627370496), (-123757470032129/1125899906842624)), (108718195/4503599627370496), by norm_num⟩
  | 6 => ⟨((868479517148803/18014398509481984), (-486208748116245/9007199254740992)), (154581565/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-692254841/8388608)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile040Terms2
