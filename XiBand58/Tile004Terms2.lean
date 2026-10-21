/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile004Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2599/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2599/160))
  have he : value ((15/16), (2599/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-755599471/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((82558165503537/2251799813685248), (-1164694896245523/18014398509481984)), (22196669/2251799813685248), by norm_num⟩
  | 1 => ⟨((-218295897/2147483648), (192476507/1073741824)), (119/4294967296), by norm_num⟩
  | 2 => ⟨((302622371/2147483648), (-1067316385/4294967296)), (167/4294967296), by norm_num⟩
  | 3 => ⟨((-559364915/4294967296), (986409791/4294967296)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((193861107/2147483648), (-1367454331/8589934592)), (219/8589934592), by norm_num⟩
  | 5 => ⟨((-429997695/8589934592), (758277691/8589934592)), (123/8589934592), by norm_num⟩
  | 6 => ⟨((397402253/17179869184), (-43799837/1073741824)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((-157404715/17179869184), (555149413/34359738368)), (93/34359738368), by norm_num⟩
  | 8 => ⟨((218209269/68719476736), (-769600501/137438953472)), (131/137438953472), by norm_num⟩
  | 9 => ⟨((-268890915/274877906944), (948349187/549755813888)), (41/137438953472), by norm_num⟩
  | 10 => ⟨((596419135/2199023255552), (-131469113/274877906944)), (23/274877906944), by norm_num⟩
  | 11 => ⟨((-300659085/4398046511104), (1060392087/8796093022208)), (47/2199023255552), by norm_num⟩
  | 12 => ⟨((69466999/4398046511104), (-980010381/35184372088832)), (11/2199023255552), by norm_num⟩
  | 13 => ⟨((-474100721/140737488355328), (418025497/70368744177664)), (19/17592186044416), by norm_num⟩
  | 14 => ⟨((187783759/281474976710656), (-1324586033/1125899906842624)), (243/1125899906842624), by norm_num⟩
  | 15 => ⟨((-555356941/4503599627370496), (489670973/2251799813685248)), (91/2251799813685248), by norm_num⟩
  | 16 => ⟨((192472049/9007199254740992), (-1357656217/36028797018963968)), (255/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (-1374178321565/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27780612238773/9903520314283042199192993792), (-1624860381137/633825300114114700748351602688)), (11545/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888831222716005/39614081257132168796771975168), (-1827557009867/39614081257132168796771975168)), (25979/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236068697304891/309485009821345068724781056), (-485316152019/618970019642690137449562112)), (110423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770216049083811/154742504910672534362390528), (-1940685820527/154742504910672534362390528)), (27609/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548639936865205/9671406556917033397649408), (-227347278245/1208925819614629174706176)), (25887/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314497404003599/151115727451828646838272), (-1590816476867/604462909807314587353088)), (90619/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943247000151057/37778931862957161709568), (-2583925194173/75557863725914323419136)), (73641/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296566304469965/4722366482869645213696), (-1936936814299/4722366482869645213696)), (110485/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620110659324235/590295810358705651712), (-1330826323265/295147905179352825856)), (151955/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821803734576395/73786976294838206464), (-3324614406783/73786976294838206464)), (190001/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820778420931649/9223372036854775808), (-3736823466935/9223372036854775808)), (106915/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398007127522247/288230376151711744), (-1866309095657/576460752303423488)), (213929/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192869860637447/144115188075855872), (-815329006523/36028797018963968)), (187299/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489074604572375/36028797018963968), (-1220634836557/9007199254740992)), (281171/36028797018963968), by norm_num⟩
  | 3 => ⟨((743030200999765/4503599627370496), (-1521674341975/2251799813685248)), (175927/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221572151315049/4503599627370496), (-12124099611711/4503599627370496)), (704881/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103293160754095/1125899906842624), (-4515846003845/562949953421312)), (530135/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161883565304611/2251799813685248), (-35638531180923/2251799813685248)), (2132407/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2161883565304611/2251799813685248), (-35638531180923/2251799813685248)), (8134487160689543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64843553374403/70368744177664), (-68430909695779/2251799813685248)), (4162015/2251799813685248), by norm_num⟩
  | 2 => ⟨((1909990431929083/2251799813685248), (-126115746335165/2251799813685248)), (3961705/1125899906842624), by norm_num⟩
  | 3 => ⟨((1613002295547159/2251799813685248), (-53486075305589/562949953421312)), (7164449/1125899906842624), by norm_num⟩
  | 4 => ⟨((70943368996459/140737488355328), (-306503843630861/2251799813685248)), (23250853/2251799813685248), by norm_num⟩
  | 5 => ⟨((530461703278129/2251799813685248), (-309006726376099/2251799813685248)), (7442575/562949953421312), by norm_num⟩
  | 6 => ⟨((82558165503537/2251799813685248), (-1164694896245523/18014398509481984)), (22196669/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-755599471/16777216)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-386060595/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-571656116705869/18014398509481984), (-141051399642139/2251799813685248)), (227011927/18014398509481984), by norm_num⟩
  | 1 => ⟨((193074195/2147483648), (762231269/4294967296)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-273510193/2147483648), (-1079781901/4294967296)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((258304243/2147483648), (509875415/2147483648)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((-182957757/2147483648), (-722292915/4294967296)), (19/536870912), by norm_num⟩
  | 5 => ⟨((414686687/8589934592), (409281985/4294967296)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((-24476997/1073741824), (-386527727/8589934592)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((634043927/68719476736), (1251560587/68719476736)), (271/68719476736), by norm_num⟩
  | 8 => ⟨((-449095429/137438953472), (-886484539/137438953472)), (97/68719476736), by norm_num⟩
  | 9 => ⟨((141375907/137438953472), (1116266589/549755813888)), (123/274877906944), by norm_num⟩
  | 10 => ⟨((-320438485/1099511627776), (-632524279/1099511627776)), (281/2199023255552), by norm_num⟩
  | 11 => ⟨((660269521/8796093022208), (651664083/4398046511104)), (73/2199023255552), by norm_num⟩
  | 12 => ⟨((-623561473/35184372088832), (-1230868917/35184372088832)), (139/17592186044416), by norm_num⟩
  | 13 => ⟨((543594673/140737488355328), (536509883/70368744177664)), (245/140737488355328), by norm_num⟩
  | 14 => ⟨((-440034195/562949953421312), (-868598263/562949953421312)), (25/70368744177664), by norm_num⟩
  | 15 => ⟨((332456201/2251799813685248), (1312492901/4503599627370496)), (19/281474976710656), by norm_num⟩
  | 16 => ⟨((-470959673/18014398509481984), (-232410775/4503599627370496)), (109/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (-664238187379/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888933885190563/316912650057057350374175801344), (-24541779173/4951760157141521099596496896)), (46255/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944364096798701/19807040628566084398385987584), (-441649726283/4951760157141521099596496896)), (52047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888439853960395/2475880078570760549798248448), (-3753004977573/2475880078570760549798248448)), (55311/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110631627307023/9671406556917033397649408), (-117245639927/4835703278458516698824704)), (110649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548536495045967/9671406556917033397649408), (-3516153564669/9671406556917033397649408)), (6485/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628949399656191/302231454903657293676544), (-3075419183531/604462909807314587353088)), (45409/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943172925856619/37778931862957161709568), (-4995278651181/75557863725914323419136)), (147631/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296454693644181/4722366482869645213696), (-468058388393/590295810358705651712)), (110769/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619956384125281/590295810358705651712), (-643175905871/73786976294838206464)), (38095/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821609677180225/73786976294838206464), (-3213454818659/36893488147419103232)), (190585/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820558441303549/9223372036854775808), (-3611805224863/4611686018427387904)), (6705/288230376151711744), by norm_num⟩
  | 6 => ⟨((795903227089039/576460752303423488), (-450955588967/72057594037927936)), (214751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192673232814059/144115188075855872), (-788003439899/18014398509481984)), (188121/144115188075855872), by norm_num⟩
  | 4 => ⟨((744387511145745/18014398509481984), (-4718682938117/18014398509481984)), (141305/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485677841924681/9007199254740992), (-11764083947683/9007199254740992)), (354015/9007199254740992), by norm_num⟩
  | 2 => ⟨((69399466841807/140737488355328), (-11715265825055/2251799813685248)), (710289/4503599627370496), by norm_num⟩
  | 1 => ⟨((551335702690649/562949953421312), (-17451262209213/1125899906842624)), (535551/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159160988166429/2251799813685248), (-68836851860865/2251799813685248)), (1082491/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2159160988166429/2251799813685248), (-68836851860865/2251799813685248)), (4129375462058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034114496400055/1125899906842624), (-66004910464455/1125899906842624)), (1071049/562949953421312), by norm_num⟩
  | 2 => ⟨((1891884237642427/2251799813685248), (-242496279927027/2251799813685248)), (2093049/562949953421312), by norm_num⟩
  | 3 => ⟨((781690606213341/1125899906842624), (-407473956514853/2251799813685248)), (15871263/2251799813685248), by norm_num⟩
  | 4 => ⟨((252922770519565/562949953421312), (-282901314893497/1125899906842624)), (27782187/2251799813685248), by norm_num⟩
  | 5 => ⟨((624732469918501/4503599627370496), (-1016817696303337/4503599627370496)), (77851017/4503599627370496), by norm_num⟩
  | 6 => ⟨((-571656116705869/18014398509481984), (-141051399642139/2251799813685248)), (227011927/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-386060595/8388608)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-1575396563/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-590484756735531/9007199254740992), (-25859250228345/2251799813685248)), (205304559/18014398509481984), by norm_num⟩
  | 1 => ⟨((101728467/536870912), (71280333/2147483648)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((-4594267/16777216), (-206026661/4294967296)), (209/4294967296), by norm_num⟩
  | 3 => ⟨((1133153245/4294967296), (198497881/4294967296)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((-1637617069/8589934592), (-286866335/8589934592)), (37/1073741824), by norm_num⟩
  | 5 => ⟨((946664425/8589934592), (165830071/8589934592)), (173/8589934592), by norm_num⟩
  | 6 => ⟨((-1824141413/34359738368), (-319540369/34359738368)), (21/2147483648), by norm_num⟩
  | 7 => ⟨((753206689/34359738368), (65970747/17179869184)), (279/68719476736), by norm_num⟩
  | 8 => ⟨((-1088523671/137438953472), (-11917499/8589934592)), (203/137438953472), by norm_num⟩
  | 9 => ⟨((699164017/274877906944), (244949351/549755813888)), (263/549755813888), by norm_num⟩
  | 10 => ⟨((-1616675143/2199023255552), (-283197875/2199023255552)), (307/2199023255552), by norm_num⟩
  | 11 => ⟨((1699197155/8796093022208), (297653505/8796093022208)), (325/8796093022208), by norm_num⟩
  | 12 => ⟨((-1637103823/35184372088832), (-71694107/8796093022208)), (315/35184372088832), by norm_num⟩
  | 13 => ⟨((363987589/35184372088832), (255043227/140737488355328)), (141/70368744177664), by norm_num⟩
  | 14 => ⟨((-601176827/281474976710656), (-105309963/281474976710656)), (235/562949953421312), by norm_num⟩
  | 15 => ⟨((926733079/2251799813685248), (40584659/562949953421312)), (183/2251799813685248), by norm_num⟩
  | 16 => ⟨((-167412695/2251799813685248), (-7331547/562949953421312)), (267/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (-241649043003/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888889665884277/316912650057057350374175801344), (-4570869251483/633825300114114700748351602688)), (92651/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888628399695327/39614081257132168796771975168), (-5140997734887/39614081257132168796771975168)), (104261/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888333416715505/2475880078570760549798248448), (-5460797536719/2475880078570760549798248448)), (110811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769999143195651/154742504910672534362390528), (-1364774059139/38685626227668133590597632)), (433/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((1548435797610893/9671406556917033397649408), (-39969496443/75557863725914323419136)), (103961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628905102479901/302231454903657293676544), (-4474776934763/604462909807314587353088)), (45503/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886200979225379/75557863725914323419136), (-3634063051519/37778931862957161709568)), (18495/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324086311740635/1180591620717411303424), (-681016568491/590295810358705651712)), (27759/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809902304664275/295147905179352825856), (-7486370989789/590295810358705651712)), (152781/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910709016799233/36893488147419103232), (-9350750402347/73786976294838206464)), (191137/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820340200684063/9223372036854775808), (-5254840827337/4611686018427387904)), (107625/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591584919665897/1152921504606846976), (-5248649826921/576460752303423488)), (215527/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192475695601187/144115188075855872), (-9171219391475/144115188075855872)), (94449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488471355181781/36028797018963968), (-13729023352949/36028797018963968)), (283971/36028797018963968), by norm_num⟩
  | 3 => ⟨((185660679757735/1125899906842624), (-4278171604247/2251799813685248)), (356057/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109979959882205/2251799813685248), (-17039931869851/2251799813685248)), (178851/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102006810066425/1125899906842624), (-25378482997369/1125899906842624)), (270339/562949953421312), by norm_num⟩
  | 0 => ⟨((269516142066415/281474976710656), (-50034139355227/1125899906842624)), (137241/140737488355328), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((269516142066415/281474976710656), (-50034139355227/1125899906842624)), (523532867968511537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((257509524425893/281474976710656), (-47908373128657/562949953421312)), (2200145/1125899906842624), by norm_num⟩
  | 2 => ⟨((934183960283845/1125899906842624), (-175317358929003/1125899906842624)), (8800229/2251799813685248), by norm_num⟩
  | 3 => ⟨((747813806709423/1125899906842624), (-581858702271633/2251799813685248)), (17344111/2251799813685248), by norm_num⟩
  | 4 => ⟨((843033380265245/2251799813685248), (-193232972339865/562949953421312)), (16001491/1125899906842624), by norm_num⟩
  | 5 => ⟨((50307124978071/2251799813685248), (-578743616054485/2251799813685248)), (5741597/281474976710656), by norm_num⟩
  | 6 => ⟨((-590484756735531/9007199254740992), (-25859250228345/2251799813685248)), (205304559/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-1575396563/33554432)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-1604865891/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-868121649630549/18014398509481984), (5768923012649/140737488355328)), (104772231/9007199254740992), by norm_num⟩
  | 1 => ⟨((304714587/2147483648), (-518378961/4294967296)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((-897213507/4294967296), (763167609/4294967296)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((110074601/536870912), (-749033485/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-162053973/1073741824), (551370847/4294967296)), (41/1073741824), by norm_num⟩
  | 5 => ⟨((95431607/1073741824), (-324695563/4294967296)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((-749313449/17179869184), (637364181/17179869184)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((157593409/8589934592), (-134048567/8589934592)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((-928048353/137438953472), (197348913/34359738368)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((151810097/68719476736), (-8070581/4294967296)), (161/274877906944), by norm_num⟩
  | 10 => ⟨((-715192907/1099511627776), (152085333/274877906944)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((765760681/4398046511104), (-651354157/4398046511104)), (103/2199023255552), by norm_num⟩
  | 12 => ⟨((-751578533/17592186044416), (79911357/2199023255552)), (51/4398046511104), by norm_num⟩
  | 13 => ⟨((680916039/70368744177664), (-72398189/8796093022208)), (187/70368744177664), by norm_num⟩
  | 14 => ⟨((-572833065/281474976710656), (974500799/562949953421312)), (317/562949953421312), by norm_num⟩
  | 15 => ⟨((899558403/2251799813685248), (-382581085/1125899906842624)), (251/2251799813685248), by norm_num⟩
  | 16 => ⟨((-331086853/4503599627370496), (281621665/4503599627370496)), (187/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (3174141264503/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444426232879125/158456325028528675187087900672), (3752179595061/633825300114114700748351602688)), (46285/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888544920522913/39614081257132168796771975168), (1055045924065/9903520314283042199192993792)), (104165/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472061253472147/618970019642690137449562112), (560335176037/309485009821345068724781056)), (110703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442477767642167/38685626227668133590597632), (2240630059745/77371252455336267181195264)), (55367/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548353580090901/9671406556917033397649408), (2099835858451/4835703278458516698824704)), (103847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314434653723621/151115727451828646838272), (3673203640249/604462909807314587353088)), (90899/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886085301471679/75557863725914323419136), (5966127462933/75557863725914323419136)), (36943/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296259062093449/4722366482869645213696), (4472121833669/4722366482869645213696)), (110883/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619687035777925/590295810358705651712), (6145149778307/590295810358705651712)), (152551/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910636230259199/36893488147419103232), (7675414322277/73786976294838206464)), (95411/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227522293012617/1152921504606846976), (8626565657515/9223372036854775808)), (26857/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591425449368279/1152921504606846976), (8616230385549/1152921504606846976)), (215083/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596169418308733/72057594037927936), (3763793420389/72057594037927936)), (94227/72057594037927936), by norm_num⟩
  | 4 => ⟨((744135702086861/18014398509481984), (11268181838853/36028797018963968)), (35399/4503599627370496), by norm_num⟩
  | 3 => ⟨((742522400185807/4503599627370496), (14044699927213/9007199254740992)), (354889/9007199254740992), by norm_num⟩
  | 2 => ⟨((8669946835739/17592186044416), (27968097001925/4503599627370496)), (356239/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203402139141189/2251799813685248), (10412466210377/562949953421312)), (1075491/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155178140963089/2251799813685248), (82096458251687/2251799813685248)), (544551/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2155178140963089/2251799813685248), (82096458251687/2251799813685248)), (2077297212840843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059709287939369/2251799813685248), (19643452672749/281474976710656)), (1082077/562949953421312), by norm_num⟩
  | 2 => ⟨((936519079157191/1125899906842624), (143742091713003/1125899906842624)), (4261143/1125899906842624), by norm_num⟩
  | 3 => ⟨((380320751201159/562949953421312), (239128204113097/1125899906842624)), (8176833/1125899906842624), by norm_num⟩
  | 4 => ⟨((926180371817687/2251799813685248), (646206062680769/2251799813685248)), (14521629/1125899906842624), by norm_num⟩
  | 5 => ⟨((195500418385105/2251799813685248), (265788889299631/1125899906842624)), (81121289/4503599627370496), by norm_num⟩
  | 6 => ⟨((-868121649630549/18014398509481984), (5768923012649/140737488355328)), (104772231/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-1604865891/33554432)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1632823291/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-17788547621887/9007199254740992), (1085603052959581/18014398509481984)), (356896811/36028797018963968), by norm_num⟩
  | 1 => ⟨((50821043/8589934592), (-1550758411/8589934592)), (257/8589934592), by norm_num⟩
  | 2 => ⟨((-4757695/536870912), (1161414255/4294967296)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((38007415/4294967296), (-144970257/536870912)), (49/1073741824), by norm_num⟩
  | 4 => ⟨((-14232505/2147483648), (1737168311/8589934592)), (37/1073741824), by norm_num⟩
  | 5 => ⟨((8527355/2147483648), (-1040818235/8589934592)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((-34060897/17179869184), (2078675185/34359738368)), (45/4294967296), by norm_num⟩
  | 7 => ⟨((58307045/68719476736), (-889593477/34359738368)), (155/34359738368), by norm_num⟩
  | 8 => ⟨((-21834037/68719476736), (1332491945/137438953472)), (117/68719476736), by norm_num⟩
  | 9 => ⟨((29070635/274877906944), (-443532125/137438953472)), (157/274877906944), by norm_num⟩
  | 10 => ⟨((-544299/17179869184), (1062962801/1099511627776)), (95/549755813888), by norm_num⟩
  | 11 => ⟨((18973953/2199023255552), (-1157946171/4398046511104)), (209/4398046511104), by norm_num⟩
  | 12 => ⟨((-18946961/8796093022208), (1156298905/17592186044416)), (105/8796093022208), by norm_num⟩
  | 13 => ⟨((34929245/70368744177664), (-532917223/35184372088832)), (49/17592186044416), by norm_num⟩
  | 14 => ⟨((-14948381/140737488355328), (1824545513/562949953421312)), (169/281474976710656), by norm_num⟩
  | 15 => ⟨((47766771/2251799813685248), (-45548749/70368744177664)), (17/140737488355328), by norm_num⟩
  | 16 => ⟨((-17887057/4503599627370496), (1091614859/9007199254740992)), (103/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (1044405583415/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777635170287361/633825300114114700748351602688), (1234502700529/316912650057057350374175801344)), (23111/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472116673128577/9903520314283042199192993792), (1388478487705/19807040628566084398385987584)), (104015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944081117722987/1237940039285380274899124224), (737417883527/618970019642690137449562112)), (55267/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769828672873989/154742504910672534362390528), (1474360531347/77371252455336267181195264)), (110555/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96767296029423/604462909807314587353088), (2763416507289/9671406556917033397649408)), (51833/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157208972572321/75557863725914323419136), (302122548773/75557863725914323419136)), (45365/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885977452151053/75557863725914323419136), (3925702082967/75557863725914323419136)), (147477/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296178836211767/4722366482869645213696), (91956963021/147573952589676412928)), (110643/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202447224754219/73786976294838206464), (252713798013/36893488147419103232)), (1189/4611686018427387904), by norm_num⟩
  | 8 => ⟨((910568760026389/36893488147419103232), (1262562645483/18446744073709551616)), (190327/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455007185292611/2305843009213693952), (5676001927591/9223372036854775808)), (107119/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99454912287737/72057594037927936), (708637103391/144115188075855872)), (214387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74513339117045/9007199254740992), (2476350805241/72057594037927936)), (93879/72057594037927936), by norm_num⟩
  | 4 => ⟨((46502794926983/1125899906842624), (7413561470523/36028797018963968)), (140987/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484828056362083/9007199254740992), (9239899482913/9007199254740992)), (88265/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219104854127973/4503599627370496), (9199434337797/2251799813685248)), (176975/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101439526354933/1125899906842624), (27396769114757/2251799813685248)), (66645/140737488355328), by norm_num⟩
  | 0 => ⟨((2154444877780193/2251799813685248), (843627164439/35184372088832)), (1075309/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2154444877780193/2251799813685248), (843627164439/35184372088832)), (4101978306296920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030002212492255/1125899906842624), (51657827475021/1125899906842624)), (527301/281474976710656), by norm_num⟩
  | 2 => ⟨((939902401774885/1125899906842624), (94515820222467/1125899906842624)), (4052655/1125899906842624), by norm_num⟩
  | 3 => ⟨((776697181761207/1125899906842624), (78901904061741/562949953421312)), (14893475/2251799813685248), by norm_num⟩
  | 4 => ⟨((1027367471624403/2251799813685248), (217720549217217/1125899906842624)), (24723277/2251799813685248), by norm_num⟩
  | 5 => ⟨((384525731942867/2251799813685248), (198666869772851/1125899906842624)), (64242695/4503599627370496), by norm_num⟩
  | 6 => ⟨((-17788547621887/9007199254740992), (1085603052959581/18014398509481984)), (356896811/36028797018963968), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1632823291/33554432)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1659416361/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((714670987919247/18014398509481984), (47016653019259/1125899906842624)), (60648869/9007199254740992), by norm_num⟩
  | 1 => ⟨((-129689685/1073741824), (-68256023/536870912)), (179/8589934592), by norm_num⟩
  | 2 => ⟨((98710789/536870912), (415613987/2147483648)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((-801405899/4294967296), (-843564073/4294967296)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((19061705/134217728), (642062437/4294967296)), (55/2147483648), by norm_num⟩
  | 5 => ⟨((-371416247/4294967296), (-390954699/4294967296)), (17/1073741824), by norm_num⟩
  | 6 => ⟨((188464183/4294967296), (793513569/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-40984531/2147483648), (-690248533/34359738368)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((499113297/68719476736), (1050738573/137438953472)), (189/137438953472), by norm_num⟩
  | 9 => ⟨((-675360725/274877906944), (-355444129/137438953472)), (65/137438953472), by norm_num⟩
  | 10 => ⟨((12850943/17179869184), (865726101/1099511627776)), (5/34359738368), by norm_num⟩
  | 11 => ⟨((-455272545/2199023255552), (-59902785/274877906944)), (179/4398046511104), by norm_num⟩
  | 12 => ⟨((924058319/17592186044416), (60791791/1099511627776)), (23/2199023255552), by norm_num⟩
  | 13 => ⟨((-216408945/17592186044416), (-56948299/4398046511104)), (87/35184372088832), by norm_num⟩
  | 14 => ⟨((94123127/35184372088832), (198148999/70368744177664)), (153/281474976710656), by norm_num⟩
  | 15 => ⟨((-152831985/281474976710656), (-160871753/281474976710656)), (63/562949953421312), by norm_num⟩
  | 16 => ⟨((930600815/9007199254740992), (979555323/9007199254740992)), (97/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (264111380663/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888783589945735/316912650057057350374175801344), (624319852465/316912650057057350374175801344)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944195177386087/19807040628566084398385987584), (702187772127/19807040628566084398385987584)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((944040664583045/1237940039285380274899124224), (745857413155/1237940039285380274899124224)), (110373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769747994220407/154742504910672534362390528), (1491226629495/154742504910672534362390528)), (6899/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774100670945671/4835703278458516698824704), (698753238069/4835703278458516698824704)), (12937/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257606051760671/604462909807314587353088), (611149962679/302231454903657293676544)), (45285/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942935547527419/37778931862957161709568), (1985266202519/75557863725914323419136)), (36799/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296099463628329/4722366482869645213696), (1488100398579/4722366482869645213696)), (110415/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619469302123375/590295810358705651712), (2044758996701/590295810358705651712)), (75925/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910501430364971/36893488147419103232), (1276940945863/36893488147419103232)), (189857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909939283869141/4611686018427387904), (1435139000403/4611686018427387904)), (106825/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49722814604791/36028797018963968), (1433366641327/576460752303423488)), (106863/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192085307403505/144115188075855872), (4891424941/281474976710656)), (187097/144115188075855872), by norm_num⟩
  | 4 => ⟨((371975234134657/9007199254740992), (1874332308049/18014398509481984)), (280817/36028797018963968), by norm_num⟩
  | 3 => ⟨((371149708883925/2251799813685248), (4671950991721/9007199254740992)), (87831/2251799813685248), by norm_num⟩
  | 2 => ⟨((2218665515858773/4503599627370496), (9302391403191/4503599627370496)), (175889/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202267408721853/2251799813685248), (865641246407/140737488355328)), (1057625/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153408686767691/2251799813685248), (6822474041175/562949953421312)), (2124491/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2153408686767691/2251799813685248), (6822474041175/562949953421312)), (8104290017134856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514746493631021/562949953421312), (52194958987831/2251799813685248)), (1028705/562949953421312), by norm_num⟩
  | 2 => ⟨((117592017499589/140737488355328), (5965710619771/140737488355328)), (3857861/1125899906842624), by norm_num⟩
  | 3 => ⟨((1568002162051107/2251799813685248), (159507168882009/2251799813685248)), (1693467/281474976710656), by norm_num⟩
  | 4 => ⟨((540276322185605/1125899906842624), (55535040048769/562949953421312)), (20786787/2251799813685248), by norm_num⟩
  | 5 => ⟨((993203534070837/4503599627370496), (426386281872897/4503599627370496)), (48101609/4503599627370496), by norm_num⟩
  | 6 => ⟨((714670987919247/18014398509481984), (47016653019259/1125899906842624)), (60648869/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1659416361/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile004Terms2
