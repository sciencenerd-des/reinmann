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
namespace Reinmann.XiBand97.Tile038Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33979/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33979/1280))
  have he : value ((69/80), (33979/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-308706647/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-369422049547949/18014398509481984), (1606485561647743/18014398509481984)), (35301763/1125899906842624), by norm_num⟩
  | 1 => ⟨((244201519/4294967296), (-2074113/8388608)), (375/4294967296), by norm_num⟩
  | 2 => ⟨((-338535189/4294967296), (92010597/268435456)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((312872949/4294967296), (-680286783/2147483648)), (121/1073741824), by norm_num⟩
  | 4 => ⟨((-108433501/2147483648), (943077731/4294967296)), (169/2147483648), by norm_num⟩
  | 5 => ⟨((120256601/4294967296), (-1045906673/8589934592)), (377/8589934592), by norm_num⟩
  | 6 => ⟨((-222281397/17179869184), (966623015/17179869184)), (175/8589934592), by norm_num⟩
  | 7 => ⟨((352168511/68719476736), (-191432005/8589934592)), (557/68719476736), by norm_num⟩
  | 8 => ⟨((-122052305/68719476736), (265381109/34359738368)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((300800751/549755813888), (-654037929/274877906944)), (15/17179869184), by norm_num⟩
  | 10 => ⟨((-83399677/549755813888), (1450702549/2199023255552)), (267/1099511627776), by norm_num⟩
  | 11 => ⟨((336338915/8796093022208), (-1462618737/8796093022208)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((-310843161/35184372088832), (675873369/17592186044416)), (501/35184372088832), by norm_num⟩
  | 13 => ⟨((265181613/140737488355328), (-576590425/70368744177664)), (429/140737488355328), by norm_num⟩
  | 14 => ⟨((-210068443/562949953421312), (456756603/281474976710656)), (171/281474976710656), by norm_num⟩
  | 15 => ⟨((310631145/4503599627370496), (-1350824753/4503599627370496)), (127/1125899906842624), by norm_num⟩
  | 16 => ⟨((-107656551/9007199254740992), (936320369/18014398509481984)), (177/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1170281644617/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444569207631239/158456325028528675187087900672), (173030438919/39614081257132168796771975168)), (184945/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944594173985119/19807040628566084398385987584), (194618484077/2475880078570760549798248448)), (104049/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888928729065349/2475880078570760549798248448), (826926678151/618970019642690137449562112)), (221145/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770594868141537/154742504910672534362390528), (413349818479/19342813113834066795298816)), (221191/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548994727649869/9671406556917033397649408), (774789750183/2417851639229258349412352)), (207415/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157287463263109/75557863725914323419136), (1355399905397/302231454903657293676544)), (5673/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1886997237488577/75557863725914323419136), (4403242288425/75557863725914323419136)), (18443/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324235789012783/1180591620717411303424), (1650425461869/2361183241434822606848)), (55349/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810313947342295/295147905179352825856), (141753203689/18446744073709551616)), (304549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455612219267769/18446744073709551616), (2833139571901/36893488147419103232)), (23805/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910751140777459/4611686018427387904), (1592318827557/2305843009213693952)), (214379/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592749968846917/1152921504606846976), (6362669879629/1152921504606846976)), (429093/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193498440429241/144115188075855872), (5559912562321/144115188075855872)), (187917/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490012094687945/36028797018963968), (8325040482603/36028797018963968)), (564505/36028797018963968), by norm_num⟩
  | 3 => ⟨((743611440545527/4503599627370496), (2595098310563/2251799813685248)), (353477/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111934540664579/2251799813685248), (10341616646603/2251799813685248)), (1417885/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209962073459565/2251799813685248), (30831557225355/2251799813685248)), (2136797/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168359050171887/2251799813685248), (30446739157987/1125899906842624)), (4313637/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168359050171887/2251799813685248), (30446739157987/1125899906842624)), (16455219277388762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2086363506297721/2251799813685248), (117274123570333/2251799813685248)), (8540891/2251799813685248), by norm_num⟩
  | 2 => ⟨((7527241781879/8796093022208), (108658172082251/1125899906842624)), (16716433/2251799813685248), by norm_num⟩
  | 3 => ⟨((1628031932840989/2251799813685248), (371936190658797/2251799813685248)), (15918327/1125899906842624), by norm_num⟩
  | 4 => ⟨((34863104686869/70368744177664), (33613334081237/140737488355328)), (28276179/1125899906842624), by norm_num⟩
  | 5 => ⟨((848533101264707/4503599627370496), (1065805176903147/4503599627370496)), (83049585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-369422049547949/18014398509481984), (1606485561647743/18014398509481984)), (35301763/1125899906842624), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-308706647/4194304)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1261826949/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((96063915717507/1125899906842624), (291579948080755/18014398509481984)), (28896705/2251799813685248), by norm_num⟩
  | 1 => ⟨((-519122253/2147483648), (-196959543/4294967296)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((735392047/2147483648), (279014203/4294967296)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((-1389015041/4294967296), (-131751127/2147483648)), (27/536870912), by norm_num⟩
  | 4 => ⟨((983843987/4294967296), (93319763/2147483648)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((-1114975965/8589934592), (-105757919/4294967296)), (177/8589934592), by norm_num⟩
  | 6 => ⟨((1052988261/17179869184), (99878249/8589934592)), (169/17179869184), by norm_num⟩
  | 7 => ⟨((-852382969/34359738368), (-161700793/34359738368)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((1207491401/137438953472), (114533211/68719476736)), (197/137438953472), by norm_num⟩
  | 9 => ⟨((-1520480333/549755813888), (-288441797/549755813888)), (125/274877906944), by norm_num⟩
  | 10 => ⟨((430784517/549755813888), (326886859/2199023255552)), (143/1099511627776), by norm_num⟩
  | 11 => ⟨((-443819797/2199023255552), (-336778259/8796093022208)), (297/8796093022208), by norm_num⟩
  | 12 => ⟨((838290781/17592186044416), (159027443/17592186044416)), (283/35184372088832), by norm_num⟩
  | 13 => ⟨((-1461573309/140737488355328), (-69316719/35184372088832)), (31/17592186044416), by norm_num⟩
  | 14 => ⟨((591564143/281474976710656), (28055579/70368744177664)), (203/562949953421312), by norm_num⟩
  | 15 => ⟨((-893881293/2251799813685248), (-169573207/2251799813685248)), (309/4503599627370496), by norm_num⟩
  | 16 => ⟨((316569551/4503599627370496), (30027317/2251799813685248)), (221/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (244209233325/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778200331565713/633825300114114700748351602688), (288832915675/633825300114114700748351602688)), (184457/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102531042773/39614081257132168796771975168), (324868347295/39614081257132168796771975168)), (103759/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944418935186255/1237940039285380274899124224), (345086620717/2475880078570760549798248448)), (220493/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770504371117727/154742504910672534362390528), (344989917591/154742504910672534362390528)), (220497/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774455135346033/4835703278458516698824704), (323325338959/9671406556917033397649408)), (103361/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157278273745423/75557863725914323419136), (70701751475/151115727451828646838272)), (180887/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886878492541161/75557863725914323419136), (459368977951/75557863725914323419136)), (146975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296854725627131/4722366482869645213696), (172179234567/2361183241434822606848)), (27559/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202563415325379/73786976294838206464), (59152454617/73786976294838206464)), (151581/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822299689473443/73786976294838206464), (591114958741/73786976294838206464)), (378973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56916766949381/288230376151711744), (664441632565/9223372036854775808)), (426373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592586845600887/1152921504606846976), (331869495937/576460752303423488)), (213205/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193358643421719/144115188075855872), (72497768599/18014398509481984)), (186575/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489808253157009/36028797018963968), (868396785735/36028797018963968)), (559807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486978283940353/9007199254740992), (541371416903/4503599627370496)), (699905/9007199254740992), by norm_num⟩
  | 2 => ⟨((555852585737561/1125899906842624), (2157248643861/4503599627370496)), (1400253/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104674776704551/1125899906842624), (1607679334183/1125899906842624)), (1050753/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167433062322373/2251799813685248), (396820501331/140737488355328)), (1051905/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167433062322373/2251799813685248), (396820501331/140737488355328)), (4012699129344749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((260776165562721/281474976710656), (12222498560165/2251799813685248)), (253865/70368744177664), by norm_num⟩
  | 2 => ⟨((1932729512506923/2251799813685248), (2830923325195/281474976710656)), (473149/70368744177664), by norm_num⟩
  | 3 => ⟨((829321159389133/1125899906842624), (19438349803553/1125899906842624)), (13147665/1125899906842624), by norm_num⟩
  | 4 => ⟨((1221060116960349/2251799813685248), (28635999874805/1125899906842624)), (4955683/281474976710656), by norm_num⟩
  | 5 => ⟨((1321349898187575/4503599627370496), (31056292965209/1125899906842624)), (22506473/1125899906842624), by norm_num⟩
  | 6 => ⟨((96063915717507/1125899906842624), (291579948080755/18014398509481984)), (28896705/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1261826949/16777216)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-643641783/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1388054892641/70368744177664), (-1446163658048007/18014398509481984)), (222161789/9007199254740992), by norm_num⟩
  | 1 => ⟨((-244872721/4294967296), (498288941/2147483648)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((353886599/4294967296), (-1440240283/4294967296)), (7/67108864), by norm_num⟩
  | 3 => ⟨((-170477305/2147483648), (693804973/2147483648)), (217/2147483648), by norm_num⟩
  | 4 => ⟨((123185697/2147483648), (-501338575/2147483648)), (315/4294967296), by norm_num⟩
  | 5 => ⟨((-17802623/536870912), (1159243887/8589934592)), (183/4294967296), by norm_num⟩
  | 6 => ⟨((68608265/4294967296), (-1116881931/17179869184)), (177/8589934592), by norm_num⟩
  | 7 => ⟨((-226632447/34359738368), (922343997/34359738368)), (147/17179869184), by norm_num⟩
  | 8 => ⟨((81881503/34359738368), (-166619815/17179869184)), (427/137438953472), by norm_num⟩
  | 9 => ⟨((-210371541/274877906944), (1712331405/549755813888)), (551/549755813888), by norm_num⟩
  | 10 => ⟨((15201299/68719476736), (-989854867/1099511627776)), (5/17179869184), by norm_num⟩
  | 11 => ⟨((-255635813/4398046511104), (260095323/1099511627776)), (169/2199023255552), by norm_num⟩
  | 12 => ⟨((123147089/8796093022208), (-1002362901/17592186044416)), (41/2199023255552), by norm_num⟩
  | 13 => ⟨((-109520267/35184372088832), (891446591/70368744177664)), (293/70368744177664), by norm_num⟩
  | 14 => ⟨((45222041/70368744177664), (-1472349743/562949953421312)), (243/281474976710656), by norm_num⟩
  | 15 => ⟨((-139422411/1125899906842624), (1134836831/2251799813685248)), (47/281474976710656), by norm_num⟩
  | 16 => ⟨((402982599/18014398509481984), (-1640050163/18014398509481984)), (273/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-54133934587/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222265272207677/79228162514264337593543950336), (-1024327477219/316912650057057350374175801344)), (184803/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889014504429169/39614081257132168796771975168), (-2304237543219/39614081257132168796771975168)), (103965/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944372101612041/1237940039285380274899124224), (-2447629800583/2475880078570760549798248448)), (55239/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770410547922915/154742504910672534362390528), (-76466552277/4835703278458516698824704)), (110495/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774411072892423/4835703278458516698824704), (-2293252939469/9671406556917033397649408)), (103607/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629074457580991/302231454903657293676544), (-2005852982189/604462909807314587353088)), (45337/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943376305495113/37778931862957161709568), (-814529486927/18889465931478580854784)), (147379/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296760043542895/4722366482869645213696), (-2442370069563/4722366482869645213696)), (221127/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620376695104547/590295810358705651712), (-839070027451/147573952589676412928)), (152073/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822135746724723/73786976294838206464), (-1048096011151/18446744073709551616)), (380327/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821151203263465/9223372036854775808), (-1178089234659/2305843009213693952)), (214033/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592400379687899/1152921504606846976), (-2353633972057/576460752303423488)), (214157/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193194221683605/144115188075855872), (-1028285264119/36028797018963968)), (375055/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489559101356653/36028797018963968), (-3079145793579/18014398509481984)), (563141/36028797018963968), by norm_num⟩
  | 3 => ⟨((743331227827689/4503599627370496), (-7677917217771/9007199254740992)), (176227/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222765600736873/4503599627370496), (-7648071648335/2251799813685248)), (706383/2251799813685248), by norm_num⟩
  | 1 => ⟨((552087501175257/562949953421312), (-22795513244857/2251799813685248)), (2126551/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165305886586859/2251799813685248), (-22499683646477/1125899906842624)), (4282855/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165305886586859/2251799813685248), (-22499683646477/1125899906842624)), (16337795266158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2081235024067735/2251799813685248), (-43270895707489/1125899906842624)), (2101967/562949953421312), by norm_num⟩
  | 2 => ⟨((480065958513011/562949953421312), (-19996649596001/281474976710656)), (2023535/281474976710656), by norm_num⟩
  | 3 => ⟨((101635970991667/140737488355328), (-34105023713071/281474976710656)), (29909817/2251799813685248), by norm_num⟩
  | 4 => ⟨((1141311536093973/2251799813685248), (-394072367359035/2251799813685248)), (50447837/2251799813685248), by norm_num⟩
  | 5 => ⟨((509503102688149/2251799813685248), (-199733269444881/1125899906842624)), (68795457/2251799813685248), by norm_num⟩
  | 6 => ⟨((1388054892641/70368744177664), (-1446163658048007/18014398509481984)), (222161789/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-643641783/8388608)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-327840865/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1321794867974639/18014398509481984), (-261264246565731/9007199254740992)), (506191133/18014398509481984), by norm_num⟩
  | 1 => ⟨((927911837/4294967296), (366819683/4294967296)), (357/4294967296), by norm_num⟩
  | 2 => ⟨((-1366089891/4294967296), (-270019543/2147483648)), (33/268435456), by norm_num⟩
  | 3 => ⟨((1340789441/4294967296), (265018689/2147483648)), (521/4294967296), by norm_num⟩
  | 4 => ⟨((-986968173/4294967296), (-390165679/4294967296)), (385/4294967296), by norm_num⟩
  | 5 => ⟨((72651689/536870912), (459527613/8589934592)), (57/1073741824), by norm_num⟩
  | 6 => ⟨((-71306155/1073741824), (-451017005/17179869184)), (449/17179869184), by norm_num⟩
  | 7 => ⟨((479900851/17179869184), (94856575/8589934592)), (95/8589934592), by norm_num⟩
  | 8 => ⟨((-353259693/34359738368), (-279299397/68719476736)), (281/68719476736), by norm_num⟩
  | 9 => ⟨((924579209/274877906944), (91375559/68719476736)), (369/274877906944), by norm_num⟩
  | 10 => ⟨((-1088946825/1099511627776), (-107619903/274877906944)), (109/274877906944), by norm_num⟩
  | 11 => ⟨((1165940901/4398046511104), (460916709/4398046511104)), (469/4398046511104), by norm_num⟩
  | 12 => ⟨((-1144347279/17592186044416), (-452380375/17592186044416)), (231/8796093022208), by norm_num⟩
  | 13 => ⟨((1036757149/70368744177664), (204924063/35184372088832)), (105/17592186044416), by norm_num⟩
  | 14 => ⟨((-872190903/281474976710656), (-86198057/70368744177664)), (355/281474976710656), by norm_num⟩
  | 15 => ⟨((1369660209/2251799813685248), (270725247/1125899906842624)), (559/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1008220227/9007199254740992), (-398566985/9007199254740992)), (413/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-3601889926255/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778042865397469/633825300114114700748351602688), (-4259378501029/633825300114114700748351602688)), (92619/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944462442169613/19807040628566084398385987584), (-2395362200115/19807040628566084398385987584)), (3257/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((944324227890071/1237940039285380274899124224), (-1272205941115/618970019642690137449562112)), (110769/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770314209242197/154742504910672534362390528), (-2543669007455/77371252455336267181195264)), (221609/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548731200586175/9671406556917033397649408), (-4767801154575/9671406556917033397649408)), (207833/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157258588874271/75557863725914323419136), (-2085124098249/302231454903657293676544)), (22741/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886621104572583/75557863725914323419136), (-1693423953133/18889465931478580854784)), (147887/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296660387117665/4722366482869645213696), (-5077684935131/4722366482869645213696)), (221953/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810119000764001/295147905179352825856), (-1744403677685/147573952589676412928)), (305385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910979942352471/36893488147419103232), (-4357859105491/36893488147419103232)), (382031/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820949934192607/9223372036854775808), (-4898262507085/4611686018427387904)), (430197/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796097419911683/576460752303423488), (-9785709705927/1152921504606846976)), (53839/144115188075855872), by norm_num⟩
  | 5 => ⟨((596504791406423/72057594037927936), (-8550338616789/144115188075855872)), (188727/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489272592900961/36028797018963968), (-12801217797887/36028797018963968)), (283671/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486287681038389/9007199254740992), (-15959069956425/9007199254740992)), (711215/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110983214231941/2251799813685248), (-7947751224857/1125899906842624)), (714277/2251799813685248), by norm_num⟩
  | 1 => ⟨((275878526833073/281474976710656), (-23684723454603/1125899906842624)), (539545/562949953421312), by norm_num⟩
  | 0 => ⟨((540544077186295/562949953421312), (-46737659611241/1125899906842624)), (1094507/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((540544077186295/562949953421312), (-46737659611241/1125899906842624)), (4175212862254905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1036119802132515/1125899906842624), (-179509847586739/2251799813685248)), (8771035/2251799813685248), by norm_num⟩
  | 2 => ⟨((1892687425499361/2251799813685248), (-20649449679323/140737488355328)), (17541679/2251799813685248), by norm_num⟩
  | 3 => ⟨((1542369498340223/2251799813685248), (-138850544401011/562949953421312)), (34635879/2251799813685248), by norm_num⟩
  | 4 => ⟨((919456551128553/2251799813685248), (-760845056334085/2251799813685248)), (64533417/2251799813685248), by norm_num⟩
  | 5 => ⟨((236713004455777/4503599627370496), (-1242675245265707/4503599627370496)), (48155083/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1321794867974639/18014398509481984), (-261264246565731/9007199254740992)), (506191133/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-327840865/4194304)), (1/8388608), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1334207931/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-375798861952881/9007199254740992), (1133230347281429/18014398509481984)), (246881479/9007199254740992), by norm_num⟩
  | 1 => ⟨((268409915/2147483648), (-101174555/536870912)), (355/4294967296), by norm_num⟩
  | 2 => ⟨((-804084245/4294967296), (1212367519/4294967296)), (267/2147483648), by norm_num⟩
  | 3 => ⟨((802940375/4294967296), (-1210642835/4294967296)), (67/536870912), by norm_num⟩
  | 4 => ⟨((-601348599/4294967296), (906690453/4294967296)), (403/4294967296), by norm_num⟩
  | 5 => ⟨((360295881/4294967296), (-1086480741/8589934592)), (485/8589934592), by norm_num⟩
  | 6 => ⟨((-359783333/8589934592), (271233785/4294967296)), (243/8589934592), by norm_num⟩
  | 7 => ⟨((76986753/4294967296), (-464310745/17179869184)), (209/17179869184), by norm_num⟩
  | 8 => ⟨((-461263401/68719476736), (347737671/34359738368)), (315/68719476736), by norm_num⟩
  | 9 => ⟨((614142959/274877906944), (-925981301/274877906944)), (421/274877906944), by norm_num⟩
  | 10 => ⟨((-735923153/1099511627776), (1109596827/1099511627776)), (507/1099511627776), by norm_num⟩
  | 11 => ⟨((400841589/2199023255552), (-604373641/2199023255552)), (277/2199023255552), by norm_num⟩
  | 12 => ⟨((-800542723/17592186044416), (301756937/4398046511104)), (555/17592186044416), by norm_num⟩
  | 13 => ⟨((184477821/17592186044416), (-1112594455/70368744177664)), (257/35184372088832), by norm_num⟩
  | 14 => ⟨((-315797807/140737488355328), (238073937/70368744177664)), (221/140737488355328), by norm_num⟩
  | 15 => ⟨((504557697/1125899906842624), (-190188207/281474976710656)), (355/1125899906842624), by norm_num⟩
  | 16 => ⟨((-47234993/562949953421312), (284876475/2251799813685248)), (267/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1404488392961/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777978531191197/633825300114114700748351602688), (1660742185541/316912650057057350374175801344)), (92527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888852735890075/39614081257132168796771975168), (3735825140757/39614081257132168796771975168)), (208229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944286049400491/1237940039285380274899124224), (3968267214261/2475880078570760549798248448)), (221291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442559547573623/38685626227668133590597632), (991772428693/38685626227668133590597632)), (110673/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548660291717299/9671406556917033397649408), (1858947947717/4835703278458516698824704)), (207571/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629003512165919/302231454903657293676544), (1625954312385/302231454903657293676544)), (90841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886521535487343/75557863725914323419136), (5282008143469/75557863725914323419136)), (295343/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648293148723711/2361183241434822606848), (3959456567297/4722366482869645213696)), (221603/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810068540579969/295147905179352825856), (1360230995709/147573952589676412928)), (304859/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821835161574217/73786976294838206464), (1699041191743/18446744073709551616)), (95327/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820811579898207/9223372036854775808), (7638828669565/9223372036854775808)), (429293/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592058929543261/1152921504606846976), (3815132535693/576460752303423488)), (429695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149111675492387/18014398509481984), (6666857878657/144115188075855872)), (94109/36028797018963968), by norm_num⟩
  | 4 => ⟨((186137974077577/4503599627370496), (155954119663/562949953421312)), (70695/4503599627370496), by norm_num⟩
  | 3 => ⟨((743043105540131/4503599627370496), (6221372579335/4503599627370496)), (708539/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221591925417931/4503599627370496), (24784961329393/4503599627370496)), (710927/2251799813685248), by norm_num⟩
  | 1 => ⟨((275817126713843/281474976710656), (18463451748195/1125899906842624)), (1072379/1125899906842624), by norm_num⟩
  | 0 => ⟨((270184112754055/281474976710656), (36428174724667/1125899906842624)), (135551/70368744177664), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((270184112754055/281474976710656), (36428174724667/1125899906842624)), (517086029321169831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1036206022889775/1125899906842624), (139867695270849/2251799813685248)), (4303979/1125899906842624), by norm_num⟩
  | 2 => ⟨((1898627351032101/2251799813685248), (257450502245443/2251799813685248)), (8456885/1125899906842624), by norm_num⟩
  | 3 => ⟨((1571411914805029/2251799813685248), (217071944908009/1125899906842624)), (32389563/2251799813685248), by norm_num⟩
  | 4 => ⟨((1012902867770393/2251799813685248), (302966043895433/1125899906842624)), (57695251/2251799813685248), by norm_num⟩
  | 5 => ⟨((585148395979907/4503599627370496), (1090239630836489/4503599627370496)), (165910115/4503599627370496), by norm_num⟩
  | 6 => ⟨((-375798861952881/9007199254740992), (1133230347281429/18014398509481984)), (246881479/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1334207931/16777216)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1355937585/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((849420614393955/18014398509481984), (247277308720481/4503599627370496)), (312585307/18014398509481984), by norm_num⟩
  | 1 => ⟨((-154142387/1073741824), (-358982713/2147483648)), (229/4294967296), by norm_num⟩
  | 2 => ⟨((117322489/536870912), (1092930925/4294967296)), (351/4294967296), by norm_num⟩
  | 3 => ⟨((-952509201/4294967296), (-277287727/1073741824)), (179/2147483648), by norm_num⟩
  | 4 => ⟨((724983909/4294967296), (844208707/4294967296)), (137/2147483648), by norm_num⟩
  | 5 => ⟨((-882891911/8589934592), (-257021235/2147483648)), (21/536870912), by norm_num⟩
  | 6 => ⟨((895994745/17179869184), (260835639/4294967296)), (343/17179869184), by norm_num⟩
  | 7 => ⟨((-779393173/34359738368), (-28361427/1073741824)), (75/8589934592), by norm_num⟩
  | 8 => ⟨((593220001/68719476736), (690776007/68719476736)), (115/34359738368), by norm_num⟩
  | 9 => ⟨((-802698491/274877906944), (-934703579/274877906944)), (313/274877906944), by norm_num⟩
  | 10 => ⟨((977533427/1099511627776), (142286301/137438953472)), (383/1099511627776), by norm_num⟩
  | 11 => ⟨((-541113173/2199023255552), (-630100125/2199023255552)), (107/1099511627776), by norm_num⟩
  | 12 => ⟨((137285933/2199023255552), (639451323/8796093022208)), (219/8796093022208), by norm_num⟩
  | 13 => ⟨((-514424743/35184372088832), (-599022739/35184372088832)), (207/35184372088832), by norm_num⟩
  | 14 => ⟨((447479335/140737488355328), (1042136097/281474976710656)), (181/140737488355328), by norm_num⟩
  | 15 => ⟨((-726592467/1125899906842624), (-846081795/1125899906842624)), (37/140737488355328), by norm_num⟩
  | 16 => ⟨((553031767/4503599627370496), (1257771/8796093022208)), (227/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (1121849406535/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222239836003895/79228162514264337593543950336), (1326442527567/633825300114114700748351602688)), (184661/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888785701921377/39614081257132168796771975168), (1491909578879/39614081257132168796771975168)), (103881/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888501260254839/2475880078570760549798248448), (1584729499113/2475880078570760549798248448)), (110383/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27658871632287/2417851639229258349412352), (396063061829/38685626227668133590597632)), (55197/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548594745662673/9671406556917033397649408), (1484729598047/9671406556917033397649408)), (51753/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314487532636301/151115727451828646838272), (649315867657/302231454903657293676544)), (181159/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886429942884655/75557863725914323419136), (2109327045845/75557863725914323419136)), (147213/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296518354476231/4722366482869645213696), (395291229907/1180591620717411303424)), (110429/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620044879148461/590295810358705651712), (2172753300165/590295810358705651712)), (151871/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821721735654231/73786976294838206464), (678480116205/18446744073709551616)), (94943/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820686482815031/9223372036854775808), (47662248773/144115188075855872)), (106843/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397984239894857/288230376151711744), (3046916907141/1152921504606846976)), (213767/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192790188995417/144115188075855872), (2662157035755/144115188075855872)), (187137/72057594037927936), by norm_num⟩
  | 4 => ⟨((5816234237155/140737488355328), (3985457852773/36028797018963968)), (561775/36028797018963968), by norm_num⟩
  | 3 => ⟨((742956807427201/4503599627370496), (2484120062443/4503599627370496)), (702859/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110641546320661/2251799813685248), (1236981071949/562949953421312)), (1407641/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206163944353307/2251799813685248), (3685648683743/562949953421312)), (2116297/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080541593865301/1125899906842624), (3635359325365/281474976710656)), (4252071/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080541593865301/1125899906842624), (3635359325365/281474976710656)), (16220363625533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1036822790000767/1125899906842624), (55822467852849/2251799813685248)), (8271377/2251799813685248), by norm_num⟩
  | 2 => ⟨((477050603857911/562949953421312), (102811993343577/2251799813685248)), (7822025/1125899906842624), by norm_num⟩
  | 3 => ⟨((403084915699279/562949953421312), (21781031870733/281474976710656)), (13971229/1125899906842624), by norm_num⟩
  | 4 => ⟨((1140988074630509/2251799813685248), (249531393463307/2251799813685248)), (44339341/2251799813685248), by norm_num⟩
  | 5 => ⟨((550487597783665/2251799813685248), (252875359929631/2251799813685248)), (109520781/4503599627370496), by norm_num⟩
  | 6 => ⟨((849420614393955/18014398509481984), (247277308720481/4503599627370496)), (312585307/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1355937585/16777216)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile038Terms2
