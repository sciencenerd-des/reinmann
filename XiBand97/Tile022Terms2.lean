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
namespace Reinmann.XiBand97.Tile022Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28609/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28609/1280))
  have he : value ((69/80), (28609/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-519838045/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((536287284288347/9007199254740992), (312934927872153/4503599627370496)), (1539023/140737488355328), by norm_num⟩
  | 1 => ⟨((-354505557/2147483648), (-827445843/4294967296)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((982898109/4294967296), (573541753/2147483648)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-908390737/4294967296), (-132516283/536870912)), (87/2147483648), by norm_num⟩
  | 4 => ⟨((314824239/2147483648), (11481661/67108864)), (123/4294967296), by norm_num⟩
  | 5 => ⟨((-174575627/2147483648), (-814948449/8589934592)), (139/8589934592), by norm_num⟩
  | 6 => ⟨((645368553/17179869184), (753172293/17179869184)), (65/8589934592), by norm_num⟩
  | 7 => ⟨((-511240449/34359738368), (-74579893/4294967296)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((88591219/17179869184), (827117481/137438953472)), (147/137438953472), by norm_num⟩
  | 9 => ⟨((-873340497/549755813888), (-254806289/137438953472)), (23/68719476736), by norm_num⟩
  | 10 => ⟨((968565605/2199023255552), (1130356869/2199023255552)), (103/1099511627776), by norm_num⟩
  | 11 => ⟨((-976521481/8796093022208), (-71227607/549755813888)), (105/4398046511104), by norm_num⟩
  | 12 => ⟨((451248741/17592186044416), (526626293/17592186044416)), (49/8796093022208), by norm_num⟩
  | 13 => ⟨((-192481103/35184372088832), (-224633557/35184372088832)), (85/70368744177664), by norm_num⟩
  | 14 => ⟨((609909641/562949953421312), (88973781/70368744177664)), (137/562949953421312), by norm_num⟩
  | 15 => ⟨((-225470479/1125899906842624), (-526267097/2251799813685248)), (205/4503599627370496), by norm_num⟩
  | 16 => ⟨((625136907/18014398509481984), (729561109/18014398509481984)), (9/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1123279861795/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55571249737547/19807040628566084398385987584), (1328648421749/633825300114114700748351602688)), (92331/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889192079602355/39614081257132168796771975168), (1494419155003/39614081257132168796771975168)), (51941/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118058307866175/154742504910672534362390528), (793716558893/1237940039285380274899124224)), (110383/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885299662801039/77371252455336267181195264), (3099604811/302231454903657293676544)), (110395/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774499591637405/4835703278458516698824704), (92959237541/604462909807314587353088)), (103507/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629151940651885/302231454903657293676544), (1300966999069/604462909807314587353088)), (22645/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887004540189577/75557863725914323419136), (1056602449059/37778931862957161709568)), (73607/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296949085844201/4722366482869645213696), (1584145894275/4722366482869645213696)), (55215/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620636782988101/590295810358705651712), (136060621111/36893488147419103232)), (2373/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1822461088118543/73786976294838206464), (1359683844525/36893488147419103232)), (189887/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821517529822641/9223372036854775808), (1528377099795/4611686018427387904)), (213687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796383550899897/576460752303423488), (1526794609969/576460752303423488)), (213767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193515546728805/144115188075855872), (1334167100455/72057594037927936)), (93569/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490041970830349/36028797018963968), (1997699572075/18014398509481984)), (35111/4503599627370496), by norm_num⟩
  | 3 => ⟨((743633787880507/4503599627370496), (1245460978711/2251799813685248)), (351429/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223980400589871/4503599627370496), (9926567643519/4503599627370496)), (703817/4503599627370496), by norm_num⟩
  | 1 => ⟨((276272932960639/281474976710656), (7398691102093/1125899906842624)), (132267/281474976710656), by norm_num⟩
  | 0 => ⟨((1084508503463799/1125899906842624), (29226868162601/2251799813685248)), (1062985/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084508503463799/1125899906842624), (29226868162601/2251799813685248)), (4054965977195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522224548773327/562949953421312), (14076201116689/562949953421312)), (2075407/1125899906842624), by norm_num⟩
  | 2 => ⟨((1936373478653959/2251799813685248), (104463108763831/2251799813685248)), (3954321/1125899906842624), by norm_num⟩
  | 3 => ⟨((103767819552065/140737488355328), (179660369521907/2251799813685248)), (14335419/2251799813685248), by norm_num⟩
  | 4 => ⟨((604909191074981/1125899906842624), (264932464307415/2251799813685248)), (23426941/2251799813685248), by norm_num⟩
  | 5 => ⟨((1237651143476583/4503599627370496), (71169773485069/562949953421312)), (30685589/2251799813685248), by norm_num⟩
  | 6 => ⟨((536287284288347/9007199254740992), (312934927872153/4503599627370496)), (1539023/140737488355328), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-519838045/8388608)), (1/16777216), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-531204673/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((689187737654833/9007199254740992), (-369979238049481/9007199254740992)), (147631517/9007199254740992), by norm_num⟩
  | 1 => ⟨((-465539907/2147483648), (499835069/4294967296)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((1318973877/4294967296), (-354034847/2147483648)), (287/4294967296), by norm_num⟩
  | 3 => ⟨((-311411199/1073741824), (668704169/4294967296)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((882294365/4294967296), (-236822697/2147483648)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((-999891267/8589934592), (134193845/2147483648)), (7/268435456), by norm_num⟩
  | 6 => ⟨((14754715/268435456), (-7920829/268435456)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-764402385/34359738368), (51294625/4294967296)), (175/34359738368), by norm_num⟩
  | 8 => ⟨((1082857519/137438953472), (-18166077/4294967296)), (125/68719476736), by norm_num⟩
  | 9 => ⟨((-681770305/274877906944), (731994621/549755813888)), (317/549755813888), by norm_num⟩
  | 10 => ⟨((386320145/549755813888), (-207389693/549755813888)), (91/549755813888), by norm_num⟩
  | 11 => ⟨((-49751245/274877906944), (53416295/549755813888)), (189/4398046511104), by norm_num⟩
  | 12 => ⟨((751764753/17592186044416), (-403572693/17592186044416)), (45/4398046511104), by norm_num⟩
  | 13 => ⟨((-1310713803/140737488355328), (703635409/140737488355328)), (79/35184372088832), by norm_num⟩
  | 14 => ⟨((132626137/70368744177664), (-284792747/281474976710656)), (129/281474976710656), by norm_num⟩
  | 15 => ⟨((-100202171/281474976710656), (430335259/2251799813685248)), (197/2251799813685248), by norm_num⟩
  | 16 => ⟨((17743383/281474976710656), (-609615799/18014398509481984)), (281/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-160442221931/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889100033750495/316912650057057350374175801344), (-379518776803/316912650057057350374175801344)), (184549/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944551109678193/19807040628566084398385987584), (-853736625905/39614081257132168796771975168)), (51907/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888837519834525/2475880078570760549798248448), (-226717287859/618970019642690137449562112)), (220617/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770503998810343/154742504910672534362390528), (-113326875265/19342813113834066795298816)), (220629/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454949270603/4835703278458516698824704), (-849681630317/9671406556917033397649408)), (206853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258225841238179/604462909807314587353088), (-92900200539/75557863725914323419136)), (90505/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471719470651079/18889465931478580854784), (-603598464073/37778931862957161709568)), (147083/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324213557591187/1180591620717411303424), (-904955464767/4722366482869645213696)), (220647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620506580253843/590295810358705651712), (-621797791731/295147905179352825856)), (303425/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822298669627201/73786976294838206464), (-48544312101/2305843009213693952)), (189667/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113833454306059/576460752303423488), (-873058161757/4611686018427387904)), (426825/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592585414751407/1152921504606846976), (-1744269578321/1152921504606846976)), (213459/576460752303423488), by norm_num⟩
  | 5 => ⟨((149169651855385/18014398509481984), (-381040223833/36028797018963968)), (186829/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489805758245195/36028797018963968), (-570524467359/9007199254740992)), (560697/36028797018963968), by norm_num⟩
  | 3 => ⟨((743487275876407/4503599627370496), (-2845385854109/9007199254740992)), (87655/1125899906842624), by norm_num⟩
  | 2 => ⟨((555850262003949/1125899906842624), (-2834560262057/2251799813685248)), (701795/2251799813685248), by norm_num⟩
  | 1 => ⟨((552332767439867/562949953421312), (-8449756209831/2251799813685248)), (2108183/2251799813685248), by norm_num⟩
  | 0 => ⟨((541844534947815/562949953421312), (-8342515054669/1125899906842624)), (4227663/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541844534947815/562949953421312), (-8342515054669/1125899906842624)), (16127254494673918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085997868046651/2251799813685248), (-32118991484909/2251799813685248)), (8200981/2251799813685248), by norm_num⟩
  | 2 => ⟨((120746620365685/140737488355328), (-14877021339583/562949953421312)), (15428225/2251799813685248), by norm_num⟩
  | 3 => ⟨((51748520027277/70368744177664), (-102110678191299/2251799813685248)), (852779/70368744177664), by norm_num⟩
  | 4 => ⟨((606570917541377/1125899906842624), (-18772810773915/281474976710656)), (21305475/1125899906842624), by norm_num⟩
  | 5 => ⟨((321777789495791/1125899906842624), (-323639172164697/4503599627370496)), (103193091/4503599627370496), by norm_num⟩
  | 6 => ⟨((689187737654833/9007199254740992), (-369979238049481/9007199254740992)), (147631517/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-531204673/8388608)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1083842831/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-147502127362699/9007199254740992), (-1459667698429675/18014398509481984)), (508081519/18014398509481984), by norm_num⟩
  | 1 => ⟨((203292839/4294967296), (1005883763/4294967296)), (11/134217728), by norm_num⟩
  | 2 => ⟨((-73448985/1073741824), (-726844505/2147483648)), (511/4294967296), by norm_num⟩
  | 3 => ⟨((283059829/4294967296), (350141805/1073741824)), (247/2147483648), by norm_num⟩
  | 4 => ⟨((-102268517/2147483648), (-1012039985/4294967296)), (359/4294967296), by norm_num⟩
  | 5 => ⟨((236475227/8589934592), (292517179/2147483648)), (417/8589934592), by norm_num⟩
  | 6 => ⟨((-227833773/17179869184), (-1127311191/17179869184)), (101/4294967296), by norm_num⟩
  | 7 => ⟨((188149801/34359738368), (465478347/17179869184)), (335/34359738368), by norm_num⟩
  | 8 => ⟨((-67977859/34359738368), (-336351367/34359738368)), (243/68719476736), by norm_num⟩
  | 9 => ⟨((87325015/137438953472), (1728320875/549755813888)), (313/274877906944), by norm_num⟩
  | 10 => ⟨((-100960703/549755813888), (-999097969/1099511627776)), (91/274877906944), by norm_num⟩
  | 11 => ⟨((106114169/2199023255552), (1050096201/4398046511104)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((-51118233/4398046511104), (-1011722801/17592186044416)), (93/4398046511104), by norm_num⟩
  | 13 => ⟨((45461753/17592186044416), (899770773/70368744177664)), (333/70368744177664), by norm_num⟩
  | 14 => ⟨((-150172991/281474976710656), (-11610143/4398046511104)), (69/70368744177664), by norm_num⟩
  | 15 => ⟨((57874103/562949953421312), (143179219/281474976710656)), (107/562949953421312), by norm_num⟩
  | 16 => ⟨((-167277673/9007199254740992), (-413841171/4503599627370496)), (621/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-2305901201067/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889060220545805/316912650057057350374175801344), (-1363515081867/316912650057057350374175801344)), (184937/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472253113733913/9903520314283042199192993792), (-766810330967/9903520314283042199192993792)), (208089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888741898282935/2475880078570760549798248448), (-814528703083/618970019642690137449562112)), (221135/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221301012482215/19342813113834066795298816), (-3257182409623/154742504910672534362390528)), (221179/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548819698770709/9671406556917033397649408), (-1526309073013/4835703278458516698824704)), (51851/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314536655550621/151115727451828646838272), (-667512717235/151115727451828646838272)), (90763/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235843575067813/9444732965739290427392), (-4336977147831/75557863725914323419136)), (295069/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648378393572439/2361183241434822606848), (-812777509515/1180591620717411303424)), (221381/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620371814163989/590295810358705651712), (-4467640624915/590295810358705651712)), (152263/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227766130171099/9223372036854775808), (-5580599730817/73786976294838206464)), (380849/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821142830466825/9223372036854775808), (-3136373003919/4611686018427387904)), (428719/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592390972514253/1152921504606846976), (-6265966149879/1152921504606846976)), (429049/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193184829769363/144115188075855872), (-342193830637/9007199254740992)), (187895/72057594037927936), by norm_num⟩
  | 4 => ⟨((372385674947175/9007199254740992), (-8197434358981/36028797018963968)), (564429/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486637921738341/9007199254740992), (-10220208504585/9007199254740992)), (88355/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111352252443273/2251799813685248), (-159069130417/35184372088832)), (1417601/4503599627370496), by norm_num⟩
  | 1 => ⟨((552057131878039/562949953421312), (-7585749681183/562949953421312)), (2136233/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082472505706789/1125899906842624), (-29948385181549/1125899906842624)), (1077991/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082472505706789/1125899906842624), (-29948385181549/1125899906842624)), (4112209322215843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((519961771344125/562949953421312), (-115172950463259/2251799813685248)), (8520685/2251799813685248), by norm_num⟩
  | 2 => ⟨((478783578342713/562949953421312), (-106378073165923/1125899906842624)), (4152917/562949953421312), by norm_num⟩
  | 3 => ⟨((804350866012375/1125899906842624), (-361894155727665/2251799813685248)), (31395163/2251799813685248), by norm_num⟩
  | 4 => ⟨((545553354196391/1125899906842624), (-517079494891641/2251799813685248)), (54949095/2251799813685248), by norm_num⟩
  | 5 => ⟨((204978843912315/1125899906842624), (-501100410631335/2251799813685248)), (156973773/4503599627370496), by norm_num⟩
  | 6 => ⟨((-147502127362699/9007199254740992), (-1459667698429675/18014398509481984)), (508081519/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1083842831/16777216)), (1/8388608), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1104117167/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-87656552764145/1125899906842624), (-230559886059985/18014398509481984)), (242071239/18014398509481984), by norm_num⟩
  | 1 => ⟨((246142741/1073741824), (161855105/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-724752281/2147483648), (-7446445/134217728)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((355664811/1073741824), (116936549/2147483648)), (63/1073741824), by norm_num⟩
  | 4 => ⟨((-1047233333/4294967296), (-86078133/2147483648)), (187/4294967296), by norm_num⟩
  | 5 => ⟨((616702929/4294967296), (25345181/1073741824)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-605281381/8589934592), (-199006237/17179869184)), (55/4294967296), by norm_num⟩
  | 7 => ⟨((254602013/8589934592), (167417635/34359738368)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((-749660091/68719476736), (-246475505/137438953472)), (277/137438953472), by norm_num⟩
  | 9 => ⟨((981034841/274877906944), (161273797/274877906944)), (183/274877906944), by norm_num⟩
  | 10 => ⟨((-577719445/549755813888), (-94972171/549755813888)), (217/1099511627776), by norm_num⟩
  | 11 => ⟨((1237134293/4398046511104), (203374373/4398046511104)), (117/2199023255552), by norm_num⟩
  | 12 => ⟨((-1214222145/17592186044416), (-99803905/8796093022208)), (29/2199023255552), by norm_num⟩
  | 13 => ⟨((550031233/35184372088832), (5651279/2199023255552)), (53/17592186044416), by norm_num⟩
  | 14 => ⟨((-462723829/140737488355328), (-19016967/35184372088832)), (45/70368744177664), by norm_num⟩
  | 15 => ⟨((363323221/562949953421312), (238909009/2251799813685248)), (285/2251799813685248), by norm_num⟩
  | 16 => ⟨((-534891527/4503599627370496), (-87931625/4503599627370496)), (53/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-1940017605017/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778041305233859/633825300114114700748351602688), (-4588296393065/633825300114114700748351602688)), (23163/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888923043252825/39614081257132168796771975168), (-5160669367655/39614081257132168796771975168)), (104263/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944323192625217/1237940039285380274899124224), (-5481787766661/2475880078570760549798248448)), (110813/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770312010161713/154742504910672534362390528), (-5480186619085/154742504910672534362390528)), (110851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548729002469995/9671406556917033397649408), (-5135974098627/9671406556917033397649408)), (103963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39314582852641/18889465931478580854784), (-4492276886541/604462909807314587353088)), (711/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1886617502128521/75557863725914323419136), (-7296762462529/75557863725914323419136)), (147963/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648328731025487/2361183241434822606848), (-5469783669087/4722366482869645213696)), (55519/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810116808642467/295147905179352825856), (-1879105844907/147573952589676412928)), (152785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821953861823037/73786976294838206464), (-586796144947/4611686018427387904)), (95571/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820942413763861/9223372036854775808), (-5276498868061/4611686018427387904)), (215257/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592186390571913/1152921504606846976), (-10541338582537/1152921504606846976)), (215535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596500573794101/72057594037927936), (-9210564258549/144115188075855872)), (94453/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489257862785691/36028797018963968), (-1723707034283/4503599627370496)), (283985/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486265648839963/9007199254740992), (-17191291454701/9007199254740992)), (178039/4503599627370496), by norm_num⟩
  | 2 => ⟨((277738946001575/562949953421312), (-8561365447385/1125899906842624)), (357727/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103459576215519/1125899906842624), (-3189134102409/140737488355328)), (270363/562949953421312), by norm_num⟩
  | 0 => ⟨((540463101279169/562949953421312), (-6293040517955/140737488355328)), (549031/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((540463101279169/562949953421312), (-6293040517955/140737488355328)), (2094387056590843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1035497824733963/1125899906842624), (-24166668274073/281474976710656)), (2206601/1125899906842624), by norm_num⟩
  | 2 => ⟨((1888109756260661/2251799813685248), (-355619994662531/2251799813685248)), (2218879/562949953421312), by norm_num⟩
  | 3 => ⟨((1526997582194285/2251799813685248), (-298183514077483/1125899906842624)), (17687417/2251799813685248), by norm_num⟩
  | 4 => ⟨((438775234758283/1125899906842624), (-808820575042745/2251799813685248)), (8339293/562949953421312), by norm_num⟩
  | 5 => ⟨((51471761935437/2251799813685248), (-1260824112462835/4503599627370496)), (49962319/2251799813685248), by norm_num⟩
  | 6 => ⟨((-87656552764145/1125899906842624), (-230559886059985/18014398509481984)), (242071239/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1104117167/16777216)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-561675663/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-753480595157705/18014398509481984), (1131979306922463/18014398509481984)), (246917519/18014398509481984), by norm_num⟩
  | 1 => ⟨((67270581/536870912), (-808502899/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-403049301/2147483648), (605514557/2147483648)), (269/4294967296), by norm_num⟩
  | 3 => ⟨((402475933/2147483648), (-604653167/2147483648)), (271/4294967296), by norm_num⟩
  | 4 => ⟨((-602855071/4294967296), (905689503/4294967296)), (205/4294967296), by norm_num⟩
  | 5 => ⟨((722396957/8589934592), (-542640655/4294967296)), (31/1073741824), by norm_num⟩
  | 6 => ⟨((-721369293/17179869184), (135467177/2147483648)), (125/8589934592), by norm_num⟩
  | 7 => ⟨((617436935/34359738368), (-463798165/17179869184)), (27/4294967296), by norm_num⟩
  | 8 => ⟨((-231209469/34359738368), (347353783/34359738368)), (41/17179869184), by norm_num⟩
  | 9 => ⟨((615681483/274877906944), (-57809941/17179869184)), (55/68719476736), by norm_num⟩
  | 10 => ⟨((-184441689/274877906944), (554185939/549755813888)), (133/549755813888), by norm_num⟩
  | 11 => ⟨((803691521/4398046511104), (-1207412875/4398046511104)), (73/1099511627776), by norm_num⟩
  | 12 => ⟨((-802548209/17592186044416), (1205695239/17592186044416)), (147/8796093022208), by norm_num⟩
  | 13 => ⟨((184939967/17592186044416), (-1111366197/70368744177664)), (273/70368744177664), by norm_num⟩
  | 14 => ⟨((-158294465/70368744177664), (951244453/281474976710656)), (59/70368744177664), by norm_num⟩
  | 15 => ⟨((505821693/1125899906842624), (-759912989/1125899906842624)), (95/562949953421312), by norm_num⟩
  | 16 => ⟨((-757653185/9007199254740992), (1138247933/9007199254740992)), (287/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (2811142280369/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888989261033573/316912650057057350374175801344), (831011241881/158456325028528675187087900672)), (5783/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472213181281083/9903520314283042199192993792), (3738705141271/39614081257132168796771975168)), (104115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944286043346785/1237940039285380274899124224), (1985663202723/1237940039285380274899124224)), (55323/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442559544358865/38685626227668133590597632), (3970147995381/154742504910672534362390528)), (55337/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774330139431997/4835703278458516698824704), (3720762066139/9671406556917033397649408)), (51893/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314501753071987/151115727451828646838272), (3254415556905/604462909807314587353088)), (45421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943260757211347/37778931862957161709568), (2643040047459/37778931862957161709568)), (147673/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648293140171895/2361183241434822606848), (3962508944559/4722366482869645213696)), (110803/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25314641492569/9223372036854775808), (2722559212167/295147905179352825856)), (152431/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821835126357735/73786976294838206464), (6801403953939/73786976294838206464)), (190655/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820811535926105/9223372036854775808), (1911179360551/2305843009213693952)), (26831/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796029440070637/576460752303423488), (7636147205479/1152921504606846976)), (214849/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596446677310149/72057594037927936), (833999660105/18014398509481984)), (47055/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489103706499635/36028797018963968), (4994378919741/18014398509481984)), (282783/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486086082271975/9007199254740992), (6226168394683/4503599627370496)), (177137/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221591604700447/4503599627370496), (24804066377559/4503599627370496)), (710937/4503599627370496), by norm_num⟩
  | 1 => ⟨((551634094043463/562949953421312), (4619420724453/281474976710656)), (536199/1125899906842624), by norm_num⟩
  | 0 => ⟨((540367752207717/562949953421312), (18228123633705/562949953421312)), (271109/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540367752207717/562949953421312), (18228123633705/562949953421312)), (1034198762060069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2072404776745991/2251799813685248), (17496919815069/281474976710656)), (4304195/2251799813685248), by norm_num⟩
  | 2 => ⟨((1898600591270957/2251799813685248), (32205971403601/281474976710656)), (4228847/1125899906842624), by norm_num⟩
  | 3 => ⟨((1571321664408767/2251799813685248), (434470424787977/2251799813685248)), (4049403/562949953421312), by norm_num⟩
  | 4 => ⟨((506325475552159/1125899906842624), (606353004263685/2251799813685248)), (28856067/2251799813685248), by norm_num⟩
  | 5 => ⟨((584241973016549/4503599627370496), (1090725636872103/4503599627370496)), (41493997/2251799813685248), by norm_num⟩
  | 6 => ⟨((-753480595157705/18014398509481984), (1131979306922463/18014398509481984)), (246917519/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-561675663/8388608)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1141646851/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((157185066221373/4503599627370496), (1142163796483607/18014398509481984)), (348091437/18014398509481984), by norm_num⟩
  | 1 => ⟨((-456384145/4294967296), (-414531625/2147483648)), (127/2147483648), by norm_num⟩
  | 2 => ⟨((694735885/4294967296), (631025417/2147483648)), (389/4294967296), by norm_num⟩
  | 3 => ⟨((-352523165/2147483648), (-640390347/2147483648)), (397/4294967296), by norm_num⟩
  | 4 => ⟨((536632343/4294967296), (487420695/2147483648)), (19/268435456), by norm_num⟩
  | 5 => ⟨((-163378921/2147483648), (-593585297/4294967296)), (93/2147483648), by norm_num⟩
  | 6 => ⟨((165803597/4294967296), (602394585/8589934592)), (95/4294967296), by norm_num⟩
  | 7 => ⟨((-72113253/4294967296), (-1048002189/34359738368)), (333/34359738368), by norm_num⟩
  | 8 => ⟨((219550417/34359738368), (797666545/68719476736)), (255/68719476736), by norm_num⟩
  | 9 => ⟨((-148539149/68719476736), (-269834855/68719476736)), (347/274877906944), by norm_num⟩
  | 10 => ⟨((723569235/1099511627776), (1314429233/1099511627776)), (425/1099511627776), by norm_num⟩
  | 11 => ⟨((-400531413/2199023255552), (-363800845/1099511627776)), (237/2199023255552), by norm_num⟩
  | 12 => ⟨((406475625/8796093022208), (369199945/4398046511104)), (121/4398046511104), by norm_num⟩
  | 13 => ⟨((-380776665/35184372088832), (-691715395/35184372088832)), (57/8796093022208), by norm_num⟩
  | 14 => ⟨((331223743/140737488355328), (1203396023/281474976710656)), (399/281474976710656), by norm_num⟩
  | 15 => ⟨((-134455749/281474976710656), (-488502159/562949953421312)), (163/562949953421312), by norm_num⟩
  | 16 => ⟨((409353545/4503599627370496), (185906973/1125899906842624)), (125/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (347661632687/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777918181722831/633825300114114700748351602688), (822130264745/316912650057057350374175801344)), (46181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944392552287651/19807040628566084398385987584), (462343313593/9903520314283042199192993792)), (51959/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944250294232439/1237940039285380274899124224), (982216449971/1237940039285380274899124224)), (110425/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885083535488155/77371252455336267181195264), (1963841220389/154742504910672534362390528)), (220877/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774297016247511/4835703278458516698824704), (460118180771/2417851639229258349412352)), (207101/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78621841393307/37778931862957161709568), (201223185007/75557863725914323419136)), (181243/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235803596765939/9444732965739290427392), (326840523617/9444732965739290427392)), (73643/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648258702751115/2361183241434822606848), (490003411829/1180591620717411303424)), (220977/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620043456808683/590295810358705651712), (2693346904315/590295810358705651712)), (18995/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821719781757459/73786976294838206464), (3364177706349/73786976294838206464)), (23751/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1820684043171961/9223372036854775808), (3781257305653/9223372036854775808)), (213839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198991777340923/144115188075855872), (472119822663/144115188075855872)), (213939/576460752303423488), by norm_num⟩
  | 5 => ⟨((596393726409861/72057594037927936), (3300008933707/144115188075855872)), (187309/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488951186907713/36028797018963968), (2470184665019/18014398509481984)), (562377/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485906469109791/9007199254740992), (6158619536231/9007199254740992)), (351881/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110632650719735/2251799813685248), (3066713100039/1125899906842624)), (704951/2251799813685248), by norm_num⟩
  | 1 => ⟨((551532145152669/562949953421312), (9137399813611/1125899906842624)), (2120823/2251799813685248), by norm_num⟩
  | 0 => ⟨((540244546025347/562949953421312), (36050599508179/2251799813685248)), (4265669/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540244546025347/562949953421312), (36050599508179/2251799813685248)), (16272235878951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1036621248048871/1125899906842624), (69193148154191/2251799813685248)), (4161915/1125899906842624), by norm_num⟩
  | 2 => ⟨((59584930820951/70368744177664), (127412902621465/2251799813685248)), (15839127/2251799813685248), by norm_num⟩
  | 3 => ⟨((1607309249574125/2251799813685248), (215774462856091/2251799813685248)), (7154023/562949953421312), by norm_num⟩
  | 4 => ⟨((1126602990873283/2251799813685248), (77008686088061/562949953421312)), (46335853/2251799813685248), by norm_num⟩
  | 5 => ⟨((521515673009387/2251799813685248), (616454201960659/4503599627370496)), (59041807/2251799813685248), by norm_num⟩
  | 6 => ⟨((157185066221373/4503599627370496), (1142163796483607/18014398509481984)), (348091437/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1141646851/16777216)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile022Terms2
