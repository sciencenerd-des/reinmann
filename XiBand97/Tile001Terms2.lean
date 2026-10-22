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
namespace Reinmann.XiBand97.Tile001Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (3717/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (3717/256))
  have he : value ((69/80), (3717/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-84424395/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-343799433839635/4503599627370496), (-28403133408853/562949953421312)), (149870585/9007199254740992), by norm_num⟩
  | 1 => ⟨((909056123/4294967296), (600816401/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((-1260219377/4294967296), (-832908389/4294967296)), (35/536870912), by norm_num⟩
  | 3 => ⟨((1164690011/4294967296), (384885401/2147483648)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-807301597/4294967296), (-533564461/4294967296)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((895326121/8589934592), (591741923/8589934592)), (205/8589934592), by norm_num⟩
  | 6 => ⟨((-827457035/17179869184), (-546885661/17179869184)), (191/17179869184), by norm_num⟩
  | 7 => ⟨((655485155/34359738368), (433225433/34359738368)), (153/34359738368), by norm_num⟩
  | 8 => ⟨((-454347687/68719476736), (-600577975/137438953472)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((1119750465/549755813888), (740069209/549755813888)), (133/274877906944), by norm_num⟩
  | 10 => ⟨((-310460751/549755813888), (-820763017/2199023255552)), (297/2199023255552), by norm_num⟩
  | 11 => ⟨((1252043603/8796093022208), (827504831/8796093022208)), (151/4398046511104), by norm_num⟩
  | 12 => ⟨((-1157133991/35184372088832), (-382388427/17592186044416)), (281/35184372088832), by norm_num⟩
  | 13 => ⟨((987155893/140737488355328), (652434363/140737488355328)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((-781993513/562949953421312), (-516837759/562949953421312)), (193/562949953421312), by norm_num⟩
  | 15 => ⟨((144543093/562949953421312), (382127611/2251799813685248)), (9/140737488355328), by norm_num⟩
  | 16 => ⟨((-801517099/18014398509481984), (-66217669/2251799813685248)), (101/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-1665764637035/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444568154149163/158456325028528675187087900672), (-3940630703491/633825300114114700748351602688)), (23147/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889183373452869/39614081257132168796771975168), (-138508460833/1237940039285380274899124224)), (104187/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944461567239919/1237940039285380274899124224), (-4708137041589/2475880078570760549798248448)), (110727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221323615759163/19342813113834066795298816), (-4706842826591/154742504910672534362390528)), (13845/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193623598504003/1208925819614629174706176), (-1102822590089/2417851639229258349412352)), (1623/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629147070157883/302231454903657293676544), (-482313078547/75557863725914323419136)), (90923/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471746875640209/18889465931478580854784), (-3133746850647/37778931862957161709568)), (73907/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296935251298153/4722366482869645213696), (-2349183372829/2361183241434822606848)), (55459/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620616046083427/590295810358705651712), (-807074211759/73786976294838206464)), (152603/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822432599094793/73786976294838206464), (-4032626852931/36893488147419103232)), (47723/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821481954845723/9223372036854775808), (-2266466962825/2305843009213693952)), (6717/288230376151711744), by norm_num⟩
  | 6 => ⟨((796363564911205/576460752303423488), (-4528222820131/576460752303423488)), (215183/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193475637024029/144115188075855872), (-989224774747/18014398509481984)), (188553/144115188075855872), by norm_num⟩
  | 4 => ⟨((744986134388181/18014398509481984), (-5924767226827/18014398509481984)), (141683/18014398509481984), by norm_num⟩
  | 3 => ⟨((92947706379947/562949953421312), (-14774929527193/9007199254740992)), (355149/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111860346107915/2251799813685248), (-14719539628019/2251799813685248)), (89141/562949953421312), by norm_num⟩
  | 1 => ⟨((1104833483086883/1125899906842624), (-21941160053029/1125899906842624)), (538391/1125899906842624), by norm_num⟩
  | 0 => ⟨((270935256610293/281474976710656), (-10832919012123/281474976710656)), (68189/70368744177664), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((270935256610293/281474976710656), (-10832919012123/281474976710656)), (260120392114138581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1041493094649043/1125899906842624), (-166836553739135/2251799813685248)), (4368643/2251799813685248), by norm_num⟩
  | 2 => ⟨((1914467264338087/2251799813685248), (-77164549707455/562949953421312)), (545601/140737488355328), by norm_num⟩
  | 3 => ⟨((396340185395393/562949953421312), (-262419427312309/1125899906842624)), (17236907/2251799813685248), by norm_num⟩
  | 4 => ⟨((993832952655711/2251799813685248), (-369508386456777/1125899906842624)), (16152997/1125899906842624), by norm_num⟩
  | 5 => ⟨((392182417329683/4503599627370496), (-326165415337153/1125899906842624)), (99443003/4503599627370496), by norm_num⟩
  | 6 => ⟨((-343799433839635/4503599627370496), (-28403133408853/562949953421312)), (149870585/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-84424395/2097152)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-690163155/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1496296511867505/18014398509481984), (456677238297623/18014398509481984)), (137123051/9007199254740992), by norm_num⟩
  | 1 => ⟨((505367189/2147483648), (-308481227/4294967296)), (187/4294967296), by norm_num⟩
  | 2 => ⟨((-178976633/536870912), (109249141/1073741824)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((676105313/2147483648), (-412701499/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-957775297/4294967296), (292317849/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((1085432701/8589934592), (-82819883/2147483648)), (13/536870912), by norm_num⟩
  | 6 => ⟨((-1025087471/17179869184), (39107733/2147483648)), (99/8589934592), by norm_num⟩
  | 7 => ⟨((207449393/8589934592), (-126629201/17179869184)), (81/17179869184), by norm_num⟩
  | 8 => ⟨((-1175496777/137438953472), (179383771/68719476736)), (231/137438953472), by norm_num⟩
  | 9 => ⟨((1480192513/549755813888), (-451762217/549755813888)), (293/549755813888), by norm_num⟩
  | 10 => ⟨((-209685059/274877906944), (63996937/274877906944)), (21/137438953472), by norm_num⟩
  | 11 => ⟨((864120011/4398046511104), (-263733783/4398046511104)), (175/4398046511104), by norm_num⟩
  | 12 => ⟨((-408039391/8796093022208), (124535679/8796093022208)), (333/35184372088832), by norm_num⟩
  | 13 => ⟨((1422846335/140737488355328), (-217129937/70368744177664)), (293/140737488355328), by norm_num⟩
  | 14 => ⟨((-1151779207/562949953421312), (87882205/140737488355328)), (239/562949953421312), by norm_num⟩
  | 15 => ⟨((870196325/2251799813685248), (-265588305/2251799813685248)), (91/1125899906842624), by norm_num⟩
  | 16 => ⟨((-38522685/562949953421312), (376234165/18014398509481984)), (65/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (3706408802821/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444547519327343/158456325028528675187087900672), (4383670701447/633825300114114700748351602688)), (11579/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889090427527379/39614081257132168796771975168), (1232639658443/9903520314283042199192993792)), (104239/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29512879034973/38685626227668133590597632), (2618705023407/1237940039285380274899124224)), (55393/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885244956821807/77371252455336267181195264), (1308984546415/38685626227668133590597632)), (55411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774447909655409/4835703278458516698824704), (2453564260441/4835703278458516698824704)), (51967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258212648264201/604462909807314587353088), (268260893235/37778931862957161709568)), (90981/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886854807502627/75557863725914323419136), (6971853065679/75557863725914323419136)), (36979/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296835493653233/4722366482869645213696), (81661354453/73786976294838206464)), (13875/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810239247919463/295147905179352825856), (7182035583677/590295810358705651712)), (152727/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822260087093373/73786976294838206464), (8971301610323/73786976294838206464)), (191063/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821287090994401/9223372036854775808), (630258406305/576460752303423488)), (107579/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796265641830263/576460752303423488), (10073415942953/1152921504606846976)), (215423/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193303169968389/144115188075855872), (2200547277743/36028797018963968)), (94397/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489711373440497/36028797018963968), (13179205352567/36028797018963968)), (70947/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486833361352181/9007199254740992), (1026994860013/562949953421312)), (355783/9007199254740992), by norm_num⟩
  | 2 => ⟨((555762355737839/1125899906842624), (16368880723877/2251799813685248)), (178679/1125899906842624), by norm_num⟩
  | 1 => ⟨((552157965241357/562949953421312), (6099016574121/281474976710656)), (33749/70368744177664), by norm_num⟩
  | 0 => ⟨((270662580014961/281474976710656), (12041286136709/281474976710656)), (1095821/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270662580014961/281474976710656), (12041286136709/281474976710656)), (4180225376609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039001626402993/1125899906842624), (46314960008829/562949953421312)), (550303/281474976710656), by norm_num⟩
  | 2 => ⟨((951189418417175/1125899906842624), (170961267457283/1125899906842624)), (1106209/281474976710656), by norm_num⟩
  | 3 => ⟨((388815004520905/562949953421312), (577730036484625/2251799813685248)), (17640407/2251799813685248), by norm_num⟩
  | 4 => ⟨((231488353907065/562949953421312), (798046452912729/2251799813685248)), (8354831/562949953421312), by norm_num⟩
  | 5 => ⟨((195853632784673/4503599627370496), (82040356608699/281474976710656)), (51172321/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1496296511867505/18014398509481984), (456677238297623/18014398509481984)), (137123051/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-690163155/16777216)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-704086791/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-80071156489911/2251799813685248), (1344369170214505/18014398509481984)), (265693289/18014398509481984), by norm_num⟩
  | 1 => ⟨((110357003/1073741824), (-463214717/2147483648)), (185/4294967296), by norm_num⟩
  | 2 => ⟨((-318972765/2147483648), (83678921/268435456)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((19207289/134217728), (-644968507/2147483648)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-444129645/4294967296), (932099379/4294967296)), (3/67108864), by norm_num⟩
  | 5 => ⟨((513479913/8589934592), (-67352843/536870912)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-247357973/8589934592), (1038265361/17179869184)), (109/8589934592), by norm_num⟩
  | 7 => ⟨((408546571/34359738368), (-428710411/17179869184)), (91/17179869184), by norm_num⟩
  | 8 => ⟨((-590425735/137438953472), (1239132465/137438953472)), (133/68719476736), by norm_num⟩
  | 9 => ⟨((47404163/34359738368), (-397950387/137438953472)), (173/274877906944), by norm_num⟩
  | 10 => ⟨((-438450093/1099511627776), (14377807/17179869184)), (101/549755813888), by norm_num⟩
  | 11 => ⟨((115207615/1099511627776), (-60446847/274877906944)), (107/2199023255552), by norm_num⟩
  | 12 => ⟨((-443990449/17592186044416), (465903625/8796093022208)), (13/1099511627776), by norm_num⟩
  | 13 => ⟨((394860755/70368744177664), (-828698265/70368744177664)), (187/70368744177664), by norm_num⟩
  | 14 => ⟨((-326084107/281474976710656), (1368712035/562949953421312)), (311/562949953421312), by norm_num⟩
  | 15 => ⟨((502668957/2251799813685248), (-527478215/1125899906842624)), (121/1125899906842624), by norm_num⟩
  | 16 => ⟨((-363225039/9007199254740992), (190576017/2251799813685248)), (11/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (328169245997/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778119260139377/633825300114114700748351602688), (3104824898043/633825300114114700748351602688)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889011061177475/39614081257132168796771975168), (3492165586743/39614081257132168796771975168)), (104089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59023135337717/77371252455336267181195264), (3709481713445/2475880078570760549798248448)), (55309/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770406435047043/154742504910672534362390528), (3708419797507/154742504910672534362390528)), (110643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548818034671765/9671406556917033397649408), (3475515612049/9671406556917033397649408)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258145062866057/604462909807314587353088), (3039948592019/604462909807314587353088)), (90813/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117921617076033/4722366482869645213696), (4937803077497/75557863725914323419136)), (73811/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81047160788169/295147905179352825856), (3701503902895/4722366482869645213696)), (55381/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620368494844199/590295810358705651712), (5086565719249/590295810358705651712)), (152369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911062240667697/36893488147419103232), (6353706572039/73786976294838206464)), (95285/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821137136469517/9223372036854775808), (1785433973677/2305843009213693952)), (107271/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99524035942087/72057594037927936), (891751541891/144115188075855872)), (107365/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193178442702545/144115188075855872), (3116790318793/72057594037927936)), (188101/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489531545737263/36028797018963968), (4666516376583/18014398509481984)), (282573/36028797018963968), by norm_num⟩
  | 3 => ⟨((92913827326375/562949953421312), (5817999395101/4503599627370496)), (353959/9007199254740992), by norm_num⟩
  | 2 => ⟨((277832869528213/562949953421312), (23181319749779/4503599627370496)), (710149/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104072958349407/1125899906842624), (34545979353473/2251799813685248)), (33463/70368744177664), by norm_num⟩
  | 0 => ⟨((541174900400079/562949953421312), (68192116438325/2251799813685248)), (2164103/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541174900400079/562949953421312), (68192116438325/2251799813685248)), (8255397805220793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2078903360757879/2251799813685248), (131108854694095/2251799813685248)), (536483/281474976710656), by norm_num⟩
  | 2 => ⟨((955824231228243/1125899906842624), (15130265854017/140737488355328)), (8424437/2251799813685248), by norm_num⟩
  | 3 => ⟨((1596853786152179/2251799813685248), (205515600671827/1125899906842624)), (16115097/2251799813685248), by norm_num⟩
  | 4 => ⟨((528687175343055/1125899906842624), (291480941646457/1125899906842624)), (14369511/1125899906842624), by norm_num⟩
  | 5 => ⟨((172794214518313/1125899906842624), (1094962241448621/4503599627370496)), (41870205/2251799813685248), by norm_num⟩
  | 6 => ⟨((-80071156489911/2251799813685248), (1344369170214505/18014398509481984)), (265693289/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-704086791/16777216)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1434514841/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((237247375283077/9007199254740992), (669894101859309/9007199254740992)), (203891771/18014398509481984), by norm_num⟩
  | 1 => ⟨((-333099565/4294967296), (-117567915/536870912)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((61299459/536870912), (692343103/2147483648)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-481313377/4294967296), (-679520673/2147483648)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((354299467/4294967296), (500201789/2147483648)), (159/4294967296), by norm_num⟩
  | 5 => ⟨((-26080329/536870912), (-294562729/2147483648)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((409556999/17179869184), (289107327/4294967296)), (187/17179869184), by norm_num⟩
  | 7 => ⟨((-21534207/2147483648), (-972867295/34359738368)), (159/34359738368), by norm_num⟩
  | 8 => ⟨((126812317/34359738368), (89517137/8589934592)), (59/34359738368), by norm_num⟩
  | 9 => ⟨((-165951613/137438953472), (-234291331/68719476736)), (39/68719476736), by norm_num⟩
  | 10 => ⟨((195453759/549755813888), (275942611/274877906944)), (93/549755813888), by norm_num⟩
  | 11 => ⟨((-418546667/4398046511104), (-1181812625/4398046511104)), (201/4398046511104), by norm_num⟩
  | 12 => ⟨((12837345/549755813888), (1159925053/17592186044416)), (199/17592186044416), by norm_num⟩
  | 13 => ⟨((-372172593/70368744177664), (-65679395/4398046511104)), (91/35184372088832), by norm_num⟩
  | 14 => ⟨((313096997/281474976710656), (442031933/140737488355328)), (155/281474976710656), by norm_num⟩
  | 15 => ⟨((-245838667/1125899906842624), (-347076281/562949953421312)), (123/1125899906842624), by norm_num⟩
  | 16 => ⟨((361928477/9007199254740992), (510972465/4503599627370496)), (183/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1602763841451/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778050665801805/633825300114114700748351602688), (236916521197/79228162514264337593543950336)), (92387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472233522320757/9903520314283042199192993792), (1065889541357/19807040628566084398385987584)), (25987/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888658807934373/2475880078570760549798248448), (566107144253/618970019642690137449562112)), (55229/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770325204125803/154742504910672534362390528), (35371387885/2417851639229258349412352)), (55237/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774371095328261/4835703278458516698824704), (2121582537219/9671406556917033397649408)), (51793/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258079009073063/604462909807314587353088), (927842133313/302231454903657293676544)), (90655/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886639115991105/75557863725914323419136), (3014174182991/75557863725914323419136)), (9209/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648337505909621/2361183241434822606848), (564870645097/1180591620717411303424)), (13817/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620259921832117/590295810358705651712), (1552462039671/295147905179352825856)), (76015/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1779287107349/72057594037927936), (969590090345/18446744073709551616)), (190105/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820987534953371/9223372036854775808), (1089828958321/2305843009213693952)), (26745/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796118542339659/576460752303423488), (2177260574729/576460752303423488)), (214075/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298262939436593/36028797018963968), (3804818556199/144115188075855872)), (187445/144115188075855872), by norm_num⟩
  | 4 => ⟨((744673120961031/18014398509481984), (2848234669891/18014398509481984)), (281427/36028797018963968), by norm_num⟩
  | 3 => ⟨((371599460219185/2251799813685248), (3550898082849/4503599627370496)), (352237/9007199254740992), by norm_num⟩
  | 2 => ⟨((138890045782777/281474976710656), (1768420994977/562949953421312)), (44115/281474976710656), by norm_num⟩
  | 1 => ⟨((2207573545734253/2251799813685248), (10540502421025/1125899906842624)), (1062189/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163795983485581/2251799813685248), (41604894596027/2251799813685248)), (2138167/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163795983485581/2251799813685248), (41604894596027/2251799813685248)), (8156459816939543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2078462775620509/2251799813685248), (79957821537335/2251799813685248)), (1047055/562949953421312), by norm_num⟩
  | 2 => ⟨((1915629546729353/2251799813685248), (147605799303337/2251799813685248)), (8029081/2251799813685248), by norm_num⟩
  | 3 => ⟨((1619970419281871/2251799813685248), (251139580610693/2251799813685248)), (7356731/1125899906842624), by norm_num⟩
  | 4 => ⟨((1137415970475327/2251799813685248), (180672673133565/1125899906842624)), (12226001/1125899906842624), by norm_num⟩
  | 5 => ⟨((1033079959909793/4503599627370496), (730082603619257/4503599627370496)), (16274855/1125899906842624), by norm_num⟩
  | 6 => ⟨((237247375283077/9007199254740992), (669894101859309/9007199254740992)), (203891771/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1434514841/33554432)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1459504659/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1202574354143853/18014398509481984), (317381899820807/9007199254740992)), (63977345/9007199254740992), by norm_num⟩
  | 1 => ⟨((-858924581/4294967296), (-226686287/2147483648)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((321638511/1073741824), (339545713/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-80295239/268435456), (-678125367/4294967296)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((240543039/1073741824), (31741907/268435456)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-144120509/1073741824), (-304288817/4294967296)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((575661947/8589934592), (303855943/8589934592)), (135/17179869184), by norm_num⟩
  | 7 => ⟨((-985445185/34359738368), (-520154889/34359738368)), (59/17179869184), by norm_num⟩
  | 8 => ⟨((369016243/34359738368), (389561197/68719476736)), (45/34359738368), by norm_num⟩
  | 9 => ⟨((-982643439/274877906944), (-259338011/137438953472)), (61/137438953472), by norm_num⟩
  | 10 => ⟨((588747333/549755813888), (77690725/137438953472)), (149/1099511627776), by norm_num⟩
  | 11 => ⟨((-1282712281/4398046511104), (-677063599/4398046511104)), (165/4398046511104), by norm_num⟩
  | 12 => ⟨((640443763/8796093022208), (676100425/17592186044416)), (167/17592186044416), by norm_num⟩
  | 13 => ⟨((-1180675723/70368744177664), (-623204881/70368744177664)), (39/17592186044416), by norm_num⟩
  | 14 => ⟨((1010568105/281474976710656), (533415707/281474976710656)), (135/281474976710656), by norm_num⟩
  | 15 => ⟨((-807304397/1125899906842624), (-213062753/562949953421312)), (55/562949953421312), by norm_num⟩
  | 16 => ⟨((604616959/4503599627370496), (319139483/4503599627370496)), (167/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (79079725807/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888992073251395/316912650057057350374175801344), (187016193693/158456325028528675187087900672)), (46137/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118053710097869/2475880078570760549798248448), (420692637127/19807040628566084398385987584)), (51907/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888579550217967/2475880078570760549798248448), (893736355059/2475880078570760549798248448)), (110307/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770246104293217/154742504910672534362390528), (893471549047/154742504910672534362390528)), (55157/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387167050548683/2417851639229258349412352), (837348330611/9671406556917033397649408)), (103425/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014436664793/604462909807314587353088), (732398666211/604462909807314587353088)), (11313/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886534499594637/75557863725914323419136), (74351311827/4722366482869645213696)), (147081/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648298411890287/2361183241434822606848), (445877508117/2361183241434822606848)), (55161/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620152858410901/590295810358705651712), (612707479735/295147905179352825856)), (75855/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821856835405561/73786976294838206464), (765323638429/36893488147419103232)), (5927/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820838642381421/9223372036854775808), (860218812855/4611686018427387904)), (6669/288230376151711744), by norm_num⟩
  | 6 => ⟨((1592089333897723/1152921504606846976), (214814251923/144115188075855872)), (106727/576460752303423488), by norm_num⟩
  | 5 => ⟨((596461878592813/72057594037927936), (750769286509/72057594037927936)), (23353/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489156795990529/36028797018963968), (2247992646307/36028797018963968)), (70085/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486165486964825/9007199254740992), (2802455283803/9007199254740992)), (350607/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221789315067207/4503599627370496), (5582368250867/4503599627370496)), (701763/4503599627370496), by norm_num⟩
  | 1 => ⟨((137933087558883/140737488355328), (32489925183/8796093022208)), (527015/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162638160076573/2251799813685248), (16411656108951/2251799813685248)), (2113663/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162638160076573/2251799813685248), (16411656108951/2251799813685248)), (8062984475142668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519221828750099/562949953421312), (3940456158177/281474976710656)), (31959/17592186044416), by norm_num⟩
  | 2 => ⟨((957560070956941/1125899906842624), (58149989074487/2251799813685248)), (478783/140737488355328), by norm_num⟩
  | 3 => ⟨((1627277751097227/2251799813685248), (12363911597715/281474976710656)), (3356491/562949953421312), by norm_num⟩
  | 4 => ⟨((585809053571817/1125899906842624), (71478887731383/1125899906842624)), (5146051/562949953421312), by norm_num⟩
  | 5 => ⟨((1201041100726003/4503599627370496), (18595338412325/281474976710656)), (24033663/2251799813685248), by norm_num⟩
  | 6 => ⟨((1202574354143853/18014398509481984), (317381899820807/9007199254740992)), (63977345/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1459504659/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1483274965/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((635787301817509/9007199254740992), (-72002859055909/4503599627370496)), (99630981/18014398509481984), by norm_num⟩
  | 1 => ⟨((-922998765/4294967296), (209059067/4294967296)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((1405045225/4294967296), (-159121255/2147483648)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((-712948619/2147483648), (322965487/4294967296)), (119/4294967296), by norm_num⟩
  | 4 => ⟨((542647017/2147483648), (-122909459/2147483648)), (23/1073741824), by norm_num⟩
  | 5 => ⟨((-1321680815/8589934592), (299360485/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((83830977/1073741824), (-151901619/8589934592)), (59/8589934592), by norm_num⟩
  | 7 => ⟨((-1166744185/34359738368), (66066841/8589934592)), (13/4294967296), by norm_num⟩
  | 8 => ⟨((888044713/68719476736), (-50285495/17179869184)), (81/68719476736), by norm_num⟩
  | 9 => ⟨((-150204003/34359738368), (136084727/137438953472)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((182919783/137438953472), (-82862601/274877906944)), (137/1099511627776), by norm_num⟩
  | 11 => ⟨((-1620082571/4398046511104), (183474217/2199023255552)), (77/2199023255552), by norm_num⟩
  | 12 => ⟨((1644125913/17592186044416), (-372394247/17592186044416)), (79/8796093022208), by norm_num⟩
  | 13 => ⟨((-770088959/35184372088832), (348850043/70368744177664)), (75/35184372088832), by norm_num⟩
  | 14 => ⟨((1339744637/281474976710656), (-151725969/140737488355328)), (33/70368744177664), by norm_num⟩
  | 15 => ⟨((-1087702029/1125899906842624), (246364329/1125899906842624)), (109/1125899906842624), by norm_num⟩
  | 16 => ⟨((1655766617/9007199254740992), (-23439429/562949953421312)), (21/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-36268216655/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777919568490993/633825300114114700748351602688), (-343059984289/633825300114114700748351602688)), (46117/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236098342586433/4951760157141521099596496896), (-385855187903/39614081257132168796771975168)), (51883/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888502428478701/2475880078570760549798248448), (-51232673563/309485009821345068724781056)), (55127/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885084512601103/77371252455336267181195264), (-204868992085/77371252455336267181195264)), (110257/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548595985834573/9671406556917033397649408), (-95999573881/2417851639229258349412352)), (103369/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257951292607919/604462909807314587353088), (-335867503007/604462909807314587353088)), (90451/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943215987649517/37778931862957161709568), (-545539182367/75557863725914323419136)), (36747/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648260002346853/2361183241434822606848), (-408939690867/4722366482869645213696)), (55123/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620047352518701/590295810358705651712), (-140485857245/147573952589676412928)), (151597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821725133364373/73786976294838206464), (-701906728019/73786976294838206464)), (47377/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910345362599529/4611686018427387904), (-788927218339/9223372036854775808)), (106607/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795970862868043/576460752303423488), (-788030904215/1152921504606846976)), (53309/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192794947010579/144115188075855872), (-344260030021/72057594037927936)), (93303/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488964272959161/36028797018963968), (-515384776649/18014398509481984)), (279957/36028797018963968), by norm_num⟩
  | 3 => ⟨((185740755095081/1125899906842624), (-321237798941/2251799813685248)), (350033/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221314030180353/4503599627370496), (-639850214553/1125899906842624)), (87541/562949953421312), by norm_num⟩
  | 1 => ⟨((2206225439298505/2251799813685248), (-3812954606207/2251799813685248)), (525579/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161265782431997/2251799813685248), (-7521962906187/2251799813685248)), (2105047/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161265782431997/2251799813685248), (-7521962906187/2251799813685248)), (8030117043502043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((518586640561639/562949953421312), (-14439081970843/2251799813685248)), (4054891/2251799813685248), by norm_num⟩
  | 2 => ⟨((955392470295623/1125899906842624), (-13301209044509/1125899906842624)), (7522693/2251799813685248), by norm_num⟩
  | 3 => ⟨((25329678636097/35184372088832), (-45147441223577/2251799813685248)), (12944643/2251799813685248), by norm_num⟩
  | 4 => ⟨((583072496792419/1125899906842624), (-32502219296341/1125899906842624)), (2394637/281474976710656), by norm_num⟩
  | 5 => ⟨((1204075567274849/4503599627370496), (-8416001298711/281474976710656)), (20947909/2251799813685248), by norm_num⟩
  | 6 => ⟨((635787301817509/9007199254740992), (-72002859055909/4503599627370496)), (99630981/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1483274965/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile001Terms2
