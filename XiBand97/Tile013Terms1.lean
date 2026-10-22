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
namespace Reinmann.XiBand97.Tile013Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5149/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5149/256))
  have he : value ((69/80), (5149/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-741442149/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((661875355471357/4503599627370496), (-283668383512607/9007199254740992)), (101237595/9007199254740992), by norm_num⟩
  | 1 => ⟨((-346729469/1073741824), (297204563/4294967296)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((761842511/2147483648), (-326512585/4294967296)), (121/4294967296), by norm_num⟩
  | 3 => ⟨((-1115959393/4294967296), (59785123/1073741824)), (91/4294967296), by norm_num⟩
  | 4 => ⟨((1226006703/8589934592), (-262722683/8589934592)), (51/4294967296), by norm_num⟩
  | 5 => ⟨((-134690603/2147483648), (230904295/17179869184)), (23/4294967296), by norm_num⟩
  | 6 => ⟨((789188009/34359738368), (-338232395/68719476736)), (137/68719476736), by norm_num⟩
  | 7 => ⟨((-990870451/137438953472), (212335009/137438953472)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((544291227/274877906944), (-116636925/274877906944)), (99/549755813888), by norm_num⟩
  | 9 => ⟨((-66440559/137438953472), (113901119/1099511627776)), (99/2199023255552), by norm_num⟩
  | 10 => ⟨((934302907/8796093022208), (-100106535/4398046511104)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((-1492998771/70368744177664), (19996049/4398046511104)), (145/70368744177664), by norm_num⟩
  | 12 => ⟨((1093484531/281474976710656), (-117162161/140737488355328)), (109/281474976710656), by norm_num⟩
  | 13 => ⟨((-1478542207/2251799813685248), (316838867/2251799813685248)), (75/1125899906842624), by norm_num⟩
  | 14 => ⟨((116024617/1125899906842624), (-198904613/9007199254740992)), (3/281474976710656), by norm_num⟩
  | 15 => ⟨((-4248869/281474976710656), (233086989/72057594037927936)), (115/72057594037927936), by norm_num⟩
  | 16 => ⟨((1194972083/576460752303423488), (-256072231/576460752303423488)), (129/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-17186231707/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444761450586335/158456325028528675187087900672), (-10172518695/19807040628566084398385987584)), (92233/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890053505367463/39614081257132168796771975168), (-366149874031/39614081257132168796771975168)), (25941/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889848056185201/2475880078570760549798248448), (-388959045839/2475880078570760549798248448)), (110251/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885757152286677/77371252455336267181195264), (-388874479559/154742504910672534362390528)), (55127/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96866050954145/604462909807314587353088), (-91119999711/2417851639229258349412352)), (51683/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629527074262799/302231454903657293676544), (-159415101211/302231454903657293676544)), (5653/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888223423029471/75557863725914323419136), (-517930772351/75557863725914323419136)), (146983/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324465746075645/1180591620717411303424), (-388300872951/4722366482869645213696)), (110243/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25342077578049/9223372036854775808), (-133418651537/147573952589676412928)), (151591/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824030673230343/73786976294838206464), (-666734819505/73786976294838206464)), (47375/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455820607510589/2305843009213693952), (-749584149205/9223372036854775808)), (213203/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398632724657039/288230376151711744), (-374484495023/576460752303423488)), (213223/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298764407046327/36028797018963968), (-654656491249/144115188075855872)), (186593/144115188075855872), by norm_num⟩
  | 4 => ⟨((373088153211791/9007199254740992), (-980603682507/36028797018963968)), (139967/18014398509481984), by norm_num⟩
  | 3 => ⟨((745075770535611/4503599627370496), (-611670784193/4503599627370496)), (174999/4503599627370496), by norm_num⟩
  | 2 => ⟨((278716916490973/562949953421312), (-609864812319/1125899906842624)), (700235/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109391702894559/1125899906842624), (-3641182302253/2251799813685248)), (1050961/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093043665984297/1125899906842624), (-3605328154927/1125899906842624)), (1052191/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093043665984297/1125899906842624), (-3605328154927/1125899906842624)), (4013790134910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2122269395523245/2251799813685248), (-14000466931697/2251799813685248)), (4099421/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000102916222121/2251799813685248), (-13195117217613/1125899906842624)), (7778197/2251799813685248), by norm_num⟩
  | 3 => ⟨((444057594140755/562949953421312), (-23440442855041/1125899906842624)), (1749985/281474976710656), by norm_num⟩
  | 4 => ⟨((87507682577377/140737488355328), (-36979865071641/1125899906842624)), (708415/70368744177664), by norm_num⟩
  | 5 => ⟨((1736277035829351/4503599627370496), (-183946570725959/4503599627370496)), (59359439/4503599627370496), by norm_num⟩
  | 6 => ⟨((661875355471357/4503599627370496), (-283668383512607/9007199254740992)), (101237595/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-741442149/16777216)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-1553991027/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-212788012452421/2251799813685248), (-896514289895231/9007199254740992)), (56119021/2251799813685248), by norm_num⟩
  | 1 => ⟨((934529315/4294967296), (984335155/4294967296)), (249/4294967296), by norm_num⟩
  | 2 => ⟨((-537958317/2147483648), (-1106697/4194304)), (73/1073741824), by norm_num⟩
  | 3 => ⟨((412898267/2147483648), (434903725/2147483648)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-950733395/8589934592), (-500701417/4294967296)), (33/1073741824), by norm_num⟩
  | 5 => ⟨((875657817/17179869184), (922326095/17179869184)), (123/8589934592), by norm_num⟩
  | 6 => ⟨((-168023053/8589934592), (-707911439/34359738368)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((884314005/137438953472), (931443615/137438953472)), (127/68719476736), by norm_num⟩
  | 8 => ⟨((-1018104123/549755813888), (-268091023/137438953472)), (295/549755813888), by norm_num⟩
  | 9 => ⟨((520949195/1099511627776), (1097426477/2199023255552)), (305/2199023255552), by norm_num⟩
  | 10 => ⟨((-959623881/8796093022208), (-1010767139/8796093022208)), (71/2199023255552), by norm_num⟩
  | 11 => ⟨((401748299/17592186044416), (846319035/35184372088832)), (15/2199023255552), by norm_num⟩
  | 12 => ⟨((-308353215/70368744177664), (-649573865/140737488355328)), (93/70368744177664), by norm_num⟩
  | 13 => ⟨((436928933/562949953421312), (460215107/562949953421312)), (133/562949953421312), by norm_num⟩
  | 14 => ⟨((-574894885/4503599627370496), (-605533969/4503599627370496)), (177/4503599627370496), by norm_num⟩
  | 15 => ⟨((705997009/36028797018963968), (743623195/36028797018963968)), (219/36028797018963968), by norm_num⟩
  | 16 => ⟨((-406404547/144115188075855872), (-428063921/144115188075855872)), (127/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-3035403535379/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222362354063679/79228162514264337593543950336), (-7017124557/1237940039285380274899124224)), (46277/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944943901384507/19807040628566084398385987584), (-4041146407825/39614081257132168796771975168)), (52073/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944835763363155/1237940039285380274899124224), (-4292846562345/2475880078570760549798248448)), (110681/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885668623135311/77371252455336267181195264), (-134120820081/4835703278458516698824704)), (110711/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387422565391549/2417851639229258349412352), (-502822898207/1208925819614629174706176)), (103823/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258907852896325/604462909807314587353088), (-3518719065021/604462909807314587353088)), (90877/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887984641340131/75557863725914323419136), (-5715966601709/75557863725914323419136)), (147733/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648841489501837/2361183241434822606848), (-4285267470427/4722366482869645213696)), (27713/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405410991468023/147573952589676412928), (-5889468890517/590295810358705651712)), (19063/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823717189351185/73786976294838206464), (-7357676648073/73786976294838206464)), (47689/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113932918256341/576460752303423488), (-8271669170583/9223372036854775808)), (107387/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398542832932829/288230376151711744), (-8264526158171/1152921504606846976)), (214991/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194738708866975/144115188075855872), (-7223429054497/144115188075855872)), (94181/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491865660501473/36028797018963968), (-5409546155027/18014398509481984)), (141515/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489527899358473/9007199254740992), (-13495801326539/9007199254740992)), (88661/2251799813685248), by norm_num⟩
  | 2 => ⟨((278555425336901/562949953421312), (-13453756621483/2251799813685248)), (177965/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108367311828157/1125899906842624), (-5018925819975/281474976710656)), (268559/562949953421312), by norm_num⟩
  | 0 => ⟨((1090775278441055/1125899906842624), (-19866381328205/562949953421312)), (1087169/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090775278441055/1125899906842624), (-19866381328205/562949953421312)), (4147220615867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055344270310821/1125899906842624), (-76986444330235/1125899906842624)), (1091619/562949953421312), by norm_num⟩
  | 2 => ⟨((983945916981159/1125899906842624), (-72162012290559/562949953421312)), (4391417/1125899906842624), by norm_num⟩
  | 3 => ⟨((105173663497449/140737488355328), (-252255167348067/1125899906842624)), (17602645/2251799813685248), by norm_num⟩
  | 4 => ⟨((572256285139417/1125899906842624), (-377022503331521/1125899906842624)), (17098355/1125899906842624), by norm_num⟩
  | 5 => ⟨((164607250375325/1125899906842624), (-1533020801293075/4503599627370496)), (115328945/4503599627370496), by norm_num⟩
  | 6 => ⟨((-212788012452421/2251799813685248), (-896514289895231/9007199254740992)), (56119021/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1553991027/33554432)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-202289361/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-510741323295647/9007199254740992), (1017672413962049/9007199254740992)), (101176407/4503599627370496), by norm_num⟩
  | 1 => ⟨((583984473/4294967296), (-72725769/268435456)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((-175041701/1073741824), (697555111/2147483648)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((559642223/4294967296), (-557554701/2147483648)), (57/1073741824), by norm_num⟩
  | 4 => ⟨((-670981721/8589934592), (668478891/4294967296)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((643577559/17179869184), (-641176949/8589934592)), (267/17179869184), by norm_num⟩
  | 6 => ⟨((-514410529/34359738368), (512491725/17179869184)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((704858615/137438953472), (-175557355/17179869184)), (297/137438953472), by norm_num⟩
  | 8 => ⟨((-422544285/274877906944), (841936303/274877906944)), (45/68719476736), by norm_num⟩
  | 9 => ⟨((225159321/549755813888), (-448638907/549755813888)), (97/549755813888), by norm_num⟩
  | 10 => ⟨((-431926777/4398046511104), (860631291/4398046511104)), (47/1099511627776), by norm_num⟩
  | 11 => ⟨((376623701/17592186044416), (-750437711/17592186044416)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((-301034731/70368744177664), (9372245/1099511627776)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((111053809/140737488355328), (-885116533/562949953421312)), (25/70368744177664), by norm_num⟩
  | 14 => ⟨((-76084401/562949953421312), (303202393/1125899906842624)), (277/4503599627370496), by norm_num⟩
  | 15 => ⟨((97302627/4503599627370496), (-48469839/1125899906842624)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-466643019/144115188075855872), (929804783/144115188075855872)), (217/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1326019868811/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444693433027469/158456325028528675187087900672), (3138584477607/633825300114114700748351602688)), (92509/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472436795994883/9903520314283042199192993792), (3530259964165/39614081257132168796771975168)), (104093/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944761135436877/1237940039285380274899124224), (1875054435813/1237940039285380274899124224)), (110621/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110699260055769/9671406556917033397649408), (3749217662809/154742504910672534362390528)), (110647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549550675065077/9671406556917033397649408), (1756972426711/4835703278458516698824704)), (103759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258785895650177/604462909807314587353088), (3073755270515/604462909807314587353088)), (90817/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887786799872281/75557863725914323419136), (4993078158761/75557863725914323419136)), (147629/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297534894368113/4722366482869645213696), (467907089977/590295810358705651712)), (110767/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50670025964417/18446744073709551616), (2572228533365/295147905179352825856)), (152377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823463991944971/73786976294838206464), (6426791547057/73786976294838206464)), (95291/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822642835768937/9223372036854775808), (3612472940559/4611686018427387904)), (53639/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796944356080709/576460752303423488), (3609228257329/576460752303423488)), (214745/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74655800362537/9007199254740992), (6308854268633/144115188075855872)), (47029/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491499578268903/36028797018963968), (4724352213775/18014398509481984)), (35325/4503599627370496), by norm_num⟩
  | 3 => ⟨((744537567644715/4503599627370496), (11785400947785/9007199254740992)), (176999/4503599627370496), by norm_num⟩
  | 2 => ⟨((278444042387103/562949953421312), (23494483603087/4503599627370496)), (177561/1125899906842624), by norm_num⟩
  | 1 => ⟨((553858502294219/562949953421312), (2190709452875/140737488355328)), (133875/281474976710656), by norm_num⟩
  | 0 => ⟨((2179092171074959/2251799813685248), (17335933691395/562949953421312)), (2164609/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179092171074959/2251799813685248), (17335933691395/562949953421312)), (8257328042037200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106596735491157/2251799813685248), (33552358567229/562949953421312)), (4322751/2251799813685248), by norm_num⟩
  | 2 => ⟨((981378896755029/1125899906842624), (125555191178523/1125899906842624)), (4301647/1125899906842624), by norm_num⟩
  | 3 => ⟨((841407328668213/1125899906842624), (27359717824781/140737488355328)), (2114593/281474976710656), by norm_num⟩
  | 4 => ⟨((1172500010916041/2251799813685248), (327143355435525/1125899906842624)), (3982719/281474976710656), by norm_num⟩
  | 5 => ⟨((840807579627931/4503599627370496), (85170889856215/281474976710656)), (103392187/4503599627370496), by norm_num⟩
  | 6 => ⟨((-510741323295647/9007199254740992), (1017672413962049/9007199254740992)), (101176407/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-202289361/4194304)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-1677037973/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((506728096203957/4503599627370496), (148930150007601/4503599627370496)), (84502709/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1200840011/4294967296), (-176466713/2147483648)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((93249229/268435456), (109625827/1073741824)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((-1235816689/4294967296), (-181606631/2147483648)), (109/4294967296), by norm_num⟩
  | 4 => ⟨((767722277/4294967296), (451275525/8589934592)), (69/4294967296), by norm_num⟩
  | 5 => ⟨((-1526174553/17179869184), (-448551021/17179869184)), (35/4294967296), by norm_num⟩
  | 6 => ⟨((1264133765/34359738368), (371535805/34359738368)), (59/17179869184), by norm_num⟩
  | 7 => ⟨((-897501257/68719476736), (-8243141/2147483648)), (43/34359738368), by norm_num⟩
  | 8 => ⟨((1115103421/274877906944), (163867487/137438953472)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((-615761757/549755813888), (-180975737/549755813888)), (123/1099511627776), by norm_num⟩
  | 10 => ⟨((1224088387/4398046511104), (179883125/2199023255552)), (125/4398046511104), by norm_num⟩
  | 11 => ⟨((-553044613/8796093022208), (-325085653/17592186044416)), (115/17592186044416), by norm_num⟩
  | 12 => ⟨((916176157/70368744177664), (269269167/70368744177664)), (97/70368744177664), by norm_num⟩
  | 13 => ⟨((-700496069/281474976710656), (-411759227/562949953421312)), (75/281474976710656), by norm_num⟩
  | 14 => ⟨((994667051/2251799813685248), (292338069/2251799813685248)), (27/562949953421312), by norm_num⟩
  | 15 => ⟨((-1318215877/18014398509481984), (-387430833/18014398509481984)), (145/18014398509481984), by norm_num⟩
  | 16 => ⟨((1637821699/144115188075855872), (481364727/144115188075855872)), (183/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (93089881229/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778663216020287/633825300114114700748351602688), (440618238875/633825300114114700748351602688)), (23061/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889623169026555/39614081257132168796771975168), (247801482343/19807040628566084398385987584)), (103777/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944695457248441/1237940039285380274899124224), (526463060089/2475880078570760549798248448)), (55133/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771057264858433/154742504910672534362390528), (526333634577/154742504910672534362390528)), (55135/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549428448848643/9671406556917033397649408), (123325078149/2417851639229258349412352)), (51691/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629339718094777/302231454903657293676544), (215750177051/302231454903657293676544)), (2827/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((14746989987747/590295810358705651712), (350465260527/37778931862957161709568)), (73505/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((10135989323111/36893488147419103232), (525472637725/4722366482869645213696)), (13783/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621265770748843/590295810358705651712), (180539760289/147573952589676412928)), (151623/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455811778156943/18446744073709551616), (451075199275/36893488147419103232)), (189545/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822401518243949/9223372036854775808), (1014165713829/9223372036854775808)), (213259/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199206341071921/144115188075855872), (1013224711593/1152921504606846976)), (106643/576460752303423488), by norm_num⟩
  | 5 => ⟨((597144156511767/72057594037927936), (110689270929/18014398509481984)), (5833/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491200305302027/36028797018963968), (165769908495/4503599627370496)), (280045/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488714066081085/9007199254740992), (827004845493/4503599627370496)), (87541/2251799813685248), by norm_num⟩
  | 2 => ⟨((139179318230255/281474976710656), (3296977458261/4503599627370496)), (700653/4503599627370496), by norm_num⟩
  | 1 => ⟨((138406609677839/140737488355328), (307372066557/140737488355328)), (131475/281474976710656), by norm_num⟩
  | 0 => ⟨((1088809239668247/1125899906842624), (9726402029973/2251799813685248)), (2106921/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088809239668247/1125899906842624), (9726402029973/2251799813685248)), (8037265786177825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105838898214845/2251799813685248), (18811967803889/2251799813685248)), (4093227/2251799813685248), by norm_num⟩
  | 2 => ⟨((492295490495349/562949953421312), (8796291151779/562949953421312)), (7724203/2251799813685248), by norm_num⟩
  | 3 => ⟨((1721485000587317/2251799813685248), (61538322414449/2251799813685248)), (13750903/2251799813685248), by norm_num⟩
  | 4 => ⟨((328595333401075/562949953421312), (23522805702787/562949953421312)), (2722065/281474976710656), by norm_num⟩
  | 5 => ⟨((763276167566805/2251799813685248), (54921288370025/1125899906842624)), (54483763/4503599627370496), by norm_num⟩
  | 6 => ⟨((506728096203957/4503599627370496), (148930150007601/4503599627370496)), (84502709/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1677037973/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-865528987/16777216)), (3/33554432), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((240780855463601/9007199254740992), (-956000661243081/9007199254740992)), (109572699/4503599627370496), by norm_num⟩
  | 1 => ⟨((-294490195/4294967296), (146156149/536870912)), (135/2147483648), by norm_num⟩
  | 2 => ⟨((188838109/2147483648), (-749766241/2147483648)), (349/4294967296), by norm_num⟩
  | 3 => ⟨((-322906791/4294967296), (1282074959/4294967296)), (75/1073741824), by norm_num⟩
  | 4 => ⟨((414119783/8589934592), (-1644228671/8589934592)), (387/8589934592), by norm_num⟩
  | 5 => ⟨((-424878509/17179869184), (843472655/8589934592)), (25/1073741824), by norm_num⟩
  | 6 => ⟨((363263953/34359738368), (-1442309763/34359738368)), (43/4294967296), by norm_num⟩
  | 7 => ⟨((-266215327/68719476736), (1056986143/68719476736)), (127/34359738368), by norm_num⟩
  | 8 => ⟨((21338401/17179869184), (-338889491/68719476736)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((-194602375/549755813888), (1545305569/1099511627776)), (47/137438953472), by norm_num⟩
  | 10 => ⟨((399316189/4398046511104), (-1585452211/4398046511104)), (97/1099511627776), by norm_num⟩
  | 11 => ⟨((-186222873/8796093022208), (184845665/2199023255552)), (91/4398046511104), by norm_num⟩
  | 12 => ⟨((159217413/35184372088832), (-632159693/35184372088832)), (313/70368744177664), by norm_num⟩
  | 13 => ⟨((-251313601/281474976710656), (997820061/281474976710656)), (249/281474976710656), by norm_num⟩
  | 14 => ⟨((368346663/2251799813685248), (-1462490243/2251799813685248)), (367/2251799813685248), by norm_num⟩
  | 15 => ⟨((-251944143/9007199254740992), (125040447/1125899906842624)), (253/9007199254740992), by norm_num⟩
  | 16 => ⟨((20194499/4503599627370496), (-1282889657/72057594037927936)), (163/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-862371479103/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778554682589987/633825300114114700748351602688), (-127542495545/39614081257132168796771975168)), (69301/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944750486258697/19807040628566084398385987584), (-1147660207757/19807040628566084398385987584)), (77973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118078809550673/154742504910672534362390528), (-2438227452235/2475880078570760549798248448)), (165715/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442731789859503/38685626227668133590597632), (-2437608359891/154742504910672534362390528)), (41435/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774653161207325/4835703278458516698824704), (-2284600247985/9671406556917033397649408)), (9713/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258572423087317/604462909807314587353088), (-999183924147/302231454903657293676544)), (136009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887440536530319/75557863725914323419136), (-1623057828027/37778931862957161709568)), (221065/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297275747298901/4722366482869645213696), (-304188640687/590295810358705651712)), (165843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621085397279369/590295810358705651712), (-836081199779/147573952589676412928)), (114053/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823021038986597/73786976294838206464), (-1044445540693/18446744073709551616)), (285239/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822146352506707/9223372036854775808), (-4696399653943/9223372036854775808)), (160521/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593394523919209/1152921504606846976), (-4691896795789/1152921504606846976)), (321227/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597031484089391/72057594037927936), (-4100349120579/144115188075855872)), (281283/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490859964012845/36028797018963968), (-6140415366815/36028797018963968)), (105585/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488284589311413/9007199254740992), (-1914464627675/2251799813685248)), (528657/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225998055003369/4503599627370496), (-15262850173063/4503599627370496)), (1059511/4503599627370496), by norm_num⟩
  | 1 => ⟨((276646153348929/281474976710656), (-22762510768437/2251799813685248)), (1594775/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174826933272583/2251799813685248), (-1406261672855/70368744177664)), (3211681/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174826933272583/2251799813685248), (-1406261672855/70368744177664)), (12251590737349700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099585907830933/2251799813685248), (-43462133609097/1125899906842624)), (24735/8796093022208), by norm_num⟩
  | 2 => ⟨((977152837784617/1125899906842624), (-162096972733261/2251799813685248)), (12297127/2251799813685248), by norm_num⟩
  | 3 => ⟨((842223012441153/1125899906842624), (-70340851766649/562949953421312)), (11557721/1125899906842624), by norm_num⟩
  | 4 => ⟨((306220942370503/562949953421312), (-420944588147049/2251799813685248)), (40359321/2251799813685248), by norm_num⟩
  | 5 => ⟨((293797409167723/1125899906842624), (-457952070818211/2251799813685248)), (29498411/1125899906842624), by norm_num⟩
  | 6 => ⟨((240780855463601/9007199254740992), (-956000661243081/9007199254740992)), (109572699/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-865528987/16777216)), (3/33554432), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-1781072683/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437908134382875/4503599627370496), (-148514799982931/4503599627370496)), (20328555/1125899906842624), by norm_num⟩
  | 1 => ⟨((275531929/1073741824), (186891113/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-1454289113/4294967296), (-493216361/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((1279317447/4294967296), (433875417/4294967296)), (245/4294967296), by norm_num⟩
  | 4 => ⟨((-844048021/4294967296), (-286255525/4294967296)), (163/4294967296), by norm_num⟩
  | 5 => ⟨((445498223/4294967296), (37772237/1073741824)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((-1567593801/34359738368), (-265821597/17179869184)), (309/34359738368), by norm_num⟩
  | 7 => ⟨((1181991403/68719476736), (100216919/17179869184)), (235/68719476736), by norm_num⟩
  | 8 => ⟨((-1559671537/274877906944), (-528956389/274877906944)), (313/274877906944), by norm_num⟩
  | 9 => ⟨((457340289/274877906944), (155105137/274877906944)), (93/274877906944), by norm_num⟩
  | 10 => ⟨((-965557793/2199023255552), (-327465079/2199023255552)), (99/1099511627776), by norm_num⟩
  | 11 => ⟨((463302249/4398046511104), (19640889/549755813888)), (3/137438953472), by norm_num⟩
  | 12 => ⟨((-815120797/35184372088832), (-276444971/35184372088832)), (85/17592186044416), by norm_num⟩
  | 13 => ⟨((1323784931/281474976710656), (224478193/140737488355328)), (139/140737488355328), by norm_num⟩
  | 14 => ⟨((-998155521/1125899906842624), (-338520469/1125899906842624)), (211/1125899906842624), by norm_num⟩
  | 15 => ⟨((1404901143/9007199254740992), (476466627/9007199254740992)), (299/9007199254740992), by norm_num⟩
  | 16 => ⟨((-57931479/2251799813685248), (-157177843/18014398509481984)), (199/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-3666356591951/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778448328332361/633825300114114700748351602688), (-4337499013483/633825300114114700748351602688)), (92627/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889380907873411/39614081257132168796771975168), (-1219673580523/9903520314283042199192993792)), (52117/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236141604384059/309485009821345068724781056), (-2591203204639/1237940039285380274899124224)), (110779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770798424567045/154742504910672534362390528), (-5181049440417/154742504910672534362390528)), (3463/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((387296244561019/2417851639229258349412352), (-2427896160383/4835703278458516698824704)), (12991/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629232796121285/302231454903657293676544), (-530922128937/75557863725914323419136)), (90975/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943632854993393/37778931862957161709568), (-6899285930229/75557863725914323419136)), (147905/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297143555405641/4722366482869645213696), (-5172101016537/4722366482869645213696)), (110991/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620901893571827/590295810358705651712), (-7107799441405/590295810358705651712)), (76357/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822789053282077/73786976294838206464), (-8878992077335/73786976294838206464)), (191045/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910940895634367/4611686018427387904), (-9980953091113/9223372036854775808)), (215135/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398281375015249/288230376151711744), (-9971066632263/1152921504606846976)), (215397/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596911282128735/72057594037927936), (-2178391906259/36028797018963968)), (5899/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490489373003537/36028797018963968), (-3262034143219/9007199254740992)), (141871/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487803946127553/9007199254740992), (-16271331868605/9007199254740992)), (355713/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112492416493187/2251799813685248), (-16213148076403/2251799813685248)), (357269/2251799813685248), by norm_num⟩
  | 1 => ⟨((552880130917919/562949953421312), (-24174523971023/1125899906842624)), (539805/1125899906842624), by norm_num⟩
  | 0 => ⟨((271377479972907/281474976710656), (-47769828631015/1125899906842624)), (1095273/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271377479972907/281474976710656), (-47769828631015/1125899906842624)), (4178134922507857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522271039596097/562949953421312), (-23028078488747/281474976710656)), (2204905/1125899906842624), by norm_num⟩
  | 2 => ⟨((961527281636351/1125899906842624), (-85456253573699/562949953421312)), (4451933/1125899906842624), by norm_num⟩
  | 3 => ⟨((1590414250485817/2251799813685248), (-583842444239803/2251799813685248)), (17911171/2251799813685248), by norm_num⟩
  | 4 => ⟨((485954718343885/1125899906842624), (-206179816188413/562949953421312)), (34588763/2251799813685248), by norm_num⟩
  | 5 => ⟨((234875308062263/4503599627370496), (-1423843151883861/4503599627370496)), (110388437/4503599627370496), by norm_num⟩
  | 6 => ⟨((-437908134382875/4503599627370496), (-148514799982931/4503599627370496)), (20328555/1125899906842624), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1781072683/33554432)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-1827635263/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-425464388388737/9007199254740992), (380228646872141/4503599627370496)), (78189799/4503599627370496), by norm_num⟩
  | 1 => ⟨((549401723/4294967296), (-490988857/2147483648)), (51/1073741824), by norm_num⟩
  | 2 => ⟨((-743903723/4294967296), (1329622473/4294967296)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((335754771/2147483648), (-1200228135/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-454620387/4294967296), (406284755/2147483648)), (87/2147483648), by norm_num⟩
  | 5 => ⟨((123113483/2147483648), (-440095805/4294967296)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((-222264995/8589934592), (794534355/17179869184)), (173/17179869184), by norm_num⟩
  | 7 => ⟨((687891159/68719476736), (-614753977/34359738368)), (135/34359738368), by norm_num⟩
  | 8 => ⟨((-116427737/34359738368), (832392315/137438953472)), (185/137438953472), by norm_num⟩
  | 9 => ⟨((560519389/549755813888), (-1001848967/549755813888)), (225/549755813888), by norm_num⟩
  | 10 => ⟨((-303582929/1099511627776), (542611459/1099511627776)), (123/1099511627776), by norm_num⟩
  | 11 => ⟨((597903863/8796093022208), (-1068668415/8796093022208)), (61/2199023255552), by norm_num⟩
  | 12 => ⟨((-134929473/8796093022208), (964669239/35184372088832)), (111/17592186044416), by norm_num⟩
  | 13 => ⟨((449717891/140737488355328), (-803806993/140737488355328)), (187/140737488355328), by norm_num⟩
  | 14 => ⟨((-347959607/562949953421312), (1243856965/1125899906842624)), (291/1125899906842624), by norm_num⟩
  | 15 => ⟨((251277889/2251799813685248), (-224561807/1125899906842624)), (53/1125899906842624), by norm_num⟩
  | 16 => ⟨((-340236569/18014398509481984), (1216249293/36028797018963968)), (289/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1355297374207/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889180599615693/316912650057057350374175801344), (3206465798913/633825300114114700748351602688)), (23129/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889283164344629/39614081257132168796771975168), (3606532296295/39614081257132168796771975168)), (104101/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236128667981303/309485009821345068724781056), (957756669547/618970019642690137449562112)), (55315/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221336917433769/19342813113834066795298816), (1914999411763/77371252455336267181195264)), (110657/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774544383595351/4835703278458516698824704), (1794766044825/4835703278458516698824704)), (103769/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258381838477675/604462909807314587353088), (3139749095029/604462909807314587353088)), (45413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943565208696639/37778931862957161709568), (2550023218203/37778931862957161709568)), (147645/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297042791650141/4722366482869645213696), (3823245402947/4722366482869645213696)), (27695/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810382244443861/295147905179352825856), (5254055904771/590295810358705651712)), (152397/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911309506716199/36893488147419103232), (3281606176059/36893488147419103232)), (190609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821692852349831/9223372036854775808), (1844406490419/2305843009213693952)), (107295/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49779359395095/36028797018963968), (7370146543679/1152921504606846976)), (839/4503599627370496), by norm_num⟩
  | 5 => ⟨((298415778575569/36028797018963968), (6440471440643/144115188075855872)), (94077/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490256778654809/36028797018963968), (9643912483947/36028797018963968)), (70667/9007199254740992), by norm_num⟩
  | 3 => ⟨((743762338837439/4503599627370496), (6012771204787/4503599627370496)), (88525/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112230276829771/2251799813685248), (11981605044885/2251799813685248)), (355251/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105409584679619/1125899906842624), (35725722353349/2251799813685248)), (33485/70368744177664), by norm_num⟩
  | 0 => ⟨((2169953924516861/2251799813685248), (35289317082453/1125899906842624)), (541551/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169953924516861/2251799813685248), (35289317082453/1125899906842624)), (2065853121043968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2088870716810095/2251799813685248), (136026642566003/2251799813685248)), (4310731/2251799813685248), by norm_num⟩
  | 2 => ⟨((1929513270963553/2251799813685248), (252368855024547/2251799813685248)), (4259231/1125899906842624), by norm_num⟩
  | 3 => ⟨((1625069600591753/2251799813685248), (432497642097953/2251799813685248)), (8253967/1125899906842624), by norm_num⟩
  | 4 => ⟨((1089704769240263/2251799813685248), (624246228487553/2251799813685248)), (30168033/2251799813685248), by norm_num⟩
  | 5 => ⟨((177141219542607/1125899906842624), (302089061482717/1125899906842624)), (91849251/4503599627370496), by norm_num⟩
  | 6 => ⟨((-425464388388737/9007199254740992), (380228646872141/4503599627370496)), (78189799/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1827635263/33554432)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile013Terms1
