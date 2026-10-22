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
namespace Reinmann.XiBand97.Tile001Terms0
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

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-84424395/8388608)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-993832952655747/2251799813685248), (739016772913555/2251799813685248)), (54903969/2251799813685248), by norm_num⟩
  | 1 => ⟨((656960019/2147483648), (-244258591/1073741824)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-455369985/4294967296), (677228615/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((841702457/34359738368), (-156473035/8589934592)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-583423685/137438953472), (108458843/34359738368)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((161759393/274877906944), (-60142353/137438953472)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-1195979383/17592186044416), (889333385/17592186044416)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((947416843/140737488355328), (-5503919/1099511627776)), (69/140737488355328), by norm_num⟩
  | 8 => ⟨((-328349657/562949953421312), (61040415/140737488355328)), (25/562949953421312), by norm_num⟩
  | 9 => ⟨((809225383/18014398509481984), (-300871051/9007199254740992)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-224364917/72057594037927936), (333676673/144115188075855872)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((452415737/2305843009213693952), (-21026095/144115188075855872)), (75/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-836241847/73786976294838206464), (621831615/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 13 => ⟨((713401451/1180591620717411303424), (-66310897/147573952589676412928)), (63/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-141283487/4722366482869645213696), (840470149/37778931862957161709568)), (51/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((52229467/37778931862957161709568), (-310703741/302231454903657293676544)), (39/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-1158486649/19342813113834066795298816), (107681711/2417851639229258349412352)), (111/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (3259392873425/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445260114851877/158456325028528675187087900672), (3866723190267/633825300114114700748351602688)), (11573/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946148382513965/19807040628566084398385987584), (1087452398719/9903520314283042199192993792)), (26045/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946115315040307/1237940039285380274899124224), (1155347064029/618970019642690137449562112)), (27679/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443473969485683/38685626227668133590597632), (4621068096741/154742504910672534362390528)), (27687/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776044238722075/4835703278458516698824704), (4331911022689/9671406556917033397649408)), (25965/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261005790303487/604462909807314587353088), (3790081659707/604462909807314587353088)), (2841/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((945696424488335/37778931862957161709568), (6158243932351/75557863725914323419136)), (36949/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325059577824749/1180591620717411303424), (2309061837659/2361183241434822606848)), (13863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406289052255259/147573952589676412928), (6349010568405/590295810358705651712)), (38145/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828105483963887/73786976294838206464), (3967448909871/36893488147419103232)), (47715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827860758794909/9223372036854775808), (8924880746331/9223372036854775808)), (26863/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599101939610569/1152921504606846976), (8922528789719/1152921504606846976)), (6723/144115188075855872), by norm_num⟩
  | 5 => ⟨((599524547822195/72057594037927936), (243892589115/4503599627370496)), (47127/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498323440591293/36028797018963968), (11701534890013/36028797018963968)), (17705/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497586452287763/9007199254740992), (3654401342753/2251799813685248)), (88753/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122259702143327/2251799813685248), (14603591961013/2251799813685248)), (44549/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120372780258767/1125899906842624), (5467550588785/281474976710656)), (134507/1125899906842624), by norm_num⟩
  | 0 => ⟨((278644794570889/281474976710656), (43598752845147/1125899906842624)), (272465/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278644794570889/281474976710656), (43598752845147/1125899906842624)), (1039371494773482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101683982630415/1125899906842624), (21580187468265/281474976710656)), (560553/1125899906842624), by norm_num⟩
  | 2 => ⟨((535685418568195/562949953421312), (168928315786937/1125899906842624)), (295737/281474976710656), by norm_num⟩
  | 3 => ⟨((994136945912521/1125899906842624), (321493713607685/1125899906842624)), (2606289/1125899906842624), by norm_num⟩
  | 4 => ⟨((392996772608629/562949953421312), (567739239755871/1125899906842624)), (6090975/1125899906842624), by norm_num⟩
  | 5 => ⟨((524838854624611/2251799813685248), (1585360741581595/2251799813685248)), (3661761/281474976710656), by norm_num⟩
  | 6 => ⟨((-993832952655747/2251799813685248), (739016772913555/2251799813685248)), (54903969/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-84424395/8388608)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-535238001/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-423635218024665/1125899906842624), (420744006276249/4503599627370496)), (73917359/2251799813685248), by norm_num⟩
  | 1 => ⟨((887700761/2147483648), (-110205301/1073741824)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-975238965/4294967296), (60536449/1073741824)), (11/536870912), by norm_num⟩
  | 3 => ⟨((1428546015/17179869184), (-177349565/8589934592)), (33/4294967296), by norm_num⟩
  | 4 => ⟨((-1569418207/68719476736), (389676823/68719476736)), (37/17179869184), by norm_num⟩
  | 5 => ⟨((1379345703/274877906944), (-342482997/274877906944)), (33/68719476736), by norm_num⟩
  | 6 => ⟨((-1010244093/1099511627776), (250837353/1099511627776)), (99/1099511627776), by norm_num⟩
  | 7 => ⟨((1268418943/8796093022208), (-157470285/4398046511104)), (127/8796093022208), by norm_num⟩
  | 8 => ⟨((-696750319/35184372088832), (86499395/17592186044416)), (71/35184372088832), by norm_num⟩
  | 9 => ⟨((1360815045/562949953421312), (-168940975/281474976710656)), (141/562949953421312), by norm_num⟩
  | 10 => ⟨((-1196006505/4503599627370496), (148480505/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | 11 => ⟨((955598141/36028797018963968), (-118634551/18014398509481984)), (103/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1399775815/576460752303423488), (86888917/144115188075855872)), (77/288230376151711744), by norm_num⟩
  | 13 => ⟨((946345177/4611686018427387904), (-458929/9007199254740992)), (53/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-594095109/36893488147419103232), (147510137/36893488147419103232)), (17/9223372036854775808), by norm_num⟩
  | 15 => ⟨((87024025/73786976294838206464), (-345720425/1180591620717411303424)), (81/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-1529690613/18889465931478580854784), (379812707/18889465931478580854784)), (181/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (1887627869609/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780497471284371/633825300114114700748351602688), (2238064681809/316912650057057350374175801344)), (2895/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59115180976319/1237940039285380274899124224), (2517594156661/19807040628566084398385987584)), (52125/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945790660702575/1237940039285380274899124224), (5349366561321/2475880078570760549798248448)), (55399/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773246401726761/154742504910672534362390528), (2674390078907/77371252455336267181195264)), (55417/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551479415618475/9671406556917033397649408), (2506929077987/4835703278458516698824704)), (51973/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260472683488549/604462909807314587353088), (4386502432865/604462909807314587353088)), (5687/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1890526217513057/75557863725914323419136), (7126897028501/75557863725914323419136)), (4623/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324897011688509/1180591620717411303424), (5344149075597/4722366482869645213696)), (13877/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624261623102909/590295810358705651712), (7346540632281/590295810358705651712)), (76375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826986544398841/73786976294838206464), (2295169450057/18446744073709551616)), (95547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456650245298379/2305843009213693952), (10324825402999/9223372036854775808)), (53799/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597840951417413/1152921504606846976), (1290065678359/144115188075855872)), (26933/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197944372698703/144115188075855872), (9025617370943/144115188075855872)), (94417/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496663648716857/36028797018963968), (6764364533399/18014398509481984)), (141929/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495506994865523/9007199254740992), (8446957073611/4503599627370496)), (177943/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120173209287839/2251799813685248), (16868363641723/2251799813685248)), (178741/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117225595657911/1125899906842624), (25238478480109/1125899906842624)), (270109/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108215887322211/1125899906842624), (50219551297991/1125899906842624)), (548233/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108215887322211/1125899906842624), (50219551297991/1125899906842624)), (2091342930320357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((544284817030409/562949953421312), (24715387337893/281474976710656)), (141019/140737488355328), by norm_num⟩
  | 2 => ⟨((521898187892549/562949953421312), (191167402974781/1125899906842624)), (1189807/562949953421312), by norm_num⟩
  | 3 => ⟨((467610793704935/562949953421312), (44306745471029/140737488355328)), (5220247/1125899906842624), by norm_num⟩
  | 4 => ⟨((332623619814865/562949953421312), (588849855381295/1125899906842624)), (5979595/562949953421312), by norm_num⟩
  | 5 => ⟨((85096141379995/1125899906842624), (1391707161420087/2251799813685248)), (53283549/2251799813685248), by norm_num⟩
  | 6 => ⟨((-423635218024665/1125899906842624), (420744006276249/4503599627370496)), (73917359/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-535238001/33554432)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-84424395/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((392182417329683/4503599627370496), (-326165415337153/1125899906842624)), (48792125/2251799813685248), by norm_num⟩
  | 1 => ⟨((-259246957/2147483648), (107803649/268435456)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((359392595/4294967296), (-597790363/2147483648)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-332149285/8589934592), (1104951213/8589934592)), (89/8589934592), by norm_num⟩
  | 4 => ⟨((460456681/34359738368), (-382946909/8589934592)), (125/34359738368), by norm_num⟩
  | 5 => ⟨((-31916425/8589934592), (849403425/68719476736)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((1843565/2147483648), (-1570030905/549755813888)), (67/274877906944), by norm_num⟩
  | 7 => ⟨((-93466469/549755813888), (621864283/1099511627776)), (27/549755813888), by norm_num⟩
  | 8 => ⟨((129572039/4398046511104), (-862086949/8796093022208)), (19/2199023255552), by norm_num⟩
  | 9 => ⟨((-159666655/35184372088832), (531158345/35184372088832)), (95/70368744177664), by norm_num⟩
  | 10 => ⟨((177075987/281474976710656), (-589073455/281474976710656)), (27/140737488355328), by norm_num⟩
  | 11 => ⟨((-357061007/4503599627370496), (74239019/281474976710656)), (55/2251799813685248), by norm_num⟩
  | 12 => ⟨((41249305/4503599627370496), (-274445689/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 13 => ⟨((-140759825/144115188075855872), (29266347/9007199254740992)), (45/144115188075855872), by norm_num⟩
  | 14 => ⟨((55752729/576460752303423488), (-1483767655/4611686018427387904)), (145/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-20610585/2305843009213693952), (1097033991/36893488147419103232)), (109/36893488147419103232), by norm_num⟩
  | 16 => ⟨((114289351/147573952589676412928), (-380203009/147573952589676412928)), (153/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-1665764637035/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780122938900869/633825300114114700748351602688), (-246775678639/79228162514264337593543950336)), (23099/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472816249737995/9903520314283042199192993792), (-2220742193487/39614081257132168796771975168)), (51979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472783728868045/618970019642690137449562112), (-2359250392373/2475880078570760549798248448)), (27617/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221600095907635/19342813113834066795298816), (-2358926212127/154742504910672534362390528)), (55243/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551062452772147/9671406556917033397649408), (-2211148921517/9671406556917033397649408)), (25899/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260108660217417/604462909807314587353088), (-967205474007/302231454903657293676544)), (11333/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236242026901411/9444732965739290427392), (-3142772212275/75557863725914323419136)), (4605/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1299146888079577/4722366482869645213696), (-2356514371835/4722366482869645213696)), (27637/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623657211404353/590295810358705651712), (-1619644828649/295147905179352825856)), (76025/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913117150138693/36893488147419103232), (-2023867986407/36893488147419103232)), (47533/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228219900088271/1152921504606846976), (-4551811332727/9223372036854775808)), (106997/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597004784428503/1152921504606846976), (-568680941963/144115188075855872)), (6691/72057594037927936), by norm_num⟩
  | 5 => ⟨((1197219036006745/144115188075855872), (-3978108351871/144115188075855872)), (93741/144115188075855872), by norm_num⟩
  | 4 => ⟨((747794124054301/18014398509481984), (-5961848618901/36028797018963968)), (140745/36028797018963968), by norm_num⟩
  | 3 => ⟨((373546192347213/2251799813685248), (-7443017227469/9007199254740992)), (176165/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118883956725209/2251799813685248), (-7429088499695/2251799813685248)), (44129/562949953421312), by norm_num⟩
  | 1 => ⟨((1115373921224229/1125899906842624), (-11108851511865/1125899906842624)), (132827/562949953421312), by norm_num⟩
  | 0 => ⟨((1104839986186847/1125899906842624), (-22078821655755/1125899906842624)), (534831/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104839986186847/1125899906842624), (-22078821655755/1125899906842624)), (2040218357566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((270935256610293/281474976710656), (-10832919012123/281474976710656)), (1070631/1125899906842624), by norm_num⟩
  | 2 => ⟨((1041493094649043/1125899906842624), (-166836553739135/2251799813685248)), (2143493/1125899906842624), by norm_num⟩
  | 3 => ⟨((1914467264338087/2251799813685248), (-77164549707455/562949953421312)), (8566445/2251799813685248), by norm_num⟩
  | 4 => ⟨((396340185395393/562949953421312), (-262419427312309/1125899906842624)), (16914721/2251799813685248), by norm_num⟩
  | 5 => ⟨((993832952655711/2251799813685248), (-369508386456777/1125899906842624)), (15851071/1125899906842624), by norm_num⟩
  | 6 => ⟨((392182417329683/4503599627370496), (-326165415337153/1125899906842624)), (48792125/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-84424395/4194304)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-1568218997/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-108141376107507/2251799813685248), (275703785484787/1125899906842624)), (94076811/4503599627370496), by norm_num⟩
  | 1 => ⟨((20747999/268435456), (-1692688465/4294967296)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((-133570465/2147483648), (1362138495/4294967296)), (15/536870912), by norm_num⟩
  | 3 => ⟨((286631161/8589934592), (-91344889/536870912)), (131/8589934592), by norm_num⟩
  | 4 => ⟨((-230657529/17179869184), (294027855/4294967296)), (107/17179869184), by norm_num⟩
  | 5 => ⟨((148491589/34359738368), (-1514302647/68719476736)), (35/17179869184), by norm_num⟩
  | 6 => ⟨((-318650657/274877906944), (1624784061/274877906944)), (19/34359738368), by norm_num⟩
  | 7 => ⟨((1144751/4294967296), (-1494279467/1099511627776)), (71/549755813888), by norm_num⟩
  | 8 => ⟨((-58956981/1099511627776), (1202475013/4398046511104)), (29/1099511627776), by norm_num⟩
  | 9 => ⟨((337378135/35184372088832), (-430068639/8796093022208)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((-217195665/140737488355328), (276867509/35184372088832)), (55/70368744177664), by norm_num⟩
  | 11 => ⟨((254227591/1125899906842624), (-648147005/562949953421312)), (131/1125899906842624), by norm_num⟩
  | 12 => ⟨((-136387841/4503599627370496), (1390869817/9007199254740992)), (71/4503599627370496), by norm_num⟩
  | 13 => ⟨((33770425/9007199254740992), (-1377549917/72057594037927936)), (143/72057594037927936), by norm_num⟩
  | 14 => ⟨((-248463553/576460752303423488), (1266903465/576460752303423488)), (67/288230376151711744), by norm_num⟩
  | 15 => ⟨((106636443/2305843009213693952), (-1087467983/4611686018427387904)), (117/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-85812367/18446744073709551616), (1750212201/73786976294838206464)), (191/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (1149201231451/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889911991151237/316912650057057350374175801344), (2723121469895/633825300114114700748351602688)), (46235/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945464301213009/19807040628566084398385987584), (765782008663/9903520314283042199192993792)), (26011/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890777402507275/2475880078570760549798248448), (3254111791001/2475880078570760549798248448)), (13821/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886221575628865/77371252455336267181195264), (1626796179675/77371252455336267181195264)), (27647/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550727078360971/9671406556917033397649408), (1524845497695/4835703278458516698824704)), (51851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629907549139341/302231454903657293676544), (166745490055/37778931862957161709568)), (45381/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889458972237041/75557863725914323419136), (4334348284321/75557863725914323419136)), (73767/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298788776795989/4722366482869645213696), (1624928096939/2361183241434822606848)), (3459/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623164517743179/590295810358705651712), (4467081855121/590295810358705651712)), (38065/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912808998891031/36893488147419103232), (5581647130697/73786976294838206464)), (47605/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825065262592065/9223372036854775808), (6276321585787/9223372036854775808)), (107177/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596310100396041/1152921504606846976), (3136266668767/576460752303423488)), (107259/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196610350161559/144115188075855872), (1371051582995/36028797018963968)), (11743/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494673549306411/36028797018963968), (8217792427211/36028797018963968)), (35275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493038483662197/9007199254740992), (10257343783643/9007199254740992)), (88349/4503599627370496), by norm_num⟩
  | 2 => ⟨((279433330826461/562949953421312), (10235014930027/2251799813685248)), (177183/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113637173981975/1125899906842624), (15296757325005/1125899906842624)), (133495/562949953421312), by norm_num⟩
  | 0 => ⟨((275330933725257/281474976710656), (30370797647811/1125899906842624)), (538853/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275330933725257/281474976710656), (30370797647811/1125899906842624)), (2055561069968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1076464769506367/1125899906842624), (29707863100557/562949953421312)), (1083253/1125899906842624), by norm_num⟩
  | 2 => ⟨((1026064718939415/1125899906842624), (113613893422367/1125899906842624)), (136607/70368744177664), by norm_num⟩
  | 3 => ⟨((923617352087575/1125899906842624), (3235611990061/17592186044416)), (2212461/562949953421312), by norm_num⟩
  | 4 => ⟨((359795407476831/562949953421312), (679498811824249/2251799813685248)), (8887547/1125899906842624), by norm_num⟩
  | 5 => ⟨((357386371295151/1125899906842624), (868569400865937/2251799813685248)), (33448573/2251799813685248), by norm_num⟩
  | 6 => ⟨((-108141376107507/2251799813685248), (275703785484787/1125899906842624)), (94076811/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1568218997/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-872935581/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((152450683252053/1125899906842624), (-741825882916453/4503599627370496)), (57268585/4503599627370496), by norm_num⟩
  | 1 => ⟨((-521001731/2147483648), (633799339/2147483648)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((933509785/4294967296), (-1135615967/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-278770833/2147483648), (678250221/4294967296)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((62436285/1073741824), (-151907657/2147483648)), (53/8589934592), by norm_num⟩
  | 5 => ⟨((-715973151/34359738368), (870982345/34359738368)), (39/17179869184), by norm_num⟩
  | 6 => ⟨((855234449/137438953472), (-520196955/68719476736)), (95/137438953472), by norm_num⟩
  | 7 => ⟨((-875642527/549755813888), (532610183/274877906944)), (99/549755813888), by norm_num⟩
  | 8 => ⟨((784470395/2199023255552), (-954309339/2199023255552)), (45/1099511627776), by norm_num⟩
  | 9 => ⟨((-312351613/4398046511104), (759952353/8796093022208)), (73/8796093022208), by norm_num⟩
  | 10 => ⟨((895454337/70368744177664), (-272330365/17592186044416)), (107/70368744177664), by norm_num⟩
  | 11 => ⟨((-291716143/140737488355328), (709746197/281474976710656)), (9/35184372088832), by norm_num⟩
  | 12 => ⟨((696913549/2251799813685248), (-847796313/2251799813685248)), (87/2251799813685248), by norm_num⟩
  | 13 => ⟨((-384215831/9007199254740992), (467399099/9007199254740992)), (49/9007199254740992), by norm_num⟩
  | 14 => ⟨((196692101/36028797018963968), (-957104871/144115188075855872)), (51/72057594037927936), by norm_num⟩
  | 15 => ⟨((-187959965/288230376151711744), (914614249/1152921504606846976)), (25/288230376151711744), by norm_num⟩
  | 16 => ⟨((336779047/4611686018427387904), (-819384371/9223372036854775808)), (91/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-574950885621/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55612009131429/19807040628566084398385987584), (-681018776653/316912650057057350374175801344)), (46167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659160430737/39614081257132168796771975168), (-1532082324941/39614081257132168796771975168)), (51943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890491382713075/2475880078570760549798248448), (-1627580736467/2475880078570760549798248448)), (27597/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443039356614813/38685626227668133590597632), (-101705748479/9671406556917033397649408)), (1725/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1550459524676359/9671406556917033397649408), (-1525279483539/9671406556917033397649408)), (12939/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629790650992389/302231454903657293676544), (-1334312877239/604462909807314587353088)), (45293/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944539820093939/37778931862957161709568), (-1083841786147/37778931862957161709568)), (73611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298504791037265/4722366482869645213696), (-1625259837253/4722366482869645213696)), (27609/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622774870869171/590295810358705651712), (-4363116109/1152921504606846976)), (18985/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912566094286975/36893488147419103232), (-1395584787041/36893488147419103232)), (94949/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228065055452841/1152921504606846976), (-1569191291369/4611686018427387904)), (53425/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797883712322237/576460752303423488), (-1568139916105/576460752303423488)), (26723/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196137916880325/144115188075855872), (-685470238869/36028797018963968)), (93577/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493969707596555/36028797018963968), (-128378058643/1125899906842624)), (140457/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492167078382375/9007199254740992), (-2563432825549/4503599627370496)), (43933/2251799813685248), by norm_num⟩
  | 2 => ⟨((558437239162349/1125899906842624), (-10228999297605/4503599627370496)), (351951/4503599627370496), by norm_num⟩
  | 1 => ⟨((556190092488903/562949953421312), (-15281802038317/2251799813685248)), (66143/281474976710656), by norm_num⟩
  | 0 => ⟨((549467069253625/562949953421312), (-30317613673297/2251799813685248)), (531589/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549467069253625/562949953421312), (-30317613673297/2251799813685248)), (2027851109031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1072410117465915/1125899906842624), (-29591494289303/1125899906842624)), (2104059/2251799813685248), by norm_num⟩
  | 2 => ⟨((1020683807259267/1125899906842624), (-112742589901357/2251799813685248)), (2059399/1125899906842624), by norm_num⟩
  | 3 => ⟨((7206858106865/8796093022208), (-204413438888173/2251799813685248)), (3940113/1125899906842624), by norm_num⟩
  | 4 => ⟨((1493061936324275/2251799813685248), (-334962044053869/2251799813685248)), (14343631/2251799813685248), by norm_num⟩
  | 5 => ⟨((58759507669083/140737488355328), (-444194972440043/2251799813685248)), (23288485/2251799813685248), by norm_num⟩
  | 6 => ⟨((152450683252053/1125899906842624), (-741825882916453/4503599627370496)), (57268585/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-872935581/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1896073927/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-105070379456005/562949953421312), (-34687662894299/9007199254740992)), (67677149/4503599627370496), by norm_num⟩
  | 1 => ⟨((389971767/1073741824), (32186067/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((-1517700039/4294967296), (-31315597/4294967296)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((492217985/2147483648), (10156223/2147483648)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((-1915623945/17179869184), (-39526195/17179869184)), (161/17179869184), by norm_num⟩
  | 5 => ⟨((1491052831/34359738368), (15382885/17179869184)), (127/34359738368), by norm_num⟩
  | 6 => ⟨((-1934303225/137438953472), (-623619/2147483648)), (167/137438953472), by norm_num⟩
  | 7 => ⟨((134427867/34359738368), (11094917/137438953472)), (47/137438953472), by norm_num⟩
  | 8 => ⟨((-1046338203/1099511627776), (-43179423/2199023255552)), (185/2199023255552), by norm_num⟩
  | 9 => ⟨((1809849003/8796093022208), (37343679/8796093022208)), (81/4398046511104), by norm_num⟩
  | 10 => ⟨((-1408721417/35184372088832), (-14533489/17592186044416)), (1/274877906944), by norm_num⟩
  | 11 => ⟨((1993632947/281474976710656), (20567901/140737488355328)), (183/281474976710656), by norm_num⟩
  | 12 => ⟨((-161642941/140737488355328), (-1667637/70368744177664)), (121/1125899906842624), by norm_num⟩
  | 13 => ⟨((774258805/4503599627370496), (7987869/2251799813685248)), (147/9007199254740992), by norm_num⟩
  | 14 => ⟨((-430468019/18014398509481984), (-35528401/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | 15 => ⟨((1786991119/576460752303423488), (36872041/576460752303423488)), (173/576460752303423488), by norm_num⟩
  | 16 => ⟨((-869331039/2305843009213693952), (-35874839/4611686018427387904)), (171/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-508175181631/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779367776599739/633825300114114700748351602688), (-4814337748233/633825300114114700748351602688)), (46337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945207478572099/19807040628566084398385987584), (-5415292061085/39614081257132168796771975168)), (52145/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890231117971135/2475880078570760549798248448), (-5752758291297/2475880078570760549798248448)), (55421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771896263618767/154742504910672534362390528), (-5751644872669/154742504910672534362390528)), (55441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550213730794069/9671406556917033397649408), (-5390984018985/9671406556917033397649408)), (51997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259365279192081/604462909807314587353088), (-4715927920149/604462909807314587353088)), (45519/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59022713038135/2361183241434822606848), (-3830582232213/37778931862957161709568)), (74007/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298238612341821/4722366482869645213696), (-5743932143963/4722366482869645213696)), (13885/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622406340058601/590295810358705651712), (-7894752056189/590295810358705651712)), (9553/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912333863200071/36893488147419103232), (-4931853893651/36893488147419103232)), (95613/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823992707010011/9223372036854775808), (-11090163856619/9223372036854775808)), (107681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595233176930607/1152921504606846976), (-11082028838383/1152921504606846976)), (53913/576460752303423488), by norm_num⟩
  | 5 => ⟨((597831569259111/72057594037927936), (-1210952788021/18014398509481984)), (5907/9007199254740992), by norm_num⟩
  | 4 => ⟨((1493242950250283/36028797018963968), (-3628281264689/9007199254740992)), (71047/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491233174690819/9007199254740992), (-18109361042399/9007199254740992)), (178191/9007199254740992), by norm_num⟩
  | 2 => ⟨((557951269641091/1125899906842624), (-9030641132915/1125899906842624)), (44763/562949953421312), by norm_num⟩
  | 1 => ⟨((555413856505253/562949953421312), (-6742922470787/281474976710656)), (16921/70368744177664), by norm_num⟩
  | 0 => ⟨((1095454086029347/1125899906842624), (-53462237574935/1125899906842624)), (137533/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095454086029347/1125899906842624), (-53462237574935/1125899906842624)), (524646760106944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1063292959237459/1125899906842624), (-104033096092831/1125899906842624)), (1122757/1125899906842624), by norm_num⟩
  | 2 => ⟨((994554689343101/1125899906842624), (-196496434418203/1125899906842624)), (291017/140737488355328), by norm_num⟩
  | 3 => ⟨((844238617996571/1125899906842624), (-43393388946505/140737488355328)), (307857/70368744177664), by norm_num⟩
  | 4 => ⟨((1052007773416985/2251799813685248), (-130151444162099/281474976710656)), (20848827/2251799813685248), by norm_num⟩
  | 5 => ⟨((20071816751827/4503599627370496), (-972877465556897/2251799813685248)), (4845143/281474976710656), by norm_num⟩
  | 6 => ⟨((-105070379456005/562949953421312), (-34687662894299/9007199254740992)), (67677149/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1896073927/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-253273185/8388608)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((127543096288701/2251799813685248), (704523166722763/4503599627370496)), (158868697/9007199254740992), by norm_num⟩
  | 1 => ⟨((-505863977/4294967296), (-1397146931/4294967296)), (5/134217728), by norm_num⟩
  | 2 => ⟨((131489321/1073741824), (363160671/1073741824)), (169/4294967296), by norm_num⟩
  | 3 => ⟨((-364565809/4294967296), (-1006895181/4294967296)), (15/536870912), by norm_num⟩
  | 4 => ⟨((94761661/2147483648), (523444917/4294967296)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-315282135/17179869184), (-217694621/4294967296)), (27/4294967296), by norm_num⟩
  | 6 => ⟨((218536923/34359738368), (603577651/34359738368)), (19/8589934592), by norm_num⟩
  | 7 => ⟨((-519354007/274877906944), (-358601269/68719476736)), (183/274877906944), by norm_num⟩
  | 8 => ⟨((539983149/1099511627776), (1491380751/1099511627776)), (193/1099511627776), by norm_num⟩
  | 9 => ⟨((-124762599/1099511627776), (-344582121/1099511627776)), (181/4398046511104), by norm_num⟩
  | 10 => ⟨((207549225/8796093022208), (1146461403/17592186044416)), (153/17592186044416), by norm_num⟩
  | 11 => ⟨((-313881077/70368744177664), (-866908897/70368744177664)), (59/35184372088832), by norm_num⟩
  | 12 => ⟨((435131567/562949953421312), (300447729/140737488355328)), (83/281474976710656), by norm_num⟩
  | 13 => ⟨((-278409433/2251799813685248), (-1537879357/4503599627370496)), (215/4503599627370496), by norm_num⟩
  | 14 => ⟨((82705163/4503599627370496), (913694349/18014398509481984)), (65/9007199254740992), by norm_num⟩
  | 15 => ⟨((-91722961/36028797018963968), (-1013319459/144115188075855872)), (73/72057594037927936), by norm_num⟩
  | 16 => ⟨((381465071/1152921504606846976), (1053569289/1152921504606846976)), (77/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (796814118195/5070602400912917605986812821504)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889600309856429/316912650057057350374175801344), (943425552993/316912650057057350374175801344)), (69289/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890227540636593/39614081257132168796771975168), (265296373029/4951760157141521099596496896)), (9745/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890032797515783/2475880078570760549798248448), (2254606380791/2475880078570760549798248448)), (41421/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442924713371543/38685626227668133590597632), (2254142106077/154742504910672534362390528)), (41427/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550029625529185/9671406556917033397649408), (132047815443/604462909807314587353088)), (9711/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259205153276329/604462909807314587353088), (115511022979/37778931862957161709568)), (33995/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944234211530425/37778931862957161709568), (375295300641/9444732965739290427392)), (55253/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298046399714825/4722366482869645213696), (2250963409171/4722366482869645213696)), (20725/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811072308947799/295147905179352825856), (1546880779565/295147905179352825856)), (28505/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228043053151155/9223372036854775808), (3865233153405/73786976294838206464)), (142575/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823634282850241/9223372036854775808), (4345681661161/9223372036854775808)), (160465/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797440677824347/576460752303423488), (2171150900371/576460752303423488)), (80275/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195362710458799/144115188075855872), (3795714735577/144115188075855872)), (70289/72057594037927936), by norm_num⟩
  | 4 => ⟨((746403553806327/18014398509481984), (5685980925609/36028797018963968)), (105529/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490714199212041/9007199254740992), (1773552115737/2251799813685248)), (8255/281474976710656), by norm_num⟩
  | 2 => ⟨((2230844326386901/4503599627370496), (884292577809/281474976710656)), (264665/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220406299306607/2251799813685248), (21123918268877/2251799813685248)), (199133/562949953421312), by norm_num⟩
  | 0 => ⟨((2189171960202843/2251799813685248), (41852833363719/2251799813685248)), (200405/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189171960202843/2251799813685248), (41852833363719/2251799813685248)), (764484406591319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2127508041595133/2251799813685248), (10172201886915/281474976710656)), (1588449/1125899906842624), by norm_num⟩
  | 2 => ⟨((2007135857879197/2251799813685248), (76885844589259/1125899906842624)), (1558177/562949953421312), by norm_num⟩
  | 3 => ⟨((1778554467964553/2251799813685248), (137063991834933/1125899906842624)), (2990565/562949953421312), by norm_num⟩
  | 4 => ⟨((1371396260590249/2251799813685248), (216516382667355/1125899906842624)), (21808975/2251799813685248), by norm_num⟩
  | 5 => ⟨((375968218270793/1125899906842624), (527453205639251/2251799813685248)), (17476131/1125899906842624), by norm_num⟩
  | 6 => ⟨((127543096288701/2251799813685248), (704523166722763/4503599627370496)), (158868697/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-253273185/8388608)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile001Terms0
