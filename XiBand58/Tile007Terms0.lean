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
namespace Reinmann.XiBand58.Tile007Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2893/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2893/160))
  have he : value ((15/16), (2893/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-1682146417/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((587545940306293/1125899906842624), (39266385729383/2251799813685248)), (18293629/2251799813685248), by norm_num⟩
  | 1 => ⟨((-12137169/33554432), (-51913041/4294967296)), (13/2147483648), by norm_num⟩
  | 2 => ⟨((1076844093/8589934592), (17991689/4294967296)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((-1990430525/68719476736), (-66511405/68719476736)), (5/8589934592), by norm_num⟩
  | 4 => ⟨((1379661307/274877906944), (46102193/274877906944)), (15/137438953472), by norm_num⟩
  | 5 => ⟨((-191261669/274877906944), (-6391121/274877906944)), (35/2199023255552), by norm_num⟩
  | 6 => ⟨((353526631/4398046511104), (2953325/1099511627776)), (17/8796093022208), by norm_num⟩
  | 7 => ⟨((-1120210229/140737488355328), (-37432483/140737488355328)), (29/140737488355328), by norm_num⟩
  | 8 => ⟨((388235281/562949953421312), (6486555/281474976710656)), (21/1125899906842624), by norm_num⟩
  | 9 => ⟨((-1913629799/36028797018963968), (-7993133/4503599627370496)), (27/18014398509481984), by norm_num⟩
  | 10 => ⟨((66321355/18014398509481984), (35458673/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 11 => ⟨((-16716531/72057594037927936), (-35749933/4611686018427387904)), (17/2305843009213693952), by norm_num⟩
  | 12 => ⟨((988758727/73786976294838206464), (66079907/147573952589676412928)), (65/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-843514245/1180591620717411303424), (-7046631/295147905179352825856)), (29/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((1336410333/37778931862957161709568), (5582117/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-1976168649/1208925819614629174706176), (-16508709/302231454903657293676544)), (37/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1369775727/19342813113834066795298816), (11442965/4835703278458516698824704)), (27/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (43511343655/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222621011290419/79228162514264337593543950336), (51614496411/633825300114114700748351602688)), (5763/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((473053959658789/9903520314283042199192993792), (1814465921/1237940039285380274899124224)), (25933/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473036310284463/618970019642690137449562112), (61687749165/2475880078570760549798248448)), (27555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773811158688057/154742504910672534362390528), (30841572975/77371252455336267181195264)), (27555/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776004882277781/4835703278458516698824704), (28911529449/4835703278458516698824704)), (25833/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315234406947857/151115727451828646838272), (12647571663/151115727451828646838272)), (5651/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472820854551091/18889465931478580854784), (82200048441/75557863725914323419136)), (36731/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325039351138193/1180591620717411303424), (61642016045/4722366482869645213696)), (27549/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812523428474435/295147905179352825856), (84744741275/590295810358705651712)), (37879/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913985817450667/36893488147419103232), (3309730757/2305843009213693952)), (47349/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913857041670401/4611686018427387904), (119123442687/9223372036854775808)), (13317/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1598960142573735/1152921504606846976), (119089871265/1152921504606846976)), (53269/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599465254001789/72057594037927936), (104165882271/144115188075855872)), (46611/144115188075855872), by norm_num⟩
  | 4 => ⟨((749078260011121/18014398509481984), (78086672565/18014398509481984)), (69919/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497396963673931/9007199254740992), (195084666161/9007199254740992)), (87401/9007199254740992), by norm_num⟩
  | 2 => ⟨((561049458846223/1125899906842624), (12180424167/140737488355328)), (87405/2251799813685248), by norm_num⟩
  | 1 => ⟨((2240406454597333/2251799813685248), (583671965551/2251799813685248)), (262239/2251799813685248), by norm_num⟩
  | 0 => ⟨((2229051490181839/2251799813685248), (1136129263/2199023255552)), (131143/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2229051490181839/2251799813685248), (1136129263/2199023255552)), (500270845653343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((8619267092403/8796093022208), (575821701825/562949953421312)), (64943/140737488355328), by norm_num⟩
  | 2 => ⟨((2162172583057541/2251799813685248), (564246084381/281474976710656)), (2038525/2251799813685248), by norm_num⟩
  | 3 => ⟨((1038051845150827/1125899906842624), (8668602999835/2251799813685248)), (3922947/2251799813685248), by norm_num⟩
  | 4 => ⟨((1914082842538435/2251799813685248), (15984474790647/2251799813685248)), (7263925/2251799813685248), by norm_num⟩
  | 5 => ⟨((813451000928485/1125899906842624), (27174359601437/2251799813685248)), (6226071/1125899906842624), by norm_num⟩
  | 6 => ⟨((587545940306293/1125899906842624), (39266385729383/2251799813685248)), (18293629/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-1682146417/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-166633687/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((424365686466743/2251799813685248), (-682823594500297/2251799813685248)), (50985559/2251799813685248), by norm_num⟩
  | 1 => ⟨((-222307853/1073741824), (89425849/268435456)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((244230139/2147483648), (-785954693/4294967296)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-715504619/17179869184), (71954957/1073741824)), (95/17179869184), by norm_num⟩
  | 4 => ⟨((786062167/68719476736), (-9881325/536870912)), (107/68719476736), by norm_num⟩
  | 5 => ⟨((-690862045/274877906944), (138953537/34359738368)), (97/274877906944), by norm_num⟩
  | 6 => ⟨((252996511/549755813888), (-814165671/1099511627776)), (73/1099511627776), by norm_num⟩
  | 7 => ⟨((-635303031/8796093022208), (1022231327/8796093022208)), (47/4398046511104), by norm_num⟩
  | 8 => ⟨((697951717/70368744177664), (-561517949/35184372088832)), (105/70368744177664), by norm_num⟩
  | 9 => ⟨((-681580741/562949953421312), (68543391/35184372088832)), (105/562949953421312), by norm_num⟩
  | 10 => ⟨((299517191/2251799813685248), (-963873429/4503599627370496)), (95/4503599627370496), by norm_num⟩
  | 11 => ⟨((-239311467/18014398509481984), (770125959/36028797018963968)), (39/18014398509481984), by norm_num⟩
  | 12 => ⟨((175273679/144115188075855872), (-1128093123/576460752303423488)), (117/576460752303423488), by norm_num⟩
  | 13 => ⟨((-236994237/2305843009213693952), (762668903/4611686018427387904)), (81/4611686018427387904), by norm_num⟩
  | 14 => ⟨((148779875/18446744073709551616), (-957574205/73786976294838206464)), (13/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-174348159/295147905179352825856), (280534077/295147905179352825856)), (125/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((95770515/2361183241434822606848), (-616396369/9444732965739290427392)), (35/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (-1321795890965/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780379599561301/633825300114114700748351602688), (-97935854409/39614081257132168796771975168)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59111054951605/1237940039285380274899124224), (-881340954309/19807040628566084398385987584)), (25977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891441744479667/2475880078570760549798248448), (-1872652523009/2475880078570760549798248448)), (55207/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443276905259299/38685626227668133590597632), (-936215456921/77371252455336267181195264)), (27607/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551350154480241/9671406556917033397649408), (-1755168547163/9671406556917033397649408)), (25885/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260360425478345/604462909807314587353088), (-1535537072521/604462909807314587353088)), (22653/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118146586434569/4722366482869645213696), (-2494806416309/75557863725914323419136)), (36817/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299453806873081/4722366482869645213696), (-1870718711685/4722366482869645213696)), (55237/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624079294493515/590295810358705651712), (-2571610928001/590295810358705651712)), (75969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826762008575561/73786976294838206464), (-100424153331/2305843009213693952)), (23747/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913176507920493/4611686018427387904), (-3613976304811/9223372036854775808)), (106899/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597598778236179/1152921504606846976), (-3612360267169/1152921504606846976)), (53473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197738980975341/144115188075855872), (-394874731639/18014398509481984)), (93631/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496368564786629/36028797018963968), (-4734863672515/36028797018963968)), (17569/4503599627370496), by norm_num⟩
  | 3 => ⟨((1495160860400317/9007199254740992), (-5912225374869/9007199254740992)), (175875/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119861083533373/2251799813685248), (-5902701494343/2251799813685248)), (176153/2251799813685248), by norm_num⟩
  | 1 => ⟨((558421088327511/562949953421312), (-551891786849/70368744177664)), (529853/2251799813685248), by norm_num⟩
  | 0 => ⟨((1107786612675121/1125899906842624), (-35131117709397/2251799813685248)), (1065293/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1107786612675121/1125899906842624), (-35131117709397/2251799813685248)), (4063770302779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1089690675794533/1125899906842624), (-17282967007219/562949953421312)), (1064775/1125899906842624), by norm_num⟩
  | 2 => ⟨((1053584743998975/1125899906842624), (-16727142335987/281474976710656)), (4252885/2251799813685248), by norm_num⟩
  | 3 => ⟨((981938136255895/1125899906842624), (-250444457718335/2251799813685248)), (4232463/1125899906842624), by norm_num⟩
  | 4 => ⟨((842456679380315/1125899906842624), (-436843386437787/2251799813685248)), (2081009/281474976710656), by norm_num⟩
  | 5 => ⟨((293998257101035/562949953421312), (-40858608579567/140737488355328)), (31373269/2251799813685248), by norm_num⟩
  | 6 => ⟨((424365686466743/2251799813685248), (-682823594500297/2251799813685248)), (50985559/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-166633687/8388608)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-1682146417/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1225063676132025/4503599627370496), (81963966372477/4503599627370496)), (9966627/1125899906842624), by norm_num⟩
  | 1 => ⟨((-809812005/2147483648), (-54181187/2147483648)), (55/4294967296), by norm_num⟩
  | 2 => ⟨((140329727/536870912), (37555537/2147483648)), (5/536870912), by norm_num⟩
  | 3 => ⟨((-1037537649/8589934592), (-17354343/2147483648)), (39/8589934592), by norm_num⟩
  | 4 => ⟨((89895787/2147483648), (96232911/34359738368)), (7/4294967296), by norm_num⟩
  | 5 => ⟨((-1595161889/137438953472), (-53362857/68719476736)), (65/137438953472), by norm_num⟩
  | 6 => ⟨((1474242621/549755813888), (6164719/34359738368)), (31/274877906944), by norm_num⟩
  | 7 => ⟨((-1167848133/2199023255552), (-39067955/1099511627776)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((809490641/8796093022208), (108319371/17592186044416)), (73/17592186044416), by norm_num⟩
  | 9 => ⟨((-1995008553/140737488355328), (-133477807/140737488355328)), (23/35184372088832), by norm_num⟩
  | 10 => ⟨((1106267643/562949953421312), (18503953/140737488355328)), (53/562949953421312), by norm_num⟩
  | 11 => ⟨((-1115354615/4503599627370496), (-9327973/562949953421312)), (55/4503599627370496), by norm_num⟩
  | 12 => ⟨((515403271/18014398509481984), (68967021/36028797018963968)), (53/36028797018963968), by norm_num⟩
  | 13 => ⟨((-1758770827/576460752303423488), (-58836057/288230376151711744)), (93/576460752303423488), by norm_num⟩
  | 14 => ⟨((1393242331/4611686018427387904), (93216107/4611686018427387904)), (19/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-257525865/9223372036854775808), (-68919981/36893488147419103232)), (29/18446744073709551616), by norm_num⟩
  | 16 => ⟨((714013309/295147905179352825856), (95543381/590295810358705651712)), (41/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (43511343655/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889982257073177/316912650057057350374175801344), (51559272231/316912650057057350374175801344)), (23053/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891086913521255/39614081257132168796771975168), (115994976645/39614081257132168796771975168)), (51869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890945877198947/2475880078570760549798248448), (61614159909/1237940039285380274899124224)), (6889/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886305964298301/77371252455336267181195264), (61604969021/77371252455336267181195264)), (6889/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775442814267927/4835703278458516698824704), (57744895079/4835703278458516698824704)), (12917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314988537735149/151115727451828646838272), (101034043997/604462909807314587353088)), (22605/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889685534831481/75557863725914323419136), (164143726287/75557863725914323419136)), (36733/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298959225166825/4722366482869645213696), (123075783179/4722366482869645213696)), (55101/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623399739053709/590295810358705651712), (21147150063/73786976294838206464)), (18941/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912956652750839/36893488147419103232), (52848382245/18446744073709551616)), (94707/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825399243445415/9223372036854775808), (237710558463/9223372036854775808)), (26637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596646278109719/1152921504606846976), (59394170111/288230376151711744)), (106551/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196906973383853/144115188075855872), (207729084347/144115188075855872)), (93237/144115188075855872), by norm_num⟩
  | 4 => ⟨((747561705115537/18014398509481984), (311292858573/36028797018963968)), (139861/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493609409452659/9007199254740992), (48573787575/1125899906842624)), (21855/1125899906842624), by norm_num⟩
  | 2 => ⟨((139789638319301/281474976710656), (775605565953/4503599627370496)), (87429/1125899906842624), by norm_num⟩
  | 1 => ⟨((2229089691548415/2251799813685248), (289869684587/562949953421312)), (4099/17592186044416), by norm_num⟩
  | 0 => ⟨((2206532375655167/2251799813685248), (2303286807301/2251799813685248)), (65609/140737488355328), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2206532375655167/2251799813685248), (2303286807301/2251799813685248)), (250278473437261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2162172583057539/2251799813685248), (2256984337525/1125899906842624)), (2059431/2251799813685248), by norm_num⟩
  | 2 => ⟨((1038051845150825/1125899906842624), (4334301499919/1125899906842624)), (3963179/2251799813685248), by norm_num⟩
  | 3 => ⟨((1914082842538427/2251799813685248), (3996118697663/562949953421312)), (7338421/2251799813685248), by norm_num⟩
  | 4 => ⟨((1626902001856957/2251799813685248), (27174359601445/2251799813685248)), (6289923/1125899906842624), by norm_num⟩
  | 5 => ⟨((1175091880612567/2251799813685248), (19633192864697/1125899906842624)), (18481241/2251799813685248), by norm_num⟩
  | 6 => ⟨((1225063676132025/4503599627370496), (81963966372477/4503599627370496)), (9966627/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-1682146417/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1952911513/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-674904769570205/4503599627370496), (183131256366513/1125899906842624)), (89720931/4503599627370496), by norm_num⟩
  | 1 => ⟨((258974391/1073741824), (-562168859/2147483648)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((-833606407/4294967296), (904775875/4294967296)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((447212585/4294967296), (-121348383/1073741824)), (127/8589934592), by norm_num⟩
  | 4 => ⟨((-719760889/17179869184), (781210753/17179869184)), (13/2147483648), by norm_num⟩
  | 5 => ⟨((463364185/34359738368), (-1005848163/68719476736)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((-497170591/137438953472), (1079233445/274877906944)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((57154657/68719476736), (-992548127/1099511627776)), (69/549755813888), by norm_num⟩
  | 8 => ⟨((-735894975/4398046511104), (798722293/4398046511104)), (113/4398046511104), by norm_num⟩
  | 9 => ⟨((526389899/17592186044416), (-35708165/1099511627776)), (41/8796093022208), by norm_num⟩
  | 10 => ⟨((-42359593/8796093022208), (367808477/70368744177664)), (107/140737488355328), by norm_num⟩
  | 11 => ⟨((793310661/1125899906842624), (-861039865/1125899906842624)), (127/1125899906842624), by norm_num⟩
  | 12 => ⟨((-851189503/9007199254740992), (923860135/9007199254740992)), (69/4503599627370496), by norm_num⟩
  | 13 => ⟨((843037943/72057594037927936), (-114376579/9007199254740992)), (139/72057594037927936), by norm_num⟩
  | 14 => ⟨((-387662065/288230376151711744), (420758863/288230376151711744)), (129/576460752303423488), by norm_num⟩
  | 15 => ⟨((41594535/288230376151711744), (-722330951/4611686018427387904)), (113/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-535550573/36893488147419103232), (581273409/36893488147419103232)), (23/9223372036854775808), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (3015907163633/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779634851430933/633825300114114700748351602688), (3572501972407/633825300114114700748351602688)), (11569/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890715692426291/39614081257132168796771975168), (4018513458591/39614081257132168796771975168)), (6509/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890551008100487/2475880078570760549798248448), (1067252872513/618970019642690137449562112)), (55339/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110763534828037/9671406556917033397649408), (2134135015855/77371252455336267181195264)), (27677/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96907152157559/604462909807314587353088), (2000357697911/4835703278458516698824704)), (25955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259628823098279/604462909807314587353088), (1749919128997/302231454903657293676544)), (45437/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889155878194771/75557863725914323419136), (5685760303691/75557863725914323419136)), (9233/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298561109288455/4722366482869645213696), (2131514033799/2361183241434822606848)), (433/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1622850911626331/590295810358705651712), (1464891003831/147573952589676412928)), (76249/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825225146142719/73786976294838206464), (3660652986609/36893488147419103232)), (47687/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824622145546415/9223372036854775808), (2058034951031/2305843009213693952)), (53691/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797932768484545/576460752303423488), (4113364410437/576460752303423488)), (107489/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196219733155603/144115188075855872), (7192301448009/144115188075855872)), (47087/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494084383706223/36028797018963968), (10776282359901/36028797018963968)), (141503/36028797018963968), by norm_num⟩
  | 3 => ⟨((373074093578759/2251799813685248), (6724530977525/4503599627370496)), (177303/9007199254740992), by norm_num⟩
  | 2 => ⟨((139622846378255/281474976710656), (13417137909023/2251799813685248)), (177941/2251799813685248), by norm_num⟩
  | 1 => ⟨((556245181308685/562949953421312), (20045940729779/1125899906842624)), (268509/1125899906842624), by norm_num⟩
  | 0 => ⟨((549473462672943/562949953421312), (39773084158177/1125899906842624)), (543423/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((549473462672943/562949953421312), (39773084158177/1125899906842624)), (2072994236472701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071234164932131/1125899906842624), (77641908097717/1125899906842624)), (1099223/1125899906842624), by norm_num⟩
  | 2 => ⟨((506934214705617/562949953421312), (18468041448293/140737488355328)), (1121655/562949953421312), by norm_num⟩
  | 3 => ⟨((893597022724985/1125899906842624), (8315199274681/35184372088832)), (2314467/562949953421312), by norm_num⟩
  | 4 => ⟨((161584896376485/281474976710656), (844742921256045/2251799813685248)), (4767829/562949953421312), by norm_num⟩
  | 5 => ⟨((425183815336079/2251799813685248), (969874473326565/2251799813685248)), (9051305/562949953421312), by norm_num⟩
  | 6 => ⟨((-674904769570205/4503599627370496), (183131256366513/1125899906842624)), (89720931/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1952911513/67108864)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-56363879/33554432), (-1087071353/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((466720597718279/4503599627370496), (-174464260484259/1125899906842624)), (105770141/4503599627370496), by norm_num⟩
  | 1 => ⟨((-797511149/4294967296), (1192466701/4294967296)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((714474077/4294967296), (-16692293/67108864)), (165/4294967296), by norm_num⟩
  | 3 => ⟨((-853443795/8589934592), (159512395/1073741824)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((764583001/17179869184), (-1143231377/17179869184)), (181/17179869184), by norm_num⟩
  | 5 => ⟨((-547979533/34359738368), (409679129/17179869184)), (131/34359738368), by norm_num⟩
  | 6 => ⟨((163641253/34359738368), (-244682153/34359738368)), (79/68719476736), by norm_num⟩
  | 7 => ⟨((-670184605/549755813888), (125260447/68719476736)), (41/137438953472), by norm_num⟩
  | 8 => ⟨((300202403/1099511627776), (-14027287/34359738368)), (149/2199023255552), by norm_num⟩
  | 9 => ⟨((-478124887/8796093022208), (44681821/549755813888)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((685347835/70368744177664), (-1024756171/70368744177664)), (87/35184372088832), by norm_num⟩
  | 11 => ⟨((-446537627/281474976710656), (333839377/140737488355328)), (115/281474976710656), by norm_num⟩
  | 12 => ⟨((266696007/1125899906842624), (-797546487/2251799813685248)), (139/2251799813685248), by norm_num⟩
  | 13 => ⟨((-588129349/18014398509481984), (439695837/9007199254740992)), (155/18014398509481984), by norm_num⟩
  | 14 => ⟨((602163617/144115188075855872), (-900376205/144115188075855872)), (161/144115188075855872), by norm_num⟩
  | 15 => ⟨((-287715297/576460752303423488), (860404049/1152921504606846976)), (39/288230376151711744), by norm_num⟩
  | 16 => ⟨((8054947/144115188075855872), (-770818551/9223372036854775808)), (141/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49430864790015/316912650057057350374175801344), (-1278284576425/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779376740924501/633825300114114700748351602688), (-1513769126251/633825300114114700748351602688)), (92349/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118151605332985/2475880078570760549798248448), (-425684324843/9903520314283042199192993792)), (51951/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118140208688493/154742504910672534362390528), (-1808848249679/2475880078570760549798248448)), (13801/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771909409316531/154742504910672534362390528), (-1808499437813/154742504910672534362390528)), (27605/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550227036821299/9671406556917033397649408), (-1695097694827/9671406556917033397649408)), (25883/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157422237916279/75557863725914323419136), (-1482840049887/604462909807314587353088)), (22651/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944374585144623/37778931862957161709568), (-602230180233/18889465931478580854784)), (147255/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649128492459489/2361183241434822606848), (-1806083177425/4722366482869645213696)), (110463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202804276589091/73786976294838206464), (-310297222747/73786976294838206464)), (75961/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912353239389599/36893488147419103232), (-1550746504417/36893488147419103232)), (47489/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824041675368955/9223372036854775808), (-1743573392171/4611686018427387904)), (213773/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398822212628067/288230376151711744), (-3484607332833/1152921504606846976)), (26733/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195719382956017/144115188075855872), (-1523088374053/72057594037927936)), (93617/72057594037927936), by norm_num⟩
  | 4 => ⟨((186667792966069/4503599627370496), (-35652822805/281474976710656)), (281057/36028797018963968), by norm_num⟩
  | 3 => ⟨((745691819316403/4503599627370496), (-5694482432069/9007199254740992)), (351681/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232184373607981/4503599627370496), (-5679553457413/2251799813685248)), (704443/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222419240692933/2251799813685248), (-4241047302279/562949953421312)), (1059377/2251799813685248), by norm_num⟩
  | 0 => ⟨((1096604512110137/1125899906842624), (-16815767042571/1125899906842624)), (1064819/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1096604512110137/1125899906842624), (-16815767042571/1125899906842624)), (4061962131980514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533910109882943/562949953421312), (-16378228563131/562949953421312)), (4212067/2251799813685248), by norm_num⟩
  | 2 => ⟨((1011783578037573/1125899906842624), (-62133422402363/1125899906842624)), (8234663/2251799813685248), by norm_num⟩
  | 3 => ⟨((1811609434211695/2251799813685248), (-223343393322689/2251799813685248)), (1963617/281474976710656), by norm_num⟩
  | 4 => ⟨((358829240852279/562949953421312), (-179683378581535/1125899906842624)), (28392351/2251799813685248), by norm_num⟩
  | 5 => ⟨((857531965124309/2251799813685248), (-114531762438803/562949953421312)), (45257391/2251799813685248), by norm_num⟩
  | 6 => ⟨((466720597718279/4503599627370496), (-174464260484259/1125899906842624)), (105770141/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56363879/33554432), (-1087071353/33554432)), (1/16777216), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3825815/2097152), (-590297753/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1176774701851867/9007199254740992), (852552294253411/9007199254740992)), (16408949/562949953421312), by norm_num⟩
  | 1 => ⟨((1091908377/4294967296), (-395534077/2147483648)), (123/2147483648), by norm_num⟩
  | 2 => ⟨((-265594449/1073741824), (769673775/4294967296)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((689097245/4294967296), (-249619335/2147483648)), (79/2147483648), by norm_num⟩
  | 4 => ⟨((-670460661/8589934592), (485736797/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((260931241/8589934592), (-756160131/34359738368)), (245/34359738368), by norm_num⟩
  | 6 => ⟨((-676998333/68719476736), (61309153/8589934592)), (161/68719476736), by norm_num⟩
  | 7 => ⟨((752787387/274877906944), (-545381043/274877906944)), (181/274877906944), by norm_num⟩
  | 8 => ⟨((-183107077/274877906944), (530631253/1099511627776)), (89/549755813888), by norm_num⟩
  | 9 => ⟨((633439857/4398046511104), (-458915885/4398046511104)), (155/4398046511104), by norm_num⟩
  | 10 => ⟨((-986093637/35184372088832), (714407263/35184372088832)), (243/35184372088832), by norm_num⟩
  | 11 => ⟨((697763497/140737488355328), (-15797413/4398046511104)), (173/140737488355328), by norm_num⟩
  | 12 => ⟨((-905190047/1125899906842624), (327897027/562949953421312)), (113/562949953421312), by norm_num⟩
  | 13 => ⟨((541974923/4503599627370496), (-392651171/4503599627370496)), (17/562949953421312), by norm_num⟩
  | 14 => ⟨((-1205296575/72057594037927936), (218303971/18014398509481984)), (19/4503599627370496), by norm_num⟩
  | 15 => ⟨((312719845/144115188075855872), (-453119907/288230376151711744)), (159/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1217049441/4611686018427387904), (440865313/2305843009213693952)), (39/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (3275578472075/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889573510572631/316912650057057350374175801344), (3878078327161/633825300114114700748351602688)), (46291/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890166899971131/39614081257132168796771975168), (2181060054721/19807040628566084398385987584)), (104179/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472491981408471/618970019642690137449562112), (4633887897339/2475880078570760549798248448)), (110719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442908371401071/38685626227668133590597632), (4632915115015/154742504910672534362390528)), (110751/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549967816440847/9671406556917033397649408), (4342324447043/9671406556917033397649408)), (103863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629575271981669/302231454903657293676544), (59351570923/9444732965739290427392)), (45457/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888378696719729/75557863725914323419136), (1542656524647/18889465931478580854784)), (73899/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162247280343241/590295810358705651712), (4626274714233/4722366482869645213696)), (110905/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622049502313763/590295810358705651712), (6358374069379/590295810358705651712)), (19073/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824223433462931/73786976294838206464), (7943837941357/73786976294838206464)), (95433/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823495287216017/9223372036854775808), (8931140802771/9223372036854775808)), (214911/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398684691462231/288230376151711744), (1115505847055/144115188075855872)), (215145/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195233908825633/144115188075855872), (7800563008981/144115188075855872)), (188515/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492605853721759/36028797018963968), (730305989873/2251799813685248)), (283299/36028797018963968), by norm_num⟩
  | 3 => ⟨((372612146510991/2251799813685248), (3644556446151/2251799813685248)), (44381/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115135569622423/2251799813685248), (14536417221853/2251799813685248)), (356435/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109721116761057/1125899906842624), (5425054638181/281474976710656)), (33633/70368744177664), by norm_num⟩
  | 0 => ⟨((1093415190269895/1125899906842624), (42983496958009/1125899906842624)), (545101/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1093415190269895/1125899906842624), (42983496958009/1125899906842624)), (2079395296336936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1060226748441383/1125899906842624), (10435831866397/140737488355328)), (2200737/1125899906842624), by norm_num⟩
  | 2 => ⟨((992193648627007/1125899906842624), (157233843182653/1125899906842624)), (4471113/1125899906842624), by norm_num⟩
  | 3 => ⟨((852407704362599/1125899906842624), (277123072143303/1125899906842624)), (4564545/562949953421312), by norm_num⟩
  | 4 => ⟨((288569922332093/562949953421312), (839228568422299/2251799813685248)), (36634121/2251799813685248), by norm_num⟩
  | 5 => ⟨((278913341817893/2251799813685248), (860382424180615/2251799813685248)), (64864047/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1176774701851867/9007199254740992), (852552294253411/9007199254740992)), (16408949/562949953421312), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-590297753/16777216)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-1261609813/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((79733106306969/562949953421312), (4008432572965/281474976710656)), (10852657/1125899906842624), by norm_num⟩
  | 1 => ⟨((-632478079/2147483648), (-127186603/4294967296)), (11/536870912), by norm_num⟩
  | 2 => ⟨((164400149/536870912), (132238553/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-455813999/2147483648), (-22915195/1073741824)), (133/8589934592), by norm_num⟩
  | 4 => ⟨((947838565/8589934592), (95301617/8589934592)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((-788389955/17179869184), (-158539313/34359738368)), (15/4294967296), by norm_num⟩
  | 6 => ⟨((1092940549/68719476736), (54945539/34359738368)), (85/68719476736), by norm_num⟩
  | 7 => ⟨((-324672283/68719476736), (-130578327/274877906944)), (103/274877906944), by norm_num⟩
  | 8 => ⟨((1350274065/1099511627776), (135764999/1099511627776)), (55/549755813888), by norm_num⟩
  | 9 => ⟨((-1247918215/4398046511104), (-62736751/2199023255552)), (13/549755813888), by norm_num⟩
  | 10 => ⟨((1037989191/17592186044416), (104365925/17592186044416)), (11/2199023255552), by norm_num⟩
  | 11 => ⟨((-1569772977/140737488355328), (-157834793/140737488355328)), (17/17592186044416), by norm_num⟩
  | 12 => ⟨((1088083713/562949953421312), (54701371/281474976710656)), (3/17592186044416), by norm_num⟩
  | 13 => ⟨((-1392373215/4503599627370496), (-17499739/562949953421312)), (125/4503599627370496), by norm_num⟩
  | 14 => ⟨((1654490689/36028797018963968), (83176421/18014398509481984)), (151/36028797018963968), by norm_num⟩
  | 15 => ⟨((-917444445/144115188075855872), (-184491205/288230376151711744)), (171/288230376151711744), by norm_num⟩
  | 16 => ⟨((1907772091/2305843009213693952), (95909669/1152921504606846976)), (181/2305843009213693952), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (32633505315/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889481004731281/316912650057057350374175801344), (154512132667/633825300114114700748351602688)), (92215/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889959256747367/39614081257132168796771975168), (43449125931/9903520314283042199192993792)), (1621/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((944873969949783/1237940039285380274899124224), (184622070849/2475880078570760549798248448)), (110229/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885707107004877/77371252455336267181195264), (46145195413/38685626227668133590597632)), (110231/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549763007683487/9671406556917033397649408), (173000626093/9671406556917033397649408)), (51671/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314743023550225/151115727451828646838272), (151331705825/604462909807314587353088)), (45213/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888090135936815/75557863725914323419136), (245831849433/75557863725914323419136)), (146945/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297763063748157/4722366482869645213696), (23037752165/590295810358705651712)), (110211/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621755646935213/590295810358705651712), (31662317995/73786976294838206464)), (151543/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823859134637651/73786976294838206464), (19778011717/4611686018427387904)), (189435/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823089598860173/9223372036854775808), (355763762387/9223372036854775808)), (213121/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594338254440451/1152921504606846976), (355463450749/1152921504606846976)), (213131/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194889274651163/144115188075855872), (38836626361/18014398509481984)), (186501/144115188075855872), by norm_num⟩
  | 4 => ⟨((746050251105071/18014398509481984), (465365353541/36028797018963968)), (279773/36028797018963968), by norm_num⟩
  | 3 => ⟨((372459283962069/2251799813685248), (145132206625/2251799813685248)), (87439/2251799813685248), by norm_num⟩
  | 2 => ⟨((17414911838717/35184372088832), (289382930401/1125899906842624)), (43727/281474976710656), by norm_num⟩
  | 1 => ⟨((554462236737261/562949953421312), (863754761413/1125899906842624)), (1049753/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092120083357799/1125899906842624), (3420026956447/2251799813685248)), (2100763/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1092120083357799/1125899906842624), (3420026956447/2251799813685248)), (8013774880416106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2118702284419083/2251799813685248), (6634835125327/2251799813685248)), (1020463/562949953421312), by norm_num⟩
  | 2 => ⟨((498363056263329/562949953421312), (12485337507661/2251799813685248)), (7705225/2251799813685248), by norm_num⟩
  | 3 => ⟨((1764675467937831/2251799813685248), (11052902519987/1125899906842624)), (13727865/2251799813685248), by norm_num⟩
  | 4 => ⟨((1382712096165201/2251799813685248), (8661864970407/562949953421312)), (85101/8796093022208), by norm_num⟩
  | 5 => ⟨((1697035662578119/4503599627370496), (85100747568357/4503599627370496)), (54851043/4503599627370496), by norm_num⟩
  | 6 => ⟨((79733106306969/562949953421312), (4008432572965/281474976710656)), (10852657/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-1261609813/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile007Terms0
