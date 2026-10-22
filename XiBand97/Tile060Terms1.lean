/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile060Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨60,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79593/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79593/2560))
  have he : value ((69/80), (79593/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-18337884619/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((117767527154741/1125899906842624), (972191082432457/9007199254740992)), (2421549/4503599627370496), by norm_num⟩
  | 1 => ⟨((-63174244403/274877906944), (-32594637149/137438953472)), (41/34359738368), by norm_num⟩
  | 2 => ⟨((17351000307/68719476736), (35808868917/137438953472)), (91/68719476736), by norm_num⟩
  | 3 => ⟨((-3177003693/17179869184), (-26226708957/137438953472)), (269/274877906944), by norm_num⟩
  | 4 => ⟨((13961181193/137438953472), (57625969503/549755813888)), (149/274877906944), by norm_num⟩
  | 5 => ⟨((-49081360713/1099511627776), (-25323439297/549755813888)), (33/137438953472), by norm_num⟩
  | 6 => ⟨((35947590683/2199023255552), (9273547201/549755813888)), (195/2199023255552), by norm_num⟩
  | 7 => ⟨((-705222587/137438953472), (-2910866547/549755813888)), (247/8796093022208), by norm_num⟩
  | 8 => ⟨((49585036821/35184372088832), (51166620147/35184372088832)), (137/17592186044416), by norm_num⟩
  | 9 => ⟨((-48421982921/140737488355328), (-24983234517/70368744177664)), (135/70368744177664), by norm_num⟩
  | 10 => ⟨((42557588383/562949953421312), (21957510761/281474976710656)), (239/562949953421312), by norm_num⟩
  | 11 => ⟨((-17001559845/1125899906842624), (-35087696219/2251799813685248)), (193/2251799813685248), by norm_num⟩
  | 12 => ⟨((49808326859/18014398509481984), (25698516165/9007199254740992)), (285/18014398509481984), by norm_num⟩
  | 13 => ⟨((-8418467687/18014398509481984), (-34747945427/72057594037927936)), (97/36028797018963968), by norm_num⟩
  | 14 => ⟨((10569865203/144115188075855872), (1363375709/18014398509481984)), (123/288230376151711744), by norm_num⟩
  | 15 => ⟨((-49545317553/4611686018427387904), (-51125633979/4611686018427387904)), (291/4611686018427387904), by norm_num⟩
  | 16 => ⟨((27215547355/18446744073709551616), (56167249755/36893488147419103232)), (161/18446744073709551616), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (65219706689/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55595157583373/19807040628566084398385987584), (1235311981141/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890052607468491/39614081257132168796771975168), (347373664885/9903520314283042199192993792)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889847046297557/2475880078570760549798248448), (738026324287/1237940039285380274899124224)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771513231879139/154742504910672534362390528), (1475731642179/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387463935730563/2417851639229258349412352), (1383157438255/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053143574899/604462909807314587353088), (604960943413/302231454903657293676544)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944110832554557/37778931862957161709568), (982742077019/37778931862957161709568)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297861556688819/4722366482869645213696), (1473554289681/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405472706198171/147573952589676412928), (2025229472757/590295810358705651712)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824027732430177/73786976294838206464), (2530176056035/73786976294838206464)), (2967/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227909844625891/1152921504606846976), (2844578166801/9223372036854775808)), (6677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594526770536653/1152921504606846976), (1421121284923/576460752303423488)), (835/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195053505179705/144115188075855872), (2484337138479/144115188075855872)), (731/18014398509481984), by norm_num⟩
  | 4 => ⟨((746172704507829/18014398509481984), (1860630786407/18014398509481984)), (1097/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490140758143473/9007199254740992), (580301675785/1125899906842624)), (10979/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229708454311151/4503599627370496), (4628695380077/2251799813685248)), (21985/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109364944503209/1125899906842624), (13817686849901/2251799813685248)), (33045/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185927969297393/2251799813685248), (27362918762099/2251799813685248)), (66369/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185927969297393/2251799813685248), (27362918762099/2251799813685248)), (253177651412200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2121650569734543/2251799813685248), (6640617993679/281474976710656)), (130469/2251799813685248), by norm_num⟩
  | 2 => ⟨((1997770340438479/2251799813685248), (100108870169027/2251799813685248)), (126007/1125899906842624), by norm_num⟩
  | 3 => ⟨((1767947809149975/2251799813685248), (177630827059339/2251799813685248)), (469577/2251799813685248), by norm_num⟩
  | 4 => ⟨((1374050537864063/2251799813685248), (17432834705625/140737488355328)), (50715/140737488355328), by norm_num⟩
  | 5 => ⟨((803897182946431/2251799813685248), (170200535647491/1125899906842624)), (1191307/2251799813685248), by norm_num⟩
  | 6 => ⟨((117767527154741/1125899906842624), (972191082432457/9007199254740992)), (2421549/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-18337884619/268435456)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-76868864833/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-242830244085495/2251799813685248), (-191169632817529/2251799813685248)), (1752405/2251799813685248), by norm_num⟩
  | 1 => ⟨((68254064961/274877906944), (26866720383/137438953472)), (495/274877906944), by norm_num⟩
  | 2 => ⟨((-39290198129/137438953472), (-15465727463/68719476736)), (287/137438953472), by norm_num⟩
  | 3 => ⟨((117798209/536870912), (47481538011/274877906944)), (443/274877906944), by norm_num⟩
  | 4 => ⟨((-34718771203/274877906944), (-6833142601/68719476736)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((63954340015/1099511627776), (12587113833/274877906944)), (237/549755813888), by norm_num⟩
  | 6 => ⟨((-49086769983/2199023255552), (-38643867567/2199023255552)), (183/1099511627776), by norm_num⟩
  | 7 => ⟨((64586551329/8796093022208), (25423083827/4398046511104)), (121/2199023255552), by norm_num⟩
  | 8 => ⟨((-74358015149/35184372088832), (-29269406919/17592186044416)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((9511980957/17592186044416), (14976733345/35184372088832)), (9/2199023255552), by norm_num⟩
  | 10 => ⟨((-17521716445/140737488355328), (-55176324707/562949953421312)), (533/562949953421312), by norm_num⟩
  | 11 => ⟨((58683989949/2251799813685248), (2887458699/140737488355328)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((-22520813409/4503599627370496), (-35459303237/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 13 => ⟨((63822879061/72057594037927936), (50244961871/72057594037927936)), (493/72057594037927936), by norm_num⟩
  | 14 => ⟨((-10496972137/72057594037927936), (-33055228629/288230376151711744)), (163/144115188075855872), by norm_num⟩
  | 15 => ⟨((25781516335/1152921504606846976), (40593320899/2305843009213693952)), (403/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-14841033797/4611686018427387904), (-11683696947/4611686018427387904)), (467/18446744073709551616), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-3223534917817/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778897949746299/633825300114114700748351602688), (-3815444053337/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889886759623647/39614081257132168796771975168), (-1072902657445/9903520314283042199192993792)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889670353498185/2475880078570760549798248448), (-2279455266787/1237940039285380274899124224)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221417000011901/19342813113834066795298816), (-4557869140927/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549689015817687/9671406556917033397649408), (-133496750133/302231454903657293676544)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629453342730321/302231454903657293676544), (-3736802872945/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887982599234661/75557863725914323419136), (-6070231065745/75557863725914323419136)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297681320643129/4722366482869645213696), (-1137714822371/1180591620717411303424)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621641479818723/590295810358705651712), (-6254484493655/590295810358705651712)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823713773444267/73786976294838206464), (-7813686362843/73786976294838206464)), (1491/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911461212920651/4611686018427387904), (-8784322781223/9223372036854775808)), (1679/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594166537168879/1152921504606846976), (-4388366479563/576460752303423488)), (6723/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194733920526591/144115188075855872), (-7671107123869/144115188075855872)), (5891/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491857294896181/36028797018963968), (-5744801552309/18014398509481984)), (2213/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489515378907543/9007199254740992), (-14332177561653/9007199254740992)), (5547/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114206099654087/2251799813685248), (-14287487069691/2251799813685248)), (87/17592186044416), by norm_num⟩
  | 1 => ⟨((554168127414701/562949953421312), (-2664959529331/140737488355328)), (16811/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090682837810993/1125899906842624), (-42194169380645/1125899906842624)), (17025/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090682837810993/1125899906842624), (-42194169380645/1125899906842624)), (64945223094749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((263746514576217/281474976710656), (-10218594059621/140737488355328)), (68523/1125899906842624), by norm_num⟩
  | 2 => ⟨((491301543752921/562949953421312), (-153199753588881/1125899906842624)), (69183/562949953421312), by norm_num⟩
  | 3 => ⟨((104587301383443/140737488355328), (-534806158049039/2251799813685248)), (558333/2251799813685248), by norm_num⟩
  | 4 => ⟨((139568317883123/281474976710656), (-794868993148101/2251799813685248)), (136881/281474976710656), by norm_num⟩
  | 5 => ⟨((546104909348779/4503599627370496), (-788265654073911/2251799813685248)), (3718079/4503599627370496), by norm_num⟩
  | 6 => ⟨((-242830244085495/2251799813685248), (-191169632817529/2251799813685248)), (1752405/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-76868864833/1073741824)), (1/536870912), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-80050673553/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((755563672882003/9007199254740992), (212960879637725/2251799813685248)), (4190053/9007199254740992), by norm_num⟩
  | 1 => ⟨((-55290605453/274877906944), (-62336167795/274877906944)), (309/274877906944), by norm_num⟩
  | 2 => ⟨((33145270361/137438953472), (4671112565/17179869184)), (187/137438953472), by norm_num⟩
  | 3 => ⟨((-52985924743/274877906944), (-14934451651/68719476736)), (301/274877906944), by norm_num⟩
  | 4 => ⟨((63527349233/549755813888), (71622502031/549755813888)), (363/549755813888), by norm_num⟩
  | 5 => ⟨((-7616596521/137438953472), (-34348651809/549755813888)), (351/1099511627776), by norm_num⟩
  | 6 => ⟨((12175867195/549755813888), (54909646533/2199023255552)), (141/1099511627776), by norm_num⟩
  | 7 => ⟨((-33367376445/4398046511104), (-37619309101/4398046511104)), (195/4398046511104), by norm_num⟩
  | 8 => ⟨((40005737121/17592186044416), (45103581729/17592186044416)), (59/4398046511104), by norm_num⟩
  | 9 => ⟨((-42635363523/70368744177664), (-12017073935/17592186044416)), (127/35184372088832), by norm_num⟩
  | 10 => ⟨((20447027329/140737488355328), (23052547825/140737488355328)), (123/140737488355328), by norm_num⟩
  | 11 => ⟨((-35658058309/1125899906842624), (-10050471901/281474976710656)), (27/140737488355328), by norm_num⟩
  | 12 => ⟨((57002859637/9007199254740992), (64266610829/9007199254740992)), (87/2251799813685248), by norm_num⟩
  | 13 => ⟨((-42057503895/36028797018963968), (-47416800709/36028797018963968)), (259/36028797018963968), by norm_num⟩
  | 14 => ⟨((900441873/4503599627370496), (16242931753/72057594037927936)), (357/288230376151711744), by norm_num⟩
  | 15 => ⟨((-9212438659/288230376151711744), (-20772719609/576460752303423488)), (115/576460752303423488), by norm_num⟩
  | 16 => ⟨((44180926223/9223372036854775808), (49810806153/9223372036854775808)), (139/4611686018427387904), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (1100999011509/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889389048088781/316912650057057350374175801344), (325747231307/158456325028528675187087900672)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889752339867353/39614081257132168796771975168), (91599831369/2475880078570760549798248448)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889528069681385/2475880078570760549798248448), (778434306479/1237940039285380274899124224)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885597160086723/77371252455336267181195264), (1556499155403/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549556832151093/9671406556917033397649408), (1458825526821/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157348958198351/75557863725914323419136), (1276080036557/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((14748413223439/590295810358705651712), (2072894778315/75557863725914323419136)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324385772585401/1180591620717411303424), (1554027992971/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621453117181549/590295810358705651712), (2135743992945/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911740436613707/36893488147419103232), (2668114163531/73786976294838206464)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822663918772831/9223372036854775808), (2999476912471/9223372036854775808)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((3113110165991/2251799813685248), (2996789746241/1152921504606846976)), (6681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74657279169713/9007199254740992), (2619171037311/144115188075855872)), (5849/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491540913153751/36028797018963968), (3922724245107/36028797018963968)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489136994394277/9007199254740992), (2446432999509/4503599627370496)), (5491/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227706486522807/4503599627370496), (2438545728337/1125899906842624)), (2749/562949953421312), by norm_num⟩
  | 1 => ⟨((553935201695915/562949953421312), (14552642098791/2251799813685248)), (33061/2251799813685248), by norm_num⟩
  | 0 => ⟨((272500637995345/281474976710656), (7198048459789/562949953421312)), (4151/140737488355328), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272500637995345/281474976710656), (7198048459789/562949953421312)), (15834808886480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((263766412205025/281474976710656), (3484275619339/140737488355328)), (16287/281474976710656), by norm_num⟩
  | 2 => ⟨((123499716233413/140737488355328), (104482169177401/2251799813685248)), (125325/1125899906842624), by norm_num⟩
  | 3 => ⟨((864562095962589/1125899906842624), (183370023092671/2251799813685248)), (463161/2251799813685248), by norm_num⟩
  | 4 => ⟨((1312836908398959/2251799813685248), (281614325639815/2251799813685248)), (786743/2251799813685248), by norm_num⟩
  | 5 => ⟨((22818332218857/70368744177664), (164185856303437/1125899906842624)), (139269/281474976710656), by norm_num⟩
  | 6 => ⟨((755563672882003/9007199254740992), (212960879637725/2251799813685248)), (4190053/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-80050673553/1073741824)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-82955437333/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-301299598277025/9007199254740992), (-1012439020666595/9007199254740992)), (5707245/9007199254740992), by norm_num⟩
  | 1 => ⟨((11424276357/137438953472), (76776625213/274877906944)), (435/274877906944), by norm_num⟩
  | 2 => ⟨((-28388260289/274877906944), (-47695686635/137438953472)), (543/274877906944), by norm_num⟩
  | 3 => ⟨((23514058923/274877906944), (19753221481/68719476736)), (113/68719476736), by norm_num⟩
  | 4 => ⟨((-29215120691/549755813888), (-49084911413/274877906944)), (141/137438953472), by norm_num⟩
  | 5 => ⟨((226865149/8589934592), (24394284555/274877906944)), (563/1099511627776), by norm_num⟩
  | 6 => ⟨((-24052851941/2199023255552), (-80823359877/2199023255552)), (469/2199023255552), by norm_num⟩
  | 7 => ⟨((17076883353/4398046511104), (28691214917/2199023255552)), (335/4398046511104), by norm_num⟩
  | 8 => ⟨((-21217230501/17592186044416), (-35647495369/8796093022208)), (209/8796093022208), by norm_num⟩
  | 9 => ⟨((2929046509/8796093022208), (78738398481/70368744177664)), (463/70368744177664), by norm_num⟩
  | 10 => ⟨((-23290902873/281474976710656), (-9782878499/35184372088832)), (231/140737488355328), by norm_num⟩
  | 11 => ⟨((5261429039/281474976710656), (35359330671/562949953421312)), (419/1125899906842624), by norm_num⟩
  | 12 => ⟨((-8716106671/2251799813685248), (-58576423945/4503599627370496)), (349/4503599627370496), by norm_num⟩
  | 13 => ⟨((26656875603/36028797018963968), (89573504851/36028797018963968)), (67/4503599627370496), by norm_num⟩
  | 14 => ⟨((-4731417675/36028797018963968), (-31797399693/72057594037927936)), (383/144115188075855872), by norm_num⟩
  | 15 => ⟨((12540939993/576460752303423488), (84281141273/1152921504606846976)), (255/576460752303423488), by norm_num⟩
  | 16 => ⟨((-31163065183/9223372036854775808), (-104715384201/9223372036854775808)), (159/2305843009213693952), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-2422919920805/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889329459425583/316912650057057350374175801344), (-1433537531619/316912650057057350374175801344)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944809046559953/19807040628566084398385987584), (-806212349295/9903520314283042199192993792)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889385205689537/2475880078570760549798248448), (-3425652691507/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771051201240811/154742504910672534362390528), (-1712404690581/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549422387469019/9671406556917033397649408), (-25077054675/75557863725914323419136)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314668439005791/151115727451828646838272), (-1403867287721/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29493824732695/1180591620717411303424), (-4560890059817/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297398565185603/4722366482869645213696), (-854799818795/1180591620717411303424)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621253676278359/590295810358705651712), (-4699014053891/590295810358705651712)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823230495379085/73786976294838206464), (-2935095936545/36893488147419103232)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911190382820723/4611686018427387904), (-6599052088069/9223372036854775808)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398406851985625/288230376151711744), (-6592914091105/1152921504606846976)), (6707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194265024912585/144115188075855872), (-1406713959/35184372088832)), (5875/144115188075855872), by norm_num⟩
  | 4 => ⟨((186394953023475/4503599627370496), (-4314533066577/18014398509481984)), (1103/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488653190333443/9007199254740992), (-5381121233843/4503599627370496)), (2763/2251799813685248), by norm_num⟩
  | 2 => ⟨((556679352996233/1125899906842624), (-2681543059793/562949953421312)), (11083/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214203920207151/2251799813685248), (-31998620690787/2251799813685248)), (33409/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176720569511417/2251799813685248), (-63280384987529/2251799813685248)), (8433/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176720569511417/2251799813685248), (-63280384987529/2251799813685248)), (32169343114757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2102366294658403/2251799813685248), (-122340995688713/2251799813685248)), (67111/1125899906842624), by norm_num⟩
  | 2 => ⟨((244525328745837/281474976710656), (-114222225362903/1125899906842624)), (265215/2251799813685248), by norm_num⟩
  | 3 => ⟨((209529164153577/281474976710656), (-396912401000477/2251799813685248)), (514613/2251799813685248), by norm_num⟩
  | 4 => ⟨((1177821691870937/2251799813685248), (-147730225606003/562949953421312)), (473785/1125899906842624), by norm_num⟩
  | 5 => ⟨((921997078613497/4503599627370496), (-1236343395758423/4503599627370496)), (744297/1125899906842624), by norm_num⟩
  | 6 => ⟨((-301299598277025/9007199254740992), (-1012439020666595/9007199254740992)), (5707245/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-82955437333/1073741824)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-85627560981/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-175366414402467/4503599627370496), (921357250878507/9007199254740992)), (2702435/4503599627370496), by norm_num⟩
  | 1 => ⟨((6863494445/68719476736), (-36060099619/137438953472)), (425/274877906944), by norm_num⟩
  | 2 => ⟨((-35209031333/274877906944), (23123082337/68719476736)), (137/68719476736), by norm_num⟩
  | 3 => ⟨((3762890929/34359738368), (-19769845061/68719476736)), (471/274877906944), by norm_num⟩
  | 4 => ⟨((-19303249341/274877906944), (50708651387/274877906944)), (19/17179869184), by norm_num⟩
  | 5 => ⟨((9902371399/274877906944), (-52026049117/549755813888)), (157/274877906944), by norm_num⟩
  | 6 => ⟨((-33865441543/2199023255552), (88962787503/2199023255552)), (539/2199023255552), by norm_num⟩
  | 7 => ⟨((12409020361/2199023255552), (-65195727041/4398046511104)), (397/4398046511104), by norm_num⟩
  | 8 => ⟨((-15914254401/8796093022208), (20902967273/4398046511104)), (511/17592186044416), by norm_num⟩
  | 9 => ⟨((36283783645/70368744177664), (-95315648847/70368744177664)), (585/70368744177664), by norm_num⟩
  | 10 => ⟨((-37226427019/281474976710656), (97791924907/281474976710656)), (301/140737488355328), by norm_num⟩
  | 11 => ⟨((34721418205/1125899906842624), (-45605697265/562949953421312)), (141/281474976710656), by norm_num⟩
  | 12 => ⟨((-29686226439/4503599627370496), (38992101299/2251799813685248)), (121/1125899906842624), by norm_num⟩
  | 13 => ⟨((5857205187/4503599627370496), (-30773158515/9007199254740992)), (3/140737488355328), by norm_num⟩
  | 14 => ⟨((-34339279271/144115188075855872), (90207535041/144115188075855872)), (565/144115188075855872), by norm_num⟩
  | 15 => ⟨((23487603281/576460752303423488), (-61700735745/576460752303423488)), (389/576460752303423488), by norm_num⟩
  | 16 => ⟨((-3765282059/576460752303423488), (19782407813/1152921504606846976)), (501/4611686018427387904), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (2519939287535/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778552152112841/633825300114114700748351602688), (2981539655673/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944748991987863/19807040628566084398385987584), (3353577888137/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889257591667925/2475880078570760549798248448), (890592914107/618970019642690137449562112)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770923589432927/154742504910672534362390528), (3561466428205/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774651376884733/4835703278458516698824704), (1668956607449/4835703278458516698824704)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629284539463471/302231454903657293676544), (729928193805/151115727451828646838272)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887434687137661/75557863725914323419136), (4742731426667/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648635498686897/2361183241434822606848), (3555472547561/4722366482869645213696)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810539138562869/295147905179352825856), (4886214806533/590295810358705651712)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823011256463875/73786976294838206464), (6103930495887/73786976294838206464)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911067067939213/4611686018427387904), (3430823819769/4611686018427387904)), (6703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593380796046739/1152921504606846976), (856882446951/144115188075855872)), (6709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194049260079905/144115188075855872), (5990771943489/144115188075855872)), (5877/144115188075855872), by norm_num⟩
  | 4 => ⟨((745418009638273/18014398509481984), (8971363505257/36028797018963968)), (2207/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488248760944525/9007199254740992), (2797087514237/2251799813685248)), (691/562949953421312), by norm_num⟩
  | 2 => ⟨((2225908794051771/4503599627370496), (22299280621271/4503599627370496)), (22179/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106495816155131/1125899906842624), (33255873977965/2251799813685248)), (33435/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174298769571135/2251799813685248), (65742567539495/2251799813685248)), (33771/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174298769571135/2251799813685248), (65742567539495/2251799813685248)), (128826145652389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2097545716749079/2251799813685248), (126959761556807/2251799813685248)), (33595/562949953421312), by norm_num⟩
  | 2 => ⟨((1946700246690123/2251799813685248), (29565672582717/281474976710656)), (265503/2251799813685248), by norm_num⟩
  | 3 => ⟨((414523703669701/562949953421312), (204478219637617/1125899906842624)), (128709/562949953421312), by norm_num⟩
  | 4 => ⟨((1146653014867409/2251799813685248), (150565904497973/562949953421312)), (472597/1125899906842624), by norm_num⟩
  | 5 => ⟨((211406818928025/1125899906842624), (306682409829831/1125899906842624)), (2936435/4503599627370496), by norm_num⟩
  | 6 => ⟨((-175366414402467/4503599627370496), (921357250878507/9007199254740992)), (2702435/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-85627560981/1073741824)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-2753173783/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((215593776617085/2251799813685248), (-167025364287897/4503599627370496)), (619711/2251799813685248), by norm_num⟩
  | 1 => ⟨((-34726827173/137438953472), (13451828365/137438953472)), (101/137438953472), by norm_num⟩
  | 2 => ⟨((91646087785/274877906944), (-35500146243/274877906944)), (269/274877906944), by norm_num⟩
  | 3 => ⟨((-20154939975/68719476736), (31228973715/274877906944)), (239/274877906944), by norm_num⟩
  | 4 => ⟨((53190042069/274877906944), (-20603762995/274877906944)), (159/274877906944), by norm_num⟩
  | 5 => ⟨((-28074314077/274877906944), (5437451175/137438953472)), (169/549755813888), by norm_num⟩
  | 6 => ⟨((98786299119/2199023255552), (-19132993837/1099511627776)), (75/549755813888), by norm_num⟩
  | 7 => ⟨((-74486487645/4398046511104), (28853181499/4398046511104)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((98287055589/17592186044416), (-38072600059/17592186044416)), (303/17592186044416), by norm_num⟩
  | 9 => ⟨((-7205143735/4398046511104), (2790993729/4398046511104)), (179/35184372088832), by norm_num⟩
  | 10 => ⟨((60847319631/140737488355328), (-2946236983/17592186044416)), (191/140737488355328), by norm_num⟩
  | 11 => ⟨((-3649535565/35184372088832), (22619020523/562949953421312)), (185/562949953421312), by norm_num⟩
  | 12 => ⟨((6420889055/281474976710656), (-19897630633/2251799813685248)), (165/2251799813685248), by norm_num⟩
  | 13 => ⟨((-41711001411/9007199254740992), (8078613533/4503599627370496)), (135/9007199254740992), by norm_num⟩
  | 14 => ⟨((62901556571/72057594037927936), (-24365627723/72057594037927936)), (205/72057594037927936), by norm_num⟩
  | 15 => ⟨((-22133441855/144115188075855872), (34294553831/576460752303423488)), (291/576460752303423488), by norm_num⟩
  | 16 => ⟨((58411421957/2305843009213693952), (-22626323413/2305843009213693952)), (97/1152921504606846976), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-120349487817/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444614558032045/158456325028528675187087900672), (-142379981757/158456325028528675187087900672)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889392602587643/39614081257132168796771975168), (-640583232227/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889145987716153/2475880078570760549798248448), (-680461709261/2475880078570760549798248448)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885406197188327/77371252455336267181195264), (-680284062027/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549198942571965/9671406556917033397649408), (-39848601441/604462909807314587353088)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258478677977599/604462909807314587353088), (-557691808331/604462909807314587353088)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887288598382775/75557863725914323419136), (-905895696919/75557863725914323419136)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81072633832457/295147905179352825856), (-679112623031/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202616219170335/73786976294838206464), (-933277779883/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911413664753937/36893488147419103232), (-1165844619301/73786976294838206464)), (2963/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227741198762785/1152921504606846976), (-655270595793/4611686018427387904)), (6667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593179209932627/1152921504606846976), (-654624962663/576460752303423488)), (6669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298469048608841/36028797018963968), (-1144142713523/144115188075855872)), (5837/144115188075855872), by norm_num⟩
  | 4 => ⟨((93161440419641/2251799813685248), (-856658190561/18014398509481984)), (2189/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487944099018589/9007199254740992), (-2136584075033/9007199254740992)), (10949/9007199254740992), by norm_num⟩
  | 2 => ⟨((139083372857481/281474976710656), (-532252761323/562949953421312)), (21911/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212215050128243/2251799813685248), (-6349301160803/2251799813685248)), (32899/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086542395189075/1125899906842624), (-12548470809017/2251799813685248)), (32965/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086542395189075/1125899906842624), (-12548470809017/2251799813685248)), (125751499656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2097051440076749/2251799813685248), (-24219640566495/2251799813685248)), (127987/2251799813685248), by norm_num⟩
  | 2 => ⟨((976338599154313/1125899906842624), (-45110432836379/2251799813685248)), (241137/2251799813685248), by norm_num⟩
  | 3 => ⟨((1692385471604991/2251799813685248), (-78236185179597/2251799813685248)), (427873/2251799813685248), by norm_num⟩
  | 4 => ⟨((1269228137625063/2251799813685248), (-117599959238877/2251799813685248)), (336443/1125899906842624), by norm_num⟩
  | 5 => ⟨((709259457798961/2251799813685248), (-265141113064159/4503599627370496)), (207207/562949953421312), by norm_num⟩
  | 6 => ⟨((215593776617085/2251799813685248), (-167025364287897/4503599627370496)), (619711/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-2753173783/33554432)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-11300600003/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-705656652512749/9007199254740992), (-127809411716907/2251799813685248)), (4959997/9007199254740992), by norm_num⟩
  | 1 => ⟨((29158838497/137438953472), (10562570285/68719476736)), (103/68719476736), by norm_num⟩
  | 2 => ⟨((-78963598455/274877906944), (-57207941169/274877906944)), (561/274877906944), by norm_num⟩
  | 3 => ⟨((35639564779/137438953472), (25820329431/137438953472)), (509/274877906944), by norm_num⟩
  | 4 => ⟨((-48256865283/274877906944), (-17480687077/137438953472)), (173/137438953472), by norm_num⟩
  | 5 => ⟨((26136402747/274877906944), (37870862523/549755813888)), (377/549755813888), by norm_num⟩
  | 6 => ⟨((-23592896905/549755813888), (-34185398957/1099511627776)), (171/549755813888), by norm_num⟩
  | 7 => ⟨((73017999095/4398046511104), (26450221863/2199023255552)), (133/1099511627776), by norm_num⟩
  | 8 => ⟨((-49434101783/8796093022208), (-17907132159/4398046511104)), (181/4398046511104), by norm_num⟩
  | 9 => ⟨((59497790789/35184372088832), (21552627931/17592186044416)), (219/17592186044416), by norm_num⟩
  | 10 => ⟨((-16112300431/35184372088832), (-23346239361/70368744177664)), (477/140737488355328), by norm_num⟩
  | 11 => ⟨((7933257895/70368744177664), (45980209597/562949953421312)), (59/70368744177664), by norm_num⟩
  | 12 => ⟨((-57289761701/2251799813685248), (-41505571949/2251799813685248)), (107/562949953421312), by norm_num⟩
  | 13 => ⟨((47736477137/9007199254740992), (17292180379/4503599627370496)), (179/4503599627370496), by norm_num⟩
  | 14 => ⟨((-36935079003/36028797018963968), (-13379455015/18014398509481984)), (139/18014398509481984), by norm_num⟩
  | 15 => ⟨((53345092331/288230376151711744), (38647718233/288230376151711744)), (101/72057594037927936), by norm_num⟩
  | 16 => ⟨((-72230594007/2305843009213693952), (-26164990283/1152921504606846976)), (549/2305843009213693952), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (-818894018431/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778358663705561/633825300114114700748351602688), (-3874803733865/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889280170757859/39614081257132168796771975168), (-4358251645099/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889025977096207/2475880078570760549798248448), (-2314768639669/1237940039285380274899124224)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770691763574735/154742504910672534362390528), (-4628294270507/154742504910672534362390528)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387271298183983/2417851639229258349412352), (-2168852736867/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314594622239133/151115727451828646838272), (-3794172212755/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887124558790599/75557863725914323419136), (-3081527699551/37778931862957161709568)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81064877150151/295147905179352825856), (-2310063552963/2361183241434822606848)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620757358030967/590295810358705651712), (-6349158857929/590295810358705651712)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227826152081135/9223372036854775808), (-7931176992377/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821680618580073/9223372036854775808), (-8915329414285/9223372036854775808)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592925754427443/1152921504606846976), (-1113284889807/144115188075855872)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596824694518541/72057594037927936), (-7782820322873/144115188075855872)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490232806527285/36028797018963968), (-11653901871265/36028797018963968)), (4427/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487488813526977/9007199254740992), (-14531845479037/9007199254740992)), (11097/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112185610928651/2251799813685248), (-3619658538605/562949953421312)), (2785/562949953421312), by norm_num⟩
  | 1 => ⟨((1105320744559333/1125899906842624), (-1349076607873/70368744177664)), (8409/562949953421312), by norm_num⟩
  | 0 => ⟨((271178223029925/281474976710656), (-42641367652681/1125899906842624)), (34073/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((271178223029925/281474976710656), (-42641367652681/1125899906842624)), (129978184226607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521708797094519/562949953421312), (-82162971946927/1125899906842624)), (136469/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921963960256947/2251799813685248), (-152287587909477/1125899906842624)), (136431/1125899906842624), by norm_num⟩
  | 3 => ⟨((49976403943017/70368744177664), (-519924113640393/2251799813685248)), (539603/2251799813685248), by norm_num⟩
  | 4 => ⟨((126968616174043/281474976710656), (-738507922136687/2251799813685248)), (507821/1125899906842624), by norm_num⟩
  | 5 => ⟨((431967294381371/4503599627370496), (-333128472033419/1125899906842624)), (1582465/2251799813685248), by norm_num⟩
  | 6 => ⟨((-705656652512749/9007199254740992), (-127809411716907/2251799813685248)), (4959997/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-11300600003/134217728)), (1/536870912), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile060Terms1
