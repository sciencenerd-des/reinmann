/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile056Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨56,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78161/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78161/2560))
  have he : value ((69/80), (78161/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-9003978991/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-300127590998037/4503599627370496), (1213456803109555/9007199254740992)), (29969009/9007199254740992), by norm_num⟩
  | 1 => ⟨((5031186823/34359738368), (-5085443709/17179869184)), (505/68719476736), by norm_num⟩
  | 2 => ⟨((-11054647341/68719476736), (698366369/2147483648)), (279/34359738368), by norm_num⟩
  | 3 => ⟨((8096514277/68719476736), (-16367655999/68719476736)), (411/68719476736), by norm_num⟩
  | 4 => ⟨((-277966565/4294967296), (17981708017/137438953472)), (227/68719476736), by norm_num⟩
  | 5 => ⟨((3908831797/137438953472), (-15803940319/274877906944)), (401/274877906944), by norm_num⟩
  | 6 => ⟨((-2862860431/274877906944), (5787467681/274877906944)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((7188968343/2199023255552), (-1816623747/274877906944)), (187/1099511627776), by norm_num⟩
  | 8 => ⟨((-1974472241/2199023255552), (15966121379/8796093022208)), (413/8796093022208), by norm_num⟩
  | 9 => ⟨((7712638107/35184372088832), (-15591624133/35184372088832)), (203/17592186044416), by norm_num⟩
  | 10 => ⟨((-3389279601/70368744177664), (6851659949/70368744177664)), (359/140737488355328), by norm_num⟩
  | 11 => ⟨((5416006137/562949953421312), (-21897651833/1125899906842624)), (577/1125899906842624), by norm_num⟩
  | 12 => ⟨((-3966727265/2251799813685248), (8019009799/2251799813685248)), (425/4503599627370496), by norm_num⟩
  | 13 => ⟨((10727126939/36028797018963968), (-10842809487/18014398509481984)), (289/18014398509481984), by norm_num⟩
  | 14 => ⟨((-3367129565/72057594037927936), (13613764281/144115188075855872)), (365/144115188075855872), by norm_num⟩
  | 15 => ⟨((7891562491/1152921504606846976), (-15953331983/1152921504606846976)), (215/576460752303423488), by norm_num⟩
  | 16 => ⟨((-8669767529/9223372036854775808), (17526526561/9223372036854775808)), (475/9223372036854775808), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1322259732479/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779040616047647/633825300114114700748351602688), (3130578495059/633825300114114700748351602688)), (2891/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890047375433635/39614081257132168796771975168), (3521305812029/39614081257132168796771975168)), (3253/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944920580861669/1237940039285380274899124224), (1870331525949/1237940039285380274899124224)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885753490667061/77371252455336267181195264), (3739848253481/154742504910672534362390528)), (1729/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549849494418595/9671406556917033397649408), (3505242170341/9671406556917033397649408)), (6485/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629523643885519/302231454903657293676544), (3066221507133/604462909807314587353088)), (11353/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944105710893785/37778931862957161709568), (155655865999/2361183241434822606848)), (9227/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324463309513201/1180591620717411303424), (1867160849625/2361183241434822606848)), (6923/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621878353945397/590295810358705651712), (80193547231/9223372036854775808)), (19047/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824010596557841/73786976294838206464), (1603006757837/18446744073709551616)), (23823/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911628677235309/4611686018427387904), (3604389685633/4611686018427387904)), (6705/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797251358229731/576460752303423488), (7202843555473/1152921504606846976)), (6711/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195029480798197/144115188075855872), (3147907210325/72057594037927936)), (23515/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492303433094991/36028797018963968), (9430384508545/36028797018963968)), (35325/36028797018963968), by norm_num⟩
  | 3 => ⟨((372519481896357/2251799813685248), (1470582969911/1125899906842624)), (44249/9007199254740992), by norm_num⟩
  | 2 => ⟨((278693980472049/562949953421312), (5864867318333/1125899906842624)), (44389/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109209031218761/1125899906842624), (17507440892563/1125899906842624)), (33467/562949953421312), by norm_num⟩
  | 0 => ⟨((546249860134889/562949953421312), (34667208568799/1125899906842624)), (135273/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546249860134889/562949953421312), (34667208568799/1125899906842624)), (516025547507857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((529511467312989/562949953421312), (8409698640565/140737488355328)), (67713/281474976710656), by norm_num⟩
  | 2 => ⟨((496049113814139/562949953421312), (253125555606495/2251799813685248)), (1083795/2251799813685248), by norm_num⟩
  | 3 => ⟨((1719941090062165/2251799813685248), (111522087158201/562949953421312)), (2153655/2251799813685248), by norm_num⟩
  | 4 => ⟨((1225332075137991/2251799813685248), (681451056127301/2251799813685248)), (2071623/1125899906842624), by norm_num⟩
  | 5 => ⟨((115137138985695/562949953421312), (741632388132133/2251799813685248)), (1754213/562949953421312), by norm_num⟩
  | 6 => ⟨((-300127590998037/4503599627370496), (1213456803109555/9007199254740992)), (29969009/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-9003978991/134217728)), (1/134217728), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-18871469049/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((231637553758805/4503599627370496), (-573056251606677/4503599627370496)), (2695777/1125899906842624), by norm_num⟩
  | 1 => ⟨((-2034626687/17179869184), (10067068347/34359738368)), (381/68719476736), by norm_num⟩
  | 2 => ⟨((4684901079/34359738368), (-11590140753/34359738368)), (221/34359738368), by norm_num⟩
  | 3 => ⟨((-1797897231/17179869184), (17791523549/68719476736)), (171/34359738368), by norm_num⟩
  | 4 => ⟨((4139811363/68719476736), (-5120812113/34359738368)), (397/137438953472), by norm_num⟩
  | 5 => ⟨((-3812907173/137438953472), (2358221127/34359738368)), (23/17179869184), by norm_num⟩
  | 6 => ⟨((1463257203/137438953472), (-7240006417/274877906944)), (285/549755813888), by norm_num⟩
  | 7 => ⟨((-481324889/137438953472), (19052263827/2199023255552)), (377/2199023255552), by norm_num⟩
  | 8 => ⟨((4433166057/4398046511104), (-10967364669/4398046511104)), (437/8796093022208), by norm_num⟩
  | 9 => ⟨((-9073548513/35184372088832), (22447369241/35184372088832)), (225/17592186044416), by norm_num⟩
  | 10 => ⟨((4178523509/70368744177664), (-5168697779/35184372088832)), (417/140737488355328), by norm_num⟩
  | 11 => ⟨((-1749346535/140737488355328), (17311078481/562949953421312)), (351/562949953421312), by norm_num⟩
  | 12 => ⟨((5370692339/2251799813685248), (-13286743751/2251799813685248)), (271/2251799813685248), by norm_num⟩
  | 13 => ⟨((-3805069575/9007199254740992), (18826989597/18014398509481984)), (193/9007199254740992), by norm_num⟩
  | 14 => ⟨((2503284709/36028797018963968), (-774120457/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 15 => ⟨((-3074147229/288230376151711744), (15210480849/576460752303423488)), (79/144115188075855872), by norm_num⟩
  | 16 => ⟨((7078485583/4611686018427387904), (-8755856615/2305843009213693952)), (183/2305843009213693952), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-772879995037/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778903948664817/633825300114114700748351602688), (-914797095793/316912650057057350374175801344)), (11549/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889893848435881/39614081257132168796771975168), (-2057934095065/39614081257132168796771975168)), (12993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889678326322773/2475880078570760549798248448), (-1093055933663/1237940039285380274899124224)), (13807/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771344468642355/154742504910672534362390528), (-1092806758669/77371252455336267181195264)), (13809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549697481464223/9671406556917033397649408), (-2048483317497/9671406556917033397649408)), (3237/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258914618923227/604462909807314587353088), (-1791893707381/604462909807314587353088)), (2833/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235999559579253/9444732965739290427392), (-2910835372067/75557863725914323419136)), (18417/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81105786891063/295147905179352825856), (-2182258953317/4722366482869645213696)), (1727/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621658374140699/590295810358705651712), (-2999196885423/590295810358705651712)), (19003/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823736986734037/73786976294838206464), (-936720863695/18446744073709551616)), (23761/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822951417862515/9223372036854775808), (-263271299671/576460752303423488)), (13371/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797099559700965/576460752303423488), (-4208714635211/1152921504606846976)), (26755/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194766460553839/144115188075855872), (-3678549593627/144115188075855872)), (23427/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491914145070755/36028797018963968), (-172177570363/1125899906842624)), (17585/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489600464648035/9007199254740992), (-3436437471483/4503599627370496)), (22009/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228624251346291/4503599627370496), (-13703149651521/4503599627370496)), (44099/2251799813685248), by norm_num⟩
  | 1 => ⟨((277136828855209/281474976710656), (-10224257624333/1125899906842624)), (33177/562949953421312), by norm_num⟩
  | 0 => ⟨((2182622153018703/2251799813685248), (-20236968971777/1125899906842624)), (33383/281474976710656), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182622153018703/2251799813685248), (-20236968971777/1125899906842624)), (127346039892101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2114842222764741/2251799813685248), (-39230535964443/1125899906842624)), (65915/281474976710656), by norm_num⟩
  | 2 => ⟨((1983480707403853/2251799813685248), (-36844480301965/562949953421312)), (256811/562949953421312), by norm_num⟩
  | 3 => ⟨((1737488137802385/2251799813685248), (-259633437782969/2251799813685248)), (1944145/2251799813685248), by norm_num⟩
  | 4 => ⟨((163838693000795/281474976710656), (-200333091593291/1125899906842624)), (1724263/1125899906842624), by norm_num⟩
  | 5 => ⟨((691636134320131/2251799813685248), (-466433105706491/2251799813685248)), (5241785/2251799813685248), by norm_num⟩
  | 6 => ⟨((231637553758805/4503599627370496), (-573056251606677/4503599627370496)), (2695777/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18871469049/268435456)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-19652609827/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-657649206356943/9007199254740992), (929522115303955/9007199254740992)), (25694707/9007199254740992), by norm_num⟩
  | 1 => ⟨((12031356225/68719476736), (-17005132189/68719476736)), (59/8589934592), by norm_num⟩
  | 2 => ⟨((-3606241527/17179869184), (5097065761/17179869184)), (285/34359738368), by norm_num⟩
  | 3 => ⟨((1441231585/8589934592), (-16296306525/68719476736)), (229/34359738368), by norm_num⟩
  | 4 => ⟨((-13823689619/137438953472), (9769209095/68719476736)), (69/17179869184), by norm_num⟩
  | 5 => ⟨((3314775999/68719476736), (-9370216123/137438953472)), (133/68719476736), by norm_num⟩
  | 6 => ⟨((-10597980931/549755813888), (3744799491/137438953472)), (107/137438953472), by norm_num⟩
  | 7 => ⟨((3630406911/549755813888), (-5131221141/549755813888)), (295/1099511627776), by norm_num⟩
  | 8 => ⟨((-4352667785/2199023255552), (6152065459/2199023255552)), (89/1099511627776), by norm_num⟩
  | 9 => ⟨((9277548005/17592186044416), (-6556448303/8796093022208)), (191/8796093022208), by norm_num⟩
  | 10 => ⟨((-4449317701/35184372088832), (6288670557/35184372088832)), (23/4398046511104), by norm_num⟩
  | 11 => ⟨((7759271187/281474976710656), (-10966962473/281474976710656)), (323/281474976710656), by norm_num⟩
  | 12 => ⟨((-12403946467/2251799813685248), (17531751647/2251799813685248)), (519/2251799813685248), by norm_num⟩
  | 13 => ⟨((2287951123/2251799813685248), (-1616896323/1125899906842624)), (385/9007199254740992), by norm_num⟩
  | 14 => ⟨((-6270019637/36028797018963968), (17724105369/72057594037927936)), (265/36028797018963968), by norm_num⟩
  | 15 => ⟨((4009293453/144115188075855872), (-5666739797/144115188075855872)), (341/288230376151711744), by norm_num⟩
  | 16 => ⟨((-4806932909/1152921504606846976), (3397062143/576460752303423488)), (411/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (2848221542259/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889386461574861/316912650057057350374175801344), (3370757909281/633825300114114700748351602688)), (11567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889746228240947/39614081257132168796771975168), (473925680487/4951760157141521099596496896)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889521195961283/2475880078570760549798248448), (4027517129347/2475880078570760549798248448)), (1729/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771187019159977/154742504910672534362390528), (251659983779/9671406556917033397649408)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549549533740097/9671406556917033397649408), (3773882734335/9671406556917033397649408)), (12975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258784826090695/604462909807314587353088), (3301130598739/604462909807314587353088)), (11357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943892464504145/37778931862957161709568), (5362431220263/75557863725914323419136)), (18461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297533375101867/4722366482869645213696), (4020156148581/4722366482869645213696)), (3463/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621438553380211/590295810358705651712), (5525006306887/590295810358705651712)), (1191/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1823460862711971/73786976294838206464), (6902196881629/73786976294838206464)), (23835/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822638927681141/9223372036854775808), (7759390204897/9223372036854775808)), (13417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398471080077023/288230376151711744), (3876208741477/576460752303423488)), (6715/288230376151711744), by norm_num⟩
  | 5 => ⟨((597244209937243/72057594037927936), (6775526330525/144115188075855872)), (23531/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491491916221855/36028797018963968), (10147624927101/36028797018963968)), (35353/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489063668834607/9007199254740992), (6328574121499/4503599627370496)), (11073/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113761882986509/2251799813685248), (12616134045347/2251799813685248)), (44443/2251799813685248), by norm_num⟩
  | 1 => ⟨((138461071337593/140737488355328), (18821876267969/1125899906842624)), (33521/562949953421312), by norm_num⟩
  | 0 => ⟨((544730739034185/562949953421312), (18617859053447/562949953421312)), (135601/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544730739034185/562949953421312), (18617859053447/562949953421312)), (517276768210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052970878038889/1125899906842624), (144122511207719/2251799813685248)), (542789/2251799813685248), by norm_num⟩
  | 2 => ⟨((980153598674235/1125899906842624), (67393560586187/562949953421312)), (542371/1125899906842624), by norm_num⟩
  | 3 => ⟨((1674275845005221/2251799813685248), (469356400401617/2251799813685248)), (134273/140737488355328), by norm_num⟩
  | 4 => ⟨((286759968500803/562949953421312), (174489774604997/562949953421312)), (4090339/2251799813685248), by norm_num⟩
  | 5 => ⟨((183975849995757/1125899906842624), (1422128044323505/4503599627370496)), (6702791/2251799813685248), by norm_num⟩
  | 6 => ⟨((-657649206356943/9007199254740992), (929522115303955/9007199254740992)), (25694707/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-19652609827/268435456)), (1/134217728), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-5091433871/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((941756955601331/9007199254740992), (-119610842199051/2251799813685248)), (12198189/9007199254740992), by norm_num⟩
  | 1 => ⟨((-8927071081/34359738368), (9070488805/68719476736)), (233/68719476736), by norm_num⟩
  | 2 => ⟨((5545734573/17179869184), (-5634829487/34359738368)), (73/17179869184), by norm_num⟩
  | 3 => ⟨((-9187088479/34359738368), (2333670877/17179869184)), (61/17179869184), by norm_num⟩
  | 4 => ⟨((11414528627/68719476736), (-5798954281/68719476736)), (153/68719476736), by norm_num⟩
  | 5 => ⟨((-2836403809/34359738368), (2881972011/68719476736)), (307/274877906944), by norm_num⟩
  | 6 => ⟨((18795196497/549755813888), (-2387143805/137438953472)), (257/549755813888), by norm_num⟩
  | 7 => ⟨((-13344088217/1099511627776), (1694808433/274877906944)), (23/137438953472), by norm_num⟩
  | 8 => ⟨((16579406773/4398046511104), (-8422881491/4398046511104)), (231/4398046511104), by norm_num⟩
  | 9 => ⟨((-1144396615/1099511627776), (2325563803/4398046511104)), (257/17592186044416), by norm_num⟩
  | 10 => ⟨((18199800055/70368744177664), (-4623047167/35184372088832)), (129/35184372088832), by norm_num⟩
  | 11 => ⟨((-16445383339/281474976710656), (4177396599/140737488355328)), (235/281474976710656), by norm_num⟩
  | 12 => ⟨((13621747473/1125899906842624), (-6920293725/1125899906842624)), (197/1125899906842624), by norm_num⟩
  | 13 => ⟨((-1301875803/562949953421312), (10582328551/9007199254740992)), (19/562949953421312), by norm_num⟩
  | 14 => ⟨((14788753555/36028797018963968), (-7513171025/36028797018963968)), (109/18014398509481984), by norm_num⟩
  | 15 => ⟨((-19599291761/288230376151711744), (4978540971/144115188075855872)), (291/288230376151711744), by norm_num⟩
  | 16 => ⟨((12175602607/1152921504606846976), (-6185604783/1152921504606846976)), (183/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (-4783567875/79228162514264337593543950336)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778663038906181/633825300114114700748351602688), (-724539243083/633825300114114700748351602688)), (11535/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944811479907665/19807040628566084398385987584), (-814954374099/39614081257132168796771975168)), (12977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889390679198753/2475880078570760549798248448), (-865699762681/2475880078570760549798248448)), (13789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771057014935721/154742504910672534362390528), (-865486927357/154742504910672534362390528)), (6895/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96839262438605/604462909807314587353088), (-811167929777/9671406556917033397649408)), (12929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157334900258815/75557863725914323419136), (-709545955981/604462909807314587353088)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887614308918299/75557863725914323419136), (-1152588635413/75557863725914323419136)), (18385/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297406300811431/4722366482869645213696), (-54004440661/295147905179352825856)), (6895/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810632636124253/295147905179352825856), (-1187496078747/590295810358705651712)), (4741/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227905803463671/9223372036854775808), (-1483468245639/73786976294838206464)), (5927/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455600165718729/2305843009213693952), (-1667662655803/9223372036854775808)), (26675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593649767355587/1152921504606846976), (-833057572275/576460752303423488)), (26681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597143676570267/72057594037927936), (-91006981869/9007199254740992)), (2919/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491198628510941/36028797018963968), (-545173561887/9007199254740992)), (1095/1125899906842624), by norm_num⟩
  | 3 => ⟨((1488711556893191/9007199254740992), (-2719800211881/9007199254740992)), (21911/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226862839664661/4503599627370496), (-5421440385069/4503599627370496)), (21927/1125899906842624), by norm_num⟩
  | 1 => ⟨((2214493313470415/2251799813685248), (-8086909774009/2251799813685248)), (8233/140737488355328), by norm_num⟩
  | 0 => ⟨((2177581467192003/2251799813685248), (-7996854666243/1125899906842624)), (132061/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177581467192003/2251799813685248), (-7996854666243/1125899906842624)), (503772739890670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2105695727792007/2251799813685248), (-30933127201107/2251799813685248)), (257293/1125899906842624), by norm_num⟩
  | 2 => ⟨((1968646419074047/2251799813685248), (-3615760679455/140737488355328)), (976535/2251799813685248), by norm_num⟩
  | 3 => ⟨((1719611941579013/2251799813685248), (-50577528397169/1125899906842624)), (1757659/2251799813685248), by norm_num⟩
  | 4 => ⟨((1308656687062849/2251799813685248), (-77248182790267/1125899906842624)), (2842427/2251799813685248), by norm_num⟩
  | 5 => ⟨((1499878619185961/4503599627370496), (-89787156351605/1125899906842624)), (3693851/2251799813685248), by norm_num⟩
  | 6 => ⟨((941756955601331/9007199254740992), (-119610842199051/2251799813685248)), (12198189/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-5091433871/67108864)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-2627718437/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-960408604432165/9007199254740992), (-111274448628523/4503599627370496)), (10606883/4503599627370496), by norm_num⟩
  | 1 => ⟨((18794246161/68719476736), (2177530865/34359738368)), (417/68719476736), by norm_num⟩
  | 2 => ⟨((-24103144807/68719476736), (-5585256393/68719476736)), (537/68719476736), by norm_num⟩
  | 3 => ⟨((2575972741/8589934592), (1193824983/17179869184)), (461/68719476736), by norm_num⟩
  | 4 => ⟨((-26428958507/137438953472), (-3062100623/68719476736)), (593/137438953472), by norm_num⟩
  | 5 => ⟨((3389447007/34359738368), (1570826605/68719476736)), (611/274877906944), by norm_num⟩
  | 6 => ⟨((-11591679897/274877906944), (-5372120921/549755813888)), (525/549755813888), by norm_num⟩
  | 7 => ⟨((16989755373/1099511627776), (1968459729/549755813888)), (387/1099511627776), by norm_num⟩
  | 8 => ⟨((-21788931063/4398046511104), (-5048999517/4398046511104)), (249/2199023255552), by norm_num⟩
  | 9 => ⟨((24838890991/17592186044416), (5755745807/17592186044416)), (285/8796093022208), by norm_num⟩
  | 10 => ⟨((-25484198995/70368744177664), (-1476319651/17592186044416)), (147/17592186044416), by norm_num⟩
  | 11 => ⟨((11884669061/140737488355328), (2753952829/140737488355328)), (551/281474976710656), by norm_num⟩
  | 12 => ⟨((-20322382847/1125899906842624), (-4709166359/1125899906842624)), (237/562949953421312), by norm_num⟩
  | 13 => ⟨((16038733177/4503599627370496), (464568201/562949953421312)), (47/562949953421312), by norm_num⟩
  | 14 => ⟨((-23507736203/36028797018963968), (-5447286439/36028797018963968)), (277/18014398509481984), by norm_num⟩
  | 15 => ⟨((8039487049/72057594037927936), (465733795/18014398509481984)), (381/144115188075855872), by norm_num⟩
  | 16 => ⟨((-5155219285/288230376151711744), (-4778334393/1152921504606846976)), (491/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-3795664870747/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778546111828887/633825300114114700748351602688), (-4490951582739/633825300114114700748351602688)), (11581/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889490850287241/39614081257132168796771975168), (-5051317915103/39614081257132168796771975168)), (1629/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889249568616583/2475880078570760549798248448), (-2682905488951/1237940039285380274899124224)), (13851/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770915067834057/154742504910672534362390528), (-5364444951497/154742504910672534362390528)), (13855/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774647117712393/4835703278458516698824704), (-2513857975085/4835703278458516698824704)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258561096435445/604462909807314587353088), (-4397800501555/604462909807314587353088)), (11375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471855181172183/18889465931478580854784), (-7143705778741/75557863725914323419136)), (18493/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324314914840265/1180591620717411303424), (-2677699903389/2361183241434822606848)), (6939/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621061281436991/590295810358705651712), (-7359808949293/590295810358705651712)), (2387/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822987905795371/73786976294838206464), (-9193964167795/73786976294838206464)), (23889/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911052487566785/4611686018427387904), (-2583810371679/2305843009213693952)), (13451/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796674014061265/576460752303423488), (-645330330521/72057594037927936)), (3367/144115188075855872), by norm_num⟩
  | 5 => ⟨((298504134878141/36028797018963968), (-9023429488269/144115188075855872)), (23607/144115188075855872), by norm_num⟩
  | 4 => ⟨((745389432369771/18014398509481984), (-13512767943579/36028797018963968)), (35487/36028797018963968), by norm_num⟩
  | 3 => ⟨((744081620903969/4503599627370496), (-16851832978855/9007199254740992)), (11123/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112847869729397/2251799813685248), (-8396602929711/1125899906842624)), (22347/1125899906842624), by norm_num⟩
  | 1 => ⟨((553141937124123/562949953421312), (-25043463444659/1125899906842624)), (67545/1125899906842624), by norm_num⟩
  | 0 => ⟨((271629776793767/281474976710656), (-49502887242811/1125899906842624)), (137115/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271629776793767/281474976710656), (-49502887242811/1125899906842624)), (523052219871139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046339223630295/1125899906842624), (-95542832045309/1125899906842624)), (34587/140737488355328), by norm_num⟩
  | 2 => ⟨((964292946072485/1125899906842624), (-88791385538059/562949953421312)), (17539/35184372088832), by norm_num⟩
  | 3 => ⟨((797873096713601/1125899906842624), (-608373133178139/2251799813685248)), (142303/140737488355328), by norm_num⟩
  | 4 => ⟨((120808254770145/281474976710656), (-862251702440271/2251799813685248)), (4457275/2251799813685248), by norm_num⟩
  | 5 => ⟨((169267803824787/4503599627370496), (-370075963986933/1125899906842624)), (14479259/4503599627370496), by norm_num⟩
  | 6 => ⟨((-960408604432165/9007199254740992), (-111274448628523/4503599627370496)), (10606883/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-2627718437/33554432)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-2703639969/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((413994361156601/9007199254740992), (206744011770719/2251799813685248)), (15633615/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4167766011/34359738368), (-16650674427/68719476736)), (317/68719476736), by norm_num⟩
  | 2 => ⟨((10998973439/68719476736), (21971042195/68719476736)), (421/68719476736), by norm_num⟩
  | 3 => ⟨((-9675640491/68719476736), (-19327613315/68719476736)), (373/68719476736), by norm_num⟩
  | 4 => ⟨((6383642489/68719476736), (1593958737/8589934592)), (31/8589934592), by norm_num⟩
  | 5 => ⟨((-842339925/17179869184), (-6730477581/68719476736)), (33/17179869184), by norm_num⟩
  | 6 => ⟨((740994451/34359738368), (11841410795/274877906944)), (117/137438953472), by norm_num⟩
  | 7 => ⟨((-8939551255/1099511627776), (-17857235401/1099511627776)), (355/1099511627776), by norm_num⟩
  | 8 => ⟨((2948998533/1099511627776), (11781566993/2199023255552)), (59/549755813888), by norm_num⟩
  | 9 => ⟨((-6917845505/8796093022208), (-3454692303/2199023255552)), (279/8796093022208), by norm_num⟩
  | 10 => ⟨((3651318177/17592186044416), (7293704835/17592186044416)), (37/4398046511104), by norm_num⟩
  | 11 => ⟨((-7008027635/140737488355328), (-3499728219/35184372088832)), (143/70368744177664), by norm_num⟩
  | 12 => ⟨((770607779/70368744177664), (192416321/8796093022208)), (253/562949953421312), by norm_num⟩
  | 13 => ⟨((-312873555/140737488355328), (-19999417197/4503599627370496)), (413/4503599627370496), by norm_num⟩
  | 14 => ⟨((3774588565/9007199254740992), (15079888155/18014398509481984)), (313/18014398509481984), by norm_num⟩
  | 15 => ⟨((-10625445993/144115188075855872), (-21224900995/144115188075855872)), (443/144115188075855872), by norm_num⟩
  | 16 => ⟨((3505145141/288230376151711744), (14003432635/576460752303423488)), (147/288230376151711744), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (1441546928683/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778456847954635/633825300114114700748351602688), (1705428324877/633825300114114700748351602688)), (11547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944695484055971/19807040628566084398385987584), (959113004557/19807040628566084398385987584)), (203/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889144149468651/2475880078570760549798248448), (2037641904667/2475880078570760549798248448)), (13805/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885405220959489/77371252455336267181195264), (2037109720117/154742504910672534362390528)), (13807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774598495439595/4835703278458516698824704), (1909225097933/9671406556917033397649408)), (6473/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78654803067373/37778931862957161709568), (208750862515/75557863725914323419136)), (5665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887285399432303/75557863725914323419136), (2712702157681/75557863725914323419136)), (18413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324289885923395/1180591620717411303424), (508400094623/1180591620717411303424)), (6907/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202615732448129/73786976294838206464), (2794696192967/590295810358705651712)), (9499/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911410989942211/36893488147419103232), (1745557585257/36893488147419103232)), (23755/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821922909548539/9223372036854775808), (981101537857/2305843009213693952)), (13367/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593171703204419/1152921504606846976), (1960268294885/576460752303423488)), (26747/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596934349405929/72057594037927936), (856530252281/36028797018963968)), (23419/144115188075855872), by norm_num⟩
  | 4 => ⟨((745284977160489/18014398509481984), (2565248180979/18014398509481984)), (8789/9007199254740992), by norm_num⟩
  | 3 => ⟨((743962255115107/4503599627370496), (3198974045853/4503599627370496)), (10999/2251799813685248), by norm_num⟩
  | 2 => ⟨((2225285167631147/4503599627370496), (12750485545601/4503599627370496)), (88145/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212117973910065/2251799813685248), (2376571686771/281474976710656)), (132601/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086398074867289/1125899906842624), (18787376021455/1125899906842624)), (66687/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086398074867289/1125899906842624), (18787376021455/1125899906842624)), (254390718700218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((130996081934851/140737488355328), (72512908181169/2251799813685248)), (261841/1125899906842624), by norm_num⟩
  | 2 => ⟨((1948528045408505/2251799813685248), (134987585361085/2251799813685248)), (1008597/2251799813685248), by norm_num⟩
  | 3 => ⟨((104875549787383/140737488355328), (233614990337515/2251799813685248)), (466611/562949953421312), by norm_num⟩
  | 4 => ⟨((1226191396308663/2251799813685248), (174086526884459/1125899906842624)), (3168967/2251799813685248), by norm_num⟩
  | 5 => ⟨((613873780701819/2251799813685248), (758374346357657/4503599627370496)), (8862439/4503599627370496), by norm_num⟩
  | 6 => ⟨((413994361156601/9007199254740992), (206744011770719/2251799813685248)), (15633615/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-2703639969/33554432)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-11097284897/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((470954232077515/9007199254740992), (-733155749267623/9007199254740992)), (3499307/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4865141689/34359738368), (7573786065/34359738368)), (291/68719476736), by norm_num⟩
  | 2 => ⟨((13175047929/68719476736), (-5127548219/17179869184)), (99/17179869184), by norm_num⟩
  | 3 => ⟨((-1486612133/8589934592), (18514210647/68719476736)), (45/8589934592), by norm_num⟩
  | 4 => ⟨((8051640571/68719476736), (-6267176483/34359738368)), (123/34359738368), by norm_num⟩
  | 5 => ⟨((-8721698747/137438953472), (3394365707/34359738368)), (67/34359738368), by norm_num⟩
  | 6 => ⟨((3936466341/137438953472), (-6128075157/137438953472)), (61/68719476736), by norm_num⟩
  | 7 => ⟨((-12183026819/1099511627776), (18965868755/1099511627776)), (95/274877906944), by norm_num⟩
  | 8 => ⟨((8248062057/2199023255552), (-6420065587/1099511627776)), (259/2199023255552), by norm_num⟩
  | 9 => ⟨((-9927184939/8796093022208), (3863524423/2199023255552)), (157/4398046511104), by norm_num⟩
  | 10 => ⟨((2688331517/8796093022208), (-16740188945/35184372088832)), (171/17592186044416), by norm_num⟩
  | 11 => ⟨((-10589289753/140737488355328), (4121206549/35184372088832)), (339/140737488355328), by norm_num⟩
  | 12 => ⟨((4779388041/281474976710656), (-14880578965/562949953421312)), (77/140737488355328), by norm_num⟩
  | 13 => ⟨((-7964813997/2251799813685248), (6199593055/1125899906842624)), (129/1125899906842624), by norm_num⟩
  | 14 => ⟨((6162604613/9007199254740992), (-2398401317/2251799813685248)), (201/9007199254740992), by norm_num⟩
  | 15 => ⟨((-8900609419/72057594037927936), (1731997645/9007199254740992)), (73/18014398509481984), by norm_num⟩
  | 16 => ⟨((12051648563/576460752303423488), (-18761346283/576460752303423488)), (199/288230376151711744), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1302359645753/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222295679487475/79228162514264337593543950336), (-1540610843593/633825300114114700748351602688)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644083198739/19807040628566084398385987584), (-1732834957759/39614081257132168796771975168)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472258742364667/618970019642690137449562112), (-1840698526779/2475880078570760549798248448)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885350657270413/77371252455336267181195264), (-920102640259/77371252455336267181195264)), (3451/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96818421241071/604462909807314587353088), (-862334276063/4835703278458516698824704)), (12943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629193717649487/302231454903657293676544), (-1508561282551/604462909807314587353088)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943570103362941/37778931862957161709568), (-2450430565747/75557863725914323419136)), (18409/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297050740699693/4722366482869645213696), (-1836964515667/4722366482869645213696)), (13809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810388202048173/295147905179352825856), (-631108020499/147573952589676412928)), (1187/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822635383259129/73786976294838206464), (-3153450288343/73786976294838206464)), (23747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910856647135771/4611686018427387904), (-3544760315043/9223372036854775808)), (6681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99560154364599/72057594037927936), (-3541174590811/1152921504606846976)), (1671/72057594037927936), by norm_num⟩
  | 5 => ⟨((596843024283755/72057594037927936), (-3094498428947/144115188075855872)), (1463/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490296835143947/36028797018963968), (-579212557311/4503599627370496)), (35137/36028797018963968), by norm_num⟩
  | 3 => ⟨((371896151431397/2251799813685248), (-5778068817969/9007199254740992)), (43967/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224609826596025/4503599627370496), (-11514070462369/4503599627370496)), (11009/562949953421312), by norm_num⟩
  | 1 => ⟨((2211116078454623/2251799813685248), (-17166297762921/2251799813685248)), (132455/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170836501400699/2251799813685248), (-33915517290541/2251799813685248)), (133155/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170836501400699/2251799813685248), (-33915517290541/2251799813685248)), (507946018699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2092273400533769/2251799813685248), (-65392174251671/2251799813685248)), (521493/2251799813685248), by norm_num⟩
  | 2 => ⟨((971074741979501/1125899906842624), (-121519067510647/2251799813685248)), (499693/1125899906842624), by norm_num⟩
  | 3 => ⟨((834261045639897/1125899906842624), (-209617385011447/2251799813685248)), (1831781/2251799813685248), by norm_num⟩
  | 4 => ⟨((608408106337257/1125899906842624), (-310641501506749/2251799813685248)), (3055637/2251799813685248), by norm_num⟩
  | 5 => ⟨((1229366433514283/4503599627370496), (-671451543899633/4503599627370496)), (2072723/1125899906842624), by norm_num⟩
  | 6 => ⟨((470954232077515/9007199254740992), (-733155749267623/9007199254740992)), (3499307/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-11097284897/134217728)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile056Terms1
