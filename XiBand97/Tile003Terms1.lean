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
namespace Reinmann.XiBand97.Tile003Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9919/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9919/640))
  have he : value ((69/80), (9919/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-571323727/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1185487287756855/9007199254740992), (-653761108580861/9007199254740992)), (242598231/9007199254740992), by norm_num⟩
  | 1 => ⟨((621028377/2147483648), (684957493/4294967296)), (257/4294967296), by norm_num⟩
  | 2 => ⟨((-682269407/2147483648), (-752502719/4294967296)), (285/4294967296), by norm_num⟩
  | 3 => ⟨((999399407/4294967296), (137784789/1073741824)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((-548976235/4294967296), (-302744125/4294967296)), (117/4294967296), by norm_num⟩
  | 5 => ⟨((964979261/17179869184), (266078733/8589934592)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((-176689679/8589934592), (-48719561/4294967296)), (77/17179869184), by norm_num⟩
  | 7 => ⟨((110921973/17179869184), (61170181/17179869184)), (49/34359738368), by norm_num⟩
  | 8 => ⟨((-974881941/549755813888), (-537618501/549755813888)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((952015361/2199023255552), (131252065/549755813888)), (27/274877906944), by norm_num⟩
  | 10 => ⟨((-209179155/2199023255552), (-461424421/8796093022208)), (3/137438953472), by norm_num⟩
  | 11 => ⟨((1337057689/70368744177664), (368673847/35184372088832)), (155/35184372088832), by norm_num⟩
  | 12 => ⟨((-979272005/281474976710656), (-135009873/70368744177664)), (229/281474976710656), by norm_num⟩
  | 13 => ⟨((82756943/140737488355328), (182552007/562949953421312)), (39/281474976710656), by norm_num⟩
  | 14 => ⟨((-103906051/1125899906842624), (-458408865/9007199254740992)), (99/4503599627370496), by norm_num⟩
  | 15 => ⟨((974101031/72057594037927936), (537187853/72057594037927936)), (117/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1070159363/576460752303423488), (-590161177/576460752303423488)), (65/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3435796187899/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779037009101973/633825300114114700748351602688), (-4067290788277/633825300114114700748351602688)), (92601/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890043112211659/39614081257132168796771975168), (-285932488777/2475880078570760549798248448)), (104201/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944918183407113/1237940039285380274899124224), (-4859910100741/2475880078570760549798248448)), (13843/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771501888224869/154742504910672534362390528), (-4858850136969/154742504910672534362390528)), (110777/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387461100744017/2417851639229258349412352), (-4554045910201/9671406556917033397649408)), (103889/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259042516314227/604462909807314587353088), (-995916052753/151115727451828646838272)), (90939/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472050768819627/18889465931478580854784), (-6471343449587/75557863725914323419136)), (147841/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648923229916235/2361183241434822606848), (-606457604791/590295810358705651712)), (27735/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621868192420269/590295810358705651712), (-6668033216681/590295810358705651712)), (152637/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823996633891495/73786976294838206464), (-1041317724649/9223372036854775808)), (190939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823239915278439/9223372036854775808), (-4682836958077/4611686018427387904)), (215003/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594483116803173/1152921504606846976), (-9357944184909/1152921504606846976)), (13453/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195009905422599/144115188075855872), (-4089754175257/72057594037927936)), (94309/72057594037927936), by norm_num⟩
  | 4 => ⟨((373067307695899/9007199254740992), (-191435699457/562949953421312)), (35435/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490026733220879/9007199254740992), (-3821115655789/2251799813685248)), (355319/9007199254740992), by norm_num⟩
  | 2 => ⟨((557356059830389/1125899906842624), (-7619454131217/1125899906842624)), (356775/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109081998142283/1125899906842624), (-22744601876835/1125899906842624)), (538809/1125899906842624), by norm_num⟩
  | 0 => ⟨((68257592016977/70368744177664), (-22517459574403/562949953421312)), (1092257/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((68257592016977/70368744177664), (-22517459574403/562949953421312)), (4166629795554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057555080178589/1125899906842624), (-87367628162177/1125899906842624)), (2206355/1125899906842624), by norm_num⟩
  | 2 => ⟨((986579391658233/1125899906842624), (-41032101719047/281474976710656)), (2243633/562949953421312), by norm_num⟩
  | 3 => ⟨((52535795830367/70368744177664), (-287637831437139/1125899906842624)), (2293069/281474976710656), by norm_num⟩
  | 4 => ⟨((1108139354268583/2251799813685248), (-858976954161281/2251799813685248)), (36764401/2251799813685248), by norm_num⟩
  | 5 => ⟨((108831037670365/1125899906842624), (-422713494126315/1125899906842624)), (128465867/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1185487287756855/9007199254740992), (-653761108580861/9007199254740992)), (242598231/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-571323727/16777216)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-598719635/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-528609545776873/9007199254740992), (34921362999533/281474976710656)), (27338943/1125899906842624), by norm_num⟩
  | 1 => ⟨((290195575/2147483648), (-76684389/268435456)), (121/2147483648), by norm_num⟩
  | 2 => ⟨((-668200005/4294967296), (176572331/536870912)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((512862457/4294967296), (-1084194179/4294967296)), (109/2147483648), by norm_num⟩
  | 4 => ⟨((-147613681/2147483648), (1248224677/8589934592)), (127/4294967296), by norm_num⟩
  | 5 => ⟨((271914449/8589934592), (-574828707/8589934592)), (59/4294967296), by norm_num⟩
  | 6 => ⟨((-417404105/34359738368), (882394675/34359738368)), (183/34359738368), by norm_num⟩
  | 7 => ⟨((68650605/17179869184), (-580511093/68719476736)), (243/137438953472), by norm_num⟩
  | 8 => ⟨((-632295439/549755813888), (1336676189/549755813888)), (141/274877906944), by norm_num⟩
  | 9 => ⟨((40442057/137438953472), (-341978963/549755813888)), (291/2199023255552), by norm_num⟩
  | 10 => ⟨((-595976177/8796093022208), (314974265/2199023255552)), (271/8796093022208), by norm_num⟩
  | 11 => ⟨((31188315/2199023255552), (-1054916433/35184372088832)), (115/17592186044416), by norm_num⟩
  | 12 => ⟨((-191503331/70368744177664), (202419571/35184372088832)), (179/140737488355328), by norm_num⟩
  | 13 => ⟨((271355517/562949953421312), (-286823561/281474976710656)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((-357039525/4503599627370496), (754783607/4503599627370496)), (85/2251799813685248), by norm_num⟩
  | 15 => ⟨((109615185/9007199254740992), (-231727131/9007199254740992)), (211/36028797018963968), by norm_num⟩
  | 16 => ⟨((-252398291/144115188075855872), (1067142875/288230376151711744)), (245/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (2621689196703/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889450293556395/316912650057057350374175801344), (1551543369347/316912650057057350374175801344)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889889876151693/39614081257132168796771975168), (1745178231519/19807040628566084398385987584)), (13011/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472418464666877/618970019642690137449562112), (926937858007/618970019642690137449562112)), (110617/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442834930800863/38685626227668133590597632), (463363154155/19342813113834066795298816)), (55321/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774846368825079/4835703278458516698824704), (108572648457/302231454903657293676544)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629455086661669/302231454903657293676544), (1519567727185/302231454903657293676544)), (22703/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943994350142249/37778931862957161709568), (4936910477919/75557863725914323419136)), (147621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297686275206277/4722366482869645213696), (3701209234061/4722366482869645213696)), (13845/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405412226805021/147573952589676412928), (5086768866525/590295810358705651712)), (9523/36893488147419103232), by norm_num⟩
  | 8 => ⟨((7123921792591/288230376151711744), (6354871754005/73786976294838206464)), (23821/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911467585921499/4611686018427387904), (3572148848611/4611686018427387904)), (214539/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594180861548113/1152921504606846976), (7138134867079/1152921504606846976)), (107363/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194748226326683/144115188075855872), (6238939571949/144115188075855872)), (2939/2251799813685248), by norm_num⟩
  | 4 => ⟨((186485286034471/4503599627370496), (9344564352675/36028797018963968)), (141283/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489552785517709/9007199254740992), (5828251693031/4503599627370496)), (176973/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228505424097509/4503599627370496), (11620253714669/2251799813685248)), (710113/4503599627370496), by norm_num⟩
  | 1 => ⟨((34638407586281/35184372088832), (8669971669631/562949953421312)), (66921/140737488355328), by norm_num⟩
  | 0 => ⟨((2181918045129477/2251799813685248), (17159629738581/562949953421312)), (2163807/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2181918045129477/2251799813685248), (17159629738581/562949953421312)), (8254268654830168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112112755526761/2251799813685248), (133016818091215/2251799813685248)), (2162613/1125899906842624), by norm_num⟩
  | 2 => ⟨((986616747891963/1125899906842624), (31191329318285/281474976710656)), (8624829/2251799813685248), by norm_num⟩
  | 3 => ⟨((1701476689011809/2251799813685248), (437323249889709/2251799813685248)), (8513617/1125899906842624), by norm_num⟩
  | 4 => ⟨((300178914875603/562949953421312), (165222350301303/562949953421312)), (32345547/2251799813685248), by norm_num⟩
  | 5 => ⟨((446284473531535/2251799813685248), (352402664039473/1125899906842624)), (13370335/562949953421312), by norm_num⟩
  | 6 => ⟨((-528609545776873/9007199254740992), (34921362999533/281474976710656)), (27338943/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-598719635/16777216)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-77937781/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((979261272124589/9007199254740992), (145250043540875/2251799813685248)), (55065715/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1119692791/4294967296), (-332159417/2147483648)), (1/33554432), by norm_num⟩
  | 2 => ⟨((1342453025/4294967296), (99560437/536870912)), (39/1073741824), by norm_num⟩
  | 3 => ⟨((-268255147/1073741824), (-636628003/4294967296)), (127/4294967296), by norm_num⟩
  | 4 => ⟨((643247749/4294967296), (763283639/8589934592)), (155/8589934592), by norm_num⟩
  | 5 => ⟨((-1233952589/17179869184), (-183027423/4294967296)), (151/17179869184), by norm_num⟩
  | 6 => ⟨((123287045/4294967296), (585174123/34359738368)), (123/34359738368), by norm_num⟩
  | 7 => ⟨((-337862197/34359738368), (-400910361/68719476736)), (43/34359738368), by norm_num⟩
  | 8 => ⟨((810158165/274877906944), (240335265/137438953472)), (105/274877906944), by norm_num⟩
  | 9 => ⟨((-215852715/274877906944), (-128066399/274877906944)), (57/549755813888), by norm_num⟩
  | 10 => ⟨((103518441/549755813888), (122835925/1099511627776)), (111/4398046511104), by norm_num⟩
  | 11 => ⟨((-361056553/8796093022208), (-428432995/17592186044416)), (99/17592186044416), by norm_num⟩
  | 12 => ⟨((144295967/17592186044416), (171222909/35184372088832)), (161/140737488355328), by norm_num⟩
  | 13 => ⟨((-212927149/140737488355328), (-252661295/281474976710656)), (121/562949953421312), by norm_num⟩
  | 14 => ⟨((18234893/70368744177664), (346203043/2251799813685248)), (21/562949953421312), by norm_num⟩
  | 15 => ⟨((-11660097/281474976710656), (-442751275/18014398509481984)), (109/18014398509481984), by norm_num⟩
  | 16 => ⟨((894710127/144115188075855872), (530835595/144115188075855872)), (133/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (697524876137/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778640198793/633825300114114700748351602688), (206373298063/158456325028528675187087900672)), (46141/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889752982596349/39614081257132168796771975168), (928512086759/39614081257132168796771975168)), (51911/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889528792558383/2475880078570760549798248448), (246583998823/618970019642690137449562112)), (110317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442798771996819/38685626227668133590597632), (986101971645/154742504910672534362390528)), (27581/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774778799845847/4835703278458516698824704), (231055506293/2417851639229258349412352)), (25859/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((9834315506765/4722366482869645213696), (404222892643/302231454903657293676544)), (45257/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887798150758473/75557863725914323419136), (1313258672205/75557863725914323419136)), (73549/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324386028012891/1180591620717411303424), (123067084381/590295810358705651712)), (431/18446744073709551616), by norm_num⟩
  | 9 => ⟨((810727324397819/295147905179352825856), (676538181297/295147905179352825856)), (151731/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911741488826327/36893488147419103232), (1690353706847/73786976294838206464)), (189693/73786976294838206464), by norm_num⟩
  | 7 => ⟨((14239582398359/72057594037927936), (1900285246493/9223372036854775808)), (213443/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593915358552211/1152921504606846976), (1898583369575/1152921504606846976)), (106747/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194519416310305/144115188075855872), (1659347849643/144115188075855872)), (11679/9007199254740992), by norm_num⟩
  | 4 => ⟨((1491546066024605/36028797018963968), (2485201603349/36028797018963968)), (280409/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489144705890511/9007199254740992), (1549913999277/4503599627370496)), (350709/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227725703065283/4503599627370496), (772459884775/562949953421312)), (10969/70368744177664), by norm_num⟩
  | 1 => ⟨((276972381727875/281474976710656), (4609866907869/1125899906842624)), (263631/562949953421312), by norm_num⟩
  | 0 => ⟨((2180118918691665/2251799813685248), (9120635313655/1125899906842624)), (2115093/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180118918691665/2251799813685248), (9120635313655/1125899906842624)), (8068439492232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055286026493011/1125899906842624), (35321203025139/2251799813685248)), (1032449/562949953421312), by norm_num⟩
  | 2 => ⟨((1977647736001171/2251799813685248), (66211875078451/2251799813685248)), (983891/281474976710656), by norm_num⟩
  | 3 => ⟨((867463113631651/1125899906842624), (116301426129875/2251799813685248)), (7144277/1125899906842624), by norm_num⟩
  | 4 => ⟨((665344000411457/1125899906842624), (22401457851023/281474976710656)), (11746767/1125899906842624), by norm_num⟩
  | 5 => ⟨((1544199200018789/4503599627370496), (423616358536045/4503599627370496)), (63012493/4503599627370496), by norm_num⟩
  | 6 => ⟨((979261272124589/9007199254740992), (145250043540875/2251799813685248)), (55065715/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-77937781/2097152)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1292254003/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((725988279109695/9007199254740992), (-383651935629957/4503599627370496)), (30561705/2251799813685248), by norm_num⟩
  | 1 => ⟨((-860220481/4294967296), (454587577/2147483648)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((267195949/1073741824), (-282401923/1073741824)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-885275987/4294967296), (935656555/4294967296)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((549957047/4294967296), (-581254799/4294967296)), (99/4294967296), by norm_num⟩
  | 5 => ⟨((-546636769/8589934592), (288872783/4294967296)), (25/2147483648), by norm_num⟩
  | 6 => ⟨((905560895/34359738368), (-478547933/17179869184)), (21/4294967296), by norm_num⟩
  | 7 => ⟨((-642924083/68719476736), (339756269/34359738368)), (61/34359738368), by norm_num⟩
  | 8 => ⟨((199700791/68719476736), (-211065653/68719476736)), (77/137438953472), by norm_num⟩
  | 9 => ⟨((-882200575/1099511627776), (233101531/274877906944)), (43/274877906944), by norm_num⟩
  | 10 => ⟨((438437215/2199023255552), (-926776871/4398046511104)), (173/4398046511104), by norm_num⟩
  | 11 => ⟨((-792345855/17592186044416), (837437821/17592186044416)), (159/17592186044416), by norm_num⟩
  | 12 => ⟨((164075457/17592186044416), (-693651603/70368744177664)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((-1003599247/562949953421312), (530356763/281474976710656)), (207/562949953421312), by norm_num⟩
  | 14 => ⟨((356264349/1125899906842624), (-94134789/281474976710656)), (149/2251799813685248), by norm_num⟩
  | 15 => ⟨((-29509455/562949953421312), (124755287/2251799813685248)), (25/2251799813685248), by norm_num⟩
  | 16 => ⟨((73328241/9007199254740992), (-155002621/18014398509481984)), (63/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1059099554317/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222332809879891/79228162514264337593543950336), (-1253247330041/633825300114114700748351602688)), (23081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889622298488933/39614081257132168796771975168), (-1409639410309/39614081257132168796771975168)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889389935412427/2475880078570760549798248448), (-748707227925/1237940039285380274899124224)), (55187/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885528112461177/77371252455336267181195264), (-1497046245817/154742504910672534362390528)), (6899/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387356852324039/2417851639229258349412352), (-350772438597/2417851639229258349412352)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258678462016491/604462909807314587353088), (-613656285701/302231454903657293676544)), (45285/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887613014443153/75557863725914323419136), (-1993650163429/75557863725914323419136)), (147197/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162175656203833/590295810358705651712), (-1494596744793/4722366482869645213696)), (6901/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621263696492095/590295810358705651712), (-2054029644335/590295810358705651712)), (75925/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823244262691863/73786976294838206464), (-1282988345923/36893488147419103232)), (189857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822397959072031/9223372036854775808), (-1442289915493/4611686018427387904)), (106825/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24900730140133/18014398509481984), (-5628715281/2251799813685248)), (106863/576460752303423488), by norm_num⟩
  | 5 => ⟨((298571079746755/36028797018963968), (-2518655334675/144115188075855872)), (187095/144115188075855872), by norm_num⟩
  | 4 => ⟨((745596664126633/18014398509481984), (-3771972762819/36028797018963968)), (140407/18014398509481984), by norm_num⟩
  | 3 => ⟨((744351812746485/4503599627370496), (-4704465973187/9007199254740992)), (175659/4503599627370496), by norm_num⟩
  | 2 => ⟨((34794423085283/70368744177664), (-4688751819199/2251799813685248)), (703537/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214453987315127/2251799813685248), (-13987934864291/2251799813685248)), (1057571/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177464475690591/2251799813685248), (-27664084111601/2251799813685248)), (2124251/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177464475690591/2251799813685248), (-27664084111601/2251799813685248)), (8103374489791106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526310799536219/562949953421312), (-13375425301893/562949953421312)), (65007/35184372088832), by norm_num⟩
  | 2 => ⟨((122934620575087/140737488355328), (-100039170331119/2251799813685248)), (3988519/1125899906842624), by norm_num⟩
  | 3 => ⟨((428423954534935/562949953421312), (-174769034050863/2251799813685248)), (14644715/2251799813685248), by norm_num⟩
  | 4 => ⟨((322654030365417/562949953421312), (-266010291832407/2251799813685248)), (12281745/1125899906842624), by norm_num⟩
  | 5 => ⟨((1416581072547271/4503599627370496), (-304926902495619/2251799813685248)), (67921097/4503599627370496), by norm_num⟩
  | 6 => ⟨((725988279109695/9007199254740992), (-383651935629957/4503599627370496)), (30561705/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1292254003/33554432)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-666939757/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-228846916274125/4503599627370496), (-436585913739281/4503599627370496)), (21999781/1125899906842624), by norm_num⟩
  | 1 => ⟨((279894233/2147483648), (1067944297/4294967296)), (217/4294967296), by norm_num⟩
  | 2 => ⟨((-717914533/4294967296), (-1369611519/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((613804807/4294967296), (1170994729/4294967296)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-393594561/4294967296), (-750885545/4294967296)), (157/4294967296), by norm_num⟩
  | 5 => ⟨((403820047/8589934592), (770393359/8589934592)), (163/8589934592), by norm_num⟩
  | 6 => ⟨((-690518647/34359738368), (-658673317/17179869184)), (281/34359738368), by norm_num⟩
  | 7 => ⟨((506041531/68719476736), (965407829/68719476736)), (13/4294967296), by norm_num⟩
  | 8 => ⟨((-324492725/137438953472), (-154763887/34359738368)), (269/274877906944), by norm_num⟩
  | 9 => ⟨((369914403/549755813888), (705709391/549755813888)), (155/549755813888), by norm_num⟩
  | 10 => ⟨((-94881171/549755813888), (-181010885/549755813888)), (161/2199023255552), by norm_num⟩
  | 11 => ⟨((707972069/17592186044416), (675321823/8796093022208)), (303/17592186044416), by norm_num⟩
  | 12 => ⟨((-75663021/8796093022208), (-577388759/35184372088832)), (261/70368744177664), by norm_num⟩
  | 13 => ⟨((238857621/140737488355328), (911367955/281474976710656)), (13/17592186044416), by norm_num⟩
  | 14 => ⟨((-350090115/1125899906842624), (-667889329/1125899906842624)), (77/562949953421312), by norm_num⟩
  | 15 => ⟨((239456911/4503599627370496), (913654563/9007199254740992)), (213/9007199254740992), by norm_num⟩
  | 16 => ⟨((-307097425/36028797018963968), (-585869421/36028797018963968)), (275/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1337518685557/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889275774023411/316912650057057350374175801344), (-3165048476257/633825300114114700748351602688)), (2891/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889497270563163/39614081257132168796771975168), (-3559983833453/39614081257132168796771975168)), (3253/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1889256789312061/2475880078570760549798248448), (-118175884225/77371252455336267181195264)), (110625/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442730684304957/38685626227668133590597632), (-3780667173775/154742504910672534362390528)), (110651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549301901882397/9671406556917033397649408), (-885838632843/2417851639229258349412352)), (103763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258568280628985/604462909807314587353088), (-3099414549129/604462909807314587353088)), (90821/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58982290337753/2361183241434822606848), (-157332358909/2361183241434822606848)), (147635/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162158732938021/590295810358705651712), (-943575798083/1180591620717411303424)), (27693/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621076577454687/590295810358705651712), (-2593474343871/295147905179352825856)), (76193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455752230314107/18446744073709551616), (-6479610496191/73786976294838206464)), (1489/576460752303423488), by norm_num⟩
  | 7 => ⟨((911065609813517/4611686018427387904), (-7283961333945/9223372036854775808)), (107285/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49793047470385/36028797018963968), (-7276965466041/1152921504606846976)), (26845/144115188075855872), by norm_num⟩
  | 5 => ⟨((149255748476961/18014398509481984), (-6359480926779/144115188075855872)), (188131/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490830303443267/36028797018963968), (-9523509912417/36028797018963968)), (282627/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488240208419595/9007199254740992), (-11876928819923/9007199254740992)), (354039/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225887486882413/4503599627370496), (-1479476745717/281474976710656)), (710347/4503599627370496), by norm_num⟩
  | 1 => ⟨((553237309959399/562949953421312), (-35302378373367/2251799813685248)), (1071207/2251799813685248), by norm_num⟩
  | 0 => ⟨((271771587202543/281474976710656), (-8723445624495/281474976710656)), (2165249/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271771587202543/281474976710656), (-8723445624495/281474976710656)), (8259769448287200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2097058799876831/2251799813685248), (-134763505641563/2251799813685248)), (4315423/2251799813685248), by norm_num⟩
  | 2 => ⟨((1944886211052955/2251799813685248), (-251005434577581/2251799813685248)), (2138569/562949953421312), by norm_num⟩
  | 3 => ⟨((1651824741769143/2251799813685248), (-433588284040535/2251799813685248)), (8341889/1125899906842624), by norm_num⟩
  | 4 => ⟨((1128220262753157/2251799813685248), (-19878872307127/70368744177664)), (30902009/2251799813685248), by norm_num⟩
  | 5 => ⟨((48196298482343/281474976710656), (-1274869790539883/4503599627370496)), (48425069/2251799813685248), by norm_num⟩
  | 6 => ⟨((-228846916274125/4503599627370496), (-436585913739281/4503599627370496)), (21999781/1125899906842624), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-666939757/16777216)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-686209359/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-461559242749029/4503599627370496), (111946087422843/18014398509481984)), (304566905/18014398509481984), by norm_num⟩
  | 1 => ⟨((1161652853/4294967296), (-2201141/134217728)), (97/2147483648), by norm_num⟩
  | 2 => ⟨((-766417119/2147483648), (92942997/4294967296)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((1348412477/4294967296), (-10220079/536870912)), (229/4294967296), by norm_num⟩
  | 4 => ⟨((-1779268915/8589934592), (53942749/4294967296)), (305/8589934592), by norm_num⟩
  | 5 => ⟨((469559267/4294967296), (-56943203/8589934592)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((-1652258433/34359738368), (100184251/34359738368)), (287/34359738368), by norm_num⟩
  | 7 => ⟨((622914961/34359738368), (-37770283/34359738368)), (109/34359738368), by norm_num⟩
  | 8 => ⟨((-1643908293/274877906944), (49838971/137438953472)), (145/137438953472), by norm_num⟩
  | 9 => ⟨((1928163657/1099511627776), (-58456845/549755813888)), (343/1099511627776), by norm_num⟩
  | 10 => ⟨((-508853443/1099511627776), (30854193/1099511627776)), (91/1099511627776), by norm_num⟩
  | 11 => ⟨((1953299503/17592186044416), (-118437795/17592186044416)), (11/549755813888), by norm_num⟩
  | 12 => ⟨((-859144895/35184372088832), (26047011/17592186044416)), (39/8796093022208), by norm_num⟩
  | 13 => ⟨((348820405/70368744177664), (-42301265/140737488355328)), (1/1099511627776), by norm_num⟩
  | 14 => ⟨((-263016299/281474976710656), (63791693/1125899906842624)), (195/1125899906842624), by norm_num⟩
  | 15 => ⟨((740389431/4503599627370496), (-11223329/1125899906842624)), (69/2251799813685248), by norm_num⟩
  | 16 => ⟨((-976965077/36028797018963968), (118476035/72057594037927936)), (367/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (4013388264349/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889223165153515/316912650057057350374175801344), (2374028166757/316912650057057350374175801344)), (23167/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889378548542195/39614081257132168796771975168), (5340471393203/39614081257132168796771975168)), (104281/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236141272703943/309485009821345068724781056), (2836464834325/1237940039285380274899124224)), (55417/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770795606271535/154742504910672534362390528), (2835721688035/77371252455336267181195264)), (13859/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549182161057163/9671406556917033397649408), (2657699599137/4835703278458516698824704)), (103985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258462952307477/604462909807314587353088), (1162348894357/151115727451828646838272)), (91029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887261092455097/75557863725914323419136), (7552308234011/75557863725914323419136)), (147999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81071237866757/295147905179352825856), (2830821033427/2361183241434822606848)), (27767/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810448136563275/295147905179352825856), (7780551522627/590295810358705651712)), (152829/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822781331441769/73786976294838206464), (9719381645681/73786976294838206464)), (191203/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821872148372407/9223372036854775808), (10925633986319/9223372036854775808)), (215333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593114664726917/1152921504606846976), (5457400120095/576460752303423488)), (53905/288230376151711744), by norm_num⟩
  | 5 => ⟨((149226468133663/18014398509481984), (2384567011851/36028797018963968)), (188991/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490470475726513/36028797018963968), (7141526143665/18014398509481984)), (71033/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487775672751309/9007199254740992), (4452809014933/2251799813685248)), (89075/2251799813685248), by norm_num⟩
  | 2 => ⟨((556228600784717/1125899906842624), (4436858253007/562949953421312)), (89501/562949953421312), by norm_num⟩
  | 1 => ⟨((138211276473385/140737488355328), (3307734213137/140737488355328)), (541277/1125899906842624), by norm_num⟩
  | 0 => ⟨((542650832292159/562949953421312), (52288044150379/1125899906842624)), (1099709/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((542650832292159/562949953421312), (52288044150379/1125899906842624)), (4195056919578170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043739018403417/1125899906842624), (50402616617497/562949953421312)), (2222255/1125899906842624), by norm_num⟩
  | 2 => ⟨((479274150806471/562949953421312), (23362279929855/140737488355328)), (2259055/562949953421312), by norm_num⟩
  | 3 => ⟨((785046600721733/1125899906842624), (318236086351485/1125899906842624)), (18386195/2251799813685248), by norm_num⟩
  | 4 => ⟨((914866331400145/2251799813685248), (443787509527065/1125899906842624)), (36033703/2251799813685248), by norm_num⟩
  | 5 => ⟨((43690375655655/4503599627370496), (1442423960761491/4503599627370496)), (28842989/1125899906842624), by norm_num⟩
  | 6 => ⟨((-461559242749029/4503599627370496), (111946087422843/18014398509481984)), (304566905/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-686209359/16777216)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-704148929/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-371910083969327/9007199254740992), (394017173114901/4503599627370496)), (77501265/4503599627370496), by norm_num⟩
  | 1 => ⟨((480247105/4294967296), (-1017587933/4294967296)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((-650266635/4294967296), (1377839603/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((586984897/4294967296), (-621876469/2147483648)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-198698071/2147483648), (210509087/1073741824)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((430467481/8589934592), (-114013835/1073741824)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-388575849/17179869184), (411673585/8589934592)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((300652259/34359738368), (-637047277/34359738368)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((-407090705/137438953472), (862578003/137438953472)), (91/68719476736), by norm_num⟩
  | 9 => ⟨((244982681/274877906944), (-1038179793/549755813888)), (221/549755813888), by norm_num⟩
  | 10 => ⟨((-530740319/2199023255552), (1124577199/2199023255552)), (121/1099511627776), by norm_num⟩
  | 11 => ⟨((522644155/8796093022208), (-1107422367/8796093022208)), (15/549755813888), by norm_num⟩
  | 12 => ⟨((-471782203/35184372088832), (249912947/8796093022208)), (109/17592186044416), by norm_num⟩
  | 13 => ⟨((393110735/140737488355328), (-832956069/140737488355328)), (23/17592186044416), by norm_num⟩
  | 14 => ⟨((-152080515/281474976710656), (644481957/562949953421312)), (287/1125899906842624), by norm_num⟩
  | 15 => ⟨((109824445/1125899906842624), (-930821063/4503599627370496)), (209/4503599627370496), by norm_num⟩
  | 16 => ⟨((-594820221/36028797018963968), (1260355083/36028797018963968)), (285/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (2620529467729/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778361559197229/633825300114114700748351602688), (3099924146991/633825300114114700748351602688)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472320897335219/9903520314283042199192993792), (1743349145273/19807040628566084398385987584)), (13011/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889029821825613/2475880078570760549798248448), (3703733494855/2475880078570760549798248448)), (13827/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770695847137011/154742504910672534362390528), (3702739896647/154742504910672534362390528)), (55321/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549089274653133/9671406556917033397649408), (433782904999/1208925819614629174706176)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78648894625411/37778931862957161709568), (3035425242307/604462909807314587353088)), (22703/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235891406141847/9444732965739290427392), (4930588400761/75557863725914323419136)), (36905/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648521733516671/2361183241434822606848), (3696211565501/4722366482869645213696)), (13845/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620765501251053/590295810358705651712), (2539740679531/295147905179352825856)), (9523/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822620404276533/73786976294838206464), (6345139616009/73786976294838206464)), (23821/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821694589173043/9223372036854775808), (7132494080817/9223372036854775808)), (214539/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99558840761855/72057594037927936), (7125264535069/1152921504606846976)), (107363/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193665062877527/144115188075855872), (6226480703895/144115188075855872)), (188097/144115188075855872), by norm_num⟩
  | 4 => ⟨((745130090991993/18014398509481984), (2330872051307/9007199254740992)), (282567/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487529769333897/9007199254740992), (11625994769331/9007199254740992)), (88487/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112236618113325/2251799813685248), (1447941310127/281474976710656)), (355061/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210844395116541/2251799813685248), (2158678565945/140737488355328)), (1070759/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085014453726157/1125899906842624), (68234294515507/2251799813685248)), (270489/281474976710656), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085014453726157/1125899906842624), (68234294515507/2251799813685248)), (1031833649755382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1044579875981867/1125899906842624), (65756463198181/1125899906842624)), (268863/140737488355328), by norm_num⟩
  | 2 => ⟨((1930585833161229/2251799813685248), (61007091087861/562949953421312)), (8484687/2251799813685248), by norm_num⟩
  | 3 => ⟨((101796677104271/140737488355328), (418436577037799/2251799813685248)), (16387711/2251799813685248), by norm_num⟩
  | 4 => ⟨((1100331860817825/2251799813685248), (75664724479433/281474976710656)), (7449297/562949953421312), by norm_num⟩
  | 5 => ⟨((374953654780669/2251799813685248), (1183143284105235/4503599627370496)), (90280787/4503599627370496), by norm_num⟩
  | 6 => ⟨((-371910083969327/9007199254740992), (394017173114901/4503599627370496)), (77501265/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-704148929/16777216)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile003Terms1
