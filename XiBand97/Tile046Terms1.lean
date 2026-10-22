/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile046Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨46,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36843/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36843/1280))
  have he : value ((69/80), (36843/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-4244234311/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((620214621503259/4503599627370496), (-542327382325749/9007199254740992)), (29822191/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5198481787/17179869184), (2272825343/17179869184)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((2855557987/8589934592), (-624238463/4294967296)), (279/17179869184), by norm_num⟩
  | 3 => ⟨((-130714629/536870912), (1828789457/17179869184)), (207/17179869184), by norm_num⟩
  | 4 => ⟨((4595350327/34359738368), (-2009130571/34359738368)), (115/17179869184), by norm_num⟩
  | 5 => ⟨((-252425417/4294967296), (441451107/17179869184)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((5916110189/274877906944), (-2586579259/274877906944)), (151/137438953472), by norm_num⟩
  | 7 => ⟨((-3714006489/549755813888), (25371855/8589934592)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((4080253169/2199023255552), (-445981307/549755813888)), (213/2199023255552), by norm_num⟩
  | 9 => ⟨((-1992273899/4398046511104), (108880121/549755813888)), (105/4398046511104), by norm_num⟩
  | 10 => ⟨((3501978541/35184372088832), (-765549049/17592186044416)), (187/35184372088832), by norm_num⟩
  | 11 => ⟨((-87439015/4398046511104), (611666613/70368744177664)), (301/281474976710656), by norm_num⟩
  | 12 => ⟨((4098627259/1125899906842624), (-895979277/562949953421312)), (223/1125899906842624), by norm_num⟩
  | 13 => ⟨((-5541910491/9007199254740992), (18929497/70368744177664)), (305/9007199254740992), by norm_num⟩
  | 14 => ⟨((1739545991/18014398509481984), (-760545939/18014398509481984)), (193/36028797018963968), by norm_num⟩
  | 15 => ⟨((-254811547/18014398509481984), (1782496245/288230376151711744)), (57/72057594037927936), by norm_num⟩
  | 16 => ⟨((4479025549/2305843009213693952), (-1958272279/2305843009213693952)), (253/2305843009213693952), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-268446469061/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779045642929881/633825300114114700748351602688), (-317786559809/316912650057057350374175801344)), (11533/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472513329236673/9903520314283042199192993792), (-714900986471/39614081257132168796771975168)), (12975/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472461961065977/618970019642690137449562112), (-759435473071/2475880078570760549798248448)), (55147/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771514079472275/154742504910672534362390528), (-379635174745/77371252455336267181195264)), (55149/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774928295119331/4835703278458516698824704), (-88955069861/1208925819614629174706176)), (51705/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053937640149/604462909807314587353088), (-622510151579/604462909807314587353088)), (45245/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944111527067915/37778931862957161709568), (-505625179107/37778931862957161709568)), (9191/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81116417795161/295147905179352825856), (-758150329885/4722366482869645213696)), (55151/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810946257940313/295147905179352825856), (-130248729957/73786976294838206464)), (75839/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912015028056403/36893488147419103232), (-1301787395583/73786976294838206464)), (47405/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911640829633669/4611686018427387904), (-1463549088513/9223372036854775808)), (106677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398632508090155/288230376151711744), (-1462347878111/1152921504606846976)), (13337/144115188075855872), by norm_num⟩
  | 5 => ⟨((149382095373073/18014398509481984), (-319551085563/36028797018963968)), (93381/144115188075855872), by norm_num⟩
  | 4 => ⟨((746175550571551/18014398509481984), (-957304842145/18014398509481984)), (70057/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490149278301741/9007199254740992), (-298568751197/1125899906842624)), (175219/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229729691722193/4503599627370496), (-4762993105469/4503599627370496)), (87667/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218772175392435/2251799813685248), (-3554662485835/1125899906842624)), (131645/562949953421312), by norm_num⟩
  | 0 => ⟨((2186053889874695/2251799813685248), (-3519651276223/562949953421312)), (263873/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2186053889874695/2251799813685248), (-3519651276223/562949953421312)), (1006595613719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2122139531797001/2251799813685248), (-27335102584621/2251799813685248)), (2062549/2251799813685248), by norm_num⟩
  | 2 => ⟨((1999613356932121/2251799813685248), (-51522254729753/2251799813685248)), (246103/140737488355328), by norm_num⟩
  | 3 => ⟨((887245617972911/1125899906842624), (-91504216414571/2251799813685248)), (1793377/562949953421312), by norm_num⟩
  | 4 => ⟨((1394638238151063/2251799813685248), (-72108288264759/1125899906842624)), (1486115/281474976710656), by norm_num⟩
  | 5 => ⟨((854524182244279/2251799813685248), (-178639283102293/2251799813685248)), (32499021/4503599627370496), by norm_num⟩
  | 6 => ⟨((620214621503259/4503599627370496), (-542327382325749/9007199254740992)), (29822191/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-4244234311/67108864)), (1/33554432), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-66638419/33554432), (-2223876147/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1179804295277051/9007199254740992), (92283364131661/2251799813685248)), (6732389/562949953421312), by norm_num⟩
  | 1 => ⟨((2590751441/8589934592), (-810586161/8589934592)), (119/4294967296), by norm_num⟩
  | 2 => ⟨((-5965425647/17179869184), (1866443611/17179869184)), (551/17179869184), by norm_num⟩
  | 3 => ⟨((4578633389/17179869184), (-358137103/4294967296)), (425/17179869184), by norm_num⟩
  | 4 => ⟨((-2635673247/17179869184), (1649282309/34359738368)), (123/8589934592), by norm_num⟩
  | 5 => ⟨((4855089543/68719476736), (-1519045143/68719476736)), (57/8589934592), by norm_num⟩
  | 6 => ⟨((-3726418935/137438953472), (582955117/68719476736)), (11/4294967296), by norm_num⟩
  | 7 => ⟨((4903083823/549755813888), (-1534061443/549755813888)), (233/274877906944), by norm_num⟩
  | 8 => ⟨((-1411220965/549755813888), (1766153505/2199023255552)), (539/2199023255552), by norm_num⟩
  | 9 => ⟨((5776811301/8796093022208), (-451857637/2199023255552)), (277/4398046511104), by norm_num⟩
  | 10 => ⟨((-2660319917/17592186044416), (832352527/17592186044416)), (513/35184372088832), by norm_num⟩
  | 11 => ⟨((1113747815/35184372088832), (-1393863651/140737488355328)), (27/8796093022208), by norm_num⟩
  | 12 => ⟨((-3419332155/562949953421312), (4179023/2199023255552)), (333/562949953421312), by norm_num⟩
  | 13 => ⟨((4845109691/4503599627370496), (-757961339/2251799813685248)), (237/2251799813685248), by norm_num⟩
  | 14 => ⟨((-6375015627/36028797018963968), (997297417/18014398509481984)), (627/36028797018963968), by norm_num⟩
  | 15 => ⟨((3914404253/144115188075855872), (-153090811/18014398509481984)), (387/144115188075855872), by norm_num⟩
  | 16 => ⟨((-563328055/144115188075855872), (1410018477/1152921504606846976)), (447/1152921504606846976), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1848643330395/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889447745837223/316912650057057350374175801344), (2188093314165/316912650057057350374175801344)), (11579/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889883854965447/39614081257132168796771975168), (4922326941105/39614081257132168796771975168)), (52119/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944833543314871/1237940039285380274899124224), (2614454879861/1237940039285380274899124224)), (55393/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771332530106455/154742504910672534362390528), (1306928578899/38685626227668133590597632)), (55411/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387421386755045/2417851639229258349412352), (1224928034531/2417851639229258349412352)), (51967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258903434728413/604462909807314587353088), (4285978230175/604462909807314587353088)), (22745/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887976912983557/75557863725914323419136), (6962333881275/75557863725914323419136)), (73957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648838351467835/2361183241434822606848), (5219667563747/4722366482869645213696)), (55499/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621634557406621/590295810358705651712), (1793414710481/147573952589676412928)), (38181/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823704261867789/73786976294838206464), (8961998461749/73786976294838206464)), (47765/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455727636619337/2305843009213693952), (10075271642859/9223372036854775808)), (13447/1152921504606846976), by norm_num⟩
  | 6 => ⟨((99634574173457/72057594037927936), (10066553300159/1152921504606846976)), (26927/288230376151711744), by norm_num⟩
  | 5 => ⟨((298680146872031/36028797018963968), (1099803670949/18014398509481984)), (47197/72057594037927936), by norm_num⟩
  | 4 => ⟨((372958500276179/9007199254740992), (13178042954117/36028797018963968)), (2217/562949953421312), by norm_num⟩
  | 3 => ⟨((1489480516214727/9007199254740992), (16438270848593/9007199254740992)), (88941/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114162657649943/2251799813685248), (4096721233443/562949953421312)), (178665/2251799813685248), by norm_num⟩
  | 1 => ⟨((554124889697431/562949953421312), (6112999433683/281474976710656)), (134981/562949953421312), by norm_num⟩
  | 0 => ⟨((545212725395721/562949953421312), (24195747316169/562949953421312)), (273903/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545212725395721/562949953421312), (24195747316169/562949953421312)), (1044857027293968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((526994415653167/562949953421312), (93733585069591/1125899906842624)), (554091/562949953421312), by norm_num⟩
  | 2 => ⟨((489433592120611/562949953421312), (87746833605041/562949953421312)), (2259323/1125899906842624), by norm_num⟩
  | 3 => ⟨((205920377894463/281474976710656), (19071965326367/70368744177664)), (4632871/1125899906842624), by norm_num⟩
  | 4 => ⟨((259940437172447/562949953421312), (55810379353653/140737488355328)), (18579761/2251799813685248), by norm_num⟩
  | 5 => ⟨((251990510659885/4503599627370496), (824648760041593/2251799813685248)), (31894151/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1179804295277051/9007199254740992), (92283364131661/2251799813685248)), (6732389/562949953421312), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-2223876147/33554432)), (1/33554432), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-4631856705/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1133511882956197/9007199254740992), (27000755380867/2251799813685248)), (9608891/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5184255191/17179869184), (-15436407/536870912)), (45/8589934592), by norm_num⟩
  | 2 => ⟨((1553912627/4294967296), (296119099/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((-4968159657/17179869184), (-236687529/8589934592)), (45/8589934592), by norm_num⟩
  | 4 => ⟨((2978281639/17179869184), (567551907/34359738368)), (55/17179869184), by norm_num⟩
  | 5 => ⟨((-5713285971/68719476736), (-272186007/34359738368)), (27/17179869184), by norm_num⟩
  | 6 => ⟨((2283310237/68719476736), (435115693/137438953472)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((-6257301513/549755813888), (-596206779/549755813888)), (123/549755813888), by norm_num⟩
  | 8 => ⟨((7502176859/2199023255552), (178705177/549755813888)), (75/1099511627776), by norm_num⟩
  | 9 => ⟨((-3997652095/4398046511104), (-380903377/4398046511104)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((7668760849/35184372088832), (365346563/17592186044416)), (5/1099511627776), by norm_num⟩
  | 11 => ⟨((-3343433707/70368744177664), (-637136579/140737488355328)), (71/70368744177664), by norm_num⟩
  | 12 => ⟨((5344802587/562949953421312), (63657783/70368744177664)), (29/140737488355328), by norm_num⟩
  | 13 => ⟨((-1971734901/1125899906842624), (-46967599/281474976710656)), (11/281474976710656), by norm_num⟩
  | 14 => ⟨((5403444341/18014398509481984), (257424877/9007199254740992)), (123/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1727585819/36028797018963968), (-658429755/144115188075855872)), (5/4503599627370496), by norm_num⟩
  | 16 => ⟨((4142569869/576460752303423488), (394711399/576460752303423488)), (49/288230376151711744), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (30935395495/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889389496738591/316912650057057350374175801344), (146443283985/633825300114114700748351602688)), (11527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944876699986937/19807040628566084398385987584), (82359483721/19807040628566084398385987584)), (25937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889529261982861/2475880078570760549798248448), (21872123769/309485009821345068724781056)), (13779/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885597793296477/77371252455336267181195264), (174935478949/154742504910672534362390528)), (13779/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774779049059953/4835703278458516698824704), (163957919797/9671406556917033397649408)), (6459/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258792851953891/604462909807314587353088), (143419103785/604462909807314587353088)), (22607/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471949741946411/18889465931478580854784), (116486717195/37778931862957161709568)), (287/590295810358705651712), by norm_num⟩
  | 10 => ⟨((648772387766549/2361183241434822606848), (174657825981/4722366482869645213696)), (27553/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621455643400489/590295810358705651712), (240037167171/590295810358705651712)), (18943/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823484344231673/73786976294838206464), (74967638187/18446744073709551616)), (47359/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911334126855489/4611686018427387904), (337112677981/9223372036854775808)), (1665/288230376151711744), by norm_num⟩
  | 6 => ⟨((1593917276549085/1152921504606846976), (336810826215/1152921504606846976)), (26641/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194521331729821/144115188075855872), (294370254489/144115188075855872)), (46625/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491549412217923/36028797018963968), (440877855735/36028797018963968)), (69943/36028797018963968), by norm_num⟩
  | 3 => ⟨((744574856809669/4503599627370496), (549913695763/9007199254740992)), (87437/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227738182015505/4503599627370496), (548142345763/2251799813685248)), (174903/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107901945487909/1125899906842624), (1635598822491/2251799813685248)), (65607/562949953421312), by norm_num⟩
  | 0 => ⟨((1090096414490067/1125899906842624), (3236055471709/2251799813685248)), (262579/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1090096414490067/1125899906842624), (3236055471709/2251799813685248)), (1001659397605514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65964321497877/70368744177664), (6266298532155/2251799813685248)), (1018427/2251799813685248), by norm_num⟩
  | 2 => ⟨((247340117567007/281474976710656), (11748174159059/2251799813685248)), (1915035/2251799813685248), by norm_num⟩
  | 3 => ⟨((869348713221601/1125899906842624), (20646913709039/2251799813685248)), (3385575/2251799813685248), by norm_num⟩
  | 4 => ⟨((335580723839713/562949953421312), (3985560296227/281474976710656)), (1322585/562949953421312), by norm_num⟩
  | 5 => ⟨((1599444252765441/4503599627370496), (38013388607245/2251799813685248)), (6457079/2251799813685248), by norm_num⟩
  | 6 => ⟨((1133511882956197/9007199254740992), (27000755380867/2251799813685248)), (9608891/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-4631856705/67108864)), (1/67108864), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-4799930863/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-392835600112117/4503599627370496), (-706070093824499/9007199254740992)), (48099759/4503599627370496), by norm_num⟩
  | 1 => ⟨((3723754101/17179869184), (1673239013/8589934592)), (229/8589934592), by norm_num⟩
  | 2 => ⟨((-578323833/2147483648), (-2078921375/8589934592)), (143/4294967296), by norm_num⟩
  | 3 => ⟨((1916107651/8589934592), (1721975183/8589934592)), (119/4294967296), by norm_num⟩
  | 4 => ⟨((-1190337161/8589934592), (-2139473791/17179869184)), (149/8589934592), by norm_num⟩
  | 5 => ⟨((2366301381/34359738368), (531639265/8589934592)), (149/17179869184), by norm_num⟩
  | 6 => ⟨((-1960012679/68719476736), (-3522863853/137438953472)), (31/8589934592), by norm_num⟩
  | 7 => ⟨((2783113451/274877906944), (2501139375/274877906944)), (177/137438953472), by norm_num⟩
  | 8 => ⟨((-3457888561/1099511627776), (-776887233/274877906944)), (221/549755813888), by norm_num⟩
  | 9 => ⟨((1909451173/2199023255552), (3431986225/4398046511104)), (491/4398046511104), by norm_num⟩
  | 10 => ⟨((-1897923167/8796093022208), (-3411266157/17592186044416)), (245/8796093022208), by norm_num⟩
  | 11 => ⟨((1714967963/35184372088832), (770607087/17592186044416)), (445/70368744177664), by norm_num⟩
  | 12 => ⟨((-1420511765/140737488355328), (-2553182233/281474976710656)), (185/140737488355328), by norm_num⟩
  | 13 => ⟨((271526087/140737488355328), (3904258159/2251799813685248)), (71/281474976710656), by norm_num⟩
  | 14 => ⟨((-771105119/2251799813685248), (-346489895/1125899906842624)), (405/9007199254740992), by norm_num⟩
  | 15 => ⟨((4087731707/72057594037927936), (3673578855/72057594037927936)), (539/72057594037927936), by norm_num⟩
  | 16 => ⟨((-2539407925/288230376151711744), (-2282125131/288230376151711744)), (337/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-784662363589/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889327967311555/316912650057057350374175801344), (-3714007840505/633825300114114700748351602688)), (11571/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889614568087301/39614081257132168796771975168), (-4177461541421/39614081257132168796771975168)), (3255/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889381241147213/2475880078570760549798248448), (-69337199801/38685626227668133590597632)), (55349/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885523495149555/77371252455336267181195264), (-4436487331847/154742504910672534362390528)), (55365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774709089042229/4835703278458516698824704), (-1039511324921/2417851639229258349412352)), (51921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629334905689537/302231454903657293676544), (-3637128313261/604462909807314587353088)), (45447/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943798941536017/37778931862957161709568), (-2954078278943/37778931862957161709568)), (73881/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648696481090155/2361183241434822606848), (-4429213117527/4722366482869645213696)), (27719/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621245277190937/590295810358705651712), (-3043537272119/295147905179352825856)), (38135/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823218955437727/73786976294838206464), (-7604204686251/73786976294838206464)), (47701/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822366353912721/9223372036854775808), (-1068544397303/1152921504606846976)), (107417/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796805606441151/576460752303423488), (-2135097641635/288230376151711744)), (53765/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194248852501875/144115188075855872), (-3731943705345/72057594037927936)), (94215/144115188075855872), by norm_num⟩
  | 4 => ⟨((372782843344745/9007199254740992), (-11177937086881/36028797018963968)), (70787/18014398509481984), by norm_num⟩
  | 3 => ⟨((744305457905983/4503599627370496), (-13941139770333/9007199254740992)), (88705/4503599627370496), by norm_num⟩
  | 2 => ⟨((278326510128451/562949953421312), (-6947141682397/1125899906842624)), (44519/562949953421312), by norm_num⟩
  | 1 => ⟨((138374645127345/140737488355328), (-5181128795357/281474976710656)), (134391/562949953421312), by norm_num⟩
  | 0 => ⟨((1088048538847103/1125899906842624), (-20491389800007/562949953421312)), (544257/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088048538847103/1125899906842624), (-20491389800007/562949953421312)), (2076175693992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524988956602167/562949953421312), (-19802494516025/281474976710656)), (545771/562949953421312), by norm_num⟩
  | 2 => ⟨((973602885061109/1125899906842624), (-295474675740709/2251799813685248)), (547365/281474976710656), by norm_num⟩
  | 3 => ⟨((1645041892569835/2251799813685248), (-511013448025555/2251799813685248)), (4361187/1125899906842624), by norm_num⟩
  | 4 => ⟨((271452647498591/562949953421312), (-373318500410045/1125899906842624)), (8351507/1125899906842624), by norm_num⟩
  | 5 => ⟨((552018720823257/4503599627370496), (-720051895772475/2251799813685248)), (54369661/4503599627370496), by norm_num⟩
  | 6 => ⟨((-392835600112117/4503599627370496), (-706070093824499/9007199254740992)), (48099759/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-4799930863/67108864)), (1/33554432), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-148462847/67108864), (-4954544101/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((2036644094997/18014398509481984), (985855809254295/9007199254740992)), (158872019/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4981889/17179869184), (-4823055695/17179869184)), (391/17179869184), by norm_num⟩
  | 2 => ⟨((3194573/8589934592), (6185446803/17179869184)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((-1365653/4294967296), (-5288452601/17179869184)), (433/17179869184), by norm_num⟩
  | 4 => ⟨((3502831/17179869184), (3391153275/17179869184)), (279/17179869184), by norm_num⟩
  | 5 => ⟨((-7187667/68719476736), (-6958509131/68719476736)), (575/68719476736), by norm_num⟩
  | 6 => ⟨((3072667/68719476736), (5949407841/137438953472)), (247/68719476736), by norm_num⟩
  | 7 => ⟨((-4503563/274877906944), (-1089994987/68719476736)), (91/68719476736), by norm_num⟩
  | 8 => ⟨((2887853/549755813888), (5591563883/1099511627776)), (469/1099511627776), by norm_num⟩
  | 9 => ⟨((-6584175/4398046511104), (-6374256973/4398046511104)), (537/4398046511104), by norm_num⟩
  | 10 => ⟨((3377615/8796093022208), (6539858531/17592186044416)), (553/17592186044416), by norm_num⟩
  | 11 => ⟨((-6300663/70368744177664), (-6099783977/70368744177664)), (259/35184372088832), by norm_num⟩
  | 12 => ⟨((5386961/281474976710656), (5215212331/281474976710656)), (445/281474976710656), by norm_num⟩
  | 13 => ⟨((-8502943/2251799813685248), (-8231849549/2251799813685248)), (705/2251799813685248), by norm_num⟩
  | 14 => ⟨((6231319/9007199254740992), (754081329/1125899906842624)), (519/9007199254740992), by norm_num⟩
  | 15 => ⟨((-2131069/18014398509481984), (-4126251563/36028797018963968)), (713/72057594037927936), by norm_num⟩
  | 16 => ⟨((1366521/72057594037927936), (1322953287/72057594037927936)), (459/288230376151711744), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039973471/10141204801825835211973625643008), (2044792087147/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889276889076315/316912650057057350374175801344), (2419355389099/633825300114114700748351602688)), (11555/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889499904358631/39614081257132168796771975168), (2721246438213/39614081257132168796771975168)), (52005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944629875737613/1237940039285380274899124224), (2890671539381/2475880078570760549798248448)), (1727/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770925883449689/154742504910672534362390528), (361242170319/19342813113834066795298816)), (27637/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549305046910853/9671406556917033397649408), (2708536434589/9671406556917033397649408)), (25915/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258571227817331/604462909807314587353088), (2369189784999/604462909807314587353088)), (22681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887438445837443/75557863725914323419136), (3848472185373/75557863725914323419136)), (18433/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648637024788033/2361183241434822606848), (2885076101399/4722366482869645213696)), (55317/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202635356547963/73786976294838206464), (3964903813645/590295810358705651712)), (76089/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455754385624521/18446744073709551616), (4953017752111/73786976294838206464)), (95153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455535496502165/2305843009213693952), (5567868750347/9223372036854775808)), (53553/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593389617260115/1152921504606846976), (5562527671799/1152921504606846976)), (107179/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597029034288871/72057594037927936), (2430604383645/72057594037927936)), (11733/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490851405574035/36028797018963968), (3639910834283/18014398509481984)), (4405/1125899906842624), by norm_num⟩
  | 3 => ⟨((1488271783332741/9007199254740992), (4539412190609/4503599627370496)), (176489/9007199254740992), by norm_num⟩
  | 2 => ⟨((139122884419845/281474976710656), (9047460029007/2251799813685248)), (353845/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106552874653615/1125899906842624), (13493005292359/1125899906842624)), (266471/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174638149874987/2251799813685248), (13337312832675/562949953421312)), (537309/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174638149874987/2251799813685248), (13337312832675/562949953421312)), (2049671177390670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049428308757907/1125899906842624), (103042301101483/2251799813685248)), (2126509/2251799813685248), by norm_num⟩
  | 2 => ⟨((243948271864893/281474976710656), (750340815699/8796093022208)), (2079385/1125899906842624), by norm_num⟩
  | 3 => ⟨((837505861767497/1125899906842624), (83238931119679/562949953421312)), (7918151/2251799813685248), by norm_num⟩
  | 4 => ⟨((1196733716353881/2251799813685248), (123835329084429/562949953421312)), (1765187/281474976710656), by norm_num⟩
  | 5 => ⟨((1054097758578889/4503599627370496), (1053009509569695/4503599627370496)), (2652837/281474976710656), by norm_num⟩
  | 6 => ⟨((2036644094997/18014398509481984), (985855809254295/9007199254740992)), (158872019/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148462847/67108864), (-4954544101/67108864)), (1/33554432), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-159302925/2097152)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((781912911560997/9007199254740992), (-246927579780403/4503599627370496)), (22876193/4503599627370496), by norm_num⟩
  | 1 => ⟨((-983959675/4294967296), (2485870511/17179869184)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((324590749/1073741824), (-820044349/4294967296)), (77/4294967296), by norm_num⟩
  | 3 => ⟨((-4568605841/17179869184), (360690675/2147483648)), (273/17179869184), by norm_num⟩
  | 4 => ⟨((1507101591/8589934592), (-1903766739/17179869184)), (91/8589934592), by norm_num⟩
  | 5 => ⟨((-198866375/2147483648), (1004829913/17179869184)), (97/17179869184), by norm_num⟩
  | 6 => ⟨((349879843/8589934592), (-441967291/17179869184)), (43/17179869184), by norm_num⟩
  | 7 => ⟨((-4221042121/274877906944), (1333002307/137438953472)), (131/137438953472), by norm_num⟩
  | 8 => ⟨((2784893037/549755813888), (-879467377/274877906944)), (175/549755813888), by norm_num⟩
  | 9 => ⟨((-1633220529/1099511627776), (1031539923/1099511627776)), (207/2199023255552), by norm_num⟩
  | 10 => ⟨((1724065043/4398046511104), (-2177834395/8796093022208)), (221/8796093022208), by norm_num⟩
  | 11 => ⟨((-827255725/8796093022208), (2089974481/35184372088832)), (107/17592186044416), by norm_num⟩
  | 12 => ⟨((2910900379/140737488355328), (-229815103/17592186044416)), (95/70368744177664), by norm_num⟩
  | 13 => ⟨((-4727404911/1125899906842624), (2985822681/1125899906842624)), (311/1125899906842624), by norm_num⟩
  | 14 => ⟨((3564540737/4503599627370496), (-2251359209/4503599627370496)), (59/1125899906842624), by norm_num⟩
  | 15 => ⟨((-2508540629/18014398509481984), (1584390939/18014398509481984)), (335/36028797018963968), by norm_num⟩
  | 16 => ⟨((3310091267/144115188075855872), (-522662315/36028797018963968)), (223/144115188075855872), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-366900347825/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55576812568363/19807040628566084398385987584), (-54257880297/39614081257132168796771975168)), (46143/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236174041383283/4951760157141521099596496896), (-976448610341/39614081257132168796771975168)), (25957/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889145682343317/2475880078570760549798248448), (-1037235830635/2475880078570760549798248448)), (27581/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110675754376911/9671406556917033397649408), (-259241255561/38685626227668133590597632)), (27583/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549198618352497/9671406556917033397649408), (-242966768129/2417851639229258349412352)), (25861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629239187078181/302231454903657293676544), (-425048081491/302231454903657293676544)), (45261/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887288066964603/75557863725914323419136), (-1380867389021/75557863725914323419136)), (73555/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297161709794169/4722366482869645213696), (-517589629865/2361183241434822606848)), (55173/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810464553258013/295147905179352825856), (-1422606087905/590295810358705651712)), (2371/18446744073709551616), by norm_num⟩
  | 8 => ⟨((911413220405055/36893488147419103232), (-888555143223/36893488147419103232)), (94855/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821928480303983/9223372036854775808), (-1997672749433/9223372036854775808)), (106733/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796588981442485/576460752303423488), (-1995704214633/1152921504606846976)), (106759/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193874949230057/144115188075855872), (-218003644125/18014398509481984)), (23361/36028797018963968), by norm_num⟩
  | 4 => ⟨((745290435872319/18014398509481984), (-2611626069065/36028797018963968)), (70113/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487940844828851/9007199254740992), (-1628408039699/4503599627370496)), (175387/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225325859103803/4503599627370496), (-6490540124409/4503599627370496)), (21943/281474976710656), by norm_num⟩
  | 1 => ⟨((1106099461597055/1125899906842624), (-9678280813981/2251799813685248)), (527425/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173036839093535/2251799813685248), (-4781911128383/562949953421312)), (1058043/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173036839093535/2251799813685248), (-4781911128383/562949953421312)), (4036113747603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((262108292696405/281474976710656), (-18458601835021/1125899906842624)), (2060045/2251799813685248), by norm_num⟩
  | 2 => ⟨((1951987715681521/2251799813685248), (-34377141933391/1125899906842624)), (1952079/1125899906842624), by norm_num⟩
  | 3 => ⟨((422498579524425/562949953421312), (-59600110406261/1125899906842624)), (7007103/2251799813685248), by norm_num⟩
  | 4 => ⟨((631022368260571/1125899906842624), (-44730374046765/562949953421312)), (2814907/562949953421312), by norm_num⟩
  | 5 => ⟨((1386219152961579/4503599627370496), (-200556844477055/2251799813685248)), (3602617/562949953421312), by norm_num⟩
  | 6 => ⟨((781912911560997/9007199254740992), (-246927579780403/4503599627370496)), (22876193/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-159302925/2097152)), (1/33554432), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-1307740649/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-361452751085815/4503599627370496), (-486541751883537/9007199254740992)), (79199107/9007199254740992), by norm_num⟩
  | 1 => ⟨((3733948499/17179869184), (2513083437/17179869184)), (411/17179869184), by norm_num⟩
  | 2 => ⟨((-631982499/2147483648), (-1701389027/8589934592)), (559/17179869184), by norm_num⟩
  | 3 => ⟨((4563840889/17179869184), (3071631265/17179869184)), (507/17179869184), by norm_num⟩
  | 4 => ⟨((-3089777559/17179869184), (-519883229/4294967296)), (345/17179869184), by norm_num⟩
  | 5 => ⟨((418363637/4294967296), (2252591813/34359738368)), (47/4294967296), by norm_num⟩
  | 6 => ⟨((-755299821/17179869184), (-2033377237/68719476736)), (171/34359738368), by norm_num⟩
  | 7 => ⟨((4675176759/274877906944), (3146564363/274877906944)), (133/68719476736), by norm_num⟩
  | 8 => ⟨((-3165153341/549755813888), (-532565891/137438953472)), (181/274877906944), by norm_num⟩
  | 9 => ⟨((3809508507/2199023255552), (2563938077/2199023255552)), (219/1099511627776), by norm_num⟩
  | 10 => ⟨((-257908507/549755813888), (-1388654605/4398046511104)), (477/8796093022208), by norm_num⟩
  | 11 => ⟨((4063587981/35184372088832), (341867853/4398046511104)), (59/4398046511104), by norm_num⟩
  | 12 => ⟨((-458516677/17592186044416), (-77149609/4398046511104)), (107/35184372088832), by norm_num⟩
  | 13 => ⟨((191028643/35184372088832), (257138479/70368744177664)), (179/281474976710656), by norm_num⟩
  | 14 => ⟨((-4729738561/4503599627370496), (-3183286445/4503599627370496)), (139/1125899906842624), by norm_num⟩
  | 15 => ⟨((1707782595/9007199254740992), (1149399933/9007199254740992)), (403/18014398509481984), by norm_num⟩
  | 16 => ⟨((-578095125/18014398509481984), (-194539545/9007199254740992)), (137/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1660304352181/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778358441011819/633825300114114700748351602688), (-982018637085/158456325028528675187087900672)), (23147/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472319976958245/9903520314283042199192993792), (-2209084174333/19807040628566084398385987584)), (52093/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889025681396831/2475880078570760549798248448), (-73330992497/38685626227668133590597632)), (55363/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885345724753411/77371252455336267181195264), (-2345961670361/77371252455336267181195264)), (13845/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387271219698683/2417851639229258349412352), (-4397339482673/9671406556917033397649408)), (1623/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258378194771239/604462909807314587353088), (-1923166862527/302231454903657293676544)), (45461/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943562022117693/37778931862957161709568), (-6247783643837/75557863725914323419136)), (36953/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297037616578423/4722366482869645213696), (-4683643350947/4722366482869645213696)), (27729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620756731735959/590295810358705651712), (-3218222520157/295147905179352825856)), (19075/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822608356209633/73786976294838206464), (-2010052932739/18446744073709551616)), (23861/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821679544104355/9223372036854775808), (-4518946561267/4611686018427387904)), (53735/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592924547117353/1152921504606846976), (-9028717342839/1152921504606846976)), (26897/288230376151711744), by norm_num⟩
  | 5 => ⟨((596824091784623/72057594037927936), (-1972453143877/36028797018963968)), (47137/72057594037927936), by norm_num⟩
  | 4 => ⟨((745115350549645/18014398509481984), (-2953526950833/9007199254740992)), (70839/18014398509481984), by norm_num⟩
  | 3 => ⟨((92967853978481/562949953421312), (-14731608482067/9007199254740992)), (177565/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112181688039413/2251799813685248), (-14677655288899/2251799813685248)), (89135/1125899906842624), by norm_num⟩
  | 1 => ⟨((552656471017847/562949953421312), (-21881901922449/1125899906842624)), (67293/281474976710656), by norm_num⟩
  | 0 => ⟨((542344850081629/562949953421312), (-43227293362185/1125899906842624)), (545437/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542344850081629/562949953421312), (-43227293362185/1125899906842624)), (2080677036765670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043328220927753/1125899906842624), (-83290174536717/1125899906842624)), (1092829/1125899906842624), by norm_num⟩
  | 2 => ⟨((1921301381830733/2251799813685248), (-308727229097467/2251799813685248)), (4374107/2251799813685248), by norm_num⟩
  | 3 => ⟨((1596983211377571/2251799813685248), (-131707545286405/562949953421312)), (4331817/1125899906842624), by norm_num⟩
  | 4 => ⟨((504664163271305/1125899906842624), (-747259103072437/2251799813685248)), (510701/70368744177664), by norm_num⟩
  | 5 => ⟨((204435359146463/2251799813685248), (-334945307044625/1125899906842624)), (25496859/2251799813685248), by norm_num⟩
  | 6 => ⟨((-361452751085815/4503599627370496), (-486541751883537/9007199254740992)), (79199107/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1307740649/16777216)), (1/33554432), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile046Terms1
