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
namespace Reinmann.XiBand97.Tile065Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨65,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81383/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81383/2560))
  have he : value ((69/80), (81383/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1017427393/536870912), (-37500585829/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1004069731266189/9007199254740992), (-908090119125487/9007199254740992)), (4655075/9007199254740992), by norm_num⟩
  | 1 => ⟨((-33663432173/137438953472), (30445525027/137438953472)), (315/274877906944), by norm_num⟩
  | 2 => ⟨((4622882533/17179869184), (-16723913965/68719476736)), (175/137438953472), by norm_num⟩
  | 3 => ⟨((-27086696319/137438953472), (48994926391/274877906944)), (129/137438953472), by norm_num⟩
  | 4 => ⟨((59515554871/549755813888), (-6728303527/68719476736)), (143/274877906944), by norm_num⟩
  | 5 => ⟨((-52307615959/1099511627776), (47307500395/1099511627776)), (127/549755813888), by norm_num⟩
  | 6 => ⟨((4788815807/274877906944), (-34648400853/2199023255552)), (47/549755813888), by norm_num⟩
  | 7 => ⟨((-24050522943/4398046511104), (43503038811/8796093022208)), (119/4398046511104), by norm_num⟩
  | 8 => ⟨((13211100027/8796093022208), (-5974121629/4398046511104)), (33/4398046511104), by norm_num⟩
  | 9 => ⟨((-51604895419/140737488355328), (5833994165/17592186044416)), (65/35184372088832), by norm_num⟩
  | 10 => ⟨((22677508905/281474976710656), (-41019505163/562949953421312)), (231/562949953421312), by norm_num⟩
  | 11 => ⟨((-36238239941/2251799813685248), (4096775677/281474976710656)), (93/1125899906842624), by norm_num⟩
  | 12 => ⟨((53082367625/18014398509481984), (-48008193095/18014398509481984)), (275/18014398509481984), by norm_num⟩
  | 13 => ⟨((-71774697089/144115188075855872), (32456855933/72057594037927936)), (375/144115188075855872), by norm_num⟩
  | 14 => ⟨((5632326017/72057594037927936), (-20375714731/288230376151711744)), (119/288230376151711744), by norm_num⟩
  | 15 => ⟨((-26401034991/2305843009213693952), (47754689267/4611686018427387904)), (281/4611686018427387904), by norm_num⟩
  | 16 => ⟨((58009002949/36893488147419103232), (-26231944235/18446744073709551616)), (311/36893488147419103232), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (-478869943377/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045171359599/633825300114114700748351602688), (-1133771156935/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236256594946917/4951760157141521099596496896), (-1275280338811/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118115451085975/154742504910672534362390528), (-1354723405359/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442878353399209/38685626227668133590597632), (-1354428798807/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387463981145165/2417851639229258349412352), (-634732032811/4835703278458516698824704)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053313816685/604462909807314587353088), (-1110468221143/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944110981453175/37778931862957161709568), (-112745281085/4722366482869645213696)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648930899265553/2361183241434822606848), (-1352430512213/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621891187349781/590295810358705651712), (-232344867681/73786976294838206464)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456007057652775/18446744073709551616), (-2322199832645/73786976294838206464)), (5933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823279379231017/9223372036854775808), (-2610758747401/9223372036854775808)), (1669/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594527469848495/1152921504606846976), (-652153827621/288230376151711744)), (3339/576460752303423488), by norm_num⟩
  | 5 => ⟨((597527101814943/72057594037927936), (-2280129288127/144115188075855872)), (2923/72057594037927936), by norm_num⟩
  | 4 => ⟨((186543328670893/4503599627370496), (-3415381354623/36028797018963968)), (8773/36028797018963968), by norm_num⟩
  | 3 => ⟨((372535646201015/2251799813685248), (-4260817356545/9007199254740992)), (5487/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114856503728203/2251799813685248), (-8496457324377/4503599627370496)), (21973/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109369477443125/1125899906842624), (-396309979843/70368744177664)), (16511/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092977482818717/1125899906842624), (-784807204661/70368744177664)), (66301/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092977482818717/1125899906842624), (-784807204661/70368744177664)), (252918251998137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((265219424606117/281474976710656), (-3047434671005/140737488355328)), (32551/562949953421312), by norm_num⟩
  | 2 => ⟨((1998165423518219/2251799813685248), (-91886121250431/2251799813685248)), (251009/2251799813685248), by norm_num⟩
  | 3 => ⟨((442337500013467/562949953421312), (-81536408906319/1125899906842624)), (465959/2251799813685248), by norm_num⟩
  | 4 => ⟨((1378455873349291/2251799813685248), (-128134343227149/1125899906842624)), (799743/2251799813685248), by norm_num⟩
  | 5 => ⟨((814666980592691/2251799813685248), (-156876767575669/1125899906842624)), (1161169/2251799813685248), by norm_num⟩
  | 6 => ⟨((1004069731266189/9007199254740992), (-908090119125487/9007199254740992)), (4655075/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-37500585829/536870912)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-533107351/268435456), (-78597600627/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22687834549103/281474976710656), (500276461235045/4503599627370496)), (871441/1125899906842624), by norm_num⟩
  | 1 => ⟨((51016278931/274877906944), (-70308173951/274877906944)), (493/274877906944), by norm_num⟩
  | 2 => ⟨((-14683665421/68719476736), (20236319157/68719476736)), (143/68719476736), by norm_num⟩
  | 3 => ⟨((11270129703/68719476736), (-31063897885/137438953472)), (221/137438953472), by norm_num⟩
  | 4 => ⟨((-12975216325/137438953472), (8940908525/68719476736)), (511/549755813888), by norm_num⟩
  | 5 => ⟨((47802463501/1099511627776), (-8234881075/137438953472)), (473/1099511627776), by norm_num⟩
  | 6 => ⟨((-18344873311/1099511627776), (50564038415/2199023255552)), (365/2199023255552), by norm_num⟩
  | 7 => ⟨((48275007793/8796093022208), (-16632571585/2199023255552)), (483/8796093022208), by norm_num⟩
  | 8 => ⟨((-27789328327/17592186044416), (76595822779/35184372088832)), (559/35184372088832), by norm_num⟩
  | 9 => ⟨((56877593911/140737488355328), (-78385955429/140737488355328)), (575/140737488355328), by norm_num⟩
  | 10 => ⟨((-26193099973/281474976710656), (18049033247/140737488355328)), (133/140737488355328), by norm_num⟩
  | 11 => ⟨((43863157481/2251799813685248), (-60450087123/2251799813685248)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((-8416554379/2251799813685248), (46397156493/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 13 => ⟨((2981512715/4503599627370496), (-32871815661/36028797018963968)), (493/72057594037927936), by norm_num⟩
  | 14 => ⟨((-31383710775/288230376151711744), (675804935/4503599627370496)), (163/144115188075855872), by norm_num⟩
  | 15 => ⟨((9635155279/576460752303423488), (-13278706083/576460752303423488)), (201/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-11092882457/4611686018427387904), (30575350681/9223372036854775808)), (465/18446744073709551616), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (89493650285/316912650057057350374175801344)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889449795732039/316912650057057350374175801344), (1694825212677/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889888699611503/39614081257132168796771975168), (1906340787827/19807040628566084398385987584)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944836267703709/1237940039285380274899124224), (4050152139283/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442834579416841/38685626227668133590597632), (1012306870379/38685626227668133590597632)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549691332595249/9671406556917033397649408), (948792123253/2417851639229258349412352)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78681803537221/37778931862957161709568), (829947590123/151115727451828646838272)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471996599258251/18889465931478580854784), (5392818377973/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162210550596561/590295810358705651712), (2021501685275/2361183241434822606848)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810823051622755/295147905179352825856), (2778256755419/295147905179352825856)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823720126160979/73786976294838206464), (6941719098689/73786976294838206464)), (745/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822930359997433/9223372036854775808), (3902021209225/4611686018427387904)), (6709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797087726916051/576460752303423488), (487331647667/72057594037927936)), (1679/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194742825618907/144115188075855872), (6815069686233/144115188075855872)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491872852792795/36028797018963968), (10207469475939/36028797018963968)), (1105/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489538663771641/9007199254740992), (12732876859059/9007199254740992)), (5537/4503599627370496), by norm_num⟩
  | 2 => ⟨((17409923669973/35184372088832), (12693239627239/2251799813685248)), (1389/281474976710656), by norm_num⟩
  | 1 => ⟨((277098503288151/281474976710656), (18940951117363/1125899906842624)), (16763/1125899906842624), by norm_num⟩
  | 0 => ⟨((136356844407371/140737488355328), (37487378596835/1125899906842624)), (33907/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((136356844407371/140737488355328), (37487378596835/1125899906842624)), (129344944480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055652270946653/1125899906842624), (72641066858649/1125899906842624)), (33981/562949953421312), by norm_num⟩
  | 2 => ⟨((985100883142265/1125899906842624), (136217627743421/1125899906842624)), (272427/2251799813685248), by norm_num⟩
  | 3 => ⟨((422714533536539/562949953421312), (238365958774957/1125899906842624)), (271319/1125899906842624), by norm_num⟩
  | 4 => ⟨((584360983734689/1125899906842624), (178987056419803/562949953421312)), (1044691/2251799813685248), by norm_num⟩
  | 5 => ⟨((94738569810491/562949953421312), (1486356671382117/4503599627370496)), (1748733/2251799813685248), by norm_num⟩
  | 6 => ⟨((-22687834549103/281474976710656), (500276461235045/4503599627370496)), (871441/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-78597600627/1073741824)), (1/536870912), by norm_num⟩, -12, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-2220696383/1073741824), (-20462741591/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((5994084379887/70368744177664), (-420669801853035/4503599627370496)), (4157167/9007199254740992), by norm_num⟩
  | 1 => ⟨((-56145260153/274877906944), (61567512773/274877906944)), (307/274877906944), by norm_num⟩
  | 2 => ⟨((16828806739/68719476736), (-36908111959/137438953472)), (93/68719476736), by norm_num⟩
  | 3 => ⟨((-53804954835/274877906944), (59001191463/274877906944)), (75/68719476736), by norm_num⟩
  | 4 => ⟨((32254661713/274877906944), (-70739339049/549755813888)), (181/274877906944), by norm_num⟩
  | 5 => ⟨((-30937320339/549755813888), (33925105341/549755813888)), (175/549755813888), by norm_num⟩
  | 6 => ⟨((12364075699/549755813888), (-13558141621/549755813888)), (141/1099511627776), by norm_num⟩
  | 7 => ⟨((-33883152767/4398046511104), (37155432801/4398046511104)), (195/4398046511104), by norm_num⟩
  | 8 => ⟨((10156031481/4398046511104), (-1392106823/549755813888)), (59/4398046511104), by norm_num⟩
  | 9 => ⟨((-5411799973/8796093022208), (47475575041/70368744177664)), (127/35184372088832), by norm_num⟩
  | 10 => ⟨((5190771829/35184372088832), (-22768291393/140737488355328)), (123/140737488355328), by norm_num⟩
  | 11 => ⟨((-18104621427/562949953421312), (39706166037/1125899906842624)), (27/140737488355328), by norm_num⟩
  | 12 => ⟨((28941990757/4503599627370496), (-31737075947/4503599627370496)), (347/9007199254740992), by norm_num⟩
  | 13 => ⟨((-21353803945/18014398509481984), (11708028367/9007199254740992)), (129/18014398509481984), by norm_num⟩
  | 14 => ⟨((114295057/562949953421312), (-16042643357/72057594037927936)), (89/72057594037927936), by norm_num⟩
  | 15 => ⟨((-37419359831/1152921504606846976), (10258287645/288230376151711744)), (115/576460752303423488), by norm_num⟩
  | 16 => ⟨((44863853025/9223372036854775808), (-24598299451/4611686018427387904)), (139/4611686018427387904), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (-1083029157691/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111173632850039/39614081257132168796771975168), (-80107644479/39614081257132168796771975168)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889752374628961/39614081257132168796771975168), (-1441676714607/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472382027194433/618970019642690137449562112), (-1531458353663/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885597180850083/77371252455336267181195264), (-1531094929687/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387389218415757/2417851639229258349412352), (-1435015474191/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258791704488545/604462909807314587353088), (-1255252647575/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887796960646839/75557863725914323419136), (-2039062280417/75557863725914323419136)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297543145600091/4722366482869645213696), (-382166030885/1180591620717411303424)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810726600008917/295147905179352825856), (-1050442866931/295147905179352825856)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455870246760941/18446744073709551616), (-2624566918455/73786976294838206464)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911332030459027/4611686018427387904), (-2950521410979/9223372036854775808)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593912564728755/1152921504606846976), (-2947878148885/1152921504606846976)), (835/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194516626241995/144115188075855872), (-322052842159/18014398509481984)), (731/18014398509481984), by norm_num⟩
  | 4 => ⟨((11652665561271/281474976710656), (-964675094791/9007199254740992)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((744568705732069/4503599627370496), (-4813008438849/9007199254740992)), (10981/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113853762916203/2251799813685248), (-4797491805563/2251799813685248)), (10995/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107871437668527/1125899906842624), (-7157564600177/1125899906842624)), (33057/2251799813685248), by norm_num⟩
  | 0 => ⟨((272501407437361/281474976710656), (-3540286419875/281474976710656)), (33201/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272501407437361/281474976710656), (-3540286419875/281474976710656)), (126651768210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263769391848029/281474976710656), (-54838723835207/2251799813685248)), (65121/1125899906842624), by norm_num⟩
  | 2 => ⟨((988042405053321/1125899906842624), (-51389210525111/1125899906842624)), (62611/562949953421312), by norm_num⟩
  | 3 => ⟨((864718912674395/1125899906842624), (-180388039300617/2251799813685248)), (462421/2251799813685248), by norm_num⟩
  | 4 => ⟨((656900166934189/1125899906842624), (-138542465680565/1125899906842624)), (392195/1125899906842624), by norm_num⟩
  | 5 => ⟨((366217113986269/1125899906842624), (-646654774762377/4503599627370496)), (2216671/4503599627370496), by norm_num⟩
  | 6 => ⟨((5994084379887/70368744177664), (-420669801853035/4503599627370496)), (4157167/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-20462741591/268435456)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2301277821/1073741824), (-42410528291/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-948411343594353/9007199254740992), (465113041992763/9007199254740992)), (2953495/4503599627370496), by norm_num⟩
  | 1 => ⟨((17980298267/68719476736), (-2204442007/17179869184)), (225/137438953472), by norm_num⟩
  | 2 => ⟨((-44679362729/137438953472), (21911330409/137438953472)), (281/137438953472), by norm_num⟩
  | 3 => ⟨((74016030369/274877906944), (-36298407093/274877906944)), (117/68719476736), by norm_num⟩
  | 4 => ⟨((-22990365757/137438953472), (45099076581/549755813888)), (73/68719476736), by norm_num⟩
  | 5 => ⟨((91406260401/1099511627776), (-22413399059/549755813888)), (583/1099511627776), by norm_num⟩
  | 6 => ⟨((-75712008101/2199023255552), (9282534061/549755813888)), (485/2199023255552), by norm_num⟩
  | 7 => ⟨((1679797075/137438953472), (-26361406417/4398046511104)), (173/2199023255552), by norm_num⟩
  | 8 => ⟨((-2087069461/549755813888), (8188204263/4398046511104)), (27/1099511627776), by norm_num⟩
  | 9 => ⟨((2304965681/2199023255552), (-2260769247/4398046511104)), (479/70368744177664), by norm_num⟩
  | 10 => ⟨((-36656797109/140737488355328), (35953923427/281474976710656)), (239/140737488355328), by norm_num⟩
  | 11 => ⟨((8280792627/140737488355328), (-32488052149/1125899906842624)), (217/562949953421312), by norm_num⟩
  | 12 => ⟨((-54871991105/4503599627370496), (3363740701/562949953421312)), (361/4503599627370496), by norm_num⟩
  | 13 => ⟨((83908784975/36028797018963968), (-20574970181/18014398509481984)), (555/36028797018963968), by norm_num⟩
  | 14 => ⟨((-930828115/2251799813685248), (29215360127/144115188075855872)), (99/36028797018963968), by norm_num⟩
  | 15 => ⟨((78951115871/1152921504606846976), (-38718636083/1152921504606846976)), (527/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-49046538209/4611686018427387904), (6013262267/1152921504606846976)), (329/4611686018427387904), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (3498351418737/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111165884052933/39614081257132168796771975168), (4139648210813/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889612453965845/39614081257132168796771975168), (4656210892537/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889378863437827/2475880078570760549798248448), (2473070009353/1237940039285380274899124224)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885522232406733/77371252455336267181195264), (4944920559309/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774707826766563/4835703278458516698824704), (4634567554189/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258667445604715/604462909807314587353088), (4053951370453/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887593744951489/75557863725914323419136), (1646310723371/18889465931478580854784)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297389601817425/4722366482869645213696), (4936808087815/4722366482869645213696)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621240239900709/590295810358705651712), (424041275487/36893488147419103232)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823212034449655/73786976294838206464), (8475651052855/73786976294838206464)), (373/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822357710603193/9223372036854775808), (9527995178841/9223372036854775808)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199200187506385/144115188075855872), (1189888599633/144115188075855872)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298559788319265/36028797018963968), (8319228438587/144115188075855872)), (5897/144115188075855872), by norm_num⟩
  | 4 => ⟨((745557215163047/18014398509481984), (12458872710515/36028797018963968)), (4431/18014398509481984), by norm_num⟩
  | 3 => ⟨((372146390588373/2251799813685248), (7769337032341/4503599627370496)), (2777/2251799813685248), by norm_num⟩
  | 2 => ⟨((556637227757847/1125899906842624), (15486360125765/2251799813685248)), (11155/2251799813685248), by norm_num⟩
  | 1 => ⟨((553467155474017/562949953421312), (23098970448531/1125899906842624)), (16847/1125899906842624), by norm_num⟩
  | 0 => ⟨((543930792197815/562949953421312), (22838478554837/562949953421312)), (2135/70368744177664), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((543930792197815/562949953421312), (22838478554837/562949953421312)), (8144378930544831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1049255298107151/1125899906842624), (88267538934341/1125899906842624)), (68785/1125899906842624), by norm_num⟩
  | 2 => ⟨((121363532798613/140737488355328), (41129403384293/281474976710656)), (138991/1125899906842624), by norm_num⟩
  | 3 => ⟨((406606663366149/562949953421312), (567480321548945/2251799813685248)), (560669/2251799813685248), by norm_num⟩
  | 4 => ⟨((1031721261204211/2251799813685248), (409878850986029/1125899906842624)), (546255/1125899906842624), by norm_num⟩
  | 5 => ⟨((174281065525105/2251799813685248), (751187068246819/2251799813685248)), (3593143/4503599627370496), by norm_num⟩
  | 6 => ⟨((-948411343594353/9007199254740992), (465113041992763/9007199254740992)), (2953495/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-42410528291/536870912)), (1/536870912), by norm_num⟩, -13, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-2375405559/1073741824), (-43776637363/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((976063259134805/9007199254740992), (277223484684341/18014398509481984)), (1087737/4503599627370496), by norm_num⟩
  | 1 => ⟨((-19100592265/68719476736), (-10849978621/274877906944)), (43/68719476736), by norm_num⟩
  | 2 => ⟨((97984103715/274877906944), (6957411423/137438953472)), (223/274877906944), by norm_num⟩
  | 3 => ⟨((-41887377311/137438953472), (-11896938639/274877906944)), (193/274877906944), by norm_num⟩
  | 4 => ⟨((6714937595/34359738368), (15257522559/549755813888)), (125/274877906944), by norm_num⟩
  | 5 => ⟨((-110230239167/1099511627776), (-7826954537/549755813888)), (259/1099511627776), by norm_num⟩
  | 6 => ⟨((94244993709/2199023255552), (13383828007/2199023255552)), (7/68719476736), by norm_num⟩
  | 7 => ⟨((-8633344145/549755813888), (-9808240299/4398046511104)), (83/2199023255552), by norm_num⟩
  | 8 => ⟨((44288181035/8796093022208), (6289409913/8796093022208)), (215/17592186044416), by norm_num⟩
  | 9 => ⟨((-50487529551/35184372088832), (-1792446435/8796093022208)), (247/70368744177664), by norm_num⟩
  | 10 => ⟨((51799182593/140737488355328), (7356054931/140737488355328)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((-96627112807/1125899906842624), (-13722115177/1125899906842624)), (241/1125899906842624), by norm_num⟩
  | 12 => ⟨((82614550303/4503599627370496), (11732176835/4503599627370496)), (13/281474976710656), by norm_num⟩
  | 13 => ⟨((-65200657759/18014398509481984), (-4629606067/9007199254740992)), (83/9007199254740992), by norm_num⟩
  | 14 => ⟨((23890912175/36028797018963968), (13571091551/144115188075855872)), (123/72057594037927936), by norm_num⟩
  | 15 => ⟨((-65364245155/576460752303423488), (-2320610837/144115188075855872)), (85/288230376151711744), by norm_num⟩
  | 16 => ⟨((41913994653/2305843009213693952), (11904498551/4611686018427387904)), (55/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (91878253523/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778556887437163/633825300114114700748351602688), (217416870103/633825300114114700748351602688)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889503576482509/39614081257132168796771975168), (244546924503/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263881435497/2475880078570760549798248448), (64943123185/618970019642690137449562112)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885465135023647/77371252455336267181195264), (259706578391/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549309431838375/9671406556917033397649408), (243404906895/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258575336913059/604462909807314587353088), (26613663725/75557863725914323419136)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887445633208795/75557863725914323419136), (172923232727/37778931862957161709568)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648639942996175/2361183241434822606848), (259270137991/4722366482869645213696)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621091601196243/590295810358705651712), (89077535019/147573952589676412928)), (4737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455757390669299/18446744073709551616), (445108410765/73786976294838206464)), (5921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455539249271581/2305843009213693952), (500363274317/9223372036854775808)), (3331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593406485289429/1152921504606846976), (499884115167/1152921504606846976)), (6663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597037456171477/72057594037927936), (436860165645/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490880827644243/36028797018963968), (654214923577/36028797018963968)), (4373/18014398509481984), by norm_num⟩
  | 3 => ⟨((744157903794685/4503599627370496), (815890307655/9007199254740992)), (5467/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226075831242317/4503599627370496), (813079717641/2251799813685248)), (1367/281474976710656), by norm_num⟩
  | 1 => ⟨((2213323973425665/2251799813685248), (606308648777/562949953421312)), (32821/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175287161505375/2251799813685248), (2397370180473/1125899906842624)), (65695/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175287161505375/2251799813685248), (2397370180473/1125899906842624)), (250606545455168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((525341020182755/562949953421312), (9263645095385/2251799813685248)), (127207/2251799813685248), by norm_num⟩
  | 2 => ⟨((980470190518295/1125899906842624), (8644769815583/1125899906842624)), (238465/2251799813685248), by norm_num⟩
  | 3 => ⟨((1707517793736133/2251799813685248), (15056292404963/1125899906842624)), (418989/2251799813685248), by norm_num⟩
  | 4 => ⟨((647195685523977/1125899906842624), (45668157591849/2251799813685248)), (646637/2251799813685248), by norm_num⟩
  | 5 => ⟨((1486245296456417/4503599627370496), (13125604851571/562949953421312)), (1539271/4503599627370496), by norm_num⟩
  | 6 => ⟨((976063259134805/9007199254740992), (277223484684341/18014398509481984)), (1087737/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-43776637363/536870912)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-611009281/268435456), (-5630182101/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-555291175392909/9007199254740992), (-369774398805889/4503599627370496)), (1311301/2251799813685248), by norm_num⟩
  | 1 => ⟨((22360919899/137438953472), (29780756759/137438953472)), (53/34359738368), by norm_num⟩
  | 2 => ⟨((-14752937389/68719476736), (-39296562203/137438953472)), (141/68719476736), by norm_num⟩
  | 3 => ⟨((51911796733/274877906944), (34568626837/137438953472)), (249/137438953472), by norm_num⟩
  | 4 => ⟨((-8562387979/68719476736), (-45614294015/274877906944)), (331/274877906944), by norm_num⟩
  | 5 => ⟨((4519326551/68719476736), (24075747391/274877906944)), (351/549755813888), by norm_num⟩
  | 6 => ⟨((-7951174573/274877906944), (-42358185079/1099511627776)), (311/1099511627776), by norm_num⟩
  | 7 => ⟨((47962526939/4398046511104), (7984691343/549755813888)), (471/4398046511104), by norm_num⟩
  | 8 => ⟨((-15821982283/4398046511104), (-42144116427/8796093022208)), (313/8796093022208), by norm_num⟩
  | 9 => ⟨((37115660723/35184372088832), (24715719857/17592186044416)), (369/35184372088832), by norm_num⟩
  | 10 => ⟨((-19590071295/70368744177664), (-13045240329/35184372088832)), (49/17592186044416), by norm_num⟩
  | 11 => ⟨((9399876589/140737488355328), (3129739737/35184372088832)), (189/281474976710656), by norm_num⟩
  | 12 => ⟨((-16537875473/1125899906842624), (-44051000495/2251799813685248)), (335/2251799813685248), by norm_num⟩
  | 13 => ⟨((53716186441/18014398509481984), (71540378913/18014398509481984)), (273/9007199254740992), by norm_num⟩
  | 14 => ⟨((-20251442221/36028797018963968), (-13485654381/18014398509481984)), (413/72057594037927936), by norm_num⟩
  | 15 => ⟨((14251924541/144115188075855872), (9490510677/72057594037927936)), (73/72057594037927936), by norm_num⟩
  | 16 => ⟨((-37611645921/2305843009213693952), (-6261500441/288230376151711744)), (387/2305843009213693952), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-2885079051207/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778452165636787/633825300114114700748351602688), (-853301310477/158456325028528675187087900672)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889385439083611/39614081257132168796771975168), (-959770883095/9903520314283042199192993792)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944568965575923/1237940039285380274899124224), (-4078077965529/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442700959315267/38685626227668133590597632), (-4077011376679/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549190388811869/9671406556917033397649408), (-955266296641/2417851639229258349412352)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258470662391327/604462909807314587353088), (-1671149682223/302231454903657293676544)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((117954661139457/4722366482869645213696), (-1357278338135/18889465931478580854784)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297150756622157/4722366482869645213696), (-2034988968855/2361183241434822606848)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620912687993151/590295810358705651712), (-2796601565443/295147905179352825856)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113925242724135/4611686018427387904), (-218343163799/2305843009213693952)), (745/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455475077780115/2305843009213693952), (-7854138680723/9223372036854775808)), (3355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593146310120685/1152921504606846976), (-245199213977/36028797018963968)), (6717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596921671686853/72057594037927936), (-1714212702393/36028797018963968)), (1471/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490525666898947/36028797018963968), (-5133919837893/18014398509481984)), (1105/4503599627370496), by norm_num⟩
  | 3 => ⟨((743929124008649/4503599627370496), (-1600540719061/1125899906842624)), (2769/2251799813685248), by norm_num⟩
  | 2 => ⟨((556280025527129/1125899906842624), (-3189673793603/562949953421312)), (22227/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211789608056783/2251799813685248), (-38048493790017/2251799813685248)), (8383/562949953421312), by norm_num⟩
  | 0 => ⟨((67869370135353/70368744177664), (-37594993221425/1125899906842624)), (67833/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((67869370135353/70368744177664), (-37594993221425/1125899906842624)), (258762368209075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523042487340357/562949953421312), (-9064921294243/140737488355328)), (67689/1125899906842624), by norm_num⟩
  | 2 => ⟨((967257132323789/1125899906842624), (-67378479418571/562949953421312)), (269003/2251799813685248), by norm_num⟩
  | 3 => ⟨((1629677587679987/2251799813685248), (-57884643551937/281474976710656)), (526593/2251799813685248), by norm_num⟩
  | 4 => ⟨((1084203213609063/2251799813685248), (-335139227542799/1125899906842624)), (61175/140737488355328), by norm_num⟩
  | 5 => ⟨((645015952692315/4503599627370496), (-322727646836151/1125899906842624)), (3050515/4503599627370496), by norm_num⟩
  | 6 => ⟨((-555291175392909/9007199254740992), (-369774398805889/4503599627370496)), (1311301/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5630182101/67108864)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-2507931583/1073741824), (-11554743885/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-522091861841155/18014398509481984), (831366504473229/9007199254740992)), (1184009/2251799813685248), by norm_num⟩
  | 1 => ⟨((21573653739/274877906944), (-34353366541/137438953472)), (393/274877906944), by norm_num⟩
  | 2 => ⟨((-29211268673/274877906944), (46515320585/137438953472)), (267/137438953472), by norm_num⟩
  | 3 => ⟨((26368527335/274877906944), (-83977215509/274877906944)), (121/68719476736), by norm_num⟩
  | 4 => ⟨((-8925911969/137438953472), (56853628837/274877906944)), (329/274877906944), by norm_num⟩
  | 5 => ⟨((9668727081/274877906944), (-30792496201/274877906944)), (179/274877906944), by norm_num⟩
  | 6 => ⟨((-17455598877/1099511627776), (55591750353/1099511627776)), (325/1099511627776), by norm_num⟩
  | 7 => ⟨((27011793171/4398046511104), (-21506464389/1099511627776)), (505/4398046511104), by norm_num⟩
  | 8 => ⟨((-9143661491/4398046511104), (58240585213/8796093022208)), (43/1099511627776), by norm_num⟩
  | 9 => ⟨((22010217191/35184372088832), (-17524269833/8796093022208)), (13/1099511627776), by norm_num⟩
  | 10 => ⟨((-5960477309/35184372088832), (9491320489/17592186044416)), (453/140737488355328), by norm_num⟩
  | 11 => ⟨((23478213491/562949953421312), (-37386141613/281474976710656)), (7/8796093022208), by norm_num⟩
  | 12 => ⟨((-21193393589/2251799813685248), (67495698875/2251799813685248)), (407/2251799813685248), by norm_num⟩
  | 13 => ⟨((8829657503/4503599627370496), (-56240535665/9007199254740992)), (341/9007199254740992), by norm_num⟩
  | 14 => ⟨((-27327035173/72057594037927936), (10878728137/9007199254740992)), (265/36028797018963968), by norm_num⟩
  | 15 => ⟨((19734128825/288230376151711744), (-62848302761/288230376151711744)), (385/288230376151711744), by norm_num⟩
  | 16 => ⟨((-13360252883/1152921504606846976), (85098179465/2305843009213693952)), (131/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (2442453780051/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778362235120079/633825300114114700748351602688), (2889271631531/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472321096843485/9903520314283042199192993792), (3249764128929/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118064419958741/154742504910672534362390528), (3452051124835/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770696800404511/154742504910672534362390528), (3451125227343/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387272556884185/2417851639229258349412352), (404305801417/1208925819614629174706176)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314595801731809/151115727451828646838272), (1414578715941/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58972900341589/2361183241434822606848), (574442253659/9444732965739290427392)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324261183807223/1180591620717411303424), (53828777113/73786976294838206464)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620767402208551/590295810358705651712), (2367157235889/295147905179352825856)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822623015923771/73786976294838206464), (5913968386487/73786976294838206464)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821697850480531/9223372036854775808), (6647821489573/9223372036854775808)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592945116693619/1152921504606846976), (6641085588365/1152921504606846976)), (1677/288230376151711744), by norm_num⟩
  | 5 => ⟨((596834360901779/72057594037927936), (1450844814429/36028797018963968)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490266572570183/36028797018963968), (8689945753199/36028797018963968)), (8825/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487539330184119/9007199254740992), (10836007472015/9007199254740992)), (2763/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224497050928167/4503599627370496), (674778240279/140737488355328)), (22169/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210891762955947/2251799813685248), (32192146871023/2251799813685248)), (4177/281474976710656), by norm_num⟩
  | 0 => ⟨((1085084854048495/1125899906842624), (63598870446921/2251799813685248)), (33741/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085084854048495/1125899906842624), (63598870446921/2251799813685248)), (128711704734420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089702520189207/2251799813685248), (122586689344477/2251799813685248)), (133885/2251799813685248), by norm_num⟩
  | 2 => ⟨((1932600358181295/2251799813685248), (14220275716115/140737488355328)), (8221/70368744177664), by norm_num⟩
  | 3 => ⟨((1635659068914045/2251799813685248), (48818033957333/281474976710656)), (504725/2251799813685248), by norm_num⟩
  | 4 => ⟨((1120373021732563/2251799813685248), (567365958437915/2251799813685248)), (908319/2251799813685248), by norm_num⟩
  | 5 => ⟨((414482482572245/2251799813685248), (1129161676664265/4503599627370496)), (2723165/4503599627370496), by norm_num⟩
  | 6 => ⟨((-522091861841155/18014398509481984), (831366504473229/9007199254740992)), (1184009/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-11554743885/134217728)), (1/536870912), by norm_num⟩, -14, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile065Terms1
