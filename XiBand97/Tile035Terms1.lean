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
namespace Reinmann.XiBand97.Tile035Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6581/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6581/256))
  have he : value ((69/80), (6581/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1895292593/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((1350984221532709/9007199254740992), (87323133794139/9007199254740992)), (132828309/9007199254740992), by norm_num⟩
  | 1 => ⟨((-353862731/1073741824), (-91490047/4294967296)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((388757945/1073741824), (50256045/2147483648)), (157/4294967296), by norm_num⟩
  | 3 => ⟨((-1138918015/4294967296), (-36807939/2147483648)), (117/4294967296), by norm_num⟩
  | 4 => ⟨((1251229327/8589934592), (20218827/2147483648)), (131/8589934592), by norm_num⟩
  | 5 => ⟨((-274923183/4294967296), (-35540243/8589934592)), (117/17179869184), by norm_num⟩
  | 6 => ⟨((1610847933/68719476736), (104119861/68719476736)), (87/34359738368), by norm_num⟩
  | 7 => ⟨((-252813905/34359738368), (-65364205/137438953472)), (111/137438953472), by norm_num⟩
  | 8 => ⟨((1110977851/549755813888), (71809919/549755813888)), (31/137438953472), by norm_num⟩
  | 9 => ⟨((-4237965/8589934592), (-17531391/549755813888)), (123/2199023255552), by norm_num⟩
  | 10 => ⟨((119190539/1099511627776), (61632645/8796093022208)), (219/17592186044416), by norm_num⟩
  | 11 => ⟨((-1523714221/70368744177664), (-98487827/70368744177664)), (177/70368744177664), by norm_num⟩
  | 12 => ⟨((1115980779/281474976710656), (72133291/281474976710656)), (33/70368744177664), by norm_num⟩
  | 13 => ⟨((-377240061/562949953421312), (-48767089/1125899906842624)), (181/2251799813685248), by norm_num⟩
  | 14 => ⟨((1894585449/18014398509481984), (61229855/9007199254740992)), (115/9007199254740992), by norm_num⟩
  | 15 => ⟨((-277521981/18014398509481984), (-17938099/18014398509481984)), (137/72057594037927936), by norm_num⟩
  | 16 => ⟨((1219556235/576460752303423488), (2463377/18014398509481984)), (19/72057594037927936), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (84079529645/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045853732843/633825300114114700748351602688), (12441653903/79228162514264337593543950336)), (138315/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118128347881551/2475880078570760549798248448), (27989074521/9903520314283042199192993792)), (77803/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944924062248973/1237940039285380274899124224), (29732643725/618970019642690137449562112)), (41333/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771514377134599/154742504910672534362390528), (118904717857/154742504910672534362390528)), (165333/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549856887803899/9671406556917033397649408), (111445707841/9671406556917033397649408)), (155001/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629527108252221/302231454903657293676544), (97487538165/604462909807314587353088)), (33907/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888223541942199/75557863725914323419136), (39591447043/18889465931478580854784)), (220397/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648931540436043/2361183241434822606848), (14841166433/590295810358705651712)), (41325/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621893109767041/590295810358705651712), (163179725687/590295810358705651712)), (227291/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912015436078987/36893488147419103232), (50966265453/18446744073709551616)), (35515/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823282678501439/9223372036854775808), (229197602209/9223372036854775808)), (159821/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594531177869245/1152921504606846976), (57252378371/288230376151711744)), (319651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597528953541271/72057594037927936), (200171932867/144115188075855872)), (139853/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492353100144663/36028797018963968), (299835636835/36028797018963968)), (419581/36028797018963968), by norm_num⟩
  | 3 => ⟨((745076135237341/4503599627370496), (374056756091/9007199254740992)), (131129/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229737150048051/4503599627370496), (745904812093/4503599627370496)), (16393/70368744177664), by norm_num⟩
  | 1 => ⟨((1109393512954959/1125899906842624), (1113351777617/2251799813685248)), (787019/1125899906842624), by norm_num⟩
  | 0 => ⟨((2186098112049385/2251799813685248), (551194844009/562949953421312)), (1574681/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2186098112049385/2251799813685248), (551194844009/562949953421312)), (6006931309226607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2122311257603555/2251799813685248), (1070224804653/562949953421312)), (765139/281474976710656), by norm_num⟩
  | 2 => ⟨((1000130366979915/1125899906842624), (8069456751093/2251799813685248)), (2890379/562949953421312), by norm_num⟩
  | 3 => ⟨((222098888596437/281474976710656), (14336103400935/2251799813685248)), (20622919/2251799813685248), by norm_num⟩
  | 4 => ⟨((700946216702629/1125899906842624), (11311956285991/1125899906842624)), (32807777/2251799813685248), by norm_num⟩
  | 5 => ⟨((872542284388645/2251799813685248), (1760607873307/140737488355328)), (20754605/1125899906842624), by norm_num⟩
  | 6 => ⟨((1350984221532709/9007199254740992), (87323133794139/9007199254740992)), (132828309/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1895292593/33554432)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-242453/4096)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1086269662780615/9007199254740992), (-590098215218373/9007199254740992)), (110848973/4503599627370496), by norm_num⟩
  | 1 => ⟨((596339305/2147483648), (323951567/2147483648)), (123/2147483648), by norm_num⟩
  | 2 => ⟨((-686560997/2147483648), (-745926049/4294967296)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((526955039/2147483648), (71564925/536870912)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((-606679409/4294967296), (-329568659/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((1117544771/17179869184), (607087905/17179869184)), (15/1073741824), by norm_num⟩
  | 6 => ⟨((-428873655/17179869184), (-465957187/34359738368)), (93/17179869184), by norm_num⟩
  | 7 => ⟨((1128592097/137438953472), (613089185/137438953472)), (247/137438953472), by norm_num⟩
  | 8 => ⟨((-1299339669/549755813888), (-705845009/549755813888)), (287/549755813888), by norm_num⟩
  | 9 => ⟨((1329706735/2199023255552), (180585355/549755813888)), (297/2199023255552), by norm_num⟩
  | 10 => ⟨((-1224705163/8796093022208), (-332650517/4398046511104)), (69/2199023255552), by norm_num⟩
  | 11 => ⟨((64090633/2199023255552), (278529499/17592186044416)), (233/35184372088832), by norm_num⟩
  | 12 => ⟨((-196765515/35184372088832), (-213779291/70368744177664)), (181/140737488355328), by norm_num⟩
  | 13 => ⟨((557623805/562949953421312), (605840011/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 14 => ⟨((-733700721/4503599627370496), (-99642727/1125899906842624)), (43/1125899906842624), by norm_num⟩
  | 15 => ⟨((901017783/36028797018963968), (489463163/36028797018963968)), (213/36028797018963968), by norm_num⟩
  | 16 => ⟨((-518667529/144115188075855872), (-563515291/288230376151711744)), (247/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-1722026021305/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889448423724989/316912650057057350374175801344), (-4076452782517/633825300114114700748351602688)), (92601/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889885457060583/39614081257132168796771975168), (-573148793087/4951760157141521099596496896)), (52101/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944834444252447/1237940039285380274899124224), (-2435387658557/1237940039285380274899124224)), (110745/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771334444014825/154742504910672534362390528), (-608707783247/19342813113834066795298816)), (55389/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549687460271577/9671406556917033397649408), (-570515738407/1208925819614629174706176)), (103891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258905227703671/604462909807314587353088), (-3992427869869/604462909807314587353088)), (22735/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887980049294641/75557863725914323419136), (-6485478835467/75557863725914323419136)), (36961/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297679249880287/4722366482869645213696), (-2431085043989/2361183241434822606848)), (55471/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621638375534809/590295810358705651712), (-3341166802369/295147905179352825856)), (2385/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1823709508075801/73786976294838206464), (-8348192783015/73786976294838206464)), (190943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822917098661657/9223372036854775808), (-9385222988469/9223372036854775808)), (215007/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594160550318779/1152921504606846976), (-9377108498171/1152921504606846976)), (215253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597363970727909/72057594037927936), (-8195845094441/144115188075855872)), (11789/9007199254740992), by norm_num⟩
  | 4 => ⟨((93240428063371/2251799813685248), (-3068881969763/9007199254740992)), (141745/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489499745038277/9007199254740992), (-7656256319885/4503599627370496)), (177667/4503599627370496), by norm_num⟩
  | 2 => ⟨((278546654605653/562949953421312), (-1908088964227/281474976710656)), (178397/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108297475426033/1125899906842624), (-22777722974371/1125899906842624)), (538849/1125899906842624), by norm_num⟩
  | 0 => ⟨((272641853279589/281474976710656), (-22539509371361/562949953421312)), (1092379/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272641853279589/281474976710656), (-22539509371361/562949953421312)), (4167095188621139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527269412409151/562949953421312), (-87328737763251/1125899906842624)), (2203671/1125899906842624), by norm_num⟩
  | 2 => ⟨((490463591788989/562949953421312), (-20448430614045/140737488355328)), (558731/140737488355328), by norm_num⟩
  | 3 => ⟨((1661705950349681/2251799813685248), (-570094626107927/2251799813685248)), (4543749/562949953421312), by norm_num⟩
  | 4 => ⟨((1081916237804137/2251799813685248), (-105174716987335/281474976710656)), (36027153/2251799813685248), by norm_num⟩
  | 5 => ⟨((51358095071045/562949953421312), (-1617056485017831/4503599627370496)), (7692905/281474976710656), by norm_num⟩
  | 6 => ⟨((-1086269662780615/9007199254740992), (-590098215218373/9007199254740992)), (110848973/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-242453/4096)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-2068388091/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((106039153450043/2251799813685248), (264173831078925/2251799813685248)), (79643803/4503599627370496), by norm_num⟩
  | 1 => ⟨((-242491517/2147483648), (-1208231317/4294967296)), (23/536870912), by norm_num⟩
  | 2 => ⟨((290734631/2147483648), (724303041/2147483648)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((-464767465/4294967296), (-1157868559/4294967296)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((278615927/4294967296), (347055943/2147483648)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-534473451/17179869184), (-166440761/2147483648)), (53/4294967296), by norm_num⟩
  | 6 => ⟨((427203787/34359738368), (66517919/2147483648)), (171/34359738368), by norm_num⟩
  | 7 => ⟨((-585365681/137438953472), (-1458313175/137438953472)), (237/137438953472), by norm_num⟩
  | 8 => ⟨((43863925/34359738368), (874220567/274877906944)), (9/17179869184), by norm_num⟩
  | 9 => ⟨((-373977239/1099511627776), (-465842081/549755813888)), (155/1099511627776), by norm_num⟩
  | 10 => ⟨((358703301/4398046511104), (893632419/4398046511104)), (151/4398046511104), by norm_num⟩
  | 11 => ⟨((-156387809/8796093022208), (-389606719/8796093022208)), (67/8796093022208), by norm_num⟩
  | 12 => ⟨((500002117/140737488355328), (622824073/70368744177664)), (217/140737488355328), by norm_num⟩
  | 13 => ⟨((-368908527/562949953421312), (-459528277/281474976710656)), (81/281474976710656), by norm_num⟩
  | 14 => ⟨((505488007/4503599627370496), (629657533/2251799813685248)), (225/4503599627370496), by norm_num⟩
  | 15 => ⟨((-161614307/9007199254740992), (-402627419/9007199254740992)), (73/9007199254740992), by norm_num⟩
  | 16 => ⟨((387534183/144115188075855872), (965458385/144115188075855872)), (177/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (193614392761/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444694301583177/158456325028528675187087900672), (458270001871/158456325028528675187087900672)), (92381/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236218911071045/4951760157141521099596496896), (2061840829763/39614081257132168796771975168)), (25985/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944763443643563/1237940039285380274899124224), (2190243589557/2475880078570760549798248448)), (55225/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((13837445814667/1208925819614629174706176), (2189723674837/154742504910672534362390528)), (110465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549555576702359/9671406556917033397649408), (2052313691407/9671406556917033397649408)), (103577/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258790489078719/604462909807314587353088), (1795222401317/604462909807314587353088)), (45323/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943897417330397/37778931862957161709568), (2916201626587/75557863725914323419136)), (147329/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324385354788945/1180591620717411303424), (2186246163141/4722366482869645213696)), (27631/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202681326494911/73786976294838206464), (1502309226941/295147905179352825856)), (38003/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227934678884297/9223372036854775808), (3753569255639/73786976294838206464)), (1485/576460752303423488), by norm_num⟩
  | 7 => ⟨((1822659619869937/9223372036854775808), (527467143901/1152921504606846976)), (26741/1152921504606846976), by norm_num⟩
  | 6 => ⟨((49809611685185/36028797018963968), (1053988698051/288230376151711744)), (214039/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194511642152181/144115188075855872), (3684709366913/144115188075855872)), (187409/144115188075855872), by norm_num⟩
  | 4 => ⟨((372883121192423/9007199254740992), (5518572082847/36028797018963968)), (140681/18014398509481984), by norm_num⟩
  | 3 => ⟨((744562190486463/4503599627370496), (6883377051863/9007199254740992)), (88035/2251799813685248), by norm_num⟩
  | 2 => ⟨((2227675054793901/4503599627370496), (13722331390571/4503599627370496)), (705595/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215678247934055/2251799813685248), (20472759792581/2251799813685248)), (132711/281474976710656), by norm_num⟩
  | 0 => ⟨((2179818944420977/2251799813685248), (40504482897961/2251799813685248)), (2136613/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179818944420977/2251799813685248), (40504482897961/2251799813685248)), (8150531777388762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2109410431803905/2251799813685248), (39209719540057/1125899906842624)), (4213495/2251799813685248), by norm_num⟩
  | 2 => ⟨((986646933349155/1125899906842624), (146921393142033/2251799813685248)), (4093797/1125899906842624), by norm_num⟩
  | 3 => ⟨((429911971420879/562949953421312), (128749936922443/1125899906842624)), (3854575/562949953421312), by norm_num⟩
  | 4 => ⟨((1283809798782467/2251799813685248), (393293498764829/2251799813685248)), (6768865/562949953421312), by norm_num⟩
  | 5 => ⟨((663241827360749/2251799813685248), (14014180025105/70368744177664)), (80661423/4503599627370496), by norm_num⟩
  | 6 => ⟨((106039153450043/2251799813685248), (264173831078925/2251799813685248)), (79643803/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-2068388091/33554432)), (1/16777216), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-66982587/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((527682714691699/9007199254740992), (-915076589620093/9007199254740992)), (69298643/2251799813685248), by norm_num⟩
  | 1 => ⟨((-312624523/2147483648), (1084270431/4294967296)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((194210689/1073741824), (-673577701/2147483648)), (207/2147483648), by norm_num⟩
  | 3 => ⟨((-643460577/4294967296), (1115851805/4294967296)), (345/4294967296), by norm_num⟩
  | 4 => ⟨((399734867/4294967296), (-173299223/1073741824)), (217/4294967296), by norm_num⟩
  | 5 => ⟨((-99330383/2147483648), (344505913/4294967296)), (109/4294967296), by norm_num⟩
  | 6 => ⟨((658204611/34359738368), (-1141420045/34359738368)), (363/34359738368), by norm_num⟩
  | 7 => ⟨((-233653859/34359738368), (202594447/17179869184)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((145152007/68719476736), (-1006856577/274877906944)), (325/274877906944), by norm_num⟩
  | 9 => ⟨((-320612611/549755813888), (1111975379/1099511627776)), (361/1099511627776), by norm_num⟩
  | 10 => ⟨((637353927/4398046511104), (-1105262005/4398046511104)), (361/4398046511104), by norm_num⟩
  | 11 => ⟨((-575914549/17592186044416), (249679355/4398046511104)), (329/17592186044416), by norm_num⟩
  | 12 => ⟨((477031297/70368744177664), (-827239853/70368744177664)), (275/70368744177664), by norm_num⟩
  | 13 => ⟨((-729463533/562949953421312), (1264993115/562949953421312)), (423/562949953421312), by norm_num⟩
  | 14 => ⟨((129474913/562949953421312), (-224527843/562949953421312)), (303/2251799813685248), by norm_num⟩
  | 15 => ⟨((-686363887/18014398509481984), (18597691/281474976710656)), (101/4503599627370496), by norm_num⟩
  | 16 => ⟨((426387547/72057594037927936), (-23106763/2251799813685248)), (253/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1364772013531/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222332740447677/79228162514264337593543950336), (-403738457613/158456325028528675187087900672)), (92359/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472405410592655/9903520314283042199192993792), (-454120626953/9903520314283042199192993792)), (51957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889389197483639/2475880078570760549798248448), (-964795341449/1237940039285380274899124224)), (220841/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771055441130203/154742504910672534362390528), (-241139514785/19342813113834066795298816)), (220867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549426625793195/9671406556917033397649408), (-1808042288173/9671406556917033397649408)), (51773/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258677727789603/604462909807314587353088), (-197691637583/75557863725914323419136)), (90617/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887611730160093/75557863725914323419136), (-321130854627/9444732965739290427392)), (294557/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297404206725997/4722366482869645213696), (-962979548111/2361183241434822606848)), (220965/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405315533285325/147573952589676412928), (-330856517181/73786976294838206464)), (151951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113952632169905/4611686018427387904), (-1653276966917/36893488147419103232)), (379991/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56949852392321/288230376151711744), (-3717109658859/9223372036854775808)), (213823/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593643714500171/1152921504606846976), (-3713658164187/1152921504606846976)), (427841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194281308719059/144115188075855872), (-811392986993/36028797018963968)), (374581/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491188069722031/36028797018963968), (-4860609985071/36028797018963968)), (70289/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488695756538653/9007199254740992), (-1515556490457/2251799813685248)), (351831/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226823470873567/4503599627370496), (-6041965853781/2251799813685248)), (1409645/4503599627370496), by norm_num⟩
  | 1 => ⟨((276801871370059/281474976710656), (-4506227275163/562949953421312)), (2120287/2251799813685248), by norm_num⟩
  | 0 => ⟨((544337101646075/562949953421312), (-35647731892037/2251799813685248)), (4263959/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544337101646075/562949953421312), (-35647731892037/2251799813685248)), (16265712746627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2104794260156481/2251799813685248), (-17234554280037/562949953421312)), (8380963/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965275231356129/2251799813685248), (-64437683500133/1125899906842624)), (8090405/1125899906842624), by norm_num⟩
  | 3 => ⟨((853916465262657/1125899906842624), (-224953892578087/2251799813685248)), (30095973/2251799813685248), by norm_num⟩
  | 4 => ⟨((1272799228147225/2251799813685248), (-21326477561407/140737488355328)), (51664541/2251799813685248), by norm_num⟩
  | 5 => ⟨((333862782310581/1125899906842624), (-771488094507559/4503599627370496)), (37031601/1125899906842624), by norm_num⟩
  | 6 => ⟨((527682714691699/9007199254740992), (-915076589620093/9007199254740992)), (69298643/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-66982587/1048576)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1106243205/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-985209993736141/9007199254740992), (-35692476762627/9007199254740992)), (160897883/4503599627370496), by norm_num⟩
  | 1 => ⟨((1204974051/4294967296), (21827077/2147483648)), (99/1073741824), by norm_num⟩
  | 2 => ⟨((-1545348709/4294967296), (-55985347/4294967296)), (255/2147483648), by norm_num⟩
  | 3 => ⟨((330311765/1073741824), (47866527/4294967296)), (219/2147483648), by norm_num⟩
  | 4 => ⟨((-1694465899/8589934592), (-61387609/8589934592)), (141/2147483648), by norm_num⟩
  | 5 => ⟨((217310961/2147483648), (62982443/17179869184)), (581/17179869184), by norm_num⟩
  | 6 => ⟨((-743188813/17179869184), (-26924463/17179869184)), (499/34359738368), by norm_num⟩
  | 7 => ⟨((544640477/34359738368), (39462791/68719476736)), (23/4294967296), by norm_num⟩
  | 8 => ⟨((-698487621/137438953472), (-25305015/137438953472)), (237/137438953472), by norm_num⟩
  | 9 => ⟨((1592520333/1099511627776), (57694295/1099511627776)), (271/549755813888), by norm_num⟩
  | 10 => ⟨((-816946801/2199023255552), (-29596589/2199023255552)), (279/2199023255552), by norm_num⟩
  | 11 => ⟨((1523947035/17592186044416), (55210001/17592186044416)), (523/17592186044416), by norm_num⟩
  | 12 => ⟨((-651474495/35184372088832), (-47203619/70368744177664)), (449/70368744177664), by norm_num⟩
  | 13 => ⟨((1028307131/281474976710656), (37253813/281474976710656)), (711/562949953421312), by norm_num⟩
  | 14 => ⟨((-753587347/1125899906842624), (-426581/17592186044416)), (523/2251799813685248), by norm_num⟩
  | 15 => ⟨((1030887137/9007199254740992), (74694565/18014398509481984)), (359/9007199254740992), by norm_num⟩
  | 16 => ⟨((-661043325/36028797018963968), (-2993559/4503599627370496)), (231/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-2022552212319/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444636161390959/158456325028528675187087900672), (-4786083265137/633825300114114700748351602688)), (92671/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889489118601379/39614081257132168796771975168), (-5383270722399/39614081257132168796771975168)), (104285/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944623810524521/1237940039285380274899124224), (-5718430517699/2475880078570760549798248448)), (55419/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885456499623815/77371252455336267181195264), (-2858487033613/77371252455336267181195264)), (221755/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549292167630343/9671406556917033397649408), (-5358115894227/9671406556917033397649408)), (51995/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629279579359691/302231454903657293676544), (-4686804320897/604462909807314587353088)), (91033/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943708667683769/37778931862957161709568), (-7613156675115/75557863725914323419136)), (148007/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297256907113853/4722366482869645213696), (-2853665072417/2361183241434822606848)), (222149/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810528577911821/295147905179352825856), (-3921728282947/295147905179352825856)), (152839/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822982237556123/73786976294838206464), (-2449534646535/18446744073709551616)), (191217/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455524474137557/2305843009213693952), (-11014407859713/9223372036854775808)), (430701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796670036972911/576460752303423488), (-2750947214123/288230376151711744)), (431279/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149251074608277/18014398509481984), (-2404093444479/36028797018963968)), (378021/144115188075855872), by norm_num⟩
  | 4 => ⟨((186345623879279/4503599627370496), (-7200345016203/18014398509481984)), (568335/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488142483058913/9007199254740992), (-8979558368131/4503599627370496)), (87/1099511627776), by norm_num⟩
  | 2 => ⟨((1112822011864607/2251799813685248), (-4474138480147/562949953421312)), (358069/1125899906842624), by norm_num⟩
  | 1 => ⟨((138279053732667/140737488355328), (-26688620707069/1125899906842624)), (16919/17592186044416), by norm_num⟩
  | 0 => ⟨((1086366128142097/1125899906842624), (-52753591839771/1125899906842624)), (275025/140737488355328), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086366128142097/1125899906842624), (-52753591839771/1125899906842624)), (1049137116015386537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((522874376206441/562949953421312), (-25450626189887/281474976710656)), (1113017/281474976710656), by norm_num⟩
  | 2 => ⟨((481049290711591/562949953421312), (-189110669070665/1125899906842624)), (4537683/562949953421312), by norm_num⟩
  | 3 => ⟨((1580728144326117/2251799813685248), (-646391763030165/2251799813685248)), (37117493/2251799813685248), by norm_num⟩
  | 4 => ⟨((924095979715853/2251799813685248), (-907513754884057/2251799813685248)), (36710683/1125899906842624), by norm_num⟩
  | 5 => ⟨((26975901000307/4503599627370496), (-1489705803026445/4503599627370496)), (119441605/2251799813685248), by norm_num⟩
  | 6 => ⟨((-985209993736141/9007199254740992), (-35692476762627/9007199254740992)), (160897883/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1106243205/16777216)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1138205411/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((67902668417731/2251799813685248), (884029615928473/9007199254740992)), (268871645/9007199254740992), by norm_num⟩
  | 1 => ⟨((-170897517/2147483648), (-1112463397/4294967296)), (85/1073741824), by norm_num⟩
  | 2 => ⟨((451008345/4294967296), (1467927341/4294967296)), (451/4294967296), by norm_num⟩
  | 3 => ⟨((-198372813/2147483648), (-1291314803/4294967296)), (399/4294967296), by norm_num⟩
  | 4 => ⟨((261758613/4294967296), (851963449/4294967296)), (265/4294967296), by norm_num⟩
  | 5 => ⟨((-138159197/4294967296), (-449676077/4294967296)), (141/4294967296), by norm_num⟩
  | 6 => ⟨((243073361/17179869184), (395573649/8589934592)), (499/34359738368), by norm_num⟩
  | 7 => ⟨((-366562591/68719476736), (-1193076043/68719476736)), (189/34359738368), by norm_num⟩
  | 8 => ⟨((241844923/137438953472), (787149019/137438953472)), (501/274877906944), by norm_num⟩
  | 9 => ⟨((-283663385/549755813888), (-461629197/274877906944)), (37/68719476736), by norm_num⟩
  | 10 => ⟨((149720787/1099511627776), (243653183/549755813888)), (157/1099511627776), by norm_num⟩
  | 11 => ⟨((-143680633/4398046511104), (-116911767/1099511627776)), (303/8796093022208), by norm_num⟩
  | 12 => ⟨((126393809/17592186044416), (205691237/8796093022208)), (67/8796093022208), by norm_num⟩
  | 13 => ⟨((-205268005/140737488355328), (-668099651/140737488355328)), (437/281474976710656), by norm_num⟩
  | 14 => ⟨((77387719/281474976710656), (1967805/2199023255552)), (331/1125899906842624), by norm_num⟩
  | 15 => ⟨((-108923001/2251799813685248), (-1418076217/9007199254740992)), (117/2251799813685248), by norm_num⟩
  | 16 => ⟨((71863511/9007199254740992), (233899027/9007199254740992)), (311/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (207230724877/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778456345367943/633825300114114700748351602688), (245165204795/79228162514264337593543950336)), (92393/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889390374641431/39614081257132168796771975168), (275756027001/4951760157141521099596496896)), (207909/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889143482009855/2475880078570760549798248448), (2343381920523/2475880078570760549798248448)), (55233/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110675608311917/9671406556917033397649408), (2342769791907/154742504910672534362390528)), (220965/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549196282228293/9671406556917033397649408), (1097848248123/4835703278458516698824704)), (207189/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314619046253107/151115727451828646838272), (30009132483/9444732965739290427392)), (181325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471821059476695/18889465931478580854784), (779932899285/18889465931478580854784)), (294717/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297158600506233/4722366482869645213696), (36542707411/73786976294838206464)), (110547/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405231111442451/147573952589676412928), (1607013923841/295147905179352825856)), (304097/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822820037456995/73786976294838206464), (2007470396209/36893488147419103232)), (190129/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821920483865371/9223372036854775808), (1128311049825/2305843009213693952)), (106995/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593168977540841/1152921504606846976), (2254396414281/576460752303423488)), (428217/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193865977181433/144115188075855872), (3940191249035/144115188075855872)), (374957/144115188075855872), by norm_num⟩
  | 4 => ⟨((372641300132531/9007199254740992), (5900295198739/36028797018963968)), (562971/36028797018963968), by norm_num⟩
  | 3 => ⟨((371979349409405/2251799813685248), (7357913404685/9007199254740992)), (704651/9007199254740992), by norm_num⟩
  | 2 => ⟨((556316862333921/1125899906842624), (14663579195597/4503599627370496)), (706061/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212082726304307/2251799813685248), (21865166030131/2251799813685248)), (531313/562949953421312), by norm_num⟩
  | 0 => ⟨((271586418476307/281474976710656), (43212012124441/2251799813685248)), (2139451/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271586418476307/281474976710656), (43212012124441/2251799813685248)), (8161357883933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2095532820537903/2251799813685248), (41693921588261/1125899906842624)), (8421383/2251799813685248), by norm_num⟩
  | 2 => ⟨((1947022218812003/2251799813685248), (9700127490701/140737488355328)), (16297653/2251799813685248), by norm_num⟩
  | 3 => ⟨((836399360298587/1125899906842624), (268391371345501/2251799813685248)), (3803771/281474976710656), by norm_num⟩
  | 4 => ⟨((605342805086467/1125899906842624), (398760795588937/2251799813685248)), (26232679/1125899906842624), by norm_num⟩
  | 5 => ⟨((1160626683277399/4503599627370496), (428789410307783/2251799813685248)), (74997949/2251799813685248), by norm_num⟩
  | 6 => ⟨((67902668417731/2251799813685248), (884029615928473/9007199254740992)), (268871645/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1138205411/16777216)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-583980757/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((382170364865757/4503599627370496), (-104611928774097/2251799813685248)), (5161173/281474976710656), by norm_num⟩
  | 1 => ⟨((-986992391/4294967296), (135085275/1073741824)), (215/4294967296), by norm_num⟩
  | 2 => ⟨((1336412471/4294967296), (-182908853/1073741824)), (293/4294967296), by norm_num⟩
  | 3 => ⟨((-1206357353/4294967296), (660435141/4294967296)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((204179767/1073741824), (-447122879/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((-442343247/4294967296), (484332481/8589934592)), (199/8589934592), by norm_num⟩
  | 6 => ⟨((798591813/17179869184), (-437198891/17179869184)), (91/8589934592), by norm_num⟩
  | 7 => ⟨((-1235786697/68719476736), (676546597/68719476736)), (71/17179869184), by norm_num⟩
  | 8 => ⟨((836643103/137438953472), (-458030537/137438953472)), (97/68719476736), by norm_num⟩
  | 9 => ⟨((-1006965121/549755813888), (551275417/549755813888)), (59/137438953472), by norm_num⟩
  | 10 => ⟨((1090764839/2199023255552), (-597152601/2199023255552)), (129/1099511627776), by norm_num⟩
  | 11 => ⟨((-1074125797/8796093022208), (588043353/8796093022208)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((969595527/35184372088832), (-530816973/35184372088832)), (233/35184372088832), by norm_num⟩
  | 13 => ⟨((-201977951/35184372088832), (221150617/70368744177664)), (49/35184372088832), by norm_num⟩
  | 14 => ⟨((1250208985/1125899906842624), (-684442255/1125899906842624)), (153/562949953421312), by norm_num⟩
  | 15 => ⟨((-451417159/2251799813685248), (247133865/2251799813685248)), (223/4503599627370496), by norm_num⟩
  | 16 => ⟨((152807541/4503599627370496), (-669250913/36028797018963968)), (19/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-652468763523/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889183194166111/316912650057057350374175801344), (-771830158795/633825300114114700748351602688)), (23069/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944644645446813/19807040628566084398385987584), (-217033231319/9903520314283042199192993792)), (12977/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((118064764633631/154742504910672534362390528), (-461085772537/1237940039285380274899124224)), (55155/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770702657782483/154742504910672534362390528), (-921924502161/154742504910672534362390528)), (27579/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549096082558845/9671406556917033397649408), (-432020914977/4835703278458516698824704)), (206857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258388693508395/604462909807314587353088), (-377887157115/302231454903657293676544)), (181013/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887142407446097/75557863725914323419136), (-153455211637/9444732965739290427392)), (294171/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648526263855433/2361183241434822606848), (-920301368681/4722366482869645213696)), (220651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779082734859/590295810358705651712), (-1264716205675/590295810358705651712)), (303431/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455659765834321/18446744073709551616), (-789924357565/36893488147419103232)), (23709/4611686018427387904), by norm_num⟩
  | 7 => ⟨((227714736224831/1152921504606846976), (-110993248897/576460752303423488)), (426837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99560477095231/72057594037927936), (-443524115649/288230376151711744)), (426931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596845602210137/72057594037927936), (-6055925233/562949953421312)), (373671/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490305840279727/36028797018963968), (-2321446227985/36028797018963968)), (560719/36028797018963968), by norm_num⟩
  | 3 => ⟨((743799039142365/4503599627370496), (-2894770470803/9007199254740992)), (701273/9007199254740992), by norm_num⟩
  | 2 => ⟨((556160846324021/1125899906842624), (-1442120766631/1125899906842624)), (175459/562949953421312), by norm_num⟩
  | 1 => ⟨((1105591414495353/1125899906842624), (-8600268671013/2251799813685248)), (527085/562949953421312), by norm_num⟩
  | 0 => ⟨((2171034927268445/2251799813685248), (-2123980296553/281474976710656)), (2114057/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2171034927268445/2251799813685248), (-2123980296553/281474976710656)), (8064487461570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2093038601419425/2251799813685248), (-4095599778117/281474976710656)), (8216741/2251799813685248), by norm_num⟩
  | 2 => ⟨((121562123007431/140737488355328), (-60909488521785/2251799813685248)), (7756985/1125899906842624), by norm_num⟩
  | 3 => ⟨((419585651803767/562949953421312), (-105221243075063/2251799813685248)), (6909923/562949953421312), by norm_num⟩
  | 4 => ⟨((1246008805999215/2251799813685248), (-156849906784561/2251799813685248)), (43784671/2251799813685248), by norm_num⟩
  | 5 => ⟨((678539913754001/2251799813685248), (-347164723766225/4503599627370496)), (109110425/4503599627370496), by norm_num⟩
  | 6 => ⟨((382170364865757/4503599627370496), (-104611928774097/2251799813685248)), (5161173/281474976710656), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-583980757/8388608)), (1/8388608), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile035Terms1
