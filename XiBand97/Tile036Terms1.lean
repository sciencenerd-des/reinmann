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
namespace Reinmann.XiBand97.Tile036Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33263/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33263/1280))
  have he : value ((69/80), (33263/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-119744563/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1154158136814163/9007199254740992), (-707603484835697/9007199254740992)), (8244945/562949953421312), by norm_num⟩
  | 1 => ⟨((-302308157/1073741824), (741369137/4294967296)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((1328477825/4294967296), (-814477245/4294967296)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-972988043/4294967296), (596529807/4294967296)), (59/2147483648), by norm_num⟩
  | 4 => ⟨((1068936621/8589934592), (-655354977/8589934592)), (33/2147483648), by norm_num⟩
  | 5 => ⟨((-469738763/8589934592), (575984825/17179869184)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((688081037/34359738368), (-421856005/34359738368)), (11/4294967296), by norm_num⟩
  | 7 => ⟨((-863924895/137438953472), (529664219/137438953472)), (113/137438953472), by norm_num⟩
  | 8 => ⟨((474559253/274877906944), (-145473905/137438953472)), (63/274877906944), by norm_num⟩
  | 9 => ⟨((-463428113/1099511627776), (284123413/1099511627776)), (125/2199023255552), by norm_num⟩
  | 10 => ⟨((25456391/274877906944), (-499426357/8796093022208)), (7/549755813888), by norm_num⟩
  | 11 => ⟨((-1301722949/70368744177664), (798074085/70368744177664)), (91/35184372088832), by norm_num⟩
  | 12 => ⟨((119174069/35184372088832), (-292257999/140737488355328)), (17/35184372088832), by norm_num⟩
  | 13 => ⟨((-1289118491/2251799813685248), (395173205/1125899906842624)), (187/2251799813685248), by norm_num⟩
  | 14 => ⟨((809280809/9007199254740992), (-496162445/9007199254740992)), (119/9007199254740992), by norm_num⟩
  | 15 => ⟨((-948358231/72057594037927936), (581429503/72057594037927936)), (71/36028797018963968), by norm_num⟩
  | 16 => ⟨((1041878007/576460752303423488), (-638765597/576460752303423488)), (79/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-716422556601/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889522737121443/316912650057057350374175801344), (-424050017175/316912650057057350374175801344)), (23071/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890053117567447/39614081257132168796771975168), (-953953958851/39614081257132168796771975168)), (103825/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944923810008701/1237940039285380274899124224), (-506690074645/1237940039285380274899124224)), (6895/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771513841279459/154742504910672534362390528), (-63322487333/9671406556917033397649408)), (110327/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193732044015443/1208925819614629174706176), (-949603251993/9671406556917033397649408)), (103439/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053714489749/604462909807314587353088), (-830668861705/604462909807314587353088)), (90517/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472055665946901/18889465931478580854784), (-337349584577/18889465931478580854784)), (147103/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20279099495613/73786976294838206464), (-505832584797/2361183241434822606848)), (27585/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621892040645993/590295810358705651712), (-1390416579291/590295810358705651712)), (151737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824029403104279/73786976294838206464), (-1737086697303/73786976294838206464)), (47425/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911640421832415/4611686018427387904), (-976469543233/4611686018427387904)), (106727/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594529115711963/1152921504606846976), (-243917004233/144115188075855872)), (106753/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195055847464943/144115188075855872), (-426404330729/36028797018963968)), (186875/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492349501520751/36028797018963968), (-2554826885219/36028797018963968)), (280429/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490146883934103/9007199254740992), (-398405609763/1125899906842624)), (350739/9007199254740992), by norm_num⟩
  | 2 => ⟨((139357732718567/281474976710656), (-6355662291299/4503599627370496)), (702089/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218760291877865/2251799813685248), (-1185820003263/281474976710656)), (263667/562949953421312), by norm_num⟩
  | 0 => ⟨((68313078218381/70368744177664), (-18786195763001/2251799813685248)), (2115511/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((68313078218381/70368744177664), (-18786195763001/2251799813685248)), (8070034035689543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530500529533683/562949953421312), (-18237398941547/1125899906842624)), (2071361/1125899906842624), by norm_num⟩
  | 2 => ⟨((1999095368571203/2251799813685248), (-17186163240637/562949953421312)), (3971033/1125899906842624), by norm_num⟩
  | 3 => ⟨((886325782841067/1125899906842624), (-122059799913167/2251799813685248)), (7293243/1125899906842624), by norm_num⟩
  | 4 => ⟨((173605295614747/281474976710656), (-96087358258023/1125899906842624)), (24546749/2251799813685248), by norm_num⟩
  | 5 => ⟨((840195465611397/2251799813685248), (-474110329242427/4503599627370496)), (68938331/4503599627370496), by norm_num⟩
  | 6 => ⟨((1154158136814163/9007199254740992), (-707603484835697/9007199254740992)), (8244945/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-119744563/2097152)), (1/16777216), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-2007784173/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-1222984097515493/9007199254740992), (180298588751273/9007199254740992)), (311683761/9007199254740992), by norm_num⟩
  | 1 => ⟨((167848167/536870912), (-98980151/2147483648)), (345/4294967296), by norm_num⟩
  | 2 => ⟨((-1545938749/4294967296), (56977555/1073741824)), (399/4294967296), by norm_num⟩
  | 3 => ⟨((37079745/134217728), (-87463779/2147483648)), (309/4294967296), by norm_num⟩
  | 4 => ⟨((-683034145/4294967296), (100696397/4294967296)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((19659303/268435456), (-92744809/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((-965700651/34359738368), (142368543/34359738368)), (257/34359738368), by norm_num⟩
  | 7 => ⟨((1270633099/137438953472), (-11707703/8589934592)), (341/137438953472), by norm_num⟩
  | 8 => ⟨((-91429401/34359738368), (215663859/549755813888)), (395/549755813888), by norm_num⟩
  | 9 => ⟨((187132423/274877906944), (-55176043/549755813888)), (203/1099511627776), by norm_num⟩
  | 10 => ⟨((-1378842649/8796093022208), (203276055/8796093022208)), (377/8796093022208), by norm_num⟩
  | 11 => ⟨((1154510011/35184372088832), (-170203787/35184372088832)), (159/17592186044416), by norm_num⟩
  | 12 => ⟨((-1772238361/281474976710656), (261272469/281474976710656)), (491/281474976710656), by norm_num⟩
  | 13 => ⟨((1255609117/1125899906842624), (-11569271/70368744177664)), (175/562949953421312), by norm_num⟩
  | 14 => ⟨((-826041953/4503599627370496), (243558683/9007199254740992)), (463/9007199254740992), by norm_num⟩
  | 15 => ⟨((1014417007/36028797018963968), (-74775279/18014398509481984)), (143/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1167890739/288230376151711744), (172176443/288230376151711744)), (331/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (3901610894995/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889447163833773/316912650057057350374175801344), (2309014555011/316912650057057350374175801344)), (138981/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944941239739897/19807040628566084398385987584), (324646720619/2475880078570760549798248448)), (156399/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889665539624299/2475880078570760549798248448), (5517872512527/2475880078570760549798248448)), (10389/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885665443457401/77371252455336267181195264), (2758305251855/77371252455336267181195264)), (166281/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24213811006139/151115727451828646838272), (2585240782793/4835703278458516698824704)), (155949/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629450947682453/302231454903657293676544), (2261415351679/302231454903657293676544)), (34129/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887974220296403/75557863725914323419136), (7347086388323/75557863725914323419136)), (867/295147905179352825856), by norm_num⟩
  | 10 => ⟨((648837258125617/2361183241434822606848), (1377028930089/1180591620717411303424)), (41641/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621631279346413/590295810358705651712), (946260760889/73786976294838206464)), (229187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911849878864919/36893488147419103232), (4728624438433/36893488147419103232)), (286727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822904921096039/9223372036854775808), (10632038051505/9223372036854775808)), (161451/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594146864807319/1152921504606846976), (5311415686443/576460752303423488)), (40415/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194714273749853/144115188075855872), (9284622686775/144115188075855872)), (17711/9007199254740992), by norm_num⟩
  | 4 => ⟨((93238935660751/2251799813685248), (13906231411161/36028797018963968)), (426007/36028797018963968), by norm_num⟩
  | 3 => ⟨((372366001853781/2251799813685248), (17346575331433/9007199254740992)), (33385/562949953421312), by norm_num⟩
  | 2 => ⟨((1114142086356213/2251799813685248), (17292285991495/2251799813685248)), (268321/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108208830750313/1125899906842624), (25802817247471/1125899906842624)), (405591/562949953421312), by norm_num⟩
  | 0 => ⟨((272575893334757/281474976710656), (51063866389237/1125899906842624)), (411833/281474976710656), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272575893334757/281474976710656), (51063866389237/1125899906842624)), (1571018220067882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((526758354084771/562949953421312), (24724718269505/281474976710656)), (3339927/1125899906842624), by norm_num⟩
  | 2 => ⟨((977099705409299/1125899906842624), (185081488280817/1125899906842624)), (3418585/562949953421312), by norm_num⟩
  | 3 => ⟨((817540414927273/1125899906842624), (321241820124209/1125899906842624)), (7057493/562949953421312), by norm_num⟩
  | 4 => ⟨((501977146998505/1125899906842624), (933042695252831/2251799813685248)), (57105949/2251799813685248), by norm_num⟩
  | 5 => ⟨((121996238240711/4503599627370496), (1663970686361479/4503599627370496)), (196490031/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1222984097515493/9007199254740992), (180298588751273/9007199254740992)), (311683761/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-2007784173/33554432)), (3/33554432), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-261361469/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((247257373931209/2251799813685248), (141052848705581/2251799813685248)), (108808813/4503599627370496), by norm_num⟩
  | 1 => ⟨((-141357729/536870912), (-322561225/2147483648)), (251/4294967296), by norm_num⟩
  | 2 => ⟨((1355844121/4294967296), (773468037/4294967296)), (19/268435456), by norm_num⟩
  | 3 => ⟨((-1083724069/4294967296), (-618231783/4294967296)), (245/4294967296), by norm_num⟩
  | 4 => ⟨((1299328411/8589934592), (741227535/8589934592)), (37/1073741824), by norm_num⟩
  | 5 => ⟨((-623130691/8589934592), (-710954401/17179869184)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((996134759/34359738368), (142066183/8589934592)), (231/34359738368), by norm_num⟩
  | 7 => ⟨((-1364929617/137438953472), (-778651037/137438953472)), (319/137438953472), by norm_num⟩
  | 8 => ⟨((818239569/274877906944), (233390455/137438953472)), (193/274877906944), by norm_num⟩
  | 9 => ⟨((-109002933/137438953472), (-248731497/549755813888)), (13/68719476736), by norm_num⟩
  | 10 => ⟨((836408377/4398046511104), (477145665/4398046511104)), (201/4398046511104), by norm_num⟩
  | 11 => ⟨((-182329063/4398046511104), (-416052849/17592186044416)), (177/17592186044416), by norm_num⟩
  | 12 => ⟨((582941331/70368744177664), (665100773/140737488355328)), (285/140737488355328), by norm_num⟩
  | 13 => ⟨((-860204469/562949953421312), (-490720615/562949953421312)), (53/140737488355328), by norm_num⟩
  | 14 => ⟨((1178674417/4503599627370496), (336199041/2251799813685248)), (293/4503599627370496), by norm_num⟩
  | 15 => ⟨((-753690083/18014398509481984), (-214978691/9007199254740992)), (189/18014398509481984), by norm_num⟩
  | 16 => ⟨((110307/17592186044416), (515496387/144115188075855872)), (229/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (337651920463/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889389331534385/316912650057057350374175801344), (799195473103/633825300114114700748351602688)), (184557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944876504807937/19807040628566084398385987584), (898932508447/39614081257132168796771975168)), (207637/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472382205736809/618970019642690137449562112), (954914324027/2475880078570760549798248448)), (110313/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885597560132607/77371252455336267181195264), (119335969671/19342813113834066795298816)), (6895/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549557631958143/9671406556917033397649408), (894779119993/9671406556917033397649408)), (12929/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258792415103513/604462909807314587353088), (391345580661/302231454903657293676544)), (45255/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887798203649869/75557863725914323419136), (635711124519/37778931862957161709568)), (294183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648772077501483/2361183241434822606848), (476586168875/2361183241434822606848)), (55165/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810727356591383/295147905179352825856), (1309971480939/590295810358705651712)), (151723/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823483066120041/73786976294838206464), (818252104807/36893488147419103232)), (379363/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455666664369223/2305843009213693952), (1839747988941/9223372036854775808)), (426861/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593915482716369/1152921504606846976), (919050175439/576460752303423488)), (213479/576460752303423488), by norm_num⟩
  | 5 => ⟨((149314942538449/18014398509481984), (803243082799/72057594037927936)), (186849/72057594037927936), by norm_num⟩
  | 4 => ⟨((745773141322463/18014398509481984), (1203015419289/18014398509481984)), (560767/36028797018963968), by norm_num⟩
  | 3 => ⟨((372286257518111/2251799813685248), (3001077280285/9007199254740992)), (701343/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227726510906105/4503599627370496), (2991407239287/2251799813685248)), (1403843/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215780661686193/2251799813685248), (8926024201559/2251799813685248)), (1054337/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180123703353623/2251799813685248), (17660171774339/2251799813685248)), (528633/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180123703353623/2251799813685248), (17660171774339/2251799813685248)), (2016574860692882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2110590582419121/2251799813685248), (34196076273337/2251799813685248)), (8255237/2251799813685248), by norm_num⟩
  | 2 => ⟨((494429301385745/562949953421312), (64103315134459/2251799813685248)), (15725841/2251799813685248), by norm_num⟩
  | 3 => ⟨((867585139305739/1125899906842624), (112601687328751/2251799813685248)), (7129707/562949953421312), by norm_num⟩
  | 4 => ⟨((1331440182900035/2251799813685248), (173535054037145/2251799813685248)), (23401855/1125899906842624), by norm_num⟩
  | 5 => ⟨((1547756186025499/4503599627370496), (410429990592547/4503599627370496)), (31280945/1125899906842624), by norm_num⟩
  | 6 => ⟨((247257373931209/2251799813685248), (141052848705581/2251799813685248)), (108808813/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-261361469/4194304)), (1/8388608), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1083381513/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-5647197648195/281474976710656), (-130093595561203/1125899906842624)), (178069007/4503599627370496), by norm_num⟩
  | 1 => ⟨((214122909/4294967296), (616589433/2147483648)), (53/536870912), by norm_num⟩
  | 2 => ⟨((-33254715/536870912), (-766083591/2147483648)), (529/4294967296), by norm_num⟩
  | 3 => ⟨((220359633/4294967296), (1269097473/4294967296)), (55/536870912), by norm_num⟩
  | 4 => ⟨((-273786559/8589934592), (-1576794375/8589934592)), (549/8589934592), by norm_num⟩
  | 5 => ⟨((17008351/1073741824), (1567274731/17179869184)), (137/4294967296), by norm_num⟩
  | 6 => ⟨((-225408877/34359738368), (-1298177133/34359738368)), (57/4294967296), by norm_num⟩
  | 7 => ⟨((160034291/68719476736), (230417785/17179869184)), (163/34359738368), by norm_num⟩
  | 8 => ⟨((-198835137/274877906944), (-286283343/68719476736)), (407/274877906944), by norm_num⟩
  | 9 => ⟨((219594113/1099511627776), (158086085/137438953472)), (451/1099511627776), by norm_num⟩
  | 10 => ⟨((-218268349/4398046511104), (-314263331/1099511627776)), (225/2199023255552), by norm_num⟩
  | 11 => ⟨((6163369/549755813888), (1135876423/17592186044416)), (51/2199023255552), by norm_num⟩
  | 12 => ⟨((-163364231/70368744177664), (-940848959/70368744177664)), (85/17592186044416), by norm_num⟩
  | 13 => ⟨((975829/2199023255552), (1438721129/562949953421312)), (261/281474976710656), by norm_num⟩
  | 14 => ⟨((-11085001/140737488355328), (-1021453629/2251799813685248)), (373/2251799813685248), by norm_num⟩
  | 15 => ⟨((235052311/18014398509481984), (169214461/2251799813685248)), (31/1125899906842624), by norm_num⟩
  | 16 => ⟨((-292041525/144115188075855872), (-1681928557/144115188075855872)), (619/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-567520921283/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55583108017951/19807040628566084398385987584), (-1343110902921/316912650057057350374175801344)), (5779/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889618728290163/39614081257132168796771975168), (-1510714439625/19807040628566084398385987584)), (208079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889385920056157/2475880078570760549798248448), (-3209565794399/2475880078570760549798248448)), (221123/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771051960006411/154742504910672534362390528), (-200548488373/9671406556917033397649408)), (221167/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387355786488657/2417851639229258349412352), (-187961761659/604462909807314587353088)), (207391/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629337233402995/302231454903657293676544), (-2630625766135/604462909807314587353088)), (90757/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58987688317741/2361183241434822606848), (-4273194451989/75557863725914323419136)), (295049/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324349893697339/1180591620717411303424), (-1601760243607/2361183241434822606848)), (55341/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405313797427239/147573952589676412928), (-4402606686709/590295810358705651712)), (304501/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455808143690615/18446744073709551616), (-5499909069099/73786976294838206464)), (380815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911191681248233/4611686018427387904), (-6182795168065/9223372036854775808)), (107169/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796815163071069/576460752303423488), (-772130763165/144115188075855872)), (53625/144115188075855872), by norm_num⟩
  | 5 => ⟨((597133969518949/72057594037927936), (-2699226644617/72057594037927936)), (375741/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491164714749719/36028797018963968), (-126324530111/562949953421312)), (564343/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488660807886649/9007199254740992), (-10083401599177/9007199254740992)), (353355/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113368195984259/2251799813685248), (-20099247473307/4503599627370496)), (708635/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107120844469117/1125899906842624), (-14990212445667/1125899906842624)), (533889/562949953421312), by norm_num⟩
  | 0 => ⟨((1088416461390141/1125899906842624), (-14822429676191/562949953421312)), (4309857/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088416461390141/1125899906842624), (-14822429676191/562949953421312)), (16440799721724700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2102800734851609/2251799813685248), (-114631692279687/2251799813685248)), (1069963/281474976710656), by norm_num⟩
  | 2 => ⟨((1957825237760585/2251799813685248), (-214093282447267/2251799813685248)), (16858129/2251799813685248), by norm_num⟩
  | 3 => ⟨((1681874074687449/2251799813685248), (-93071601894371/562949953421312)), (16260097/1125899906842624), by norm_num⟩
  | 4 => ⟨((1194645819530577/2251799813685248), (-278061510378389/1125899906842624)), (14832957/562949953421312), by norm_num⟩
  | 5 => ⟨((992899824497897/4503599627370496), (-295039566951783/1125899906842624)), (2883147/70368744177664), by norm_num⟩
  | 6 => ⟨((-5647197648195/281474976710656), (-130093595561203/1125899906842624)), (178069007/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1083381513/16777216)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-279569729/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-765848040935165/9007199254740992), (310398720539711/4503599627370496)), (89796545/2251799813685248), by norm_num⟩
  | 1 => ⟨((936680527/4294967296), (-379637241/2147483648)), (441/4294967296), by norm_num⟩
  | 2 => ⟨((-600634529/2147483648), (486875149/2147483648)), (71/536870912), by norm_num⟩
  | 3 => ⟨((513532383/2147483648), (-832540067/4294967296)), (61/536870912), by norm_num⟩
  | 4 => ⟨((-329296139/2147483648), (266927889/2147483648)), (315/4294967296), by norm_num⟩
  | 5 => ⟨((10557849/134217728), (-273862607/4294967296)), (325/8589934592), by norm_num⟩
  | 6 => ⟨((-577714091/17179869184), (117073953/4294967296)), (279/17179869184), by norm_num⟩
  | 7 => ⟨((423373539/34359738368), (-343187155/34359738368)), (411/68719476736), by norm_num⟩
  | 8 => ⟨((-1085931687/274877906944), (880257673/274877906944)), (529/274877906944), by norm_num⟩
  | 9 => ⟨((618968841/549755813888), (-501736967/549755813888)), (303/549755813888), by norm_num⟩
  | 10 => ⟨((-635049493/2199023255552), (514771965/2199023255552)), (313/2199023255552), by norm_num⟩
  | 11 => ⟨((592316287/8796093022208), (-960264743/17592186044416)), (293/8796093022208), by norm_num⟩
  | 12 => ⟨((-1012840853/70368744177664), (821010145/70368744177664)), (63/8796093022208), by norm_num⟩
  | 13 => ⟨((799349383/281474976710656), (-647953675/281474976710656)), (25/17592186044416), by norm_num⟩
  | 14 => ⟨((-585797339/1125899906842624), (949696207/2251799813685248)), (589/2251799813685248), by norm_num⟩
  | 15 => ⟨((400677469/4503599627370496), (-162394845/2251799813685248)), (405/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1027717417/72057594037927936), (833069107/72057594037927936)), (261/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (3204972839773/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778549211975203/633825300114114700748351602688), (1896028540107/316912650057057350374175801344)), (92573/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944747255809397/19807040628566084398385987584), (1066306269629/9903520314283042199192993792)), (104169/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236156710800425/309485009821345068724781056), (4530777179619/2475880078570760549798248448)), (221415/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770919441497769/154742504910672534362390528), (4529624831951/154742504910672534362390528)), (221477/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774649303709105/4835703278458516698824704), (4245299156285/9671406556917033397649408)), (207701/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258565193404903/604462909807314587353088), (3713412914175/604462909807314587353088)), (181805/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887427890837249/75557863725914323419136), (1508000464535/18889465931478580854784)), (147779/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297265478531253/4722366482869645213696), (2260997309527/2361183241434822606848)), (110889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621070004374373/590295810358705651712), (6214482693273/590295810358705651712)), (305121/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28484373287241/1152921504606846976), (485200964465/4611686018427387904)), (381667/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822119941698225/9223372036854775808), (8726899581389/9223372036854775808)), (214871/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593364846033205/1152921504606846976), (8718507057011/1152921504606846976)), (53775/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194033333094959/144115188075855872), (476203659319/9007199254740992)), (376941/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490808198811819/36028797018963968), (44570444297/140737488355328)), (141611/9007199254740992), by norm_num⟩
  | 3 => ⟨((744103566814105/4503599627370496), (14229583927255/9007199254740992)), (709865/9007199254740992), by norm_num⟩
  | 2 => ⟨((17389102242045/35184372088832), (14180219404003/2251799813685248)), (89073/281474976710656), by norm_num⟩
  | 1 => ⟨((553196324849929/562949953421312), (10573586497977/562949953421312)), (268923/281474976710656), by norm_num⟩
  | 0 => ⟨((8490957656375/8796093022208), (41803254545691/1125899906842624)), (2178745/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((8490957656375/8796093022208), (41803254545691/1125899906842624)), (8311252598289107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523794022220347/562949953421312), (80706209756983/1125899906842624)), (4368119/1125899906842624), by norm_num⟩
  | 2 => ⟨((968938012990019/1125899906842624), (300370787632923/2251799813685248)), (17509635/2251799813685248), by norm_num⟩
  | 3 => ⟨((1627649518278745/2251799813685248), (258496046016613/1125899906842624)), (34808499/2251799813685248), by norm_num⟩
  | 4 => ⟨((1057803680705467/2251799813685248), (747386090395531/2251799813685248)), (4144005/140737488355328), by norm_num⟩
  | 5 => ⟨((497702020749561/4503599627370496), (702182984938259/2251799813685248)), (212614725/4503599627370496), by norm_num⟩
  | 6 => ⟨((-765848040935165/9007199254740992), (310398720539711/4503599627370496)), (89796545/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-279569729/4194304)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1150588865/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((99472243665871/1125899906842624), (471188046596627/9007199254740992)), (179375809/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1001407447/4294967296), (-592943319/4294967296)), (57/1073741824), by norm_num⟩
  | 2 => ⟨((1321385831/4294967296), (391202853/2147483648)), (303/4294967296), by norm_num⟩
  | 3 => ⟨((-1162404321/4294967296), (-688271171/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((766912911/4294967296), (227048385/2147483648)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-809570855/8589934592), (-119838741/2147483648)), (3/134217728), by norm_num⟩
  | 6 => ⟨((356083983/8589934592), (26355109/1073741824)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((-1073972623/68719476736), (-158977471/17179869184)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((354284415/68719476736), (104887665/34359738368)), (173/137438953472), by norm_num⟩
  | 9 => ⟨((-415545281/274877906944), (-492096997/549755813888)), (205/549755813888), by norm_num⟩
  | 10 => ⟨((877318255/2199023255552), (519468875/2199023255552)), (219/2199023255552), by norm_num⟩
  | 11 => ⟨((-841924789/8796093022208), (-124628013/2199023255552)), (53/2199023255552), by norm_num⟩
  | 12 => ⟨((370314631/17592186044416), (438533961/35184372088832)), (189/35184372088832), by norm_num⟩
  | 13 => ⟨((-601404025/140737488355328), (-11128041/4398046511104)), (309/281474976710656), by norm_num⟩
  | 14 => ⟨((906936971/1125899906842624), (134251603/281474976710656)), (235/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1276511285/9007199254740992), (-188958761/2251799813685248)), (333/9007199254740992), by norm_num⟩
  | 16 => ⟨((105274577/4503599627370496), (498673003/36028797018963968)), (111/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (696373320219/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778458042317079/633825300114114700748351602688), (823847466473/633825300114114700748351602688)), (92281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472348094613099/9903520314283042199192993792), (926645041645/39614081257132168796771975168)), (51911/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889145735637157/2475880078570760549798248448), (123041478025/309485009821345068724781056)), (220633/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812126635563/154742504910672534362390528), (984074831419/154742504910672534362390528)), (220647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96824917183457/604462909807314587353088), (922297192891/9671406556917033397649408)), (206871/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258478427179205/604462909807314587353088), (806737187167/604462909807314587353088)), (181027/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471822039926877/18889465931478580854784), (327609136481/18889465931478580854784)), (294195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297161785103677/4722366482869645213696), (30699380373/147573952589676412928)), (220671/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620929219403163/590295810358705651712), (675023196499/295147905179352825856)), (75865/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822826595904689/73786976294838206464), (421617301585/18446744073709551616)), (379383/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821928673984523/9223372036854775808), (473945490897/2305843009213693952)), (213443/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593178180517785/1152921504606846976), (946956936827/576460752303423488)), (426987/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596937583270519/72057594037927936), (1655075479109/144115188075855872)), (373727/144115188075855872), by norm_num⟩
  | 4 => ⟨((372645312828963/9007199254740992), (2478420992501/36028797018963968)), (35051/2251799813685248), by norm_num⟩
  | 3 => ⟨((743970706371231/4503599627370496), (3090703536663/9007199254740992)), (701419/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225327273849159/4503599627370496), (3079746812361/2251799813685248)), (1404035/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106100868809471/1125899906842624), (9184647669963/2251799813685248)), (2109067/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173045207388513/2251799813685248), (2269008208689/281474976710656)), (4230283/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173045207388513/2251799813685248), (2269008208689/281474976710656)), (16137249001509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524224660998897/562949953421312), (17517214038125/1125899906842624)), (2058217/562949953421312), by norm_num⟩
  | 2 => ⟨((1952108036125069/2251799813685248), (16312205969593/562949953421312)), (1948655/281474976710656), by norm_num⟩
  | 3 => ⟨((1690411533277897/2251799813685248), (28282432715949/562949953421312)), (27932377/2251799813685248), by norm_num⟩
  | 4 => ⟨((315824346212425/562949953421312), (169851512240613/2251799813685248)), (22371969/1125899906842624), by norm_num⟩
  | 5 => ⟨((1391838419058249/4503599627370496), (190579082494165/2251799813685248)), (113908397/4503599627370496), by norm_num⟩
  | 6 => ⟨((99472243665871/1125899906842624), (471188046596627/9007199254740992)), (179375809/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1150588865/16777216)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-295167177/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((535788809603905/18014398509481984), (-829185039223277/9007199254740992)), (252095103/9007199254740992), by norm_num⟩
  | 1 => ⟨((-345931767/4294967296), (267681445/1073741824)), (41/536870912), by norm_num⟩
  | 2 => ⟨((58550037/536870912), (-724894791/2147483648)), (447/4294967296), by norm_num⟩
  | 3 => ⟨((-105704293/1073741824), (654350495/2147483648)), (203/2147483648), by norm_num⟩
  | 4 => ⟨((71563133/1073741824), (-886006995/4294967296)), (277/4294967296), by norm_num⟩
  | 5 => ⟨((-310074491/8589934592), (119967571/1073741824)), (151/4294967296), by norm_num⟩
  | 6 => ⟨((34987387/2147483648), (-866341879/17179869184)), (137/8589934592), by norm_num⟩
  | 7 => ⟨((-433131887/68719476736), (335156757/17179869184)), (213/34359738368), by norm_num⟩
  | 8 => ⟨((293235723/137438953472), (-907621323/137438953472)), (145/68719476736), by norm_num⟩
  | 9 => ⟨((-176466013/274877906944), (136549117/68719476736)), (351/549755813888), by norm_num⟩
  | 10 => ⟨((191151529/1099511627776), (-295825491/549755813888)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((-376471227/8796093022208), (1165251317/8796093022208)), (189/4398046511104), by norm_num⟩
  | 12 => ⟨((339834327/35184372088832), (-1051853021/35184372088832)), (343/35184372088832), by norm_num⟩
  | 13 => ⟨((-283165667/140737488355328), (876452549/140737488355328)), (287/140737488355328), by norm_num⟩
  | 14 => ⟨((219093383/562949953421312), (-678136429/562949953421312)), (223/562949953421312), by norm_num⟩
  | 15 => ⟨((-4944299/70368744177664), (244856999/1125899906842624)), (81/1125899906842624), by norm_num⟩
  | 16 => ⟨((428461117/36028797018963968), (-1326170091/36028797018963968)), (441/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1639076967803/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889182346688291/316912650057057350374175801344), (-1938926592447/633825300114114700748351602688)), (92391/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944643644866067/19807040628566084398385987584), (-2180848192917/39614081257132168796771975168)), (6497/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((944516991753183/1237940039285380274899124224), (-289574885237/309485009821345068724781056)), (110463/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110668766708813/9671406556917033397649408), (-1157989087917/77371252455336267181195264)), (110479/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549093693078403/9671406556917033397649408), (-1085285020081/4835703278458516698824704)), (207183/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629193227195559/302231454903657293676544), (-1898589525107/604462909807314587353088)), (181319/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29486538922361/1180591620717411303424), (-385496546849/9444732965739290427392)), (294707/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297049347535315/4722366482869645213696), (-1155949318435/2361183241434822606848)), (110543/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620774315814691/590295810358705651712), (-3177105532457/590295810358705651712)), (76021/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822632514250577/73786976294838206464), (-3968750943647/73786976294838206464)), (190121/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910854855787931/4611686018427387904), (-2230614966945/4611686018427387904)), (427959/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398239611049461/288230376151711744), (-4456715396783/1152921504606846976)), (214097/576460752303423488), by norm_num⟩
  | 5 => ⟨((596841014522707/72057594037927936), (-1947276347815/72057594037927936)), (187467/72057594037927936), by norm_num⟩
  | 4 => ⟨((372572453678859/9007199254740992), (-2915848210003/18014398509481984)), (281465/18014398509481984), by norm_num⟩
  | 3 => ⟨((743787051250921/4503599627370496), (-3635959867875/4503599627370496)), (352295/4503599627370496), by norm_num⟩
  | 2 => ⟨((278072958034101/562949953421312), (-14490862110995/4503599627370496)), (11031/35184372088832), by norm_num⟩
  | 1 => ⟨((276383005012109/281474976710656), (-10802143196389/1125899906842624)), (2124947/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170681811349973/2251799813685248), (-42683158284173/2251799813685248)), (2138999/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170681811349973/2251799813685248), (-42683158284173/2251799813685248)), (8159633640769576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2091676909065971/2251799813685248), (-41145556001621/1125899906842624)), (8409959/2251799813685248), by norm_num⟩
  | 2 => ⟨((1939932865371327/2251799813685248), (-38219742659283/562949953421312)), (16238551/2251799813685248), by norm_num⟩
  | 3 => ⟨((103804951925433/140737488355328), (-16463216321489/140737488355328)), (15092031/1125899906842624), by norm_num⟩
  | 4 => ⟨((597107745795331/1125899906842624), (-388573284633405/2251799813685248)), (12896997/562949953421312), by norm_num⟩
  | 5 => ⟨((141571359393781/562949953421312), (-206075261800489/1125899906842624)), (72522335/2251799813685248), by norm_num⟩
  | 6 => ⟨((535788809603905/18014398509481984), (-829185039223277/9007199254740992)), (252095103/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-295167177/4194304)), (1/8388608), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile036Terms1
