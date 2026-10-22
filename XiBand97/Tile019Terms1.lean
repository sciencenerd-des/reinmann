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
namespace Reinmann.XiBand97.Tile019Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5507/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5507/256))
  have he : value ((69/80), (5507/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-396496593/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1340141372061153/9007199254740992), (191845769867405/9007199254740992)), (226972367/9007199254740992), by norm_num⟩
  | 1 => ⟨((87755667/268435456), (-25125041/536870912)), (15/268435456), by norm_num⟩
  | 2 => ⟨((-1542551267/4294967296), (110410715/2147483648)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((564888593/2147483648), (-5054107/134217728)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((-310296775/2147483648), (88840065/4294967296)), (219/8589934592), by norm_num⟩
  | 5 => ⟨((1090866721/17179869184), (-156161259/17179869184)), (195/17179869184), by norm_num⟩
  | 6 => ⟨((-1597919447/68719476736), (228747571/68719476736)), (9/2147483648), by norm_num⟩
  | 7 => ⟨((1003139395/137438953472), (-35900699/34359738368)), (183/137438953472), by norm_num⟩
  | 8 => ⟨((-1102061267/549755813888), (39440949/137438953472)), (203/549755813888), by norm_num⟩
  | 9 => ⟨((1076211601/2199023255552), (-154063329/2199023255552)), (25/274877906944), by norm_num⟩
  | 10 => ⟨((-118233929/1099511627776), (135404693/8796093022208)), (89/4398046511104), by norm_num⟩
  | 11 => ⟨((377871265/17592186044416), (-54093549/17592186044416)), (287/70368744177664), by norm_num⟩
  | 12 => ⟨((-1107024041/281474976710656), (79237117/140737488355328)), (53/70368744177664), by norm_num⟩
  | 13 => ⟨((187106187/281474976710656), (-107139533/1125899906842624)), (289/2251799813685248), by norm_num⟩
  | 14 => ⟨((-469844929/4503599627370496), (33629945/2251799813685248)), (183/9007199254740992), by norm_num⟩
  | 15 => ⟨((1101178481/72057594037927936), (-78818711/36028797018963968)), (27/9007199254740992), by norm_num⟩
  | 16 => ⟨((-302442053/144115188075855872), (173182409/576460752303423488)), (239/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (3907060284165/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889517207418063/316912650057057350374175801344), (4625172575425/633825300114114700748351602688)), (92655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472510011481127/9903520314283042199192993792), (5202421927235/39614081257132168796771975168)), (52133/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236229114765945/309485009821345068724781056), (5526500959477/2475880078570760549798248448)), (110817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55359319533199/4835703278458516698824704), (5525294490343/154742504910672534362390528)), (13857/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387460185253529/2417851639229258349412352), (2589340888353/4835703278458516698824704)), (3249/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259039084500345/604462909807314587353088), (4530064819885/604462909807314587353088)), (22753/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888197072154811/75557863725914323419136), (1839738058969/18889465931478580854784)), (73985/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324460396171333/1180591620717411303424), (1379277906071/1180591620717411303424)), (27761/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621860883882935/590295810358705651712), (3791306065263/295147905179352825856)), (152793/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823986591449439/73786976294838206464), (2368285288201/18446744073709551616)), (95577/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823227372418923/9223372036854775808), (5325119565259/4611686018427387904)), (215271/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594469020098217/1152921504606846976), (5320717288645/576460752303423488)), (107775/576460752303423488), by norm_num⟩
  | 5 => ⟨((298748956556863/36028797018963968), (4650675952679/72057594037927936)), (188921/144115188075855872), by norm_num⟩
  | 4 => ⟨((373061157893703/9007199254740992), (13932225628799/36028797018963968)), (142005/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489989913137073/9007199254740992), (17380638299421/9007199254740992)), (356115/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114666232250677/2251799813685248), (17328693289091/2251799813685248)), (89443/562949953421312), by norm_num⟩
  | 1 => ⟨((1108990636076261/1125899906842624), (25863250679123/1125899906842624)), (67601/140737488355328), by norm_num⟩
  | 0 => ⟨((1091849447510501/1125899906842624), (51207793454803/1125899906842624)), (1098275/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1091849447510501/1125899906842624), (51207793454803/1125899906842624)), (4189586643699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528249878470211/562949953421312), (49659122140485/562949953421312)), (278753/140737488355328), by norm_num⟩
  | 2 => ⟨((491308159830391/562949953421312), (5824768497675/35184372088832)), (1144641/281474976710656), by norm_num⟩
  | 3 => ⟨((826709930147513/1125899906842624), (10167000724091/35184372088832)), (9507741/1125899906842624), by norm_num⟩
  | 4 => ⟨((128253091522861/281474976710656), (477778056530439/1125899906842624)), (9728601/562949953421312), by norm_num⟩
  | 5 => ⟨((3875768202015/140737488355328), (1741583242045779/4503599627370496)), (136978497/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1340141372061153/9007199254740992), (191845769867405/9007199254740992)), (226972367/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-396496593/8388608)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-831018507/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((229694005884845/2251799813685248), (103384015813815/1125899906842624)), (136019243/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1008777607/4294967296), (-908090567/4294967296)), (19/536870912), by norm_num⟩
  | 2 => ⟨((290349535/1073741824), (522738951/2147483648)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-891406015/4294967296), (-100304243/536870912)), (139/4294967296), by norm_num⟩
  | 4 => ⟨((1026269101/8589934592), (923836219/8589934592)), (81/4294967296), by norm_num⟩
  | 5 => ⟨((-945228773/17179869184), (-850884603/17179869184)), (19/2147483648), by norm_num⟩
  | 6 => ⟨((362744947/17179869184), (163269517/8589934592)), (119/34359738368), by norm_num⟩
  | 7 => ⟨((-477286347/68719476736), (-214823975/34359738368)), (159/137438953472), by norm_num⟩
  | 8 => ⟨((274748107/137438953472), (989300965/549755813888)), (185/549755813888), by norm_num⟩
  | 9 => ⟨((-281169287/549755813888), (-1012422069/2199023255552)), (3/34359738368), by norm_num⟩
  | 10 => ⟨((517932967/4398046511104), (466237593/4398046511104)), (45/2199023255552), by norm_num⟩
  | 11 => ⟨((-216833587/8796093022208), (-24398903/1099511627776)), (153/35184372088832), by norm_num⟩
  | 12 => ⟨((332851857/70368744177664), (149814801/35184372088832)), (15/17592186044416), by norm_num⟩
  | 13 => ⟨((-471642907/562949953421312), (-849135575/1125899906842624)), (173/1125899906842624), by norm_num⟩
  | 14 => ⟨((155142561/1125899906842624), (139657637/1125899906842624)), (29/1125899906842624), by norm_num⟩
  | 15 => ⟨((-762088423/36028797018963968), (-686023665/36028797018963968)), (9/2251799813685248), by norm_num⟩
  | 16 => ⟨((877386721/288230376151711744), (197453483/72057594037927936)), (21/36028797018963968), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (954709539461/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905056637245/633825300114114700748351602688), (1130014387263/633825300114114700748351602688)), (11539/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889895157706951/39614081257132168796771975168), (158880627537/4951760157141521099596496896)), (51929/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472419949718293/618970019642690137449562112), (1350211749311/2475880078570760549798248448)), (110357/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885673016375969/77371252455336267181195264), (674952034709/77371252455336267181195264)), (110367/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774849522519685/4835703278458516698824704), (316302062499/2417851639229258349412352)), (103479/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629458042103623/302231454903657293676544), (276682627583/151115727451828646838272)), (45277/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235999879968259/9444732965739290427392), (1797824727595/75557863725914323419136)), (4599/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648847335860957/2361183241434822606848), (168479120557/590295810358705651712)), (13799/590295810358705651712), by norm_num⟩
  | 9 => ⟨((6334615212803/2305843009213693952), (463100107771/147573952589676412928)), (151815/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911870637087805/36893488147419103232), (2314196438721/73786976294838206464)), (189809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911478386317533/4611686018427387904), (2601679061583/9223372036854775808)), (106795/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398551284324527/288230376151711744), (2599440953867/1152921504606846976)), (106829/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194772470678979/144115188075855872), (2271995446319/144115188075855872)), (46757/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491924645326215/36028797018963968), (212685537105/2251799813685248)), (35087/4503599627370496), by norm_num⟩
  | 3 => ⟨((744808090078983/4503599627370496), (2122465834461/4503599627370496)), (87785/2251799813685248), by norm_num⟩
  | 2 => ⟨((557165854577173/1125899906842624), (4231790884651/2251799813685248)), (703093/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217172600309909/2251799813685248), (3157465780155/562949953421312)), (1056679/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182854246022545/2251799813685248), (1562428207387/140737488355328)), (2121557/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182854246022545/2251799813685248), (1562428207387/140737488355328)), (8093097695357512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2115742122304553/2251799813685248), (12116718460931/562949953421312)), (4160305/2251799813685248), by norm_num⟩
  | 2 => ⟨((993431046366309/1125899906842624), (22769210190085/562949953421312)), (7996955/2251799813685248), by norm_num⟩
  | 3 => ⟨((1749412163849475/2251799813685248), (160722211035637/2251799813685248)), (14759025/2251799813685248), by norm_num⟩
  | 4 => ⟨((168454766241961/281474976710656), (249728585354459/2251799813685248)), (25039279/2251799813685248), by norm_num⟩
  | 5 => ⟨((1557655482743153/4503599627370496), (298910908255017/2251799813685248)), (17762197/1125899906842624), by norm_num⟩
  | 6 => ⟨((229694005884845/2251799813685248), (103384015813815/1125899906842624)), (136019243/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-831018507/16777216)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1730833189/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((17843000295735/562949953421312), (-551137560100781/4503599627370496)), (41980007/2251799813685248), by norm_num⟩
  | 1 => ⟨((-163214287/2147483648), (1260347509/4294967296)), (97/2147483648), by norm_num⟩
  | 2 => ⟨((391370767/4294967296), (-1511090667/4294967296)), (235/4294967296), by norm_num⟩
  | 3 => ⟨((-312822037/4294967296), (1207812389/4294967296)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((187528621/4294967296), (-1448103809/8589934592)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((-359739195/17179869184), (1388960511/17179869184)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((71884743/8589934592), (-277548487/8589934592)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((-196996669/68719476736), (380304117/34359738368)), (249/137438953472), by norm_num⟩
  | 8 => ⟨((236188691/274877906944), (-227982361/68719476736)), (151/274877906944), by norm_num⟩
  | 9 => ⟨((-251713665/1099511627776), (485935845/549755813888)), (163/1099511627776), by norm_num⟩
  | 10 => ⟨((241433203/4398046511104), (-233044653/1099511627776)), (79/2199023255552), by norm_num⟩
  | 11 => ⟨((-421041117/35184372088832), (406412125/8796093022208)), (139/17592186044416), by norm_num⟩
  | 12 => ⟨((336537501/140737488355328), (-324844571/35184372088832)), (225/140737488355328), by norm_num⟩
  | 13 => ⟨((-31037757/70368744177664), (479349699/281474976710656)), (21/70368744177664), by norm_num⟩
  | 14 => ⟨((340229901/4503599627370496), (-1313634717/4503599627370496)), (29/562949953421312), by norm_num⟩
  | 15 => ⟨((-217556179/18014398509481984), (1679977855/36028797018963968)), (299/36028797018963968), by norm_num⟩
  | 16 => ⟨((260838467/144115188075855872), (-1007102739/144115188075855872)), (181/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1716016612909/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778776797317491/633825300114114700748351602688), (-63463687829/19807040628566084398385987584)), (5775/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472437701335267/9903520314283042199192993792), (-1142138844755/19807040628566084398385987584)), (103963/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889526343802533/2475880078570760549798248448), (-303316602263/309485009821345068724781056)), (27619/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885596243503927/77371252455336267181195264), (-2425956736141/154742504910672534362390528)), (27623/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((24211796869351/151115727451828646838272), (-1136861260355/4835703278458516698824704)), (103605/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258789948299715/604462909807314587353088), (-1988895474801/604462909807314587353088)), (5667/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887793888734151/75557863725914323419136), (-3230808551927/75557863725914323419136)), (147375/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648770325499757/2361183241434822606848), (-2422103544181/4722366482869645213696)), (110561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621449460440481/590295810358705651712), (-1664381730301/295147905179352825856)), (152067/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823475848898131/73786976294838206464), (-4158512269983/73786976294838206464)), (47539/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822657643891533/9223372036854775808), (-1168742652489/2305843009213693952)), (214023/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593905353343275/1152921504606846976), (-4670779190275/1152921504606846976)), (107073/576460752303423488), by norm_num⟩
  | 5 => ⟨((298627356139443/36028797018963968), (-4082220837995/144115188075855872)), (46879/36028797018963968), by norm_num⟩
  | 4 => ⟨((745764305347267/18014398509481984), (-1528480081305/9007199254740992)), (140775/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489118583269129/9007199254740992), (-7625955945711/9007199254740992)), (176211/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227660607370549/4503599627370496), (-15202677065911/4503599627370496)), (706299/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215649493215777/2251799813685248), (-2835159116849/281474976710656)), (1063097/2251799813685248), by norm_num⟩
  | 0 => ⟨((136233336140869/140737488355328), (-44873637218721/2251799813685248)), (1070423/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((136233336140869/140737488355328), (-44873637218721/2251799813685248)), (4083339695457076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2109079114445995/2251799813685248), (-43437504637335/1125899906842624)), (4229987/2251799813685248), by norm_num⟩
  | 2 => ⟨((1972052496304423/2251799813685248), (-162737616829841/2251799813685248)), (8250163/2251799813685248), by norm_num⟩
  | 3 => ⟨((1715297910930969/2251799813685248), (-285040545399725/2251799813685248)), (15642925/2251799813685248), by norm_num⟩
  | 4 => ⟨((317634675308917/562949953421312), (-54282073508857/281474976710656)), (3474015/281474976710656), by norm_num⟩
  | 5 => ⟨((1266266919812399/4503599627370496), (-122510846225627/562949953421312)), (84163567/4503599627370496), by norm_num⟩
  | 6 => ⟨((17843000295735/562949953421312), (-551137560100781/4503599627370496)), (41980007/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1730833189/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-224204897/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-527563868300583/4503599627370496), (25098165819365/4503599627370496)), (345699609/18014398509481984), by norm_num⟩
  | 1 => ⟨((625108225/2147483648), (-3717339/268435456)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-1553335585/4294967296), (73897923/4294967296)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((321657827/1073741824), (-61209813/4294967296)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((-799289673/4294967296), (2376573/268435456)), (17/536870912), by norm_num⟩
  | 5 => ⟨((794464089/8589934592), (-37795597/8589934592)), (273/17179869184), by norm_num⟩
  | 6 => ⟨((-329028183/8589934592), (31306177/17179869184)), (229/34359738368), by norm_num⟩
  | 7 => ⟨((934404937/68719476736), (-88906203/137438953472)), (41/17179869184), by norm_num⟩
  | 8 => ⟨((-1160954521/274877906944), (6903863/34359738368)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((320540401/274877906944), (-30498587/549755813888)), (115/549755813888), by norm_num⟩
  | 10 => ⟨((-637210379/2199023255552), (60628913/4398046511104)), (115/2199023255552), by norm_num⟩
  | 11 => ⟨((575784839/8796093022208), (-3424027/1099511627776)), (105/8796093022208), by norm_num⟩
  | 12 => ⟨((-1907695433/140737488355328), (90756133/140737488355328)), (175/70368744177664), by norm_num⟩
  | 13 => ⟨((729299241/281474976710656), (-69390929/562949953421312)), (135/281474976710656), by norm_num⟩
  | 14 => ⟨((-1035566019/2251799813685248), (49265709/2251799813685248)), (193/2251799813685248), by norm_num⟩
  | 15 => ⟨((686209303/9007199254740992), (-32645517/9007199254740992)), (129/9007199254740992), by norm_num⟩
  | 16 => ⟨((-426291515/36028797018963968), (40560531/72057594037927936)), (323/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (2015175911271/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778651142106101/633825300114114700748351602688), (2384585868317/316912650057057350374175801344)), (46335/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944804453532783/19807040628566084398385987584), (5364279933725/39614081257132168796771975168)), (26071/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((59042964822589/77371252455336267181195264), (2849148731369/1237940039285380274899124224)), (27709/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771040227774373/154742504910672534362390528), (712111403157/19342813113834066795298816)), (27719/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774705709031993/4835703278458516698824704), (2669670775427/4835703278458516698824704)), (25997/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258663476520137/604462909807314587353088), (4670430057365/604462909807314587353088)), (91031/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887586802388227/75557863725914323419136), (1896662084373/18889465931478580854784)), (37001/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297383964110339/4722366482869645213696), (5687536179805/4722366482869645213696)), (3471/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810615894404155/295147905179352825856), (122130962057/9223372036854775808)), (152835/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455800105770173/18446744073709551616), (9764507167503/73786976294838206464)), (191211/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911171604855897/4611686018427387904), (10976864073885/9223372036854775808)), (107671/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796792602427609/576460752303423488), (2741652235641/288230376151711744)), (107815/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194222880953323/144115188075855872), (9584249914191/144115188075855872)), (189001/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491086005190161/36028797018963968), (14353319372019/36028797018963968)), (284151/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488543027431847/9007199254740992), (17901325428935/9007199254740992)), (178163/4503599627370496), by norm_num⟩
  | 2 => ⟨((556610733277555/1125899906842624), (17840886707843/2251799813685248)), (358037/2251799813685248), by norm_num⟩
  | 1 => ⟨((276707217847669/281474976710656), (26610398879585/1125899906842624)), (541343/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087547952552229/1125899906842624), (26309038420823/562949953421312)), (549949/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087547952552229/1125899906842624), (26309038420823/562949953421312)), (2097888948680686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1048043329534593/1125899906842624), (25412863696225/281474976710656)), (1113835/562949953421312), by norm_num⟩
  | 2 => ⟨((966393012122485/1125899906842624), (94622202628615/562949953421312)), (4549501/1125899906842624), by norm_num⟩
  | 3 => ⟨((398837411522915/562949953421312), (1269015939719/4398046511104)), (18678655/2251799813685248), by norm_num⟩
  | 4 => ⟨((942794026935477/2251799813685248), (920646985066643/2251799813685248)), (18622963/1125899906842624), by norm_num⟩
  | 5 => ⟨((4581857794607/562949953421312), (770921529668721/2251799813685248)), (123289089/4503599627370496), by norm_num⟩
  | 6 => ⟨((-527563868300583/4503599627370496), (25098165819365/4503599627370496)), (345699609/18014398509481984), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-224204897/4194304)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-462853771/8388608)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((194504380965553/9007199254740992), (241619630105905/2251799813685248)), (111577539/4503599627370496), by norm_num⟩
  | 1 => ⟨((-237891143/4294967296), (-295516069/1073741824)), (275/4294967296), by norm_num⟩
  | 2 => ⟨((305089367/4294967296), (1515967503/4294967296)), (355/4294967296), by norm_num⟩
  | 3 => ⟨((-260846259/4294967296), (-40503957/134217728)), (153/2147483648), by norm_num⟩
  | 4 => ⟨((167264361/4294967296), (207781197/1073741824)), (395/8589934592), by norm_num⟩
  | 5 => ⟨((-85804923/4294967296), (-1705434393/17179869184)), (51/2147483648), by norm_num⟩
  | 6 => ⟨((293447043/34359738368), (1458117617/34359738368)), (351/34359738368), by norm_num⟩
  | 7 => ⟨((-53762629/17179869184), (-1068570813/68719476736)), (259/68719476736), by norm_num⟩
  | 8 => ⟨((275796841/274877906944), (685207505/137438953472)), (335/274877906944), by norm_num⟩
  | 9 => ⟨((-314402191/1099511627776), (-1562242267/1099511627776)), (3/8589934592), by norm_num⟩
  | 10 => ⟨((322570279/4398046511104), (200353615/549755813888)), (99/1099511627776), by norm_num⟩
  | 11 => ⟨((-75216039/4398046511104), (-1494972731/17592186044416)), (93/4398046511104), by norm_num⟩
  | 12 => ⟨((257233775/70368744177664), (1278176449/70368744177664)), (5/1099511627776), by norm_num⟩
  | 13 => ⟨((-101506401/140737488355328), (-1008756265/281474976710656)), (127/140737488355328), by norm_num⟩
  | 14 => ⟨((297552889/2251799813685248), (1478519277/2251799813685248)), (375/2251799813685248), by norm_num⟩
  | 15 => ⟨((-101761079/4503599627370496), (-1011287219/9007199254740992)), (129/4503599627370496), by norm_num⟩
  | 16 => ⟨((130506007/36028797018963968), (324237563/18014398509481984)), (333/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (446860457077/2535301200456458802993406410752)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778554517499459/633825300114114700748351602688), (528715981333/158456325028528675187087900672)), (34653/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944750388771193/19807040628566084398385987584), (1189380515797/19807040628566084398385987584)), (155959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472315183381677/618970019642690137449562112), (1263431534685/1237940039285380274899124224)), (165729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770926926527615/154742504910672534362390528), (2526221438927/154742504910672534362390528)), (41439/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774653044796497/4835703278458516698824704), (2367651067985/9671406556917033397649408)), (4857/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258572204911265/604462909807314587353088), (517753344991/151115727451828646838272)), (17003/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471860038727661/18889465931478580854784), (3364119777595/75557863725914323419136)), (110545/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648637718704733/2361183241434822606848), (1260986484957/2361183241434822606848)), (20733/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810542466377001/295147905179352825856), (866474708057/147573952589676412928)), (228137/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823020400765659/73786976294838206464), (2164827057475/36893488147419103232)), (142641/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822145555482115/9223372036854775808), (4867124230355/9223372036854775808)), (321095/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593393628299015/1152921504606846976), (4862457258051/1152921504606846976)), (40161/144115188075855872), by norm_num⟩
  | 5 => ⟨((298515518461939/36028797018963968), (2124702515765/72057594037927936)), (281343/144115188075855872), by norm_num⟩
  | 4 => ⟨((745429200915135/18014398509481984), (6363630583479/36028797018963968)), (211223/18014398509481984), by norm_num⟩
  | 3 => ⟨((744141125910617/4503599627370496), (3968116576765/4503599627370496)), (528815/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225992231476965/4503599627370496), (494302167561/140737488355328)), (529953/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106578820080325/1125899906842624), (23589924944049/2251799813685248)), (1595569/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087396237133697/1125899906842624), (23318003643641/1125899906842624)), (3214065/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087396237133697/1125899906842624), (23318003643641/1125899906842624)), (12260684975630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524863196122371/562949953421312), (90082286233315/2251799813685248)), (6341431/2251799813685248), by norm_num⟩
  | 2 => ⟨((1953809192659695/2251799813685248), (83987708639249/1125899906842624)), (1541521/281474976710656), by norm_num⟩
  | 3 => ⟨((841361340711365/1125899906842624), (291492975907539/2251799813685248)), (23240259/2251799813685248), by norm_num⟩
  | 4 => ⟨((1219729858257721/2251799813685248), (435653150918669/2251799813685248)), (40750767/2251799813685248), by norm_num⟩
  | 5 => ⟨((9006318324595/35184372088832), (471959499055037/2251799813685248)), (29957427/1125899906842624), by norm_num⟩
  | 6 => ⟨((194504380965553/9007199254740992), (241619630105905/2251799813685248)), (111577539/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-462853771/8388608)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-952453609/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1804239681488419/18014398509481984), (-407237094706479/18014398509481984)), (140471405/18014398509481984), by norm_num⟩
  | 1 => ⟨((-567614073/2147483648), (128116851/2147483648)), (91/4294967296), by norm_num⟩
  | 2 => ⟨((1497966079/4294967296), (-338107715/4294967296)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((-1317739453/4294967296), (74357137/1073741824)), (55/2147483648), by norm_num⟩
  | 4 => ⟨((1738794981/8589934592), (-392465495/8589934592)), (37/2147483648), by norm_num⟩
  | 5 => ⟨((-114719491/1073741824), (51786947/2147483648)), (5/536870912), by norm_num⟩
  | 6 => ⟨((201834209/4294967296), (-364449925/34359738368)), (143/34359738368), by norm_num⟩
  | 7 => ⟨((-1217490397/68719476736), (274801213/68719476736)), (55/34359738368), by norm_num⟩
  | 8 => ⟨((803256739/137438953472), (-181304039/137438953472)), (37/68719476736), by norm_num⟩
  | 9 => ⟨((-942151371/549755813888), (6645441/17179869184)), (89/549755813888), by norm_num⟩
  | 10 => ⟨((62159787/137438953472), (-224482557/2199023255552)), (3/68719476736), by norm_num⟩
  | 11 => ⟨((-954433405/8796093022208), (841509/34359738368)), (47/4398046511104), by norm_num⟩
  | 12 => ⟨((839601491/35184372088832), (-379014911/70368744177664)), (21/8796093022208), by norm_num⟩
  | 13 => ⟨((-681771221/140737488355328), (307766793/281474976710656)), (139/281474976710656), by norm_num⟩
  | 14 => ⟨((128516667/140737488355328), (-232061203/1125899906842624)), (107/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1447094835/9007199254740992), (326625503/9007199254740992)), (153/9007199254740992), by norm_num⟩
  | 16 => ⟨((954741557/36028797018963968), (-215495857/36028797018963968)), (103/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-289168407943/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889229171591539/316912650057057350374175801344), (-5345342733/9903520314283042199192993792)), (46117/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236174091715555/4951760157141521099596496896), (-384788602695/39614081257132168796771975168)), (51883/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889146135201635/2475880078570760549798248448), (-204371499999/1237940039285380274899124224)), (55127/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770812551024983/154742504910672534362390528), (-102159073387/38685626227668133590597632)), (6891/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387299774789629/2417851639229258349412352), (-95745797229/2417851639229258349412352)), (103369/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629239412355967/302231454903657293676544), (-167498499131/302231454903657293676544)), (90451/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943644427518459/37778931862957161709568), (-544157793581/75557863725914323419136)), (146987/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324290587432051/1180591620717411303424), (-407932651597/4722366482869645213696)), (55123/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810465032880879/295147905179352825856), (-280302909941/295147905179352825856)), (37899/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822827758708915/73786976294838206464), (-175076304645/18446744073709551616)), (189507/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821930126082811/9223372036854775808), (-787222293353/9223372036854775808)), (53303/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199147476524475/144115188075855872), (-196611673869/288230376151711744)), (106617/576460752303423488), by norm_num⟩
  | 5 => ⟨((149234599475805/18014398509481984), (-687269339787/144115188075855872)), (46651/36028797018963968), by norm_num⟩
  | 4 => ⟨((11645188258675/281474976710656), (-514581770507/18014398509481984)), (139977/18014398509481984), by norm_num⟩
  | 3 => ⟨((743972835307811/4503599627370496), (-320853594233/2251799813685248)), (175013/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225337880761731/4503599627370496), (-2557731643959/4503599627370496)), (700309/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106111419256075/1125899906842624), (-119185472543/70368744177664)), (525557/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173107948053539/2251799813685248), (-942212728057/281474976710656)), (2104875/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173107948053539/2251799813685248), (-942212728057/281474976710656)), (8029460915572356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1048570416483023/1125899906842624), (-14548575450831/2251799813685248)), (509591/281474976710656), by norm_num⟩
  | 2 => ⟨((1953010203446347/2251799813685248), (-27098689194305/2251799813685248)), (955767/281474976710656), by norm_num⟩
  | 3 => ⟨((1693540648077581/2251799813685248), (-11751492334011/562949953421312)), (840449/140737488355328), by norm_num⟩
  | 4 => ⟨((1272702106164397/2251799813685248), (-35352396464851/1125899906842624)), (20788217/2251799813685248), by norm_num⟩
  | 5 => ⟨((1434205184207169/4503599627370496), (-159847493246355/4503599627370496)), (49608379/4503599627370496), by norm_num⟩
  | 6 => ⟨((1804239681488419/18014398509481984), (-407237094706479/18014398509481984)), (140471405/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-952453609/16777216)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-488676801/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-117582597550547/9007199254740992), (-863417381194715/9007199254740992)), (292080227/18014398509481984), by norm_num⟩
  | 1 => ⟨((75917143/2147483648), (69683123/268435456)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((-102793717/2147483648), (-754821581/2147483648)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((46395091/1073741824), (1362729823/4294967296)), (59/1073741824), by norm_num⟩
  | 4 => ⟨((-251280471/8589934592), (-1845170385/8589934592)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((68048013/4294967296), (499681403/4294967296)), (11/536870912), by norm_num⟩
  | 6 => ⟨((-245703247/34359738368), (-112763527/2147483648)), (5/536870912), by norm_num⟩
  | 7 => ⟨((47526909/17179869184), (697986953/34359738368)), (125/34359738368), by norm_num⟩
  | 8 => ⟨((-128705255/137438953472), (-472545927/68719476736)), (171/137438953472), by norm_num⟩
  | 9 => ⟨((38726699/137438953472), (568745819/274877906944)), (13/34359738368), by norm_num⟩
  | 10 => ⟨((-20974769/274877906944), (-1232153783/2199023255552)), (227/2199023255552), by norm_num⟩
  | 11 => ⟨((10327405/549755813888), (1213357927/8796093022208)), (225/8796093022208), by norm_num⟩
  | 12 => ⟨((-149158033/35184372088832), (-1095278059/35184372088832)), (205/35184372088832), by norm_num⟩
  | 13 => ⟨((248570733/281474976710656), (1825272595/281474976710656)), (43/35184372088832), by norm_num⟩
  | 14 => ⟨((-48081573/281474976710656), (-706132831/562949953421312)), (67/281474976710656), by norm_num⟩
  | 15 => ⟨((138887801/4503599627370496), (127482877/562949953421312)), (195/4503599627370496), by norm_num⟩
  | 16 => ⟨((-188057569/36028797018963968), (-1380920123/36028797018963968)), (133/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-17362861811/79228162514264337593543950336)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222295375567637/79228162514264337593543950336), (-2629016415273/633825300114114700748351602688)), (92459/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889285295796445/39614081257132168796771975168), (-2957038324631/39614081257132168796771975168)), (104033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889031741005513/2475880078570760549798248448), (-1570552131409/1237940039285380274899124224)), (55277/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885348942767995/77371252455336267181195264), (-3140261955007/154742504910672534362390528)), (6911/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774545656115787/4835703278458516698824704), (-1471550447099/4835703278458516698824704)), (103689/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258384223364873/604462909807314587353088), (-2574318890081/604462909807314587353088)), (90751/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887134588769547/75557863725914323419136), (-4181591840167/75557863725914323419136)), (18439/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297046178854021/4722366482869645213696), (-783681924417/1180591620717411303424)), (6917/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620769566126637/590295810358705651712), (-2153934608601/295147905179352825856)), (152235/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822625988843317/73786976294838206464), (-2690633266999/36893488147419103232)), (95193/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455425390732737/2305843009213693952), (-756127433623/1152921504606846976)), (26789/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592949288118631/1152921504606846976), (-6042892765677/1152921504606846976)), (214471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149209110860391/18014398509481984), (-330040345765/9007199254740992)), (187841/144115188075855872), by norm_num⟩
  | 4 => ⟨((186284230900081/4503599627370496), (-7907214268543/36028797018963968)), (282119/36028797018963968), by norm_num⟩
  | 3 => ⟨((743775106829265/4503599627370496), (-4929993525087/4503599627370496)), (176639/4503599627370496), by norm_num⟩
  | 2 => ⟨((278065520021657/562949953421312), (-19648036630473/4503599627370496)), (354221/2251799813685248), by norm_num⟩
  | 1 => ⟨((552736420989529/562949953421312), (-29292752563975/2251799813685248)), (266849/562949953421312), by norm_num⟩
  | 0 => ⟨((2170329989505341/2251799813685248), (-28935768438285/1125899906842624)), (538449/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170329989505341/2251799813685248), (-28935768438285/1125899906842624)), (2054019930125999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2090320427224145/2251799813685248), (-111555504409097/2251799813685248)), (2131225/1125899906842624), by norm_num⟩
  | 2 => ⟨((30232725058883/35184372088832), (-207111438786381/2251799813685248)), (4167949/1125899906842624), by norm_num⟩
  | 3 => ⟨((821769586969121/1125899906842624), (-355927522001499/2251799813685248)), (15858909/2251799813685248), by norm_num⟩
  | 4 => ⟨((1143323931241489/2251799813685248), (-519567345140563/2251799813685248)), (28163571/2251799813685248), by norm_num⟩
  | 5 => ⟨((460626819182277/2251799813685248), (-131901995901365/562949953421312)), (20798011/1125899906842624), by norm_num⟩
  | 6 => ⟨((-117582597550547/9007199254740992), (-863417381194715/9007199254740992)), (292080227/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-488676801/8388608)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile019Terms1
