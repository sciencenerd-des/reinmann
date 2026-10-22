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
namespace Reinmann.XiBand97.Tile038Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33979/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33979/1280))
  have he : value ((69/80), (33979/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22364231/8388608), (-1376656183/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((291516425849579/4503599627370496), (-114309051607125/4503599627370496)), (108441049/9007199254740992), by norm_num⟩
  | 1 => ⟨((-429673027/2147483648), (168482843/2147483648)), (161/4294967296), by norm_num⟩
  | 2 => ⟨((41504299/134217728), (-130196905/1073741824)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((-684221601/2147483648), (268296107/2147483648)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((33046219/134217728), (-25916083/268435456)), (51/1073741824), by norm_num⟩
  | 5 => ⟨((-1307485003/8589934592), (256344681/4294967296)), (127/4294967296), by norm_num⟩
  | 6 => ⟨((336790971/4294967296), (-264124097/8589934592)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((-594877251/17179869184), (466525027/34359738368)), (235/34359738368), by norm_num⟩
  | 8 => ⟨((919395419/68719476736), (-180256083/34359738368)), (183/68719476736), by norm_num⟩
  | 9 => ⟨((-1263062343/274877906944), (123817601/68719476736)), (127/137438953472), by norm_num⟩
  | 10 => ⟨((780835865/549755813888), (-306180369/549755813888)), (159/549755813888), by norm_num⟩
  | 11 => ⟨((-438835783/1099511627776), (344151461/2199023255552)), (181/2199023255552), by norm_num⟩
  | 12 => ⟨((452153345/4398046511104), (-44324449/1099511627776)), (47/2199023255552), by norm_num⟩
  | 13 => ⟨((-860077037/35184372088832), (337252317/35184372088832)), (181/35184372088832), by norm_num⟩
  | 14 => ⟨((189895331/35184372088832), (-595692131/281474976710656)), (161/140737488355328), by norm_num⟩
  | 15 => ⟨((-626106165/562949953421312), (491015911/1125899906842624)), (267/1125899906842624), by norm_num⟩
  | 16 => ⟨((60478773/281474976710656), (-379437757/4503599627370496)), (13/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-243388930725/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777857658985191/633825300114114700748351602688), (-287757010017/316912650057057350374175801344)), (92257/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944358551037873/19807040628566084398385987584), (-323652344153/19807040628566084398385987584)), (103793/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944214224488321/1237940039285380274899124224), (-343787152661/1237940039285380274899124224)), (27571/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((27657735291689/2417851639229258349412352), (-687364122085/154742504910672534362390528)), (110289/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548526655985913/9671406556917033397649408), (-644180635121/9671406556917033397649408)), (103401/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257890642765867/604462909807314587353088), (-281717464051/302231454903657293676544)), (90481/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471583361282881/18889465931478580854784), (-457581804933/37778931862957161709568)), (147041/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81027883103899/295147905179352825856), (-686007043513/4722366482869645213696)), (110289/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809972905530107/295147905179352825856), (-942665885503/590295810358705651712)), (151661/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28462472837419/1152921504606846976), (-588721182595/36893488147419103232)), (189597/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910274035069663/4611686018427387904), (-661700035299/4611686018427387904)), (426651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591799165251145/1152921504606846976), (-660936776739/576460752303423488)), (426721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192670312946389/144115188075855872), (-288731097633/36028797018963968)), (186731/72057594037927936), by norm_num⟩
  | 4 => ⟨((186097191811449/4503599627370496), (-1728962546955/36028797018963968)), (280177/18014398509481984), by norm_num⟩
  | 3 => ⟨((742846494784841/4503599627370496), (-1077612181777/4503599627370496)), (700725/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110424521324011/2251799813685248), (-4292565137275/4503599627370496)), (350577/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205530742198693/2251799813685248), (-799290404523/281474976710656)), (526407/562949953421312), by norm_num⟩
  | 0 => ⟨((2159887507338483/2251799813685248), (-12611651297375/2251799813685248)), (4220041/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159887507338483/2251799813685248), (-12611651297375/2251799813685248)), (16098178872115325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035828087882695/1125899906842624), (-12096878203187/1125899906842624)), (2035713/562949953421312), by norm_num⟩
  | 2 => ⟨((1905664058882297/2251799813685248), (-44516519247953/2251799813685248)), (3789457/562949953421312), by norm_num⟩
  | 3 => ⟨((805927277098783/1125899906842624), (-75347311285659/2251799813685248)), (26255001/2251799813685248), by norm_num⟩
  | 4 => ⟨((575627964531801/1125899906842624), (-107868298153529/2251799813685248)), (39344073/2251799813685248), by norm_num⟩
  | 5 => ⟨((583424261994007/2251799813685248), (-13787195586007/281474976710656)), (43999539/2251799813685248), by norm_num⟩
  | 6 => ⟨((291516425849579/4503599627370496), (-114309051607125/4503599627370496)), (108441049/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1376656183/16777216)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45371695/16777216), (-349113411/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((20589470413961/18014398509481984), (-602609738430261/9007199254740992)), (194828939/18014398509481984), by norm_num⟩
  | 1 => ⟨((-7695933/2147483648), (1801947927/8589934592)), (293/8589934592), by norm_num⟩
  | 2 => ⟨((24130553/4294967296), (-1412499325/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-25220403/4294967296), (184536811/536870912)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((19769607/4294967296), (-1157228207/4294967296)), (193/4294967296), by norm_num⟩
  | 5 => ⟨((-24794995/8589934592), (362848235/2147483648)), (61/2147483648), by norm_num⟩
  | 6 => ⟨((12957427/8589934592), (-1516944723/17179869184)), (257/17179869184), by norm_num⟩
  | 7 => ⟨((-5803991/8589934592), (679481629/17179869184)), (29/4294967296), by norm_num⟩
  | 8 => ⟨((4549595/17179869184), (-1065255359/68719476736)), (23/8589934592), by norm_num⟩
  | 9 => ⟨((-25360407/274877906944), (1484489785/274877906944)), (129/137438953472), by norm_num⟩
  | 10 => ⟨((7951741/274877906944), (-1861843653/1099511627776)), (163/549755813888), by norm_num⟩
  | 11 => ⟨((-4533207/549755813888), (1061418183/2199023255552)), (47/549755813888), by norm_num⟩
  | 12 => ⟨((1184487/549755813888), (-554678429/4398046511104)), (99/4398046511104), by norm_num⟩
  | 13 => ⟨((-2285509/4398046511104), (267567847/8796093022208)), (3/549755813888), by norm_num⟩
  | 14 => ⟨((32759773/281474976710656), (-958808499/140737488355328)), (173/140737488355328), by norm_num⟩
  | 15 => ⟨((-53499/2199023255552), (1603380535/1125899906842624)), (73/281474976710656), by norm_num⟩
  | 16 => ⟨((21471463/4503599627370496), (-628423799/2251799813685248)), (115/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1011943241241/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222224465241231/79228162514264337593543950336), (-598168777385/158456325028528675187087900672)), (23109/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888647280345913/39614081257132168796771975168), (-1345564528395/19807040628566084398385987584)), (52003/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472088517681721/618970019642690137449562112), (-2858535829075/2475880078570760549798248448)), (27631/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770020463949143/154742504910672534362390528), (-2857648824371/154742504910672534362390528)), (6909/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548456493638721/9671406556917033397649408), (-2678103677519/9671406556917033397649408)), (12957/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257829021139541/604462909807314587353088), (-2342399013089/604462909807314587353088)), (2835/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((235779110002419/9444732965739290427392), (-3804633529539/75557863725914323419136)), (147459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648185165041857/2361183241434822606848), (-2851931718033/4722366482869645213696)), (110629/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619840976951279/590295810358705651712), (-1959449797013/295147905179352825856)), (76085/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821466305993517/73786976294838206464), (-305929214567/4611686018427387904)), (190297/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820398367304221/9223372036854775808), (-5501564319011/9223372036854775808)), (26775/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795823950122835/576460752303423488), (-5495119004955/1152921504606846976)), (214345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298134050963233/36028797018963968), (-4800987237781/144115188075855872)), (46929/36028797018963968), by norm_num⟩
  | 4 => ⟨((372143219866311/9007199254740992), (-7187019764127/36028797018963968)), (70475/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485431090124445/9007199254740992), (-4479259387317/4503599627370496)), (352949/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110153559214867/2251799813685248), (-17841473322085/4503599627370496)), (353811/2251799813685248), by norm_num⟩
  | 1 => ⟨((551168237271675/562949953421312), (-1660875641665/140737488355328)), (33305/70368744177664), by norm_num⟩
  | 0 => ⟨((269749339882541/281474976710656), (-26199736902925/1125899906842624)), (2148919/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269749339882541/281474976710656), (-26199736902925/1125899906842624)), (8197475441939543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129179875203365/140737488355328), (-100433250831035/2251799813685248)), (4218811/2251799813685248), by norm_num⟩
  | 2 => ⟨((1892662845320677/2251799813685248), (-92185493433457/1125899906842624)), (507565/140737488355328), by norm_num⟩
  | 3 => ⟨((196963555757439/281474976710656), (-309931739471127/2251799813685248)), (7490753/1125899906842624), by norm_num⟩
  | 4 => ⟨((1059951870208879/2251799813685248), (-433752642325099/2251799813685248)), (25090801/2251799813685248), by norm_num⟩
  | 5 => ⟨((830763557888843/4503599627370496), (-816692357191563/4503599627370496)), (33287367/2251799813685248), by norm_num⟩
  | 6 => ⟨((20589470413961/18014398509481984), (-602609738430261/9007199254740992)), (194828939/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-349113411/4194304)), (1/16777216), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45987547/16777216), (-88463025/1048576)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1042153570961763/18014398509481984), (-513852714369857/18014398509481984)), (419893839/18014398509481984), by norm_num⟩
  | 1 => ⟨((394823569/2147483648), (389349839/4294967296)), (5/67108864), by norm_num⟩
  | 2 => ⟨((-313692639/1073741824), (-618687373/4294967296)), (511/4294967296), by norm_num⟩
  | 3 => ⟨((664621395/2147483648), (327703629/2147483648)), (17/134217728), by norm_num⟩
  | 4 => ⟨((-1056101285/4294967296), (-520729887/4294967296)), (217/2147483648), by norm_num⟩
  | 5 => ⟨((1342538693/8589934592), (661963045/8589934592)), (277/4294967296), by norm_num⟩
  | 6 => ⟨((-711110039/8589934592), (-701251397/17179869184)), (589/17179869184), by norm_num⟩
  | 7 => ⟨((161424713/4294967296), (318373527/17179869184)), (537/34359738368), by norm_num⟩
  | 8 => ⟨((-1026032855/68719476736), (-505904103/68719476736)), (429/68719476736), by norm_num⟩
  | 9 => ⟨((724619477/137438953472), (89321693/34359738368)), (305/137438953472), by norm_num⟩
  | 10 => ⟨((-460575941/274877906944), (-227095319/274877906944)), (195/274877906944), by norm_num⟩
  | 11 => ⟨((532267321/1099511627776), (131222027/549755813888)), (453/2199023255552), by norm_num⟩
  | 12 => ⟨((-281929033/2199023255552), (-556040887/8796093022208)), (241/4398046511104), by norm_num⟩
  | 13 => ⟨((1102751561/35184372088832), (135932913/8796093022208)), (237/17592186044416), by norm_num⟩
  | 14 => ⟨((-500657689/70368744177664), (-493716703/140737488355328)), (433/140737488355328), by norm_num⟩
  | 15 => ⟨((848595779/562949953421312), (26150971/35184372088832)), (369/562949953421312), by norm_num⟩
  | 16 => ⟨((-1348441533/4503599627370496), (-166218387/1125899906842624)), (589/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-3495566050743/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444433276316335/158456325028528675187087900672), (-2066135315149/316912650057057350374175801344)), (92607/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472144130026199/9903520314283042199192993792), (-290480372871/2475880078570760549798248448)), (104209/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888278460695885/2475880078570760549798248448), (-4936783785805/2475880078570760549798248448)), (221505/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884972186902071/77371252455336267181195264), (-1233807205741/38685626227668133590597632)), (110787/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548384649448825/9671406556917033397649408), (-2312562674093/4835703278458516698824704)), (103899/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628882824145989/302231454903657293676544), (-4045333539677/604462909807314587353088)), (22737/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((7367691193295/295147905179352825856), (-3285286123921/37778931862957161709568)), (73929/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296291545786407/4722366482869645213696), (-615652801163/590295810358705651712)), (221907/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404932824063203/147573952589676412928), (-6767784425655/590295810358705651712)), (305315/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821327180143873/73786976294838206464), (-2113284917385/18446744073709551616)), (381935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910119535996699/4611686018427387904), (-9500725733855/9223372036854775808)), (107519/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591485139930445/1152921504606846976), (-2372353575629/288230376151711744)), (430577/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596194950995089/72057594037927936), (-4145262306459/72057594037927936)), (377319/144115188075855872), by norm_num⟩
  | 4 => ⟨((744172841150313/18014398509481984), (-12410392258109/36028797018963968)), (567107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485133605679119/9007199254740992), (-15468619724685/9007199254740992)), (355431/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219671943462523/4503599627370496), (-3850550979589/562949953421312)), (178459/562949953421312), by norm_num⟩
  | 1 => ⟨((2203620570728021/2251799813685248), (-45875513098793/2251799813685248)), (269553/281474976710656), by norm_num⟩
  | 0 => ⟨((2155496867753293/2251799813685248), (-90432511680487/2251799813685248)), (2186395/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155496867753293/2251799813685248), (-90432511680487/2251799813685248)), (8340435032371139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2059680740507293/2251799813685248), (-173129950971387/2251799813685248)), (8722781/2251799813685248), by norm_num⟩
  | 2 => ⟨((1870641762777099/2251799813685248), (-316717697064861/2251799813685248)), (17298447/2251799813685248), by norm_num⟩
  | 3 => ⟨((754727503829265/1125899906842624), (-526214939302707/2251799813685248)), (33606827/2251799813685248), by norm_num⟩
  | 4 => ⟨((444433880320019/1125899906842624), (-352739071389863/1125899906842624)), (30381213/1125899906842624), by norm_num⟩
  | 5 => ⟨((259691367046337/4503599627370496), (-1113912121569719/4503599627370496)), (86043463/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1042153570961763/18014398509481984), (-513852714369857/18014398509481984)), (419893839/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-88463025/1048576)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/1048576), (-716794637/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-909319405954535/18014398509481984), (164214753193665/4503599627370496)), (205728787/18014398509481984), by norm_num⟩
  | 1 => ⟨((21807747/134217728), (-252049875/2147483648)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-561571437/2147483648), (811317249/4294967296)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((1205085815/4294967296), (-870509827/4294967296)), (281/4294967296), by norm_num⟩
  | 4 => ⟨((-969755399/4294967296), (700515759/4294967296)), (57/1073741824), by norm_num⟩
  | 5 => ⟨((312152221/2147483648), (-56371831/536870912)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((-669852825/8589934592), (483877131/8589934592)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((616049447/17179869184), (-890023085/34359738368)), (299/34359738368), by norm_num⟩
  | 8 => ⟨((-123936667/8589934592), (44763653/4294967296)), (121/34359738368), by norm_num⟩
  | 9 => ⟨((709220873/137438953472), (-256157583/68719476736)), (175/137438953472), by norm_num⟩
  | 10 => ⟨((-913157569/549755813888), (659631561/549755813888)), (227/549755813888), by norm_num⟩
  | 11 => ⟨((1068851209/2199023255552), (-193024735/549755813888)), (67/549755813888), by norm_num⟩
  | 12 => ⟨((-573416553/4398046511104), (207107551/2199023255552)), (145/4398046511104), by norm_num⟩
  | 13 => ⟨((1135850265/35184372088832), (-410248301/17592186044416)), (289/35184372088832), by norm_num⟩
  | 14 => ⟨((-1044617417/140737488355328), (94324167/17592186044416)), (67/35184372088832), by norm_num⟩
  | 15 => ⟨((112083125/70368744177664), (-647717933/562949953421312)), (29/70368744177664), by norm_num⟩
  | 16 => ⟨((-721563323/2251799813685248), (521230899/2251799813685248)), (47/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (3277390282609/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777679997113379/633825300114114700748351602688), (484266195657/79228162514264337593543950336)), (46291/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472129212263271/9903520314283042199192993792), (2178668767935/19807040628566084398385987584)), (26045/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888215159660091/2475880078570760549798248448), (578544834415/309485009821345068724781056)), (110719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769881184560063/154742504910672534362390528), (4626882615089/154742504910672534362390528)), (110751/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548325528227745/9671406556917033397649408), (4336134623865/9671406556917033397649408)), (103863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157214254478119/75557863725914323419136), (948137628647/151115727451828646838272)), (90915/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235755662175373/9444732965739290427392), (1539989273725/18889465931478580854784)), (147799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296229003932917/4722366482869645213696), (4617398677215/4722366482869645213696)), (55453/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619645616417283/590295810358705651712), (3172375249291/295147905179352825856)), (76293/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821220552516335/73786976294838206464), (7924682907143/73786976294838206464)), (190869/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820119764082177/9223372036854775808), (8906673534579/9223372036854775808)), (107457/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795683320321709/576460752303423488), (2223984847803/288230376151711744)), (215149/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298071780658807/36028797018963968), (7771883806985/144115188075855872)), (23565/18014398509481984), by norm_num⟩
  | 4 => ⟨((744096661432757/18014398509481984), (11633731254189/36028797018963968)), (283309/36028797018963968), by norm_num⟩
  | 3 => ⟨((371236577737405/2251799813685248), (14500070428007/9007199254740992)), (44383/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219306768875777/4503599627370496), (3609268298857/562949953421312)), (712915/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101548087808813/1125899906842624), (21498617596307/1125899906842624)), (67273/140737488355328), by norm_num⟩
  | 0 => ⟨((2154540525846117/2251799813685248), (84744536817101/2251799813685248)), (1090423/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154540525846117/2251799813685248), (84744536817101/2251799813685248)), (4159633640769576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2058292754455645/2251799813685248), (162168535414955/2251799813685248)), (1084363/562949953421312), by norm_num⟩
  | 2 => ⟨((934867834071701/1125899906842624), (296465360212471/2251799813685248)), (133659/35184372088832), by norm_num⟩
  | 3 => ⟨((756732400946479/1125899906842624), (123081957594415/562949953421312)), (4114501/562949953421312), by norm_num⟩
  | 4 => ⟨((909578640852845/2251799813685248), (661800252172031/2251799813685248)), (7329991/562949953421312), by norm_num⟩
  | 5 => ⟨((21613473795187/281474976710656), (1069294650844743/4503599627370496)), (40920843/2251799813685248), by norm_num⟩
  | 6 => ⟨((-909319405954535/18014398509481984), (164214753193665/4503599627370496)), (205728787/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-716794637/8388608)), (1/16777216), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47145793/16777216), (-1451056985/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((103879596072971/18014398509481984), (1079452499844841/18014398509481984)), (342475517/18014398509481984), by norm_num⟩
  | 1 => ⟨((-80692709/4294967296), (-419254357/2147483648)), (267/4294967296), by norm_num⟩
  | 2 => ⟨((65726159/2147483648), (1365971169/4294967296)), (437/4294967296), by norm_num⟩
  | 3 => ⟨((-142761447/4294967296), (-741744323/2147483648)), (477/4294967296), by norm_num⟩
  | 4 => ⟨((29070661/1073741824), (604168653/2147483648)), (195/2147483648), by norm_num⟩
  | 5 => ⟨((-4735751/268435456), (-787375919/4294967296)), (255/4294967296), by norm_num⟩
  | 6 => ⟨((164581695/17179869184), (1710231171/17179869184)), (139/4294967296), by norm_num⟩
  | 7 => ⟨((-76603293/17179869184), (-796014037/17179869184)), (519/34359738368), by norm_num⟩
  | 8 => ⟨((62395231/34359738368), (1296745289/68719476736)), (53/8589934592), by norm_num⟩
  | 9 => ⟨((-180701943/274877906944), (-1877742817/274877906944)), (77/34359738368), by norm_num⟩
  | 10 => ⟨((117748875/549755813888), (611786737/274877906944)), (403/549755813888), by norm_num⟩
  | 11 => ⟨((-139504437/2199023255552), (-724821909/1099511627776)), (479/2199023255552), by norm_num⟩
  | 12 => ⟨((37876577/2199023255552), (1574359835/8796093022208)), (261/4398046511104), by norm_num⟩
  | 13 => ⟨((-151883747/35184372088832), (-1578281947/35184372088832)), (525/35184372088832), by norm_num⟩
  | 14 => ⟨((35346565/35184372088832), (1469198557/140737488355328)), (491/140737488355328), by norm_num⟩
  | 15 => ⟨((-61420011/281474976710656), (-1276477529/562949953421312)), (429/562949953421312), by norm_num⟩
  | 16 => ⟨((100056163/2251799813685248), (1039721755/2251799813685248)), (351/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (1921167423133/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888816598260809/316912650057057350374175801344), (567710500415/158456325028528675187087900672)), (184847/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888464500064483/39614081257132168796771975168), (79814926601/1237940039285380274899124224)), (207983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944079971862205/1237940039285380274899124224), (678232432745/618970019642690137449562112)), (221015/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769826423576397/154742504910672534362390528), (1356027575967/77371252455336267181195264)), (55263/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193534334098937/1208925819614629174706176), (2541622827503/9671406556917033397649408)), (207277/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257670019853353/604462909807314587353088), (2222991504855/604462909807314587353088)), (181407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885974675245153/75557863725914323419136), (1805310591351/37778931862957161709568)), (294861/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296176827179469/4722366482869645213696), (21144095645/36893488147419103232)), (55303/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809787577559881/295147905179352825856), (3718889785251/590295810358705651712)), (19017/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821134395369225/73786976294838206464), (4644908499247/73786976294838206464)), (95125/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910012735742209/4611686018427387904), (5220434041301/9223372036854775808)), (214141/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591275633169237/1152921504606846976), (1303520231755/288230376151711744)), (214279/576460752303423488), by norm_num⟩
  | 5 => ⟨((596105588201107/72057594037927936), (1138795762581/36028797018963968)), (375299/144115188075855872), by norm_num⟩
  | 4 => ⟨((93005421752317/2251799813685248), (6818522755459/36028797018963968)), (281785/18014398509481984), by norm_num⟩
  | 3 => ⟨((742412943377505/4503599627370496), (8498266004771/9007199254740992)), (352777/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109552034956427/2251799813685248), (16922082257775/4503599627370496)), (707193/2251799813685248), by norm_num⟩
  | 1 => ⟨((68840208944949/70368744177664), (25197741126381/2251799813685248)), (2129811/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154494920987561/2251799813685248), (49658391035999/2251799813685248)), (536591/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154494920987561/2251799813685248), (49658391035999/2251799813685248)), (2046932221532726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1030149834049457/1125899906842624), (23756275007497/562949953421312)), (8403795/2251799813685248), by norm_num⟩
  | 2 => ⟨((1881075274538085/2251799813685248), (173887732704303/2251799813685248)), (16087495/2251799813685248), by norm_num⟩
  | 3 => ⟨((1557956983375015/2251799813685248), (145259766231277/1125899906842624)), (7340619/562949953421312), by norm_num⟩
  | 4 => ⟨((1040424796674307/2251799813685248), (201002296765509/1125899906842624)), (24103319/1125899906842624), by norm_num⟩
  | 5 => ⟨((817902247542731/4503599627370496), (742971102395001/4503599627370496)), (123518393/4503599627370496), by norm_num⟩
  | 6 => ⟨((103879596072971/18014398509481984), (1079452499844841/18014398509481984)), (342475517/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1451056985/16777216)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47691909/16777216), (-733932689/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((934456052447133/18014398509481984), (478203762477657/18014398509481984)), (98265949/9007199254740992), by norm_num⟩
  | 1 => ⟨((-367142523/2147483648), (-375767133/4294967296)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((605020931/2147483648), (619233585/4294967296)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((-1329366859/4294967296), (-340148813/2147483648)), (287/4294967296), by norm_num⟩
  | 4 => ⟨((273836019/1073741824), (560537499/4294967296)), (119/2147483648), by norm_num⟩
  | 5 => ⟨((-722015077/4294967296), (-369488031/4294967296)), (159/4294967296), by norm_num⟩
  | 6 => ⟨((198303659/2147483648), (405924091/8589934592)), (11/536870912), by norm_num⟩
  | 7 => ⟨((-746944583/17179869184), (-382245595/17179869184)), (167/17179869184), by norm_num⟩
  | 8 => ⟨((1230903747/68719476736), (314954781/34359738368)), (277/68719476736), by norm_num⟩
  | 9 => ⟨((-225380997/34359738368), (-115337731/34359738368)), (205/137438953472), by norm_num⟩
  | 10 => ⟨((594255199/274877906944), (608214953/549755813888)), (17/34359738368), by norm_num⟩
  | 11 => ⟨((-712206615/1099511627776), (-182234297/549755813888)), (165/1099511627776), by norm_num⟩
  | 12 => ⟨((782438939/4398046511104), (100102419/1099511627776)), (183/4398046511104), by norm_num⟩
  | 13 => ⟨((-793474185/17592186044416), (-203028457/8796093022208)), (187/17592186044416), by norm_num⟩
  | 14 => ⟨((2918707/274877906944), (382370671/70368744177664)), (89/35184372088832), by norm_num⟩
  | 15 => ⟨((-656696807/281474976710656), (-672123389/562949953421312)), (315/562949953421312), by norm_num⟩
  | 16 => ⟨((1082182773/2251799813685248), (553802261/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (616135137125/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777585561392765/633825300114114700748351602688), (728239650581/633825300114114700748351602688)), (5767/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944205529473477/19807040628566084398385987584), (819069918387/39614081257132168796771975168)), (103811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59003230049691/77371252455336267181195264), (870009611813/2475880078570760549798248448)), (220609/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769770065106441/154742504910672534362390528), (217431517943/38685626227668133590597632)), (55155/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774111037086935/4835703278458516698824704), (407533530291/4835703278458516698824704)), (206845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257624233290785/604462909807314587353088), (89110336523/75557863725914323419136)), (181003/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942950358207935/37778931862957161709568), (1157870336195/75557863725914323419136)), (294153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296121746383621/4722366482869645213696), (867909527985/4722366482869645213696)), (55159/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619500049180839/590295810358705651712), (1192574691833/590295810358705651712)), (303409/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910520728324963/36893488147419103232), (372379503857/18446744073709551616)), (379313/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909961105268965/4611686018427387904), (837029466869/4611686018427387904)), (426799/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591173987398383/1152921504606846976), (418000089773/288230376151711744)), (53361/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192124048326353/144115188075855872), (730343902951/72057594037927936)), (373629/144115188075855872), by norm_num⟩
  | 4 => ⟨((371989916787937/9007199254740992), (68325473415/1125899906842624)), (280323/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484673326759303/9007199254740992), (2724958948891/9007199254740992)), (350583/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218817709490057/4503599627370496), (678226714659/562949953421312)), (350853/1125899906842624), by norm_num⟩
  | 1 => ⟨((550625912026621/562949953421312), (4039362269891/1125899906842624)), (2107843/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076956245105729/1125899906842624), (3979761213377/562949953421312)), (4226733/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076956245105729/1125899906842624), (3979761213377/562949953421312)), (16123706826216887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64380245572147/70368744177664), (30454065529113/2251799813685248)), (4072875/1125899906842624), by norm_num⟩
  | 2 => ⟨((1884432234389619/2251799813685248), (55724746557489/2251799813685248)), (7562699/1125899906842624), by norm_num⟩
  | 3 => ⟨((787809728259371/1125899906842624), (93267179460565/2251799813685248)), (26064171/2251799813685248), by norm_num⟩
  | 4 => ⟨((68663905255947/140737488355328), (32630250193553/562949953421312)), (9658529/562949953421312), by norm_num⟩
  | 5 => ⟨((1056875148212111/4503599627370496), (127358840004943/2251799813685248)), (2636051/140737488355328), by norm_num⟩
  | 6 => ⟨((934456052447133/18014398509481984), (478203762477657/18014398509481984)), (98265949/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-733932689/8388608)), (1/8388608), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile038Terms3
