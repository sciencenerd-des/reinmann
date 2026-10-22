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
namespace Reinmann.XiBand97.Tile001Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (3717/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (3717/256))
  have he : value ((69/80), (3717/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-535238001/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1196573173165773/9007199254740992), (-316621358165391/4503599627370496)), (126107851/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1253671639/4294967296), (663459997/4294967296)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((1377299069/4294967296), (-364442653/2147483648)), (151/4294967296), by norm_num⟩
  | 3 => ⟨((-504372561/2147483648), (266920785/2147483648)), (113/4294967296), by norm_num⟩
  | 4 => ⟨((1108219787/8589934592), (-586484909/8589934592)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-974003101/17179869184), (515455623/17179869184)), (57/8589934592), by norm_num⟩
  | 6 => ⟨((713367851/34359738368), (-377523921/34359738368)), (85/34359738368), by norm_num⟩
  | 7 => ⟨((-895673929/137438953472), (474002765/137438953472)), (109/137438953472), by norm_num⟩
  | 8 => ⟨((983998385/549755813888), (-520745263/549755813888)), (61/274877906944), by norm_num⟩
  | 9 => ⟨((-240229493/549755813888), (127132699/549755813888)), (121/2199023255552), by norm_num⟩
  | 10 => ⟨((422270517/4398046511104), (-446942545/8796093022208)), (109/8796093022208), by norm_num⟩
  | 11 => ⟨((-674780479/35184372088832), (714205923/70368744177664)), (177/70368744177664), by norm_num⟩
  | 12 => ⟨((494214751/140737488355328), (-523090269/281474976710656)), (33/70368744177664), by norm_num⟩
  | 13 => ⟨((-1336493289/2251799813685248), (22102823/70368744177664)), (181/2251799813685248), by norm_num⟩
  | 14 => ⟨((839021687/9007199254740992), (-444021631/9007199254740992)), (29/2251799813685248), by norm_num⟩
  | 15 => ⟨((-245802543/18014398509481984), (8130127/1125899906842624)), (69/36028797018963968), by norm_num⟩
  | 16 => ⟨((540083389/288230376151711744), (-142909719/144115188075855872)), (77/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-634038905449/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045557651003/633825300114114700748351602688), (-750574381747/633825300114114700748351602688)), (46137/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945026608075749/19807040628566084398385987584), (-422127937451/19807040628566084398385987584)), (51907/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472461932724297/618970019642690137449562112), (-112106058823/309485009821345068724781056)), (110307/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771513959055065/154742504910672534362390528), (-56040841463/9671406556917033397649408)), (55157/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387464117465183/2417851639229258349412352), (-840405485555/9671406556917033397649408)), (103425/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629526912413779/302231454903657293676544), (-367573864777/302231454903657293676544)), (11313/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888222856797195/75557863725914323419136), (-1194226944077/75557863725914323419136)), (147081/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297862524463085/4722366482869645213696), (-223832686621/1180591620717411303424)), (55161/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621892275628077/590295810358705651712), (-1230528414331/590295810358705651712)), (151709/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912014862993763/36893488147419103232), (-1537333934741/73786976294838206464)), (189663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823281246943453/9223372036854775808), (-1728364871685/9223372036854775808)), (213407/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594529568953331/1152921504606846976), (-863473117597/576460752303423488)), (213453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195056300148043/144115188075855872), (-1509483527919/144115188075855872)), (186823/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492350292461683/36028797018963968), (-2261040277619/36028797018963968)), (17521/2251799813685248), by norm_num⟩
  | 3 => ⟨((1490148067840533/9007199254740992), (-1410367602289/4503599627370496)), (43825/1125899906842624), by norm_num⟩
  | 2 => ⟨((2229726674513819/4503599627370496), (-5624809457665/4503599627370496)), (701743/4503599627370496), by norm_num⟩
  | 1 => ⟨((554691541933867/562949953421312), (-4197841114889/1125899906842624)), (131747/281474976710656), by norm_num⟩
  | 0 => ⟨((1093018000092459/1125899906842624), (-16625957220807/2251799813685248)), (264179/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093018000092459/1125899906842624), (-16625957220807/2251799813685248)), (1007762910009288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1061035031313599/1125899906842624), (-4035099035151/281474976710656)), (1033657/562949953421312), by norm_num⟩
  | 2 => ⟨((1999351484881861/2251799813685248), (-30421044748969/1125899906842624)), (7911397/2251799813685248), by norm_num⟩
  | 3 => ⟨((886780560148643/1125899906842624), (-108042216933961/2251799813685248)), (14476429/2251799813685248), by norm_num⟩
  | 4 => ⟨((1391707161420079/2251799813685248), (-170192282759983/2251799813685248)), (24193001/2251799813685248), by norm_num⟩
  | 5 => ⟨((847270436049321/2251799813685248), (-420744006276229/4503599627370496)), (67123259/4503599627370496), by norm_num⟩
  | 6 => ⟨((1196573173165773/9007199254740992), (-316621358165391/4503599627370496)), (126107851/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-535238001/16777216)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1121807079/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-266475721394313/4503599627370496), (-1115419402516837/9007199254740992)), (109415053/4503599627370496), by norm_num⟩
  | 1 => ⟨((585158371/4294967296), (306170951/1073741824)), (121/2147483648), by norm_num⟩
  | 2 => ⟨((-673688471/4294967296), (-176246167/536870912)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((258537505/2147483648), (541095729/2147483648)), (109/2147483648), by norm_num⟩
  | 4 => ⟨((-595304605/8589934592), (-77869935/536870912)), (253/8589934592), by norm_num⟩
  | 5 => ⟨((137073951/4294967296), (573766885/8589934592)), (235/17179869184), by norm_num⟩
  | 6 => ⟨((-210416291/17179869184), (-440382359/17179869184)), (183/34359738368), by norm_num⟩
  | 7 => ⟨((553715903/137438953472), (1158877549/137438953472)), (243/137438953472), by norm_num⟩
  | 8 => ⟨((-19921531/17179869184), (-1334207085/549755813888)), (141/274877906944), by norm_num⟩
  | 9 => ⟨((163096961/549755813888), (682694521/1099511627776)), (73/549755813888), by norm_num⟩
  | 10 => ⟨((-300435705/4398046511104), (-628784891/4398046511104)), (271/8796093022208), by norm_num⟩
  | 11 => ⟨((503111837/35184372088832), (526483897/17592186044416)), (229/35184372088832), by norm_num⟩
  | 12 => ⟨((-386152605/140737488355328), (-808182649/140737488355328)), (89/70368744177664), by norm_num⟩
  | 13 => ⟨((273584379/562949953421312), (572587483/562949953421312)), (255/1125899906842624), by norm_num⟩
  | 14 => ⟨((-359972179/4503599627370496), (-753389373/4503599627370496)), (85/2251799813685248), by norm_num⟩
  | 15 => ⟨((110515543/9007199254740992), (925196341/36028797018963968)), (211/36028797018963968), by norm_num⟩
  | 16 => ⟨((-127235721/72057594037927936), (-266292913/72057594037927936)), (245/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-2626755066969/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444725141794981/158456325028528675187087900672), (-3109082809801/633825300114114700748351602688)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944944926298695/19807040628566084398385987584), (-874275203315/9903520314283042199192993792)), (104089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944836916087935/1237940039285380274899124224), (-1857457922927/1237940039285380274899124224)), (55309/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885669847532329/77371252455336267181195264), (-3714068006191/154742504910672534362390528)), (110643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387423177380251/2417851639229258349412352), (-3481038106831/9671406556917033397649408)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258910146962495/604462909807314587353088), (-1522503948803/302231454903657293676544)), (90813/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887988654173495/75557863725914323419136), (-2473224964601/37778931862957161709568)), (73811/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297686237760273/4722366482869645213696), (-463545120269/590295810358705651712)), (55381/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810824425542321/295147905179352825856), (-5096597844519/590295810358705651712)), (152369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823723901771579/73786976294838206464), (-6367151004257/73786976294838206464)), (190571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911467537755041/4611686018427387904), (-3579051133431/4611686018427387904)), (107271/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398545188321473/288230376151711744), (-223497732907/36028797018963968)), (214729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194748118204743/144115188075855872), (-6250994602913/144115188075855872)), (188099/144115188075855872), by norm_num⟩
  | 4 => ⟨((745941049688859/18014398509481984), (-4681309967763/18014398509481984)), (282571/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489552502800603/9007199254740992), (-1459878209785/1125899906842624)), (353955/9007199254740992), by norm_num⟩
  | 2 => ⟨((557126179876597/1125899906842624), (-2910676306953/562949953421312)), (355067/2251799813685248), by norm_num⟩
  | 1 => ⟨((554214170732923/562949953421312), (-34746887330579/2251799813685248)), (535389/1125899906842624), by norm_num⟩
  | 0 => ⟨((2181913870227469/2251799813685248), (-17192776199015/562949953421312)), (67623/70368744177664), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2181913870227469/2251799813685248), (-17192776199015/562949953421312)), (257961273461794831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((528024143546373/562949953421312), (-133273505498535/2251799813685248)), (2162865/1125899906842624), by norm_num⟩
  | 2 => ⟨((1973172785793331/2251799813685248), (-125005123760301/1125899906842624)), (4313379/1125899906842624), by norm_num⟩
  | 3 => ⟨((1701263893640937/2251799813685248), (-109537582688081/562949953421312)), (4258563/562949953421312), by norm_num⟩
  | 4 => ⟨((1200072540660435/2251799813685248), (-165514121896085/562949953421312)), (8092043/562949953421312), by norm_num⟩
  | 5 => ⟨((444913133044035/2251799813685248), (-176417949385957/562949953421312)), (13383453/562949953421312), by norm_num⟩
  | 6 => ⟨((-266475721394313/4503599627370496), (-1115419402516837/9007199254740992)), (109415053/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1121807079/33554432)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-584120843/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1100727307060985/9007199254740992), (291398759351113/9007199254740992)), (49228041/2251799813685248), by norm_num⟩
  | 1 => ⟨((1258577731/4294967296), (-83296741/1073741824)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((-377242199/1073741824), (399473723/4294967296)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((1206116381/4294967296), (-319298717/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-90379399/536870912), (191411221/4294967296)), (267/8589934592), by norm_num⟩
  | 5 => ⟨((1387010135/17179869184), (-183593625/8589934592)), (259/17179869184), by norm_num⟩
  | 6 => ⟨((-1108635015/34359738368), (146746095/17179869184)), (209/34359738368), by norm_num⟩
  | 7 => ⟨((759540189/68719476736), (-402150591/137438953472)), (289/137438953472), by norm_num⟩
  | 8 => ⟨((-455324457/137438953472), (120539375/137438953472)), (175/274877906944), by norm_num⟩
  | 9 => ⟨((970506989/1099511627776), (-256925153/1099511627776)), (189/1099511627776), by norm_num⟩
  | 10 => ⟨((-58179353/274877906944), (61607961/1099511627776)), (183/4398046511104), by norm_num⟩
  | 11 => ⟨((811682883/17592186044416), (-214879183/17592186044416)), (161/17592186044416), by norm_num⟩
  | 12 => ⟨((-1297553699/140737488355328), (343505185/140737488355328)), (65/35184372088832), by norm_num⟩
  | 13 => ⟨((478676597/281474976710656), (-253442911/562949953421312)), (97/281474976710656), by norm_num⟩
  | 14 => ⟨((-1311790113/4503599627370496), (347274033/4503599627370496)), (67/1125899906842624), by norm_num⟩
  | 15 => ⟨((104851177/2251799813685248), (-111030235/9007199254740992)), (173/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1005688567/144115188075855872), (66559719/36028797018963968)), (105/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (3755164294335/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889384216650887/316912650057057350374175801344), (2222044450893/316912650057057350374175801344)), (46319/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((29527201933611/618970019642690137449562112), (4998668163843/39614081257132168796771975168)), (52123/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889515230056661/2475880078570760549798248448), (5309961263103/2475880078570760549798248448)), (110793/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771180682398481/154742504910672534362390528), (5308697160947/154742504910672534362390528)), (55415/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549543199242053/9671406556917033397649408), (621945079169/1208925819614629174706176)), (51971/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629389444951595/302231454903657293676544), (4352272771369/604462909807314587353088)), (90989/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471943636371961/18889465931478580854784), (7069925902069/75557863725914323419136)), (147929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297524942997507/4722366482869645213696), (2650121055445/2361183241434822606848)), (111011/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202678239138345/73786976294838206464), (3642127414129/295147905179352825856)), (152743/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911721747570733/36893488147419103232), (2274988157795/18446744073709551616)), (191085/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455654309354579/2305843009213693952), (5115035278551/4611686018427387904)), (215185/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593859945149933/1152921504606846976), (5110426659959/576460752303423488)), (215453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194464077681355/144115188075855872), (8932881334955/144115188075855872)), (23603/18014398509481984), by norm_num⟩
  | 4 => ⟨((372862347875463/9007199254740992), (13378601572239/36028797018963968)), (283841/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489000029857011/9007199254740992), (16687014266975/9007199254740992)), (88965/2251799813685248), by norm_num⟩
  | 2 => ⟨((139210324142839/281474976710656), (8316352017115/1125899906842624)), (357453/2251799813685248), by norm_num⟩
  | 1 => ⟨((138441345805121/140737488355328), (24813443492951/1125899906842624)), (540171/1125899906842624), by norm_num⟩
  | 0 => ⟨((68061995872283/70368744177664), (6135677778721/140737488355328)), (548183/562949953421312), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((68061995872283/70368744177664), (6135677778721/140737488355328)), (2091152193309593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1051153878203785/1125899906842624), (5934544953575/70368744177664)), (2216449/1125899906842624), by norm_num⟩
  | 2 => ⟨((243340560317167/281474976710656), (177298032421193/1125899906842624)), (4512457/1125899906842624), by norm_num⟩
  | 3 => ⟨((813570953208343/1125899906842624), (613110309935001/2251799813685248)), (9223387/1125899906842624), by norm_num⟩
  | 4 => ⟨((252207869196745/562949953421312), (886062315564973/2251799813685248)), (36704353/2251799813685248), by norm_num⟩
  | 5 => ⟨((206620961666315/4503599627370496), (1587863270800765/4503599627370496)), (123547131/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1100727307060985/9007199254740992), (291398759351113/9007199254740992)), (49228041/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-584120843/16777216)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1210633161/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-51354725473369/9007199254740992), (2110143980326151/18014398509481984)), (344992127/18014398509481984), by norm_num⟩
  | 1 => ⟨((3803125/268435456), (-312537599/1073741824)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((-75603285/4294967296), (388313379/1073741824)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((62622369/4294967296), (-643281665/2147483648)), (27/536870912), by norm_num⟩
  | 4 => ⟨((-77805371/8589934592), (1598494887/8589934592)), (271/8589934592), by norm_num⟩
  | 5 => ⟨((77335633/17179869184), (-1588844229/17179869184)), (17/1073741824), by norm_num⟩
  | 6 => ⟨((-16014319/8589934592), (329010799/8589934592)), (227/34359738368), by norm_num⟩
  | 7 => ⟨((90957915/137438953472), (-58397223/4294967296)), (325/137438953472), by norm_num⟩
  | 8 => ⟨((-28252741/137438953472), (580446591/137438953472)), (51/68719476736), by norm_num⟩
  | 9 => ⟨((62404821/1099511627776), (-1282093861/1099511627776)), (227/1099511627776), by norm_num⟩
  | 10 => ⟨((-31014031/2199023255552), (79647089/274877906944)), (227/4398046511104), by norm_num⟩
  | 11 => ⟨((56048707/17592186044416), (-1151508835/17592186044416)), (207/17592186044416), by norm_num⟩
  | 12 => ⟨((-11606317/17592186044416), (119224665/8796093022208)), (173/70368744177664), by norm_num⟩
  | 13 => ⟨((70992281/562949953421312), (-1458521417/562949953421312)), (267/562949953421312), by norm_num⟩
  | 14 => ⟨((-25201313/1125899906842624), (1035511305/2251799813685248)), (191/2251799813685248), by norm_num⟩
  | 15 => ⟨((66797771/18014398509481984), (-686173047/9007199254740992)), (255/18014398509481984), by norm_num⟩
  | 16 => ⟨((-82993113/144115188075855872), (1705075967/144115188075855872)), (319/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (2109491102183/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778659983855909/633825300114114700748351602688), (1248095177069/316912650057057350374175801344)), (46223/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889619351126117/39614081257132168796771975168), (1403842349819/19807040628566084398385987584)), (52009/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889386620550693/2475880078570760549798248448), (2982512389993/2475880078570760549798248448)), (110537/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885526352018745/77371252455336267181195264), (2981778417669/154742504910672534362390528)), (55279/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387355972427725/2417851639229258349412352), (698659407113/2417851639229258349412352)), (51835/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258675163785613/604462909807314587353088), (2444528520137/604462909807314587353088)), (90733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943803622649259/37778931862957161709568), (992724489265/18889465931478580854784)), (73741/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324350141196579/1180591620717411303424), (1488447843141/2361183241434822606848)), (13831/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405314168436987/147573952589676412928), (2045578051355/295147905179352825856)), (76099/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823234613762755/73786976294838206464), (5110833554745/73786976294838206464)), (190335/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822385908918451/9223372036854775808), (2872705987661/4611686018427387904)), (214247/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398408296916983/288230376151711744), (2870035608143/576460752303423488)), (107199/576460752303423488), by norm_num⟩
  | 5 => ⟨((597135398284449/72057594037927936), (5016559399873/144115188075855872)), (187769/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491169706451349/36028797018963968), (3756423430523/18014398509481984)), (35249/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488668277510497/9007199254740992), (4685051355799/4503599627370496)), (353085/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226755003397831/4503599627370496), (1167341244987/281474976710656)), (707959/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107139362192269/1125899906842624), (6964938222633/562949953421312)), (1066423/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088471547701403/1125899906842624), (27548157026765/1125899906842624)), (537713/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088471547701403/1125899906842624), (27548157026765/1125899906842624)), (2051212312938499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((262903345582525/281474976710656), (106529487863029/2251799813685248)), (4263955/2251799813685248), by norm_num⟩
  | 2 => ⟨((1959416758534017/2251799813685248), (99500705496721/1125899906842624)), (4184343/1125899906842624), by norm_num⟩
  | 3 => ⟨((1687411309368591/2251799813685248), (43290559989247/281474976710656)), (16043277/2251799813685248), by norm_num⟩
  | 4 => ⟨((1211216141426757/2251799813685248), (519044224594401/2251799813685248)), (28979297/2251799813685248), by norm_num⟩
  | 5 => ⟨((1063715901288659/4503599627370496), (1116750679385123/4503599627370496)), (89069605/4503599627370496), by norm_num⟩
  | 6 => ⟨((-51354725473369/9007199254740992), (2110143980326151/18014398509481984)), (344992127/18014398509481984), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1210633161/33554432)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-624814769/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((884579489798381/9007199254740992), (108809412185657/2251799813685248)), (22579163/2251799813685248), by norm_num⟩
  | 1 => ⟨((-270474147/1073741824), (-532323135/4294967296)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((1387504979/4294967296), (341345471/2147483648)), (37/1073741824), by norm_num⟩
  | 3 => ⟨((-1186293335/4294967296), (-583689231/4294967296)), (1/33554432), by norm_num⟩
  | 4 => ⟨((380347791/2147483648), (187141665/2147483648)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((-390229129/4294967296), (-384007115/8589934592)), (11/1073741824), by norm_num⟩
  | 6 => ⟨((166819659/4294967296), (328319601/17179869184)), (153/34359738368), by norm_num⟩
  | 7 => ⟨((-978020519/68719476736), (-120303307/17179869184)), (115/68719476736), by norm_num⟩
  | 8 => ⟨((1254286551/274877906944), (154285945/68719476736)), (75/137438953472), by norm_num⟩
  | 9 => ⟨((-1429858437/1099511627776), (-703530019/1099511627776)), (173/1099511627776), by norm_num⟩
  | 10 => ⟨((45843931/137438953472), (180451887/1099511627776)), (45/1099511627776), by norm_num⟩
  | 11 => ⟨((-85518081/1099511627776), (-673236293/17592186044416)), (85/8796093022208), by norm_num⟩
  | 12 => ⟨((584932125/35184372088832), (287802833/35184372088832)), (37/17592186044416), by norm_num⟩
  | 13 => ⟨((-923274633/281474976710656), (-454276733/281474976710656)), (119/281474976710656), by norm_num⟩
  | 14 => ⟨((1353230101/2251799813685248), (665826751/2251799813685248)), (177/2251799813685248), by norm_num⟩
  | 15 => ⟨((-462795557/4503599627370496), (-227708253/4503599627370496)), (123/9007199254740992), by norm_num⟩
  | 16 => ⟨((1187047167/72057594037927936), (584060137/72057594037927936)), (5/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (297809254113/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222319580846959/79228162514264337593543950336), (352361703849/316912650057057350374175801344)), (46135/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59046977883047/1237940039285380274899124224), (792661206709/39614081257132168796771975168)), (811/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((1889263561774073/2475880078570760549798248448), (421006264787/1237940039285380274899124224)), (110301/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770929930522947/154742504910672534362390528), (841798862549/154742504910672534362390528)), (110307/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549309092444237/9671406556917033397649408), (788959488109/9671406556917033397649408)), (103419/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314643754717305/151115727451828646838272), (690112691733/604462909807314587353088)), (45249/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943722538454021/37778931862957161709568), (1121007941789/75557863725914323419136)), (147071/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297279434256361/4722366482869645213696), (840384102661/4722366482869645213696)), (110313/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621090924043793/590295810358705651712), (288731054441/147573952589676412928)), (151697/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227878579040661/9223372036854775808), (721374989847/36893488147419103232)), (94823/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822155835243877/9223372036854775808), (1621849912191/9223372036854775808)), (106693/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398351294930815/288230376151711744), (810148292799/576460752303423488)), (213429/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194073608656739/144115188075855872), (354003500219/36028797018963968)), (186799/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490878550414969/36028797018963968), (2120534924467/36028797018963968)), (35037/4503599627370496), by norm_num⟩
  | 3 => ⟨((186039050021169/1125899906842624), (2644579133473/9007199254740992)), (87635/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113033671047023/2251799813685248), (1317733516833/1125899906842624)), (701593/4503599627370496), by norm_num⟩
  | 1 => ⟨((138331692688905/140737488355328), (3930497756869/1125899906842624)), (1053681/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175236927658653/2251799813685248), (15541295181993/2251799813685248)), (2112575/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175236927658653/2251799813685248), (15541295181993/2251799813685248)), (8058834084517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2101169975607463/2251799813685248), (15012879465599/1125899906842624)), (4110653/2251799813685248), by norm_num⟩
  | 2 => ⟨((490053966317169/562949953421312), (14008621631825/562949953421312)), (3890491/1125899906842624), by norm_num⟩
  | 3 => ⟨((1704994534344205/2251799813685248), (97557241834243/2251799813685248)), (6967053/1125899906842624), by norm_num⟩
  | 4 => ⟨((1286743576893427/2251799813685248), (147734770295465/2251799813685248)), (5577083/562949953421312), by norm_num⟩
  | 5 => ⟨((1451180038644961/4503599627370496), (84419922946173/1125899906842624)), (56844875/4503599627370496), by norm_num⟩
  | 6 => ⟨((884579489798381/9007199254740992), (108809412185657/2251799813685248)), (22579163/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-624814769/16777216)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1285734543/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((753349946831037/9007199254740992), (-536418285948847/9007199254740992)), (95012805/9007199254740992), by norm_num⟩
  | 1 => ⟨((-948016023/4294967296), (675029091/4294967296)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((1250934317/4294967296), (-890720235/4294967296)), (163/4294967296), by norm_num⟩
  | 3 => ⟨((-550214563/2147483648), (783553921/4294967296)), (73/2147483648), by norm_num⟩
  | 4 => ⟨((726023887/4294967296), (-516960929/4294967296)), (99/4294967296), by norm_num⟩
  | 5 => ⟨((-95800933/1073741824), (545715811/8589934592)), (53/4294967296), by norm_num⟩
  | 6 => ⟨((674197745/17179869184), (-480058437/17179869184)), (95/17179869184), by norm_num⟩
  | 7 => ⟨((-508356143/34359738368), (723943849/68719476736)), (73/34359738368), by norm_num⟩
  | 8 => ⟨((335395251/68719476736), (-238816165/68719476736)), (49/68719476736), by norm_num⟩
  | 9 => ⟨((-393389909/274877906944), (560221823/549755813888)), (117/549755813888), by norm_num⟩
  | 10 => ⟨((415271409/1099511627776), (-591383003/2199023255552)), (125/2199023255552), by norm_num⟩
  | 11 => ⟨((-199259101/2199023255552), (567524963/8796093022208)), (121/8796093022208), by norm_num⟩
  | 12 => ⟨((175285397/8796093022208), (-249621819/17592186044416)), (27/8796093022208), by norm_num⟩
  | 13 => ⟨((-1138678675/281474976710656), (810789281/281474976710656)), (89/140737488355328), by norm_num⟩
  | 14 => ⟨((214645593/281474976710656), (-305674199/562949953421312)), (17/140737488355328), by norm_num⟩
  | 15 => ⟨((-1208452321/9007199254740992), (53779449/562949953421312)), (97/4503599627370496), by norm_num⟩
  | 16 => ⟨((797293739/36028797018963968), (-141927049/9007199254740992)), (65/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-201502140053/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444614479707921/158456325028528675187087900672), (-119193988879/79228162514264337593543950336)), (46147/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889392232636955/39614081257132168796771975168), (-1072533599717/39614081257132168796771975168)), (103837/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944572785821335/1237940039285380274899124224), (-1139302428907/2475880078570760549798248448)), (55167/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770811952452101/154742504910672534362390528), (-1139004964883/154742504910672534362390528)), (55171/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549198500820077/9671406556917033397649408), (-533750603163/4835703278458516698824704)), (51727/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629239132009315/302231454903657293676544), (-7294904125/4722366482869645213696)), (90531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29488873036271/1180591620717411303424), (-758374068889/37778931862957161709568)), (18391/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648580776681565/2361183241434822606848), (-284260857355/1180591620717411303424)), (13795/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620928872029677/590295810358705651712), (-97662123475/36893488147419103232)), (151767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822826118651523/73786976294838206464), (-975991099815/36893488147419103232)), (94871/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56935252437363/288230376151711744), (-2194248467351/9223372036854775808)), (106753/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199147188852945/144115188075855872), (-2192086127301/1152921504606846976)), (53391/288230376151711744), by norm_num⟩
  | 5 => ⟨((298468624459295/36028797018963968), (-957822768223/72057594037927936)), (93467/72057594037927936), by norm_num⟩
  | 4 => ⟨((745290041654491/18014398509481984), (-2868615665213/36028797018963968)), (70133/9007199254740992), by norm_num⟩
  | 3 => ⟨((371984916293333/2251799813685248), (-894323303073/2251799813685248)), (175447/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112661460215933/2251799813685248), (-7129220198183/4503599627370496)), (702479/4503599627370496), by norm_num⟩
  | 1 => ⟨((138262067321687/140737488355328), (-10630634285559/2251799813685248)), (1055455/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173019456711397/2251799813685248), (-10504898809183/1125899906842624)), (2117909/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173019456711397/2251799813685248), (-10504898809183/1125899906842624)), (8079181679732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1048399622150049/1125899906842624), (-40549518415281/2251799813685248)), (1031787/562949953421312), by norm_num⟩
  | 2 => ⟨((1951737796914155/2251799813685248), (-75516659210257/2251799813685248)), (979345/281474976710656), by norm_num⟩
  | 3 => ⟨((844563899279347/1125899906842624), (-130907478703563/2251799813685248)), (14106985/2251799813685248), by norm_num⟩
  | 4 => ⟨((1259444083193991/2251799813685248), (-24549191714731/281474976710656)), (22804169/2251799813685248), by norm_num⟩
  | 5 => ⟨((687285330250273/2251799813685248), (-54921994511959/562949953421312)), (58973569/4503599627370496), by norm_num⟩
  | 6 => ⟨((753349946831037/9007199254740992), (-536418285948847/9007199254740992)), (95012805/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1285734543/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1319347499/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-21649985857511/4503599627370496), (-870310492781387/9007199254740992)), (8923315/562949953421312), by norm_num⟩
  | 1 => ⟨((55913209/4294967296), (280957759/1073741824)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((-4731743/268435456), (-1521695431/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((34170127/2147483648), (686804603/2147483648)), (231/4294967296), by norm_num⟩
  | 4 => ⟨((-92534419/8589934592), (-1859901343/8589934592)), (315/8589934592), by norm_num⟩
  | 5 => ⟨((100235141/17179869184), (1007341241/8589934592)), (343/17179869184), by norm_num⟩
  | 6 => ⟨((-45240299/17179869184), (-1818620433/34359738368)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((70007429/68719476736), (703559347/34359738368)), (243/68719476736), by norm_num⟩
  | 8 => ⟨((-11848977/34359738368), (-1905274031/274877906944)), (331/274877906944), by norm_num⟩
  | 9 => ⟨((28522333/274877906944), (1146572827/549755813888)), (201/549755813888), by norm_num⟩
  | 10 => ⟨((-7723991/274877906944), (-620995355/1099511627776)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((60849325/8796093022208), (1223044797/8796093022208)), (109/4398046511104), by norm_num⟩
  | 12 => ⟨((-13731919/8796093022208), (-276005559/8796093022208)), (99/17592186044416), by norm_num⟩
  | 13 => ⟨((22884139/70368744177664), (459961175/70368744177664)), (83/70368744177664), by norm_num⟩
  | 14 => ⟨((-35412227/562949953421312), (-1423540517/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 15 => ⟨((51145647/4503599627370496), (1028005115/4503599627370496)), (189/4503599627370496), by norm_num⟩
  | 16 => ⟨((-34626245/18014398509481984), (-1391944729/36028797018963968)), (129/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-2110892162355/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778363366945467/633825300114114700748351602688), (-2497054761781/633825300114114700748351602688)), (46223/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472321430917939/9903520314283042199192993792), (-1404306206339/19807040628566084398385987584)), (52009/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889032222219645/2475880078570760549798248448), (-1491719695603/1237940039285380274899124224)), (110537/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770698396643105/154742504910672534362390528), (-745659861657/38685626227668133590597632)), (55279/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549091823133021/9671406556917033397649408), (-349421849435/1208925819614629174706176)), (51835/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629192351058271/302231454903657293676544), (-1222551773781/302231454903657293676544)), (90733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887135426148291/75557863725914323419136), (-3971701252857/75557863725914323419136)), (73741/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40532714337971/147573952589676412928), (-2977383539227/4722366482869645213696)), (13831/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405192646338141/147573952589676412928), (-4091640859123/590295810358705651712)), (76099/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911313694558407/36893488147419103232), (-5111160812953/73786976294838206464)), (1487/576460752303423488), by norm_num⟩
  | 7 => ⟨((455425827882737/2305843009213693952), (-1436349388545/2305843009213693952)), (214249/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796475626450381/576460752303423488), (-1434894868371/288230376151711744)), (214399/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193674848677477/144115188075855872), (-2507796694941/72057594037927936)), (93885/72057594037927936), by norm_num⟩
  | 4 => ⟨((745138636813665/18014398509481984), (-938791187577/4503599627370496)), (281995/36028797018963968), by norm_num⟩
  | 3 => ⟨((743777669947187/4503599627370496), (-9365093423395/9007199254740992)), (176545/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224536928950161/4503599627370496), (-583183799377/140737488355328)), (176993/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105485540740449/1125899906842624), (-13911291833513/1125899906842624)), (1066453/2251799813685248), by norm_num⟩
  | 0 => ⟨((542601371190639/562949953421312), (-54967352486055/2251799813685248)), (2150963/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542601371190639/562949953421312), (-54967352486055/2251799813685248)), (8205272683150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090611487680887/2251799813685248), (-26490241848667/562949953421312)), (265715/140737488355328), by norm_num⟩
  | 2 => ⟨((967987615799099/1125899906842624), (-196752139630505/2251799813685248)), (2073585/562949953421312), by norm_num⟩
  | 3 => ⟨((823627542370645/1125899906842624), (-169156808155705/1125899906842624)), (3927873/562949953421312), by norm_num⟩
  | 4 => ⟨((577092420789145/1125899906842624), (-494971907644079/2251799813685248)), (13853917/1125899906842624), by norm_num⟩
  | 5 => ⟨((482789567955903/2251799813685248), (-1014813251760467/4503599627370496)), (10146231/562949953421312), by norm_num⟩
  | 6 => ⟨((-21649985857511/4503599627370496), (-870310492781387/9007199254740992)), (8923315/562949953421312), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1319347499/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile001Terms1
