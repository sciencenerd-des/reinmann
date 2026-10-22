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
namespace Reinmann.XiBand97.Tile016Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53459/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53459/2560))
  have he : value ((69/80), (53459/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-769795219/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-439045441699213/9007199254740992), (-320158437012939/2251799813685248)), (29367585/1125899906842624), by norm_num⟩
  | 1 => ⟨((229997977/2147483648), (335435861/1073741824)), (249/4294967296), by norm_num⟩
  | 2 => ⟨((-63169651/536870912), (-368513959/1073741824)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((370127759/4294967296), (1079610571/4294967296)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-406626905/8589934592), (-1186073441/8589934592)), (57/2147483648), by norm_num⟩
  | 5 => ⟨((89345063/4294967296), (521213943/8589934592)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((-523496449/68719476736), (-190870681/8589934592)), (149/34359738368), by norm_num⟩
  | 7 => ⟨((164319895/68719476736), (958596003/137438953472)), (189/137438953472), by norm_num⟩
  | 8 => ⟨((-11282741/17179869184), (-1053125349/549755813888)), (209/549755813888), by norm_num⟩
  | 9 => ⟨((176289535/1099511627776), (1028423511/2199023255552)), (103/1099511627776), by norm_num⟩
  | 10 => ⟨((-309878159/8796093022208), (-451935483/4398046511104)), (183/8796093022208), by norm_num⟩
  | 11 => ⟨((495179569/70368744177664), (361092273/17592186044416)), (295/70368744177664), by norm_num⟩
  | 12 => ⟨((-362673573/281474976710656), (-264466939/70368744177664)), (109/140737488355328), by norm_num⟩
  | 13 => ⟨((490384793/2251799813685248), (1430383405/2251799813685248)), (297/2251799813685248), by norm_num⟩
  | 14 => ⟨((-153926503/4503599627370496), (-448981939/4503599627370496)), (47/2251799813685248), by norm_num⟩
  | 15 => ⟨((180379251/36028797018963968), (1052281761/72057594037927936)), (223/72057594037927936), by norm_num⟩
  | 16 => ⟨((-99083431/144115188075855872), (-578024837/288230376151711744)), (247/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-2476360395963/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779041261627497/633825300114114700748351602688), (-1465756010561/316912650057057350374175801344)), (92489/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890048138475403/39614081257132168796771975168), (-1648697530887/19807040628566084398385987584)), (26017/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889842019929813/2475880078570760549798248448), (-437850510247/309485009821345068724781056)), (55297/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221438486614193/19342813113834066795298816), (-3502041271041/154742504910672534362390528)), (55309/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549850405700005/9671406556917033397649408), (-3282353361967/9671406556917033397649408)), (51865/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259048141780801/604462909807314587353088), (-717812259645/151115727451828646838272)), (45395/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944106457835857/37778931862957161709568), (-2332130512801/37778931862957161709568)), (147581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648927225620239/2361183241434822606848), (-3496867314921/4722366482869645213696)), (13841/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405470043172299/147573952589676412928), (-4806034523027/590295810358705651712)), (152319/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912006547822497/36893488147419103232), (-6004307331927/73786976294838206464)), (190501/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823260475802441/9223372036854775808), (-6750398493131/9223372036854775808)), (214455/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594506224484989/1152921504606846976), (-6744842423665/1152921504606846976)), (26829/144115188075855872), by norm_num⟩
  | 5 => ⟨((597516492242889/72057594037927936), (-5895490667049/144115188075855872)), (94001/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492309554796189/36028797018963968), (-2207688351107/9007199254740992)), (141201/18014398509481984), by norm_num⟩
  | 3 => ⟨((186260886331733/1125899906842624), (-11016620412209/9007199254740992)), (88425/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114787341674611/2251799813685248), (-10983934796441/2251799813685248)), (709497/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109231768831245/1125899906842624), (-16394350548987/1125899906842624)), (1069499/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185134849230303/2251799813685248), (-8115867210713/281474976710656)), (2160081/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185134849230303/2251799813685248), (-8115867210713/281474976710656)), (8240055092818450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2118571452528915/2251799813685248), (-31502381634593/562949953421312)), (1079207/562949953421312), by norm_num⟩
  | 2 => ⟨((993087078946975/1125899906842624), (-118554137916007/1125899906842624)), (8605979/2251799813685248), by norm_num⟩
  | 3 => ⟨((107932203480757/140737488355328), (-209138630893485/1125899906842624)), (16993983/2251799813685248), by norm_num⟩
  | 4 => ⟨((1246682949147159/2251799813685248), (-641557371218441/2251799813685248)), (16189435/1125899906842624), by norm_num⟩
  | 5 => ⟨((507426329900769/2251799813685248), (-88797706476485/281474976710656)), (13575605/562949953421312), by norm_num⟩
  | 6 => ⟨((-439045441699213/9007199254740992), (-320158437012939/2251799813685248)), (29367585/1125899906842624), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-769795219/16777216)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-12604815/262144)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-354663902839909/4503599627370496), (1012448392744523/9007199254740992)), (222798149/9007199254740992), by norm_num⟩
  | 1 => ⟨((778812233/4294967296), (-555812973/2147483648)), (247/4294967296), by norm_num⟩
  | 2 => ⟨((-56040045/268435456), (639903333/2147483648)), (9/134217728), by norm_num⟩
  | 3 => ⟨((688197185/4294967296), (-982287917/4294967296)), (223/4294967296), by norm_num⟩
  | 4 => ⟨((-396158145/4294967296), (565450379/4294967296)), (65/2147483648), by norm_num⟩
  | 5 => ⟨((729750271/17179869184), (-1041598091/17179869184)), (121/8589934592), by norm_num⟩
  | 6 => ⟨((-17503251/1073741824), (799456079/34359738368)), (47/8589934592), by norm_num⟩
  | 7 => ⟨((736964111/137438953472), (-1051894657/137438953472)), (125/68719476736), by norm_num⟩
  | 8 => ⟨((-106057661/68719476736), (605519239/274877906944)), (291/549755813888), by norm_num⟩
  | 9 => ⟨((434145403/1099511627776), (-1239341843/2199023255552)), (75/549755813888), by norm_num⟩
  | 10 => ⟨((-799725387/8796093022208), (1141476021/8796093022208)), (279/8796093022208), by norm_num⟩
  | 11 => ⟨((334806501/17592186044416), (-477881031/17592186044416)), (59/8796093022208), by norm_num⟩
  | 12 => ⟨((-128486743/35184372088832), (183393623/35184372088832)), (183/140737488355328), by norm_num⟩
  | 13 => ⟨((364125119/562949953421312), (-64966065/70368744177664)), (261/1125899906842624), by norm_num⟩
  | 14 => ⟨((-239551163/2251799813685248), (341919755/2251799813685248)), (87/2251799813685248), by norm_num⟩
  | 15 => ⟨((588359399/36028797018963968), (-839785953/36028797018963968)), (27/4503599627370496), by norm_num⟩
  | 16 => ⟨((-677373791/288230376151711744), (241709827/72057594037927936)), (251/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (2842206322709/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778899683817397/633825300114114700748351602688), (1682047734667/316912650057057350374175801344)), (92531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889888808744057/39614081257132168796771975168), (3783937536981/39614081257132168796771975168)), (104119/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59052270567175/77371252455336267181195264), (2009808909339/1237940039285380274899124224)), (110651/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442834612010409/38685626227668133590597632), (1004675040235/38685626227668133590597632)), (110679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549691462925267/9671406556917033397649408), (1883278283973/4835703278458516698824704)), (103791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629454489366433/302231454903657293676544), (1647381182269/302231454903657293676544)), (90847/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887986610679133/75557863725914323419136), (5352161832759/75557863725914323419136)), (147681/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324421144567899/1180591620717411303424), (4012523167383/4722366482869645213696)), (110809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202705795417429/73786976294838206464), (2757311533893/295147905179352825856)), (152441/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823720483538559/73786976294838206464), (6727915823/72057594037927936)), (47667/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822930806341947/9223372036854775808), (968151047889/1152921504606846976)), (26833/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797087977725299/576460752303423488), (1934630872187/288230376151711744)), (214867/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194743326588575/144115188075855872), (6763692239235/144115188075855872)), (188237/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491873728030233/36028797018963968), (10130518468119/36028797018963968)), (282813/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489539973710421/9007199254740992), (1579611211777/1125899906842624)), (177159/4503599627370496), by norm_num⟩
  | 2 => ⟨((34819898350031/70368744177664), (6298777486161/1125899906842624)), (355523/2251799813685248), by norm_num⟩
  | 1 => ⟨((554198631258855/562949953421312), (18798180807837/1125899906842624)), (536301/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090864427122639/1125899906842624), (18602433475677/562949953421312)), (1084709/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090864427122639/1125899906842624), (18602433475677/562949953421312)), (4137836460593795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527844877245769/562949953421312), (72094269883861/1125899906842624)), (2173599/1125899906842624), by norm_num⟩
  | 2 => ⟨((246310366322681/281474976710656), (67598533059101/562949953421312)), (8708947/2251799813685248), by norm_num⟩
  | 3 => ⟨((845921109374753/1125899906842624), (473227698894989/2251799813685248)), (17333407/2251799813685248), by norm_num⟩
  | 4 => ⟨((1171678593322147/2251799813685248), (355549634211015/1125899906842624)), (33331595/2251799813685248), by norm_num⟩
  | 5 => ⟨((770200398124937/4503599627370496), (740012309685351/2251799813685248)), (111477033/4503599627370496), by norm_num⟩
  | 6 => ⟨((-354663902839909/4503599627370496), (1012448392744523/9007199254740992)), (222798149/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-12604815/262144)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-840099977/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((139725575121543/1125899906842624), (27107054981761/1125899906842624)), (83936539/9007199254740992), by norm_num⟩
  | 1 => ⟨((-319526001/1073741824), (-247954861/4294967296)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1532379775/4294967296), (297284895/4294967296)), (15/536870912), by norm_num⟩
  | 3 => ⟨((-306207185/1073741824), (-59404837/1073741824)), (49/2147483648), by norm_num⟩
  | 4 => ⟨((1468505523/8589934592), (71223289/2147483648)), (15/1073741824), by norm_num⟩
  | 5 => ⟨((-1408528981/17179869184), (-273257581/17179869184)), (117/17179869184), by norm_num⟩
  | 6 => ⟨((1125834995/34359738368), (109207177/17179869184)), (95/34359738368), by norm_num⟩
  | 7 => ⟨((-385662059/34359738368), (-149638499/68719476736)), (133/137438953472), by norm_num⟩
  | 8 => ⟨((231194307/68719476736), (179408725/274877906944)), (41/137438953472), by norm_num⟩
  | 9 => ⟨((-985563975/1099511627776), (-95600741/549755813888)), (89/1099511627776), by norm_num⟩
  | 10 => ⟨((945311679/4398046511104), (45848113/1099511627776)), (87/4398046511104), by norm_num⟩
  | 11 => ⟨((-103034473/2199023255552), (-79955617/8796093022208)), (77/17592186044416), by norm_num⟩
  | 12 => ⟨((1317684671/140737488355328), (255633595/140737488355328)), (125/140737488355328), by norm_num⟩
  | 13 => ⟨((-486103053/281474976710656), (-188610027/562949953421312)), (47/281474976710656), by norm_num⟩
  | 14 => ⟨((666070979/2251799813685248), (129219169/2251799813685248)), (131/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1703646349/36028797018963968), (-165255485/18014398509481984)), (85/18014398509481984), by norm_num⟩
  | 16 => ⟨((510645691/72057594037927936), (198132673/144115188075855872)), (13/18014398509481984), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (3900136365/158456325028528675187087900672)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778958247073/633825300114114700748351602688), (147701044229/316912650057057350374175801344)), (46115/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59054792448487/1237940039285380274899124224), (10383355569/1237940039285380274899124224)), (6485/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889529215170265/2475880078570760549798248448), (352959628997/2475880078570760549798248448)), (110247/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771195536870309/154742504910672534362390528), (176437946283/77371252455336267181195264)), (55125/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774779024207479/4835703278458516698824704), (330732207373/9671406556917033397649408)), (51681/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157349100671787/75557863725914323419136), (289301771107/604462909807314587353088)), (90445/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471949721577231/18889465931478580854784), (469948738201/75557863725914323419136)), (146977/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648772354684233/2361183241434822606848), (352315810797/4722366482869645213696)), (110237/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621455544215111/590295810358705651712), (484197533291/590295810358705651712)), (151583/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455871051987939/18446744073709551616), (151223019105/18446744073709551616)), (189489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822668083510925/9223372036854775808), (680016037365/9223372036854775808)), (213189/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593917085279859/1152921504606846976), (339703568077/576460752303423488)), (26651/144115188075855872), by norm_num⟩
  | 5 => ⟨((597260570358793/72057594037927936), (593796964561/144115188075855872)), (93289/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491549078523913/36028797018963968), (889328721275/36028797018963968)), (279907/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489149214231059/9007199254740992), (554636625765/4503599627370496)), (349957/9007199254740992), by norm_num⟩
  | 2 => ⟨((556934234392527/1125899906842624), (2211400002215/4503599627370496)), (700135/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107900707061945/1125899906842624), (1649645596009/1125899906842624)), (525381/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180185458360169/2251799813685248), (3263845365411/1125899906842624)), (1051901/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180185458360169/2251799813685248), (3263845365411/1125899906842624)), (4012683872703170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2110829743040049/2251799813685248), (3160044760977/562949953421312)), (4085987/2251799813685248), by norm_num⟩
  | 2 => ⟨((1978613908260599/2251799813685248), (2962215570971/281474976710656)), (7706255/2251799813685248), by norm_num⟩
  | 3 => ⟨((217290153415461/281474976710656), (41645484770849/2251799813685248)), (13704881/2251799813685248), by norm_num⟩
  | 4 => ⟨((1341161112372517/2251799813685248), (8037263099431/281474976710656)), (21666431/2251799813685248), by norm_num⟩
  | 5 => ⟨((1593906236383447/4503599627370496), (153182564856471/4503599627370496)), (27046175/2251799813685248), by norm_num⟩
  | 6 => ⟨((139725575121543/1125899906842624), (27107054981761/1125899906842624)), (83936539/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-840099977/16777216)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-870584317/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-28818059149067/4503599627370496), (-2109495001295465/18014398509481984)), (43195623/2251799813685248), by norm_num⟩
  | 1 => ⟨((17073199/1073741824), (624882955/2147483648)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((-84850611/4294967296), (-776387905/2147483648)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((70281949/4294967296), (1286167645/4294967296)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-87322041/8589934592), (-1598003267/8589934592)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((2712339/536870912), (1588355577/17179869184)), (271/17179869184), by norm_num⟩
  | 6 => ⟨((-71892365/34359738368), (-1315638445/34359738368)), (113/17179869184), by norm_num⟩
  | 7 => ⟨((102083323/137438953472), (1868136411/137438953472)), (81/34359738368), by norm_num⟩
  | 8 => ⟨((-31708441/137438953472), (-1160536147/274877906944)), (203/274877906944), by norm_num⟩
  | 9 => ⟨((2188681/34359738368), (640849775/549755813888)), (113/549755813888), by norm_num⟩
  | 10 => ⟨((-34807475/2199023255552), (-636980747/2199023255552)), (227/4398046511104), by norm_num⟩
  | 11 => ⟨((62904237/17592186044416), (575577343/8796093022208)), (207/17592186044416), by norm_num⟩
  | 12 => ⟨((-52103719/70368744177664), (-476751989/35184372088832)), (345/140737488355328), by norm_num⟩
  | 13 => ⟨((79675617/562949953421312), (729036423/281474976710656)), (133/281474976710656), by norm_num⟩
  | 14 => ⟨((-56567563/2251799813685248), (-1035192831/2251799813685248)), (191/2251799813685248), by norm_num⟩
  | 15 => ⟨((18742015/4503599627370496), (685962013/9007199254740992)), (255/18014398509481984), by norm_num⟩
  | 16 => ⟨((-93144315/144115188075855872), (-1704551567/144115188075855872)), (319/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1058623698647/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222332494909751/79228162514264337593543950336), (-2505368486731/633825300114114700748351602688)), (92447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236202415261773/4951760157141521099596496896), (-2818008113085/39614081257132168796771975168)), (52009/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889386587898891/2475880078570760549798248448), (-1496739306351/1237940039285380274899124224)), (55269/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771052669356341/154742504910672534362390528), (-46761592749/2417851639229258349412352)), (110559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774711927521279/4835703278458516698824704), (-2804913053769/9671406556917033397649408)), (103671/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258675131297647/604462909807314587353088), (-2453516644689/604462909807314587353088)), (45367/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943803594235887/37778931862957161709568), (-1992749137155/37778931862957161709568)), (36871/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162175064830009/590295810358705651712), (-746960303299/1180591620717411303424)), (110649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621256604573157/590295810358705651712), (-2053099274319/295147905179352825856)), (19025/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823234518719811/73786976294838206464), (-5129625135005/73786976294838206464)), (190339/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911192895111643/4611686018427387904), (-1441634181817/2305843009213693952)), (53563/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398408263571239/288230376151711744), (-5761176256287/1152921504606846976)), (214403/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597135331686047/72057594037927936), (-1258751036191/36028797018963968)), (187773/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491169473775323/36028797018963968), (-1885117418821/9007199254740992)), (17625/2251799813685248), by norm_num⟩
  | 3 => ⟨((1488667929331957/9007199254740992), (-9404553760145/9007199254740992)), (176549/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226754135870047/4503599627370496), (-18746129854531/4503599627370496)), (707991/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107138499030989/1125899906842624), (-1747636140551/140737488355328)), (133311/281474976710656), by norm_num⟩
  | 0 => ⟨((2176937959941593/2251799813685248), (-55298851792513/2251799813685248)), (268881/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176937959941593/2251799813685248), (-55298851792513/2251799813685248)), (1025699616552257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2103206905712571/2251799813685248), (-106920845162777/2251799813685248)), (2132361/1125899906842624), by norm_num⟩
  | 2 => ⟨((979671282121225/1125899906842624), (-99865298213587/1125899906842624)), (4185799/1125899906842624), by norm_num⟩
  | 3 => ⟨((421788267968351/562949953421312), (-347580328040647/2251799813685248)), (8026865/1125899906842624), by norm_num⟩
  | 4 => ⟨((605221074032829/1125899906842624), (-65105833854833/281474976710656)), (29012403/2251799813685248), by norm_num⟩
  | 5 => ⟨((530193195698063/2251799813685248), (-279978157574767/1125899906842624)), (89224361/4503599627370496), by norm_num⟩
  | 6 => ⟨((-28818059149067/4503599627370496), (-2109495001295465/18014398509481984)), (43195623/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-870584317/16777216)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-112328399/2097152)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-486997421203715/4503599627370496), (76234394499315/4503599627370496)), (250050377/9007199254740992), by norm_num⟩
  | 1 => ⟨((297814303/1073741824), (-186478959/4294967296)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((-763878605/2147483648), (239154543/4294967296)), (397/4294967296), by norm_num⟩
  | 3 => ⟨((1306206625/4294967296), (-204473097/4294967296)), (341/4294967296), by norm_num⟩
  | 4 => ⟨((-837588461/4294967296), (262231569/8589934592)), (55/1073741824), by norm_num⟩
  | 5 => ⟨((429674397/4294967296), (-134522139/8589934592)), (227/8589934592), by norm_num⟩
  | 6 => ⟨((-1469457425/34359738368), (57507079/8589934592)), (195/17179869184), by norm_num⟩
  | 7 => ⟨((269220277/17179869184), (-84287283/34359738368)), (9/2147483648), by norm_num⟩
  | 8 => ⟨((-1381072753/274877906944), (54048153/68719476736)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((787195927/549755813888), (-30806839/137438953472)), (213/549755813888), by norm_num⟩
  | 10 => ⟨((-807647075/2199023255552), (126428771/2199023255552)), (439/4398046511104), by norm_num⟩
  | 11 => ⟨((1506599161/17592186044416), (-235842469/17592186044416)), (411/17592186044416), by norm_num⟩
  | 12 => ⟨((-644058425/35184372088832), (100820665/35184372088832)), (353/70368744177664), by norm_num⟩
  | 13 => ⟨((1016601381/281474976710656), (-4973075/8796093022208)), (35/35184372088832), by norm_num⟩
  | 14 => ⟨((-372504437/562949953421312), (233246821/2251799813685248)), (103/562949953421312), by norm_num⟩
  | 15 => ⟨((509576009/4503599627370496), (-39884419/2251799813685248)), (71/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1307036657/72057594037927936), (102301515/36028797018963968)), (183/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (3890006366535/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778545568229673/633825300114114700748351602688), (2301287237327/316912650057057350374175801344)), (138979/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944745104143513/19807040628566084398385987584), (5176867163155/39614081257132168796771975168)), (39099/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889248846581149/2475880078570760549798248448), (5499176687817/2475880078570760549798248448)), (166221/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770914300932935/154742504910672534362390528), (5497776475939/154742504910672534362390528)), (83139/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387323367204441/2417851639229258349412352), (5152677923171/9671406556917033397649408)), (77973/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258560378053679/604462909807314587353088), (4507105886493/604462909807314587353088)), (68257/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887419468144939/75557863725914323419136), (7321258867289/75557863725914323419136)), (221947/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297258639004191/4722366482869645213696), (5488504959745/4722366482869645213696)), (166561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621059751924805/590295810358705651712), (7542731540947/590295810358705651712)), (114591/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911492902188863/36893488147419103232), (9422471846101/73786976294838206464)), (286719/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822102350852413/9223372036854775808), (2648028090905/2305843009213693952)), (322893/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398336269807243/288230376151711744), (10581905667951/1152921504606846976)), (161655/576460752303423488), by norm_num⟩
  | 5 => ⟨((597006797447173/72057594037927936), (4623845138781/72057594037927936)), (141683/72057594037927936), by norm_num⟩
  | 4 => ⟨((186346715158661/4503599627370496), (6924297231265/18014398509481984)), (425989/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488155545807291/9007199254740992), (4317656668071/2251799813685248)), (534135/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112838283297271/2251799813685248), (17210512816297/2251799813685248)), (134153/562949953421312), by norm_num⟩
  | 1 => ⟨((553132400968803/562949953421312), (25665698232651/1125899906842624)), (811125/1125899906842624), by norm_num⟩
  | 0 => ⟨((543231195985789/562949953421312), (50732402445037/1125899906842624)), (205897/140737488355328), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543231195985789/562949953421312), (50732402445037/1125899906842624)), (785434723437261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1046120303725535/1125899906842624), (97910741400575/1125899906842624)), (1663701/562949953421312), by norm_num⟩
  | 2 => ⟨((963479231139881/1125899906842624), (22743232748637/140737488355328)), (1690493/281474976710656), by norm_num⟩
  | 3 => ⟨((1590173205810681/2251799813685248), (622794470993203/2251799813685248)), (27516949/2251799813685248), by norm_num⟩
  | 4 => ⟨((118837044170623/281474976710656), (439804228813591/1125899906842624)), (13521211/562949953421312), by norm_num⟩
  | 5 => ⟨((115563130240489/4503599627370496), (1485461625803381/4503599627370496)), (43961169/1125899906842624), by norm_num⟩
  | 6 => ⟨((-486997421203715/4503599627370496), (76234394499315/4503599627370496)), (250050377/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-112328399/2097152)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1849181677/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((60877601894195/4503599627370496), (1833528172939901/18014398509481984)), (286098435/18014398509481984), by norm_num⟩
  | 1 => ⟨((-153216821/4294967296), (-576828237/2147483648)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((202173987/4294967296), (761141393/2147483648)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((-177849581/4294967296), (-669565257/2147483648)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((58669405/2147483648), (1767021099/8589934592)), (143/4294967296), by norm_num⟩
  | 5 => ⟨((-247731077/17179869184), (-1865307993/17179869184)), (19/1073741824), by norm_num⟩
  | 6 => ⟨((217925505/34359738368), (820442455/17179869184)), (135/17179869184), by norm_num⟩
  | 7 => ⟨((-20539925/8589934592), (-1237254099/68719476736)), (103/34359738368), by norm_num⟩
  | 8 => ⟨((108412079/137438953472), (1632592249/274877906944)), (137/137438953472), by norm_num⟩
  | 9 => ⟨((-127158085/549755813888), (-957445453/549755813888)), (81/274877906944), by norm_num⟩
  | 10 => ⟨((67115495/1099511627776), (15792209/34359738368)), (173/2199023255552), by norm_num⟩
  | 11 => ⟨((-128815737/8796093022208), (-969926863/8796093022208)), (21/1099511627776), by norm_num⟩
  | 12 => ⟨((226634743/70368744177664), (1706461731/70368744177664)), (149/35184372088832), by norm_num⟩
  | 13 => ⟨((-184031409/281474976710656), (-1385677027/281474976710656)), (61/70368744177664), by norm_num⟩
  | 14 => ⟨((138762697/1125899906842624), (1044823175/1125899906842624)), (93/562949953421312), by norm_num⟩
  | 15 => ⟨((-195308113/9007199254740992), (-1470585737/9007199254740992)), (33/1125899906842624), by norm_num⟩
  | 16 => ⟨((128857327/36028797018963968), (970240017/36028797018963968)), (11/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (1874144591707/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444613943156597/158456325028528675187087900672), (1108607429989/316912650057057350374175801344)), (92419/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889389698330171/39614081257132168796771975168), (2493870058013/39614081257132168796771975168)), (103985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889142721383433/2475880078570760549798248448), (2649121518339/2475880078570760549798248448)), (27625/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770808925106735/154742504910672534362390528), (2648429407285/154742504910672534362390528)), (110519/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549195474661041/9671406556917033397649408), (1241083711769/4835703278458516698824704)), (103631/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258475428254471/604462909807314587353088), (2171161599761/604462909807314587353088)), (11337/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887282914252727/75557863725914323419136), (3526760200909/75557863725914323419136)), (73709/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648578762833667/2361183241434822606848), (2643865457611/4722366482869645213696)), (110595/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810461417306665/295147905179352825856), (3633358372807/590295810358705651712)), (19015/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911408911953079/36893488147419103232), (4538764759031/73786976294838206464)), (47557/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910958859804319/4611686018427387904), (1275520005125/2305843009213693952)), (107057/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593165871436005/1152921504606846976), (637130792541/144115188075855872)), (26781/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193862875676331/144115188075855872), (4454258478545/144115188075855872)), (93809/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490559783231169/36028797018963968), (3335044059317/18014398509481984)), (2201/281474976710656), by norm_num⟩
  | 3 => ⟨((1487909292323109/9007199254740992), (4158934263599/4503599627370496)), (352691/9007199254740992), by norm_num⟩
  | 2 => ⟨((278155907263281/562949953421312), (8288321360699/2251799813685248)), (176743/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106021279684799/1125899906842624), (6179421074487/562949953421312)), (532225/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086285960056577/1125899906842624), (48848979294377/2251799813685248)), (1072467/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086285960056577/1125899906842624), (48848979294377/2251799813685248)), (4091136936668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523767976244433/562949953421312), (94260528929937/2251799813685248)), (2115997/1125899906842624), by norm_num⟩
  | 2 => ⟨((972653344469359/1125899906842624), (175399771071351/2251799813685248)), (8229189/2251799813685248), by norm_num⟩
  | 3 => ⟨((1666867992228409/2251799813685248), (151526057436255/1125899906842624)), (15500219/2251799813685248), by norm_num⟩
  | 4 => ⟨((298273441411075/562949953421312), (14020669910023/70368744177664)), (27119813/2251799813685248), by norm_num⟩
  | 5 => ⟨((1085510036045225/4503599627370496), (950875224805547/4503599627370496)), (79090681/4503599627370496), by norm_num⟩
  | 6 => ⟨((60877601894195/4503599627370496), (1833528172939901/18014398509481984)), (286098435/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1849181677/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1897524831/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1742770515729489/18014398509481984), (-3448925573311/18014398509481984)), (26993949/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1125218879/4294967296), (2226797/4294967296)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((761787303/2147483648), (-3015139/4294967296)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-687652753/2147483648), (680429/1073741824)), (45/2147483648), by norm_num⟩
  | 4 => ⟨((58193693/268435456), (-460659/1073741824)), (31/2147483648), by norm_num⟩
  | 5 => ⟨((-1008585229/8589934592), (3991961/17179869184)), (137/17179869184), by norm_num⟩
  | 6 => ⟨((113804143/2147483648), (-3603477/34359738368)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((-176107047/8589934592), (2788113/68719476736)), (99/68719476736), by norm_num⟩
  | 8 => ⟨((119226681/17179869184), (-3775175/274877906944)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((-1147988755/549755813888), (2271859/549755813888)), (21/137438953472), by norm_num⟩
  | 10 => ⟨((1243524471/2199023255552), (-2460923/2199023255552)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((-1224555161/8796093022208), (2423383/8796093022208)), (93/8796093022208), by norm_num⟩
  | 12 => ⟨((1105385617/35184372088832), (-546887/8796093022208)), (43/17592186044416), by norm_num⟩
  | 13 => ⟨((-460529191/70368744177664), (911383/70368744177664)), (73/140737488355328), by norm_num⟩
  | 14 => ⟨((712649239/562949953421312), (-705163/281474976710656)), (115/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1029274621/4503599627370496), (4073849/9007199254740992)), (169/9007199254740992), by norm_num⟩
  | 16 => ⟨((174207959/4503599627370496), (-2758047/36028797018963968)), (29/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-2577852177/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778366707484359/633825300114114700748351602688), (-1524719777/316912650057057350374175801344)), (92201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644833851439/19807040628566084398385987584), (-857481185/9903520314283042199192993792)), (51863/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889036657921895/2475880078570760549798248448), (-1821713569/1237940039285380274899124224)), (110209/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770703107891881/154742504910672534362390528), (-1821225591/77371252455336267181195264)), (55105/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549096532487357/9671406556917033397649408), (-3413761399/9671406556917033397649408)), (103321/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78649319695267/37778931862957161709568), (-2986005057/604462909807314587353088)), (45203/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887143144889883/75557863725914323419136), (-2425158145/37778931862957161709568)), (73455/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297053126524159/4722366482869645213696), (-1818019457/2361183241434822606848)), (110183/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779980325613/590295810358705651712), (-2498397711/295147905179352825856)), (151501/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822640296502955/73786976294838206464), (-6241860047/73786976294838206464)), (189377/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821719429724735/9223372036854775808), (-1754103173/2305843009213693952)), (106525/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592969363837723/1152921504606846976), (-1752329979/288230376151711744)), (213051/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193692932109229/144115188075855872), (-3062592619/72057594037927936)), (46605/36028797018963968), by norm_num⟩
  | 4 => ⟨((372577214459619/9007199254740992), (-9171862659/36028797018963968)), (279633/36028797018963968), by norm_num⟩
  | 3 => ⟨((743801296426347/4503599627370496), (-5718515521/4503599627370496)), (174773/4503599627370496), by norm_num⟩
  | 2 => ⟨((556163657656701/1125899906842624), (-22790887059/4503599627370496)), (699109/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105602598404495/1125899906842624), (-33979149921/2251799813685248)), (1048715/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085550709734433/1125899906842624), (-33567051389/1125899906842624)), (2097683/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085550709734433/1125899906842624), (-33567051389/1125899906842624)), (8002025612837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093295034694237/2251799813685248), (-8091024841/140737488355328)), (4045141/2251799813685248), by norm_num⟩
  | 2 => ⟨((972973720595813/1125899906842624), (-60171963857/562949953421312)), (7521271/2251799813685248), by norm_num⟩
  | 3 => ⟨((840818833658295/1125899906842624), (-207996249733/1125899906842624)), (6500493/1125899906842624), by norm_num⟩
  | 4 => ⟨((627921064275277/1125899906842624), (-621324020165/2251799813685248)), (19423003/2251799813685248), by norm_num⟩
  | 5 => ⟨((1400780883108553/4503599627370496), (-1386064383275/4503599627370496)), (43350735/4503599627370496), by norm_num⟩
  | 6 => ⟨((1742770515729489/18014398509481984), (-3448925573311/18014398509481984)), (26993949/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1897524831/33554432)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile016Terms1
