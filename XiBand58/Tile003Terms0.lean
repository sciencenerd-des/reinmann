/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile003Terms0
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
  | 0 => ⟨((15/16), (2501/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2501/160))
  have he : value ((15/16), (2501/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-21804525/33554432), (-727108225/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47066691616135/562949953421312), (1160576753849049/2251799813685248)), (48271745/2251799813685248), by norm_num⟩
  | 1 => ⟨((124451235/2147483648), (-1534367571/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((-172526045/8589934592), (265885639/2147483648)), (3/536870912), by norm_num⟩
  | 3 => ⟨((79723961/17179869184), (-61432627/2147483648)), (23/17179869184), by norm_num⟩
  | 4 => ⟨((-221041755/274877906944), (681309635/137438953472)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((245143151/2199023255552), (-188899141/274877906944)), (75/2199023255552), by norm_num⟩
  | 6 => ⟨((-226560379/17592186044416), (43644969/549755813888)), (71/17592186044416), by norm_num⟩
  | 7 => ⟨((179473929/140737488355328), (-553186509/70368744177664)), (29/70368744177664), by norm_num⟩
  | 8 => ⟨((-15550231/140737488355328), (383439669/562949953421312)), (83/2251799813685248), by norm_num⟩
  | 9 => ⟨((153295627/18014398509481984), (-472498001/9007199254740992)), (53/18014398509481984), by norm_num⟩
  | 10 => ⟨((-170010291/288230376151711744), (1048034103/288230376151711744)), (61/288230376151711744), by norm_num⟩
  | 11 => ⟨((171406769/4611686018427387904), (-264160685/1152921504606846976)), (63/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-39603373/18446744073709551616), (30517039/2305843009213693952)), (15/18446744073709551616), by norm_num⟩
  | 13 => ⟨((135143219/1180591620717411303424), (-1666189749/2361183241434822606848)), (105/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-214112323/37778931862957161709568), (1319902545/37778931862957161709568)), (85/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((158305443/604462909807314587353088), (-121984897/75557863725914323419136)), (65/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-219457943/19342813113834066795298816), (1352855799/19342813113834066795298816)), (23/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (1127810121395/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890482138711673/316912650057057350374175801344), (2675686226761/633825300114114700748351602688)), (23117/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946105659037671/19807040628566084398385987584), (3009964354349/39614081257132168796771975168)), (13005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118258759747715/154742504910672534362390528), (1598937100319/1237940039285380274899124224)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773805756229181/154742504910672534362390528), (3197634616753/154742504910672534362390528)), (13823/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776002181351513/4835703278458516698824704), (2997527861105/9671406556917033397649408)), (6481/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78808285262433/37778931862957161709568), (1311291123939/302231454903657293676544)), (11345/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891274558206025/75557863725914323419136), (532652329839/9444732965739290427392)), (36881/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650075103506081/2361183241434822606848), (798874018131/1180591620717411303424)), (13835/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50782376961003/18446744073709551616), (137285245269/18446744073709551616)), (19031/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57123649884887/2305843009213693952), (343149416657/4611686018427387904)), (47601/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827695540263271/9223372036854775808), (3087643871055/4611686018427387904)), (53583/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199867411087271/144115188075855872), (6173534894167/1152921504606846976)), (53623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198909662986897/144115188075855872), (5399870184859/144115188075855872)), (46965/144115188075855872), by norm_num⟩
  | 4 => ⟨((374530015294273/9007199254740992), (8095857351945/36028797018963968)), (35269/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497342315278131/9007199254740992), (1264113476593/1125899906842624)), (44165/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122030676982137/2251799813685248), (10102527006953/2251799813685248)), (11071/281474976710656), by norm_num⟩
  | 1 => ⟨((1120066955265303/1125899906842624), (15127803646377/1125899906842624)), (133447/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114117976161365/1125899906842624), (30151451662365/1125899906842624)), (269275/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114117976161365/1125899906842624), (30151451662365/1125899906842624)), (1027202610496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101651885065767/1125899906842624), (59671866211633/1125899906842624)), (273669/562949953421312), by norm_num⟩
  | 2 => ⟨((537381758759183/562949953421312), (116773477816135/1125899906842624)), (564559/562949953421312), by norm_num⟩
  | 3 => ⟨((1013838411860469/1125899906842624), (222939664543493/1125899906842624)), (1194943/562949953421312), by norm_num⟩
  | 4 => ⟨((868786137552917/1125899906842624), (401500691256517/1125899906842624)), (5250483/1125899906842624), by norm_num⟩
  | 5 => ⟨((527210761913337/1125899906842624), (309812828530887/562949953421312)), (11847625/1125899906842624), by norm_num⟩
  | 6 => ⟨((-47066691616135/562949953421312), (1160576753849049/2251799813685248)), (48271745/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-727108225/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-69118709/67108864), (-1152439271/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-85120075485129/2251799813685248), (399715170404543/1125899906842624)), (131014491/4503599627370496), by norm_num⟩
  | 1 => ⟨((89181863/2147483648), (-1675155633/4294967296)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((-195952581/8589934592), (460086641/2147483648)), (157/8589934592), by norm_num⟩
  | 3 => ⟨((35879319/4294967296), (-1347884901/17179869184)), (117/17179869184), by norm_num⟩
  | 4 => ⟨((-157669843/68719476736), (370200729/17179869184)), (131/68719476736), by norm_num⟩
  | 5 => ⟨((69287211/137438953472), (-1301462625/274877906944)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-50746521/549755813888), (953201889/1099511627776)), (87/1099511627776), by norm_num⟩
  | 7 => ⟨((127430289/8796093022208), (-598399605/4398046511104)), (7/549755813888), by norm_num⟩
  | 8 => ⟨((-139996481/70368744177664), (82176145/4398046511104)), (63/35184372088832), by norm_num⟩
  | 9 => ⟨((136712759/562949953421312), (-1283978279/562949953421312)), (125/562949953421312), by norm_num⟩
  | 10 => ⟨((-60077727/2251799813685248), (1128475453/4503599627370496)), (7/281474976710656), by norm_num⟩
  | 11 => ⟨((96003097/36028797018963968), (-901641455/36028797018963968)), (181/72057594037927936), by norm_num⟩
  | 12 => ⟨((-70313455/288230376151711744), (1320739177/576460752303423488)), (135/576460752303423488), by norm_num⟩
  | 13 => ⟨((190147017/9223372036854775808), (-223227737/1152921504606846976)), (185/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-14921275/9223372036854775808), (1121100503/73786976294838206464)), (59/36893488147419103232), by norm_num⟩
  | 15 => ⟨((34971085/295147905179352825856), (-1313765109/1180591620717411303424)), (35/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-153678655/18889465931478580854784), (721659247/9444732965739290427392)), (39/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (2184313756963/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890188666209765/316912650057057350374175801344), (161842411183/39614081257132168796771975168)), (11557/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891551073061445/39614081257132168796771975168), (1456444773795/19807040628566084398385987584)), (52015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472859680959529/618970019642690137449562112), (3094619137719/2475880078570760549798248448)), (55275/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886552206056287/77371252455336267181195264), (3094252372537/154742504910672534362390528)), (55285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775673473062999/4835703278458516698824704), (1450235959389/4835703278458516698824704)), (25921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260357418252217/604462909807314587353088), (1268761628459/302231454903657293676544)), (11343/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945170060759609/37778931862957161709568), (4122744675499/75557863725914323419136)), (73751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162431191636753/590295810358705651712), (772854808711/1180591620717411303424)), (13833/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624072885812641/590295810358705651712), (4249662665307/590295810358705651712)), (76111/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456688299967233/18446744073709551616), (82976878399/1152921504606846976)), (5949/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1826342009801257/9223372036854775808), (5972192935487/9223372036854775808)), (13393/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399396600775017/288230376151711744), (186547349881/36028797018963968)), (53611/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197726614160497/144115188075855872), (2610156771863/72057594037927936)), (93907/144115188075855872), by norm_num⟩
  | 4 => ⟨((187043367697263/4503599627370496), (244513947593/1125899906842624)), (35259/9007199254740992), by norm_num⟩
  | 3 => ⟨((1495128463008911/9007199254740992), (38164129227/35184372088832)), (176601/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119820652251051/2251799813685248), (2438552051773/562949953421312)), (88531/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116761510338999/1125899906842624), (14591798492883/1125899906842624)), (266745/1125899906842624), by norm_num⟩
  | 0 => ⟨((553772797056223/562949953421312), (29025592882951/1125899906842624)), (269055/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((553772797056223/562949953421312), (29025592882951/1125899906842624)), (1026363374950218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((544371107300849/562949953421312), (1784526277527/35184372088832)), (1086421/1125899906842624), by norm_num⟩
  | 2 => ⟨((524957254112737/562949953421312), (110440458423095/1125899906842624)), (2211339/1125899906842624), by norm_num⟩
  | 3 => ⟨((968224060682875/1125899906842624), (102986987465563/562949953421312)), (4558023/1125899906842624), by norm_num⟩
  | 4 => ⟨((397474299401205/562949953421312), (354256994233295/1125899906842624)), (9507101/1125899906842624), by norm_num⟩
  | 5 => ⟨((899627495653565/2251799813685248), (250125343709683/562949953421312)), (19407789/1125899906842624), by norm_num⟩
  | 6 => ⟨((-85120075485129/2251799813685248), (399715170404543/1125899906842624)), (131014491/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-1152439271/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-21804525/16777216), (-727108225/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1164840691654127/4503599627370496), (-48516309343551/562949953421312)), (106201107/4503599627370496), by norm_num⟩
  | 1 => ⟨((1540004809/4294967296), (128284237/1073741824)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((-1067449991/4294967296), (-355679429/4294967296)), (101/4294967296), by norm_num⟩
  | 3 => ⟨((986533269/8589934592), (328717591/8589934592)), (95/8589934592), by norm_num⟩
  | 4 => ⟨((-341906377/8589934592), (-455699343/34359738368)), (67/17179869184), by norm_num⟩
  | 5 => ⟨((189593153/17179869184), (63173343/17179869184)), (151/137438953472), by norm_num⟩
  | 6 => ⟨((-700885117/274877906944), (-467076529/549755813888)), (71/274877906944), by norm_num⟩
  | 7 => ⟨((277609453/549755813888), (46250397/274877906944)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((-1539393677/17592186044416), (-512933317/17592186044416)), (161/17592186044416), by norm_num⟩
  | 9 => ⟨((237116975/17592186044416), (316034029/70368744177664)), (101/70368744177664), by norm_num⟩
  | 10 => ⟨((-1051884561/562949953421312), (-175246477/281474976710656)), (57/281474976710656), by norm_num⟩
  | 11 => ⟨((530262413/2251799813685248), (353371931/4503599627370496)), (117/4503599627370496), by norm_num⟩
  | 12 => ⟨((-980133057/36028797018963968), (-163292505/18014398509481984)), (55/18014398509481984), by norm_num⟩
  | 13 => ⟨((836155649/288230376151711744), (278611051/288230376151711744)), (95/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1324751841/4611686018427387904), (-441413633/4611686018427387904)), (153/4611686018427387904), by norm_num⟩
  | 15 => ⟨((979464537/36893488147419103232), (20397641/2305843009213693952)), (115/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1357826165/590295810358705651712), (-452434155/590295810358705651712)), (81/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-3673309898305/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779954404024017/633825300114114700748351602688), (-4352731244937/633825300114114700748351602688)), (46315/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945537473122995/19807040628566084398385987584), (-4896229778191/39614081257132168796771975168)), (26059/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890932416399213/2475880078570760549798248448), (-2600775476287/1237940039285380274899124224)), (55391/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772597629351031/154742504910672534362390528), (-1300192733477/38685626227668133590597632)), (3463/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550871332501297/9671406556917033397649408), (-304680868107/604462909807314587353088)), (12991/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314985187954925/151115727451828646838272), (-4264703190285/604462909807314587353088)), (45489/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472415523298115/18889465931478580854784), (-866073520125/9444732965739290427392)), (73953/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298940185230775/4722366482869645213696), (-2597540348093/2361183241434822606848)), (6937/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623371190341063/590295810358705651712), (-7141024861847/590295810358705651712)), (38179/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912937034603019/36893488147419103232), (-8922963726423/73786976294838206464)), (23881/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456337556337261/2305843009213693952), (-10033771688077/9223372036854775808)), (107569/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596591170246713/1152921504606846976), (-5014033421951/576460752303423488)), (26925/288230376151711744), by norm_num⟩
  | 5 => ⟨((299212978095567/36028797018963968), (-8768138191777/144115188075855872)), (94385/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495027158894825/36028797018963968), (-1642420107051/4503599627370496)), (141873/36028797018963968), by norm_num⟩
  | 3 => ⟨((373366310806717/2251799813685248), (-2050213345129/1125899906842624)), (88929/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118137267511333/2251799813685248), (-2045992423597/281474976710656)), (178635/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114186273408101/1125899906842624), (-12233700440031/562949953421312)), (134949/562949953421312), by norm_num⟩
  | 0 => ⟨((1102195995811279/1125899906842624), (-24298118773487/562949953421312)), (547601/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1102195995811279/1125899906842624), (-24298118773487/562949953421312)), (2088932041648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1076893613286507/1125899906842624), (-47573126270145/562949953421312)), (139927/140737488355328), by norm_num⟩
  | 2 => ⟨((510989937014731/562949953421312), (-91004885128839/562949953421312)), (1165291/562949953421312), by norm_num⟩
  | 3 => ⟨((898228430703105/1125899906842624), (-330420707825981/1125899906842624)), (1246113/281474976710656), by norm_num⟩
  | 4 => ⟨((619625657061765/1125899906842624), (-527210761913359/1125899906842624)), (1359833/140737488355328), by norm_num⟩
  | 5 => ⟨((188266766464479/2251799813685248), (-1160576753849081/2251799813685248)), (44323827/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1164840691654127/4503599627370496), (-48516309343551/562949953421312)), (106201107/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-727108225/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-50628539/33554432), (-211036627/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((995730908338051/4503599627370496), (-49368779727585/9007199254740992)), (15575837/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1528327059/4294967296), (18943783/2147483648)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((307468439/1073741824), (-30488843/4294967296)), (21/2147483648), by norm_num⟩
  | 3 => ⟨((-659801817/4294967296), (32713267/8589934592)), (47/8589934592), by norm_num⟩
  | 4 => ⟨((1061910059/17179869184), (-13162493/8589934592)), (39/17179869184), by norm_num⟩
  | 5 => ⟨((-1367262647/68719476736), (4236843/8589934592)), (13/17179869184), by norm_num⟩
  | 6 => ⟨((1467016227/274877906944), (-36367657/274877906944)), (29/137438953472), by norm_num⟩
  | 7 => ⟨((-674591867/549755813888), (33446563/1099511627776)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((542856863/2199023255552), (-26915083/4398046511104)), (23/2199023255552), by norm_num⟩
  | 9 => ⟨((-776617259/17592186044416), (38505027/35184372088832)), (17/8796093022208), by norm_num⟩
  | 10 => ⟨((62495863/8796093022208), (-6197145/35184372088832)), (45/140737488355328), by norm_num⟩
  | 11 => ⟨((-585211411/562949953421312), (28335/1099511627776)), (55/1125899906842624), by norm_num⟩
  | 12 => ⟨((627907621/4503599627370496), (-31131937/9007199254740992)), (61/9007199254740992), by norm_num⟩
  | 13 => ⟨((-1243788715/72057594037927936), (30833797/72057594037927936)), (31/36028797018963968), by norm_num⟩
  | 14 => ⟨((571943061/288230376151711744), (-14178595/288230376151711744)), (59/576460752303423488), by norm_num⟩
  | 15 => ⟨((-1963747939/9223372036854775808), (24340873/4611686018427387904)), (103/9223372036854775808), by norm_num⟩
  | 16 => ⟨((197533149/9223372036854775808), (-9793781/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (-32285418827/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444910417413677/158456325028528675187087900672), (-19121895367/316912650057057350374175801344)), (46103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890723758927385/39614081257132168796771975168), (-43018528339/39614081257132168796771975168)), (51865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890560081084451/2475880078570760549798248448), (-22850075377/1237940039285380274899124224)), (55107/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886113097531955/77371252455336267181195264), (-22846118863/77371252455336267181195264)), (13777/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550524069827737/9671406556917033397649408), (-21414033609/4835703278458516698824704)), (3229/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259637853533591/604462909807314587353088), (-9366538837/151115727451828646838272)), (22603/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889171676128083/75557863725914323419136), (-3804171911/4722366482869645213696)), (73459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298573940115015/4722366482869645213696), (-45636284687/4722366482869645213696)), (55095/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101429384320539/36893488147419103232), (-62727510485/590295810358705651712)), (75755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912625791757177/36893488147419103232), (-78375831867/73786976294838206464)), (94695/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456163792744451/2305843009213693952), (-88126695709/9223372036854775808)), (106533/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797951330663931/576460752303423488), (-88069088789/1152921504606846976)), (53267/576460752303423488), by norm_num⟩
  | 5 => ⟨((598128410484573/72057594037927936), (-38497847877/72057594037927936)), (93219/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494149205205963/36028797018963968), (-28841039193/9007199254740992)), (139831/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492393442348773/9007199254740992), (-71989527221/4503599627370496)), (87397/4503599627370496), by norm_num⟩
  | 2 => ⟨((2234207637975305/4503599627370496), (-287280824747/4503599627370496)), (349603/4503599627370496), by norm_num⟩
  | 1 => ⟨((2225463196976619/2251799813685248), (-429232011573/2251799813685248)), (524449/2251799813685248), by norm_num⟩
  | 0 => ⟨((2199332682055369/2251799813685248), (-851730976121/2251799813685248)), (1049081/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2199332682055369/2251799813685248), (-851730976121/2251799813685248)), (4001926430709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((537021929249005/562949953421312), (-1663771140505/2251799813685248)), (2050069/2251799813685248), by norm_num⟩
  | 2 => ⟨((1024575551461463/1125899906842624), (-793571064597/562949953421312)), (1957163/1125899906842624), by norm_num⟩
  | 3 => ⟨((932367553503275/1125899906842624), (-5777234769747/2251799813685248)), (7135157/2251799813685248), by norm_num⟩
  | 4 => ⟨((1544188618245965/2251799813685248), (-4784178607305/1125899906842624)), (11853985/2251799813685248), by norm_num⟩
  | 5 => ⟨((2117796547250169/4503599627370496), (-6561572754521/1125899906842624)), (16358659/2251799813685248), by norm_num⟩
  | 6 => ⟨((995730908338051/4503599627370496), (-49368779727585/9007199254740992)), (15575837/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-211036627/8388608)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-112727759/67108864), (-234943437/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1619637736801563/9007199254740992), (-442836072117289/9007199254740992)), (144546971/9007199254740992), by norm_num⟩
  | 1 => ⟨((691891015/2147483648), (378349173/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((-619851139/2147483648), (-338955357/4294967296)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((1480832197/8589934592), (202442157/4294967296)), (69/4294967296), by norm_num⟩
  | 4 => ⟨((-331661889/4294967296), (-90681913/4294967296)), (125/17179869184), by norm_num⟩
  | 5 => ⟨((59425833/2147483648), (129984141/17179869184)), (91/34359738368), by norm_num⟩
  | 6 => ⟨((-1135752523/137438953472), (-155266877/68719476736)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((1162854479/549755813888), (158971941/274877906944)), (57/274877906944), by norm_num⟩
  | 8 => ⟨((-520888881/1099511627776), (-284839481/2199023255552)), (13/274877906944), by norm_num⟩
  | 9 => ⟨((1659213485/17592186044416), (56707093/2199023255552)), (21/2199023255552), by norm_num⟩
  | 10 => ⟨((-1189164589/70368744177664), (-325137507/70368744177664)), (61/35184372088832), by norm_num⟩
  | 11 => ⟨((1549597755/562949953421312), (423685969/562949953421312)), (161/562949953421312), by norm_num⟩
  | 12 => ⟨((-925502151/2251799813685248), (-126523891/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | 13 => ⟨((1020478303/18014398509481984), (69753963/4503599627370496)), (55/9007199254740992), by norm_num⟩
  | 14 => ⟨((-522414761/72057594037927936), (-285673883/144115188075855872)), (57/72057594037927936), by norm_num⟩
  | 15 => ⟨((62402773/72057594037927936), (272991405/1152921504606846976)), (111/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-223621519/2305843009213693952), (-61141867/2305843009213693952)), (101/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (-936154096033/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889683726782263/316912650057057350374175801344), (-4434446582829/633825300114114700748351602688)), (46319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945207351147103/19807040628566084398385987584), (-4987985287767/39614081257132168796771975168)), (52123/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890230985893095/2475880078570760549798248448), (-2649411390233/1237940039285380274899124224)), (13849/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221487035938583/19342813113834066795298816), (-2648898564917/77371252455336267181195264)), (55415/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775106959410583/4835703278458516698824704), (-2482797532709/4835703278458516698824704)), (25985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259365609249969/604462909807314587353088), (-2171902974731/302231454903657293676544)), (22747/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888727663736669/75557863725914323419136), (-882080180347/9444732965739290427392)), (73963/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298239518425517/4722366482869645213696), (-2645346642237/2361183241434822606848)), (55505/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622408026234789/590295810358705651712), (-7271798141749/590295810358705651712)), (38185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114041905869787/4611686018427387904), (-9085390074421/73786976294838206464)), (23885/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823996726596293/9223372036854775808), (-10215072270079/9223372036854775808)), (53795/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797619163772689/576460752303423488), (-10207583032611/1152921504606846976)), (26931/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195668915465837/144115188075855872), (-8923210071007/144115188075855872)), (11801/18014398509481984), by norm_num⟩
  | 4 => ⟨((746627075186177/18014398509481984), (-13367965748841/36028797018963968)), (70957/18014398509481984), by norm_num⟩
  | 3 => ⟨((745625798963259/4503599627370496), (-16680472718243/9007199254740992)), (695/35184372088832), by norm_num⟩
  | 2 => ⟨((1115927571854527/2251799813685248), (-8318125030529/1125899906842624)), (178713/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110881696694697/1125899906842624), (-3105479203665/140737488355328)), (33757/140737488355328), by norm_num⟩
  | 0 => ⟨((1095627261552177/1125899906842624), (-49245600667579/1125899906842624)), (548083/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1095627261552177/1125899906842624), (-49245600667579/1125899906842624)), (2090770725730514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064014624915199/1125899906842624), (-95843018149309/1125899906842624)), (1114639/1125899906842624), by norm_num⟩
  | 2 => ⟨((31167880440593/35184372088832), (-181149980361677/1125899906842624)), (2296515/1125899906842624), by norm_num⟩
  | 3 => ⟨((854370741515959/1125899906842624), (-320941406342201/1125899906842624)), (1201925/281474976710656), by norm_num⟩
  | 4 => ⟨((278419943834871/562949953421312), (-121770570213791/281474976710656)), (20074781/2251799813685248), by norm_num⟩
  | 5 => ⟨((258713982422101/4503599627370496), (-1927182627222459/4503599627370496)), (74452477/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1619637736801563/9007199254740992), (-442836072117289/9007199254740992)), (144546971/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-234943437/8388608)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3825815/2097152), (-1020625427/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((786462097540401/9007199254740992), (305483375415875/2251799813685248)), (185150577/9007199254740992), by norm_num⟩
  | 1 => ⟨((-729744233/4294967296), (-566905213/2147483648)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((710008355/4294967296), (68946663/268435456)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((-28783593/268435456), (-357770697/2147483648)), (7/268435456), by norm_num⟩
  | 4 => ⟨((224041143/4294967296), (348094815/4294967296)), (55/4294967296), by norm_num⟩
  | 5 => ⟨((-348771147/17179869184), (-1083777973/34359738368)), (173/34359738368), by norm_num⟩
  | 6 => ⟨((452451543/68719476736), (351489093/34359738368)), (57/34359738368), by norm_num⟩
  | 7 => ⟨((-503102885/274877906944), (-390837825/137438953472)), (129/274877906944), by norm_num⟩
  | 8 => ⟨((489496505/1099511627776), (380267645/549755813888)), (127/1099511627776), by norm_num⟩
  | 9 => ⟨((-423340541/4398046511104), (-657748151/4398046511104)), (111/4398046511104), by norm_num⟩
  | 10 => ⟨((164756531/8796093022208), (511967521/17592186044416)), (175/35184372088832), by norm_num⟩
  | 11 => ⟨((-233164659/70368744177664), (-724540215/140737488355328)), (63/70368744177664), by norm_num⟩
  | 12 => ⟨((604956635/1125899906842624), (234981693/281474976710656)), (165/1125899906842624), by norm_num⟩
  | 13 => ⟨((-181106347/2251799813685248), (-1125546489/9007199254740992)), (25/1125899906842624), by norm_num⟩
  | 14 => ⟨((805523837/72057594037927936), (1251549907/72057594037927936)), (7/2251799813685248), by norm_num⟩
  | 15 => ⟨((-835987739/576460752303423488), (-1298881955/576460752303423488)), (235/576460752303423488), by norm_num⟩
  | 16 => ⟨((813378513/4611686018427387904), (1263753789/4611686018427387904)), (231/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (1301202906515/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779153795610531/633825300114114700748351602688), (1540542177211/633825300114114700748351602688)), (1443/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((945087454220909/19807040628566084398385987584), (1732831333499/39614081257132168796771975168)), (51953/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472494233245547/618970019642690137449562112), (1840790566665/2475880078570760549798248448)), (110411/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442910763308721/38685626227668133590597632), (1840405107305/154742504910672534362390528)), (13803/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549977381060455/9671406556917033397649408), (1724970340477/9671406556917033397649408)), (6471/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259159507595799/604462909807314587353088), (1508939716111/604462909807314587353088)), (5663/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472098594170351/18889465931478580854784), (2451259787575/75557863725914323419136)), (73631/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297990976721165/4722366482869645213696), (1837773741917/4722366482869645213696)), (110469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622068592791407/590295810358705651712), (1262924410317/295147905179352825856)), (75965/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456062416459507/18446744073709551616), (1577838360217/36893488147419103232)), (189967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227941006518663/1152921504606846976), (3547890450369/9223372036854775808)), (106893/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99673474456675/72057594037927936), (3545085088727/1152921504606846976)), (26735/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195270690447457/144115188075855872), (1549398059397/72057594037927936)), (187249/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492670123008703/36028797018963968), (4641894250077/36028797018963968)), (281083/36028797018963968), by norm_num⟩
  | 3 => ⟨((186318099133949/1125899906842624), (2895679043735/4503599627370496)), (351721/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230510968553031/4503599627370496), (11549747521103/4503599627370496)), (704545/4503599627370496), by norm_num⟩
  | 1 => ⟨((2219919830952269/2251799813685248), (8621205568205/1125899906842624)), (529791/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094126446041285/1125899906842624), (17078623971387/1125899906842624)), (2130261/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1094126446041285/1125899906842624), (17078623971387/1125899906842624)), (8126300820357512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2125981169829631/2251799813685248), (66386626503917/2251799813685248)), (4204917/2251799813685248), by norm_num⟩
  | 2 => ⟨((250654427785357/281474976710656), (62677293522313/1125899906842624)), (8187873/2251799813685248), by norm_num⟩
  | 3 => ⟨((1778690673097561/2251799813685248), (223257375509011/2251799813685248)), (7747137/1125899906842624), by norm_num⟩
  | 4 => ⟨((691423952502453/1125899906842624), (176350406063949/1125899906842624)), (27550169/2251799813685248), by norm_num⟩
  | 5 => ⟨((99246747792313/281474976710656), (433192663202491/2251799813685248)), (42467951/2251799813685248), by norm_num⟩
  | 6 => ⟨((786462097540401/9007199254740992), (305483375415875/2251799813685248)), (185150577/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-1020625427/33554432)), (1/16777216), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-65413575/33554432), (-545331169/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((297431403000913/4503599627370496), (-1135815858436585/9007199254740992)), (171024085/9007199254740992), by norm_num⟩
  | 1 => ⟨((-589839187/4294967296), (70388993/268435456)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((306634027/2147483648), (-1170958369/4294967296)), (181/4294967296), by norm_num⟩
  | 3 => ⟨((-425085023/4294967296), (202911623/1073741824)), (1/33554432), by norm_num⟩
  | 4 => ⟨((6905777/134217728), (-210971429/2147483648)), (135/8589934592), by norm_num⟩
  | 5 => ⟨((-367620085/17179869184), (350962203/8589934592)), (57/8589934592), by norm_num⟩
  | 6 => ⟨((509629651/68719476736), (-486536923/34359738368)), (5/2147483648), by norm_num⟩
  | 7 => ⟨((-302784305/137438953472), (1156257245/274877906944)), (3/4294967296), by norm_num⟩
  | 8 => ⟨((314811131/549755813888), (-601092337/549755813888)), (101/549755813888), by norm_num⟩
  | 9 => ⟨((-4546051/34359738368), (277763639/1099511627776)), (189/4398046511104), by norm_num⟩
  | 10 => ⟨((242003131/8796093022208), (-57759325/1099511627776)), (5/549755813888), by norm_num⟩
  | 11 => ⟨((-731972893/140737488355328), (698805177/70368744177664)), (245/140737488355328), by norm_num⟩
  | 12 => ⟨((507364947/562949953421312), (-242187419/140737488355328)), (43/140737488355328), by norm_num⟩
  | 13 => ⟨((-20289149/140737488355328), (619833329/2251799813685248)), (223/4503599627370496), by norm_num⟩
  | 14 => ⟨((385738051/18014398509481984), (-736518385/18014398509481984)), (135/18014398509481984), by norm_num⟩
  | 15 => ⟨((-106949297/36028797018963968), (816825027/144115188075855872)), (19/18014398509481984), by norm_num⟩
  | 16 => ⟨((222394811/576460752303423488), (-849269947/1152921504606846976)), (5/36028797018963968), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (-1417689674925/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778960515465085/633825300114114700748351602688), (-1678108534607/633825300114114700748351602688)), (92365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472489372789529/9903520314283042199192993792), (-1887548542655/39614081257132168796771975168)), (51961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236218244264271/309485009821345068724781056), (-501280349221/618970019642690137449562112)), (110429/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771412104742297/154742504910672534362390528), (-2004672734189/154742504910672534362390528)), (110443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193720112390491/1208925819614629174706176), (-1878904111679/9671406556917033397649408)), (103555/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258970118178171/604462909807314587353088), (-1643564664519/604462909807314587353088)), (45313/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944043339700059/37778931862957161709568), (-2669899572271/75557863725914323419136)), (147293/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297760256720549/4722366482869645213696), (-250205450269/590295810358705651712)), (55247/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621751438857249/590295810358705651712), (-1375495636803/295147905179352825856)), (151969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823853352531015/73786976294838206464), (-3436837071527/73786976294838206464)), (47505/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823082377223287/9223372036854775808), (-3863828049115/9223372036854775808)), (213853/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594330138336809/1152921504606846976), (-3860563409925/1152921504606846976)), (106977/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194881168834043/144115188075855872), (-3374323605193/144115188075855872)), (46831/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492086340145183/36028797018963968), (-5054154995185/36028797018963968)), (281215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489815938906761/9007199254740992), (-788110534653/1125899906842624)), (175959/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229055884214857/4503599627370496), (-12571415077711/4503599627370496)), (705039/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108871883488431/1125899906842624), (-4690375179493/562949953421312)), (1060573/2251799813685248), by norm_num⟩
  | 0 => ⟨((34123859829175/35184372088832), (-37142081092489/2251799813685248)), (1066625/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((34123859829175/35184372088832), (-37142081092489/2251799813685248)), (4068851475242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058743700289001/1125899906842624), (-72045120814661/2251799813685248)), (4208275/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988881234004485/2251799813685248), (-67747867581753/1125899906842624)), (8183815/2251799813685248), by norm_num⟩
  | 3 => ⟨((1748507769118259/2251799813685248), (-239350694778951/2251799813685248)), (7720717/1125899906842624), by norm_num⟩
  | 4 => ⟨((1332263483344917/2251799813685248), (-2903972544133/17592186044416)), (6815745/562949953421312), by norm_num⟩
  | 5 => ⟨((726866918099685/2251799813685248), (-109959517464649/562949953421312)), (10315161/562949953421312), by norm_num⟩
  | 6 => ⟨((297431403000913/4503599627370496), (-1135815858436585/9007199254740992)), (171024085/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-545331169/16777216)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile003Terms0
