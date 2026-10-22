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
namespace Reinmann.XiBand97.Tile000Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (18227/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (18227/1280))
  have he : value ((69/80), (18227/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-662385127/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-558794484447969/1125899906842624), (533708370773735/2251799813685248)), (27000649/1125899906842624), by norm_num⟩
  | 1 => ⟨((738767283/2147483648), (-352800801/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-1024148919/8589934592), (489085761/8589934592)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((946514581/34359738368), (-226005611/17179869184)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-656073913/137438953472), (9790947/4294967296)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((727609253/1099511627776), (-173736123/549755813888)), (21/549755813888), by norm_num⟩
  | 6 => ⟨((-1344907473/17592186044416), (642265087/17592186044416)), (5/1099511627776), by norm_num⟩
  | 7 => ⟨((1065392941/140737488355328), (-254390991/70368744177664)), (65/140737488355328), by norm_num⟩
  | 8 => ⟨((-738474113/1125899906842624), (88165199/281474976710656)), (47/1125899906842624), by norm_num⟩
  | 9 => ⟨((227498333/4503599627370496), (-54321297/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 10 => ⟨((-252303725/72057594037927936), (481953969/288230376151711744)), (69/288230376151711744), by norm_num⟩
  | 11 => ⟨((1017504673/4611686018427387904), (-242956389/2305843009213693952)), (71/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-470186997/36893488147419103232), (449078763/73786976294838206464)), (67/73786976294838206464), by norm_num⟩
  | 13 => ⟨((802237025/1180591620717411303424), (-383110989/1180591620717411303424)), (59/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-635506665/18889465931478580854784), (303488345/18889465931478580854784)), (3/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((939732593/604462909807314587353088), (-112193115/151115727451828646838272)), (73/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-1302745995/19342813113834066795298816), (622130731/19342813113834066795298816)), (13/2417851639229258349412352), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (3511923158549/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222629897181985/79228162514264337593543950336), (4166308035559/633825300114114700748351602688)), (23153/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892295244955689/39614081257132168796771975168), (2343409745863/19807040628566084398385987584)), (13027/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946114460076797/1237940039285380274899124224), (4979438819861/2475880078570760549798248448)), (13845/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443473515328403/38685626227668133590597632), (2489546677887/77371252455336267181195264)), (13849/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552086661004563/9671406556917033397649408), (4667532774101/9671406556917033397649408)), (25977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261004087592881/604462909807314587353088), (2041861857653/302231454903657293676544)), (11369/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945694934818205/37778931862957161709568), (3317680794585/37778931862957161709568)), (18483/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300235890963435/4722366482869645213696), (2487958734011/2361183241434822606848)), (6935/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812576289590253/295147905179352825856), (1710226152861/147573952589676412928)), (19083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828100494011375/73786976294838206464), (534353525431/4611686018427387904)), (373/576460752303423488), by norm_num⟩
  | 7 => ⟨((1827854522973595/9223372036854775808), (9616333785749/9223372036854775808)), (26881/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199886865817677/144115188075855872), (9613793052855/1152921504606846976)), (841/18014398509481984), by norm_num⟩
  | 5 => ⟨((37470065167731/4503599627370496), (8409205592609/144115188075855872)), (47167/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498311178902279/36028797018963968), (12608069235807/36028797018963968)), (35445/18014398509481984), by norm_num⟩
  | 3 => ⟨((93598004523695/562949953421312), (7875007475567/4503599627370496)), (22215/2251799813685248), by norm_num⟩
  | 2 => ⟨((280559187356525/562949953421312), (15734851509211/2251799813685248)), (89231/2251799813685248), by norm_num⟩
  | 1 => ⟨((280081735407383/281474976710656), (11782086464409/562949953421312)), (134775/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114441998512271/1125899906842624), (46974757741513/1125899906842624)), (136635/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114441998512271/1125899906842624), (46974757741513/1125899906842624)), (521221163036155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((275285203562159/281474976710656), (92993422557231/1125899906842624)), (281891/562949953421312), by norm_num⟩
  | 2 => ⟨((267311354421649/281474976710656), (181896902934463/1125899906842624)), (298975/281474976710656), by norm_num⟩
  | 3 => ⟨((493027521007609/562949953421312), (345487958160465/1125899906842624)), (2657859/1125899906842624), by norm_num⟩
  | 4 => ⟨((757565225350861/1125899906842624), (605151738674559/1125899906842624)), (6286623/1125899906842624), by norm_num⟩
  | 5 => ⟨((368942998534399/2251799813685248), (1628712856246955/2251799813685248)), (7608925/562949953421312), by norm_num⟩
  | 6 => ⟨((-558794484447969/1125899906842624), (533708370773735/2251799813685248)), (27000649/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-662385127/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1049855587/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-435607704506991/1125899906842624), (-55743004979409/2251799813685248)), (140920457/4503599627370496), by norm_num⟩
  | 1 => ⟨((228197087/536870912), (116805935/4294967296)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((-2005600993/8589934592), (-32081109/2147483648)), (169/8589934592), by norm_num⟩
  | 3 => ⟨((734459299/8589934592), (23496467/4294967296)), (63/8589934592), by norm_num⟩
  | 4 => ⟨((-1613772023/68719476736), (-51627015/34359738368)), (141/68719476736), by norm_num⟩
  | 5 => ⟨((1418327821/274877906944), (90748917/274877906944)), (63/137438953472), by norm_num⟩
  | 6 => ⟨((-259698729/274877906944), (-33232625/549755813888)), (47/549755813888), by norm_num⟩
  | 7 => ⟨((652133063/4398046511104), (83450903/8796093022208)), (15/1099511627776), by norm_num⟩
  | 8 => ⟨((-716441397/35184372088832), (-22920047/17592186044416)), (67/35184372088832), by norm_num⟩
  | 9 => ⟨((1399273463/562949953421312), (89529761/562949953421312)), (133/562949953421312), by norm_num⟩
  | 10 => ⟨((-614903609/2251799813685248), (-78686797/4503599627370496)), (119/4503599627370496), by norm_num⟩
  | 11 => ⟨((1965209197/72057594037927936), (125740047/72057594037927936)), (193/72057594037927936), by norm_num⟩
  | 12 => ⟨((-359833829/144115188075855872), (-92093041/576460752303423488)), (9/36028797018963968), by norm_num⟩
  | 13 => ⟨((973090133/4611686018427387904), (124522519/9223372036854775808)), (197/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-76360627/4611686018427387904), (-39086277/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 15 => ⟨((715867505/590295810358705651712), (45803375/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-393230419/4722366482869645213696), (-100640301/18889465931478580854784)), (21/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-4009043601545/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780496106931927/633825300114114700748351602688), (-4753319781355/633825300114114700748351602688)), (23167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945842087430585/19807040628566084398385987584), (-5346995118609/39614081257132168796771975168)), (13035/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891579503229445/2475880078570760549798248448), (-1420157132391/618970019642690137449562112)), (55417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773244470198111/154742504910672534362390528), (-2840002603205/77371252455336267181195264)), (13859/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775738742204229/4835703278458516698824704), (-5324342362535/9671406556917033397649408)), (6499/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260470873317855/604462909807314587353088), (-4658136781627/604462909807314587353088)), (22757/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945261525196035/37778931862957161709568), (-7568228979961/75557863725914323419136)), (73999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649792737051979/2361183241434822606848), (-5675083289335/4722366482869645213696)), (55533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203032220655127/73786976294838206464), (-1950367434269/147573952589676412928)), (38207/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826981241649051/73786976294838206464), (-4874590318463/36893488147419103232)), (5975/4611686018427387904), by norm_num⟩
  | 7 => ⟨((913297177737033/4611686018427387904), (-10964172469861/9223372036854775808)), (6729/576460752303423488), by norm_num⟩
  | 6 => ⟨((798916750611873/576460752303423488), (-2739899568839/288230376151711744)), (107807/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197936927186555/144115188075855872), (-9584496330057/144115188075855872)), (94493/144115188075855872), by norm_num⟩
  | 4 => ⟨((374162657404863/9007199254740992), (-7183212362751/18014398509481984)), (35515/9007199254740992), by norm_num⟩
  | 3 => ⟨((373871871838903/2251799813685248), (-2242492080175/1125899906842624)), (44535/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120148861975107/2251799813685248), (-4478181532015/562949953421312)), (44747/562949953421312), by norm_num⟩
  | 1 => ⟨((1117177012600259/1125899906842624), (-13400411003111/562949953421312)), (270605/1125899906842624), by norm_num⟩
  | 0 => ⟨((138508837297805/140737488355328), (-6665892232311/140737488355328)), (549727/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138508837297805/140737488355328), (-6665892232311/140737488355328)), (2097042088035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1087998037424827/1125899906842624), (-13120668749165/140737488355328)), (1134119/1125899906842624), by norm_num⟩
  | 2 => ⟨((1041586376918473/1125899906842624), (-50715918038665/281474976710656)), (2403345/1125899906842624), by norm_num⟩
  | 3 => ⟨((463517451577501/562949953421312), (-375344266401977/1125899906842624)), (5312805/1125899906842624), by norm_num⟩
  | 4 => ⟨((319082712850423/562949953421312), (-618096215372329/1125899906842624)), (12291123/1125899906842624), by norm_num⟩
  | 5 => ⟨((44785826784635/2251799813685248), (-1401359506328831/2251799813685248)), (27428489/1125899906842624), by norm_num⟩
  | 6 => ⟨((-435607704506991/1125899906842624), (-55743004979409/2251799813685248)), (140920457/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1049855587/67108864)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-662385127/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((428173265005319/2251799813685248), (-529768751342097/2251799813685248)), (10146201/562949953421312), by norm_num⟩
  | 1 => ⟨((-566076453/2147483648), (43774571/134217728)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((784748595/4294967296), (-970951055/4294967296)), (39/2147483648), by norm_num⟩
  | 3 => ⟨((-725261701/8589934592), (897349315/8589934592)), (37/4294967296), by norm_num⟩
  | 4 => ⟨((502713103/17179869184), (-155498787/4294967296)), (53/17179869184), by norm_num⟩
  | 5 => ⟨((-34845417/4294967296), (689814693/68719476736)), (15/17179869184), by norm_num⟩
  | 6 => ⟨((257632027/137438953472), (-318762073/137438953472)), (57/274877906944), by norm_num⟩
  | 7 => ⟨((-816351603/2199023255552), (1010052719/2199023255552)), (93/2199023255552), by norm_num⟩
  | 8 => ⟨((141462953/2199023255552), (-350057597/4398046511104)), (33/4398046511104), by norm_num⟩
  | 9 => ⟨((-348638745/35184372088832), (862725107/70368744177664)), (83/70368744177664), by norm_num⟩
  | 10 => ⟨((386652741/281474976710656), (-956792761/562949953421312)), (47/281474976710656), by norm_num⟩
  | 11 => ⟨((-194914369/1125899906842624), (482325967/2251799813685248)), (97/4503599627370496), by norm_num⟩
  | 12 => ⟨((180139127/9007199254740992), (-891527691/36028797018963968)), (23/9007199254740992), by norm_num⟩
  | 13 => ⟨((-614709799/288230376151711744), (760566037/288230376151711744)), (81/288230376151711744), by norm_num⟩
  | 14 => ⟨((486953559/2305843009213693952), (-602496233/2305843009213693952)), (33/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-360032519/18446744073709551616), (445459803/18446744073709551616)), (99/36893488147419103232), by norm_num⟩
  | 16 => ⟨((499111051/295147905179352825856), (-617538413/295147905179352825856)), (35/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-290176016697/2535301200456458802993406410752)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445031002280013/158456325028528675187087900672), (-171953184389/79228162514264337593543950336)), (5771/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945633133044159/19807040628566084398385987584), (-1547413115425/39614081257132168796771975168)), (6493/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891136340772527/2475880078570760549798248448), (-1643925737783/2475880078570760549798248448)), (55195/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221600285170655/19342813113834066795298816), (-821849993281/77371252455336267181195264)), (55201/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193882995820527/1208925819614629174706176), (-48147778517/302231454903657293676544)), (51757/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630055039532971/302231454903657293676544), (-84243625869/37778931862957161709568)), (45293/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944969348766631/37778931862957161709568), (-2189884762119/75557863725914323419136)), (18403/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162393613043101/590295810358705651712), (-821010167753/2361183241434822606848)), (55219/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623660234715075/590295810358705651712), (-2257139113129/590295810358705651712)), (37971/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826238455563573/73786976294838206464), (-2820465899841/73786976294838206464)), (11869/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912882196082865/4611686018427387904), (-99115854843/288230376151711744)), (106853/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597010621180757/1152921504606846976), (-3170062060963/1152921504606846976)), (53447/576460752303423488), by norm_num⟩
  | 5 => ⟨((149653108526441/18014398509481984), (-346494285959/18014398509481984)), (23395/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495598444241277/36028797018963968), (-4154233749531/36028797018963968)), (70231/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494200043151747/9007199254740992), (-5186326527111/9007199254740992)), (43935/2251799813685248), by norm_num⟩
  | 2 => ⟨((2237806026399975/4503599627370496), (-10353277197409/4503599627370496)), (351969/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115411927124673/1125899906842624), (-967596876813/140737488355328)), (529179/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209906939208297/2251799813685248), (-30770079805771/2251799813685248)), (1063273/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209906939208297/2251799813685248), (-30770079805771/2251799813685248)), (4056064614302825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2168372984345681/2251799813685248), (-7549406975423/281474976710656)), (2116043/2251799813685248), by norm_num⟩
  | 2 => ⟨((2086417177834149/2251799813685248), (-116315349411437/2251799813685248)), (4188801/2251799813685248), by norm_num⟩
  | 3 => ⟨((1927172812200655/2251799813685248), (-215545219946203/2251799813685248)), (8195053/2251799813685248), by norm_num⟩
  | 4 => ⟨((1628712856246983/2251799813685248), (-92235749633603/562949953421312)), (15596137/2251799813685248), by norm_num⟩
  | 5 => ⟨((558794484447987/1125899906842624), (-533708370773763/2251799813685248)), (13835917/1125899906842624), by norm_num⟩
  | 6 => ⟨((428173265005319/2251799813685248), (-529768751342097/2251799813685248)), (10146201/562949953421312), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-662385127/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-384502659/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-674563292701485/4503599627370496), (224714239415255/1125899906842624)), (100559599/4503599627370496), by norm_num⟩
  | 1 => ⟨((517686719/2147483648), (-172454651/536870912)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-104148079/536870912), (555110107/2147483648)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((893972623/8589934592), (-74451271/536870912)), (141/8589934592), by norm_num⟩
  | 4 => ⟨((-179849179/4294967296), (479298793/8589934592)), (29/4294967296), by norm_num⟩
  | 5 => ⟨((115782435/8589934592), (-617121319/34359738368)), (19/8589934592), by norm_num⟩
  | 6 => ⟨((-496919041/137438953472), (20692051/4294967296)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((457005911/549755813888), (-608961305/549755813888)), (155/1099511627776), by norm_num⟩
  | 8 => ⟨((-735522639/4398046511104), (245021353/1099511627776)), (127/4398046511104), by norm_num⟩
  | 9 => ⟨((526123565/17592186044416), (-43816295/1099511627776)), (23/4398046511104), by norm_num⟩
  | 10 => ⟨((-338705285/70368744177664), (902650961/140737488355328)), (121/140737488355328), by norm_num⟩
  | 11 => ⟨((198227319/281474976710656), (-1056553221/1125899906842624)), (9/70368744177664), by norm_num⟩
  | 12 => ⟨((-850758833/9007199254740992), (566818937/4503599627370496)), (157/9007199254740992), by norm_num⟩
  | 13 => ⟨((842611397/72057594037927936), (-1122781399/72057594037927936)), (157/72057594037927936), by norm_num⟩
  | 14 => ⟨((-774931845/576460752303423488), (516299129/288230376151711744)), (147/576460752303423488), by norm_num⟩
  | 15 => ⟨((665175835/4611686018427387904), (-110793519/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 16 => ⟨((-133819901/9223372036854775808), (89157645/4611686018427387904)), (105/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (2884759624059/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111238856489925/39614081257132168796771975168), (3417830860589/633825300114114700748351602688)), (46269/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472731476504125/9903520314283042199192993792), (15017864471/154742504910672534362390528)), (52063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890774369617997/2475880078570760549798248448), (4084279002735/2475880078570760549798248448)), (55329/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772439929499567/154742504910672534362390528), (255226645609/9671406556917033397649408)), (55343/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193840482171917/1208925819614629174706176), (3827706242601/9671406556917033397649408)), (51899/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314953019856347/151115727451828646838272), (3348549547135/604462909807314587353088)), (45427/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59045427840159/2361183241434822606848), (5440092916943/75557863725914323419136)), (73847/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324696121809021/1180591620717411303424), (4078932159111/4722366482869645213696)), (27705/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623158086095445/590295810358705651712), (350417708809/36893488147419103232)), (76227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825609158640471/73786976294838206464), (7005581795895/73786976294838206464)), (5959/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1825054220224991/9223372036854775808), (984683475233/1152921504606846976)), (6709/576460752303423488), by norm_num⟩
  | 6 => ⟨((1596297686751091/1152921504606846976), (1968175903167/288230376151711744)), (107447/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196597947786301/144115188075855872), (6883256583177/144115188075855872)), (23533/36028797018963968), by norm_num⟩
  | 4 => ⟨((747325935249373/18014398509481984), (2578542079481/9007199254740992)), (141429/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493006016129281/9007199254740992), (12873960052541/9007199254740992)), (22149/1125899906842624), by norm_num⟩
  | 2 => ⟨((1117692827533189/2251799813685248), (12845841874129/2251799813685248)), (88901/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113556448190143/1125899906842624), (4799623352235/281474976710656)), (268229/1125899906842624), by norm_num⟩
  | 0 => ⟨((275270721261537/281474976710656), (19058034162555/562949953421312)), (542581/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275270721261537/281474976710656), (19058034162555/562949953421312)), (2069782261375045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((537761251119033/562949953421312), (2329744757003/35184372088832)), (1097981/1125899906842624), by norm_num⟩
  | 2 => ⟨((511231358194513/562949953421312), (71216075827689/562949953421312)), (2243113/1125899906842624), by norm_num⟩
  | 3 => ⟨((910509968381885/1125899906842624), (258693625956659/1125899906842624)), (4641605/1125899906842624), by norm_num⟩
  | 4 => ⟨((676886111971855/1125899906842624), (836817282811327/2251799813685248)), (19280511/2251799813685248), by norm_num⟩
  | 5 => ⟨((502902639314303/2251799813685248), (1006181799199999/2251799813685248)), (37512825/2251799813685248), by norm_num⟩
  | 6 => ⟨((-674563292701485/4503599627370496), (224714239415255/1125899906842624)), (100559599/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-384502659/16777216)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-856120357/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((891208208578413/4503599627370496), (-357649189446135/4503599627370496)), (41095477/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1522856471/4294967296), (152783709/1073741824)), (9/536870912), by norm_num⟩
  | 2 => ⟨((1364296251/4294967296), (-547503315/4294967296)), (67/4294967296), by norm_num⟩
  | 3 => ⟨((-407415121/2147483648), (326998083/4294967296)), (21/2147483648), by norm_num⟩
  | 4 => ⟨((729989901/8589934592), (-73237739/2147483648)), (77/17179869184), by norm_num⟩
  | 5 => ⟨((-523186527/17179869184), (52489765/4294967296)), (57/34359738368), by norm_num⟩
  | 6 => ⟨((1249899219/137438953472), (-501594845/137438953472)), (35/68719476736), by norm_num⟩
  | 7 => ⟨((-1279725007/549755813888), (513564179/549755813888)), (37/274877906944), by norm_num⟩
  | 8 => ⟨((286619925/549755813888), (-115022935/549755813888)), (17/549755813888), by norm_num⟩
  | 9 => ⟨((-456492413/4398046511104), (366388325/8796093022208)), (7/1099511627776), by norm_num⟩
  | 10 => ⟨((654339683/35184372088832), (-525183801/70368744177664)), (41/35184372088832), by norm_num⟩
  | 11 => ⟨((-852668599/281474976710656), (342182927/281474976710656)), (55/281474976710656), by norm_num⟩
  | 12 => ⟨((127314753/281474976710656), (-408739667/2251799813685248)), (17/562949953421312), by norm_num⟩
  | 13 => ⟨((-561519789/9007199254740992), (450685027/18014398509481984)), (19/4503599627370496), by norm_num⟩
  | 14 => ⟨((1149838171/144115188075855872), (-461439523/144115188075855872)), (5/9007199254740992), by norm_num⟩
  | 15 => ⟨((-1098791163/1152921504606846976), (440953939/1152921504606846976)), (39/576460752303423488), by norm_num⟩
  | 16 => ⟨((30762023/288230376151711744), (-197520849/4611686018427387904)), (71/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-124280110749/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792549118847/316912650057057350374175801344), (-147207511287/158456325028528675187087900672)), (46129/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890660113944373/39614081257132168796771975168), (-662343348413/39614081257132168796771975168)), (25949/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890492455198137/2475880078570760549798248448), (-175907213353/618970019642690137449562112)), (6893/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772158565705047/154742504910672534362390528), (-351752030939/77371252455336267181195264)), (27573/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550460663618975/9671406556917033397649408), (-659402497717/9671406556917033397649408)), (25851/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157447796177681/75557863725914323419136), (-576844659763/604462909807314587353088)), (22621/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236135188444775/9444732965739290427392), (-468562079877/37778931862957161709568)), (36761/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324626576918067/1180591620717411303424), (-351312916189/2361183241434822606848)), (27573/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622777144766209/590295810358705651712), (-965757564965/590295810358705651712)), (9479/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912567656734047/36893488147419103232), (-1206667764945/73786976294838206464)), (94801/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228065543396309/1152921504606846976), (-678386994155/4611686018427387904)), (106665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595771812604443/1152921504606846976), (-1355865514993/1152921504606846976)), (106683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196142300429863/144115188075855872), (-1185361097977/144115188075855872)), (11671/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493977368894735/36028797018963968), (-444000300523/9007199254740992)), (140091/36028797018963968), by norm_num⟩
  | 3 => ⟨((186522318815937/1125899906842624), (-2216435242857/9007199254740992)), (10949/562949953421312), by norm_num⟩
  | 2 => ⟨((139611097988529/281474976710656), (-2211094879157/2251799813685248)), (87645/1125899906842624), by norm_num⟩
  | 1 => ⟨((2224817385149075/2251799813685248), (-6606645896167/2251799813685248)), (526401/2251799813685248), by norm_num⟩
  | 0 => ⟨((1099019145005689/1125899906842624), (-3276778614211/562949953421312)), (527469/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1099019145005689/1125899906842624), (-3276778614211/562949953421312)), (2012134556296920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2145484025065317/2251799813685248), (-25588366490319/2251799813685248)), (2071785/2251799813685248), by norm_num⟩
  | 2 => ⟨((255487127970901/281474976710656), (-6095061292621/281474976710656)), (249689/140737488355328), by norm_num⟩
  | 3 => ⟨((1854133494892345/2251799813685248), (-88517123484641/2251799813685248)), (7425365/2251799813685248), by norm_num⟩
  | 4 => ⟨((1523215214285981/2251799813685248), (-72885059554115/1125899906842624)), (12811877/2251799813685248), by norm_num⟩
  | 5 => ⟨((510466260685285/1125899906842624), (-197210481912733/2251799813685248)), (9495887/1125899906842624), by norm_num⟩
  | 6 => ⟨((891208208578413/4503599627370496), (-357649189446135/4503599627370496)), (41095477/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-856120357/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-929775073/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-355068122509201/2251799813685248), (-225029741866629/2251799813685248)), (75478829/4503599627370496), by norm_num⟩
  | 1 => ⟨((164730707/536870912), (417602213/2147483648)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-1282204619/4294967296), (-812616385/4294967296)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((415842497/2147483648), (65886603/536870912)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((-809192135/8589934592), (-256418819/4294967296)), (93/8589934592), by norm_num⟩
  | 5 => ⟨((1259692151/34359738368), (199587193/8589934592)), (147/34359738368), by norm_num⟩
  | 6 => ⟨((-817082581/68719476736), (-258919163/34359738368)), (97/68719476736), by norm_num⟩
  | 7 => ⟨((454276939/137438953472), (575809631/274877906944)), (109/274877906944), by norm_num⟩
  | 8 => ⟨((-441991053/549755813888), (-560236903/1099511627776)), (27/274877906944), by norm_num⟩
  | 9 => ⟨((764511001/4398046511104), (121130075/1099511627776)), (95/4398046511104), by norm_num⟩
  | 10 => ⟨((-1190135773/35184372088832), (-754266375/35184372088832)), (75/17592186044416), by norm_num⟩
  | 11 => ⟨((842144465/140737488355328), (533721671/140737488355328)), (27/35184372088832), by norm_num⟩
  | 12 => ⟨((-1092491641/1125899906842624), (-21636967/35184372088832)), (71/562949953421312), by norm_num⟩
  | 13 => ⟨((40882511/281474976710656), (414558461/4503599627370496)), (43/2251799813685248), by norm_num⟩
  | 14 => ⟨((-727348051/36028797018963968), (-115241931/9007199254740992)), (97/36028797018963968), by norm_num⟩
  | 15 => ⟨((377427721/144115188075855872), (478400945/288230376151711744)), (103/288230376151711744), by norm_num⟩
  | 16 => ⟨((-734440433/2305843009213693952), (-465462627/2305843009213693952)), (51/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-839114824549/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222421465156459/79228162514264337593543950336), (-3974792867651/633825300114114700748351602688)), (5787/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890419622022381/39614081257132168796771975168), (-4470960114039/39614081257132168796771975168)), (407/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((945118182374401/1237940039285380274899124224), (-4749579330611/2475880078570760549798248448)), (27683/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885950918440535/77371252455336267181195264), (-2374330768003/77371252455336267181195264)), (27691/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775109651218617/4835703278458516698824704), (-4450895089157/9671406556917033397649408)), (25969/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629685250443621/302231454903657293676544), (-486694770611/75557863725914323419136)), (5683/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944367975873149/37778931862957161709568), (-3162601977511/37778931862957161709568)), (73911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324561507729681/1180591620717411303424), (-1185575886271/1180591620717411303424)), (27731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622417462279541/590295810358705651712), (-6518068566739/590295810358705651712)), (38153/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912341505141005/36893488147419103232), (-8143687938531/73786976294838206464)), (23863/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912005899052455/4611686018427387904), (-2289072554381/2305843009213693952)), (107479/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398813658874161/288230376151711744), (-9149592910589/1152921504606846976)), (53799/576460752303423488), by norm_num⟩
  | 5 => ⟨((298921143360191/36028797018963968), (-7998360824929/144115188075855872)), (23571/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493280408170179/36028797018963968), (-11982479060787/36028797018963968)), (141695/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491289255190171/9007199254740992), (-467242142193/281474976710656)), (22199/1125899906842624), by norm_num⟩
  | 2 => ⟨((278993113440211/562949953421312), (-7456120173023/1125899906842624)), (178303/2251799813685248), by norm_num⟩
  | 1 => ⟨((277741745904327/281474976710656), (-5567412721063/281474976710656)), (269233/1125899906842624), by norm_num⟩
  | 0 => ⟨((547934553370965/562949953421312), (-689763024997/17592186044416)), (545605/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547934553370965/562949953421312), (-689763024997/17592186044416)), (2081317905906295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064908457218117/1125899906842624), (-85934742636149/1125899906842624)), (552445/562949953421312), by norm_num⟩
  | 2 => ⟨((1000661990835575/1125899906842624), (-162559093656429/1125899906842624)), (2258737/1125899906842624), by norm_num⟩
  | 3 => ⟨((865884218523953/1125899906842624), (-72238529063759/281474976710656)), (4667219/1125899906842624), by norm_num⟩
  | 4 => ⟨((591758640833813/1125899906842624), (-888891837088477/2251799813685248)), (19148713/2251799813685248), by norm_num⟩
  | 5 => ⟨((271153969483695/2251799813685248), (-467190220166945/1125899906842624)), (35246445/2251799813685248), by norm_num⟩
  | 6 => ⟨((-355068122509201/2251799813685248), (-225029741866629/2251799813685248)), (75478829/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-929775073/33554432)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1987155381/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-173887305070919/4503599627370496), (364412219618061/2251799813685248)), (191082313/9007199254740992), by norm_num⟩
  | 1 => ⟨((86209413/1073741824), (-1445339027/4294967296)), (3/67108864), by norm_num⟩
  | 2 => ⟨((-358534869/4294967296), (1502749007/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((124258717/2147483648), (-1041626237/4294967296)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((-129194369/4294967296), (541500217/4294967296)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((107460855/8589934592), (-900814437/17179869184)), (127/17179869184), by norm_num⟩
  | 6 => ⟨((-297944755/68719476736), (1248793975/68719476736)), (179/68719476736), by norm_num⟩
  | 7 => ⟨((354033543/274877906944), (-1483882325/274877906944)), (215/274877906944), by norm_num⟩
  | 8 => ⟨((-92024007/274877906944), (1542823275/1099511627776)), (113/549755813888), by norm_num⟩
  | 9 => ⟨((340192965/4398046511104), (-1425871471/4398046511104)), (211/4398046511104), by norm_num⟩
  | 10 => ⟨((-282964553/17592186044416), (296501637/4398046511104)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((213966635/70368744177664), (-56050711/4398046511104)), (17/8796093022208), by norm_num⟩
  | 12 => ⟨((-74155185/140737488355328), (621622277/281474976710656)), (191/562949953421312), by norm_num⟩
  | 13 => ⟨((379572609/4503599627370496), (-198865721/562949953421312)), (31/562949953421312), by norm_num⟩
  | 14 => ⟨((-225514015/18014398509481984), (945210609/18014398509481984)), (149/18014398509481984), by norm_num⟩
  | 15 => ⟨((125051523/72057594037927936), (-524136055/72057594037927936)), (167/144115188075855872), by norm_num⟩
  | 16 => ⟨((-65009333/288230376151711744), (544955143/576460752303423488)), (11/72057594037927936), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (2351219091761/10141204801825835211973625643008)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889599189593375/316912650057057350374175801344), (2783836432111/633825300114114700748351602688)), (17339/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236278111473071/4951760157141521099596496896), (391414444265/4951760157141521099596496896)), (78039/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890029818261971/2475880078570760549798248448), (3326413285131/2475880078570760549798248448)), (82931/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442923922224725/38685626227668133590597632), (3325727718897/154742504910672534362390528)), (20737/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550026461920283/9671406556917033397649408), (3117141455403/9671406556917033397649408)), (38891/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259202188432213/604462909807314587353088), (2726770642021/604462909807314587353088)), (34039/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888463236661459/75557863725914323419136), (276852335295/4722366482869645213696)), (27665/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298042187712583/4722366482869645213696), (830258507241/1180591620717411303424)), (41513/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202767287912321/73786976294838206464), (4564482144737/590295810358705651712)), (3569/18446744073709551616), by norm_num⟩
  | 8 => ⟨((57010492130345/2305843009213693952), (356418391029/4611686018427387904)), (71417/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911811722423529/4611686018427387904), (400720853129/576460752303423488)), (40197/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398717293573205/288230376151711744), (6406539457257/1152921504606846976)), (80457/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195350543339077/144115188075855872), (1400026763629/36028797018963968)), (70471/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492785847154295/36028797018963968), (8388939381459/36028797018963968)), (211695/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490682372451379/9007199254740992), (10466556793283/9007199254740992)), (265117/9007199254740992), by norm_num⟩
  | 2 => ⟨((557691245722511/1125899906842624), (5218584988567/1125899906842624)), (531725/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110124140585589/1125899906842624), (31164851189997/2251799813685248)), (400663/1125899906842624), by norm_num⟩
  | 0 => ⟨((2188701240603657/2251799813685248), (30872359720867/1125899906842624)), (1617651/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188701240603657/2251799813685248), (30872359720867/1125899906842624)), (6170848855025481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((265709715909837/281474976710656), (30007273120269/562949953421312)), (1616679/1125899906842624), by norm_num⟩
  | 2 => ⟨((1000110842410005/1125899906842624), (226612656206713/2251799813685248)), (6449219/2251799813685248), by norm_num⟩
  | 3 => ⟨((876972603973933/1125899906842624), (402589560798931/2251799813685248)), (12755435/2251799813685248), by norm_num⟩
  | 4 => ⟨((647092476939505/1125899906842624), (627160573192783/2251799813685248)), (6107901/562949953421312), by norm_num⟩
  | 5 => ⟨((569137763708179/2251799813685248), (45056279679003/140737488355328)), (10423119/562949953421312), by norm_num⟩
  | 6 => ⟨((-173887305070919/4503599627370496), (364412219618061/2251799813685248)), (191082313/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1987155381/67108864)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile000Terms0
