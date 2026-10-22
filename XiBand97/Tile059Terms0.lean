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
namespace Reinmann.XiBand97.Tile059Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨59,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15847/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15847/512))
  have he : value ((69/80), (15847/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-2567700857/4294967296), (-92143015127/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-1063893212872745/2251799813685248), (-634019688207753/2251799813685248)), (1704619/2251799813685248), by norm_num⟩
  | 1 => ⟨((22504717435/68719476736), (13411528299/68719476736)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((-62396325757/549755813888), (-18592326055/274877906944)), (105/549755813888), by norm_num⟩
  | 3 => ⟨((57666449701/2199023255552), (34365915693/2199023255552)), (99/2199023255552), by norm_num⟩
  | 4 => ⟨((-39971337023/8796093022208), (-11910318785/4398046511104)), (139/17592186044416), by norm_num⟩
  | 5 => ⟨((44329631297/70368744177664), (26417932433/70368744177664)), (79/70368744177664), by norm_num⟩
  | 6 => ⟨((-81938557197/1125899906842624), (-24415353843/562949953421312)), (149/1125899906842624), by norm_num⟩
  | 7 => ⟨((32454559943/4503599627370496), (38682134123/9007199254740992)), (15/1125899906842624), by norm_num⟩
  | 8 => ⟨((-22495786721/36028797018963968), (-26812412205/72057594037927936)), (85/72057594037927936), by norm_num⟩
  | 9 => ⟨((433135865/9007199254740992), (8259976855/288230376151711744)), (107/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-30743234931/9223372036854775808), (-36642429879/18446744073709551616)), (121/18446744073709551616), by norm_num⟩
  | 11 => ⟨((30995762347/147573952589676412928), (36943413759/295147905179352825856)), (31/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-55949545/4611686018427387904), (-8535741029/1180591620717411303424)), (117/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((48876332105/75557863725914323419136), (29127506847/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-77436552673/2417851639229258349412352), (-46147769709/2417851639229258349412352)), (41/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((57253256701/38685626227668133590597632), (34119676227/38685626227668133590597632)), (123/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-9921233365/154742504910672534362390528), (-47299914757/1237940039285380274899124224)), (173/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-3392211238445/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1781039797087375/633825300114114700748351602688), (-4024289912689/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892295979682661/39614081257132168796771975168), (-1131765030779/9903520314283042199192993792)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473057436661599/618970019642690137449562112), (-2404852572529/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773894939380623/154742504910672534362390528), (-4809371690105/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552087538979729/9671406556917033397649408), (-4508431493311/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261004910596973/604462909807314587353088), (-3944522899063/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472847827424555/18889465931478580854784), (-50071752511/590295810358705651712)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((325059265207599/1180591620717411303424), (-4806305618773/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625154333659999/590295810358705651712), (-6607722702991/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828102905898649/73786976294838206464), (-8258230762497/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827857537048763/9223372036854775808), (-2322137836871/2305843009213693952)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799549158148301/576460752303423488), (-9286100280255/1152921504606846976)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599522736885537/72057594037927936), (-4061287920709/72057594037927936)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498317105561437/36028797018963968), (-1522291104325/4503599627370496)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497576956257033/9007199254740992), (-15213199936061/9007199254740992)), (347/1125899906842624), by norm_num⟩
  | 2 => ⟨((280561960885643/562949953421312), (-15198583396821/2251799813685248)), (2787/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120349097520719/1125899906842624), (-22761159576007/1125899906842624)), (4209/1125899906842624), by norm_num⟩
  | 0 => ⟨((278627075857483/281474976710656), (-22687207640005/562949953421312)), (8529/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278627075857483/281474976710656), (-22687207640005/562949953421312)), (32535557273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((550701671310111/562949953421312), (-44915327095695/562949953421312)), (8787/562949953421312), by norm_num⟩
  | 2 => ⟨((133784070122383/140737488355328), (-175752359858731/1125899906842624)), (9297/281474976710656), by norm_num⟩
  | 3 => ⟨((989958748566241/1125899906842624), (-83534480792177/281474976710656)), (10289/140737488355328), by norm_num⟩
  | 4 => ⟨((771267647226761/1125899906842624), (-587588218558851/1125899906842624)), (193605/1125899906842624), by norm_num⟩
  | 5 => ⟨((443367776394047/2251799813685248), (-1610046435253483/2251799813685248)), (934653/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1063893212872745/2251799813685248), (-634019688207753/2251799813685248)), (1704619/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-92143015127/4294967296)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1017427393/1073741824), (-1140962685/33554432)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-742336756222601/2251799813685248), (-459412353391647/2251799813685248)), (2419457/2251799813685248), by norm_num⟩
  | 1 => ⟨((6222078573/17179869184), (30805423401/137438953472)), (41/34359738368), by norm_num⟩
  | 2 => ⟨((-54685215851/274877906944), (-16921608353/137438953472)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((40051900095/549755813888), (12393524587/274877906944)), (269/1099511627776), by norm_num⟩
  | 4 => ⟨((-44001509629/2199023255552), (-13615678411/1099511627776)), (75/1099511627776), by norm_num⟩
  | 5 => ⟨((77344958717/17592186044416), (47866725187/17592186044416)), (133/8796093022208), by norm_num⟩
  | 6 => ⟨((-56648081409/70368744177664), (-4382247709/8796093022208)), (197/70368744177664), by norm_num⟩
  | 7 => ⟨((8890611195/70368744177664), (44017290835/562949953421312)), (125/281474976710656), by norm_num⟩
  | 8 => ⟨((-78138677701/4503599627370496), (-48357936625/4503599627370496)), (277/4503599627370496), by norm_num⟩
  | 9 => ⟨((76305876927/36028797018963968), (5902958159/4503599627370496)), (273/36028797018963968), by norm_num⟩
  | 10 => ⟨((-8383057409/36028797018963968), (-41504399187/288230376151711744)), (121/144115188075855872), by norm_num⟩
  | 11 => ⟨((26791941487/1152921504606846976), (33161631259/2305843009213693952)), (195/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-39245274873/18446744073709551616), (-24287850409/18446744073709551616)), (9/1152921504606846976), by norm_num⟩
  | 13 => ⟨((26532517691/147573952589676412928), (32840530369/295147905179352825856)), (197/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-66626171393/4722366482869645213696), (-10308288637/1180591620717411303424)), (125/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((78076086015/75557863725914323419136), (24159600153/37778931862957161709568)), (295/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-21443836887/302231454903657293676544), (-26542033617/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (-105324750603/316912650057057350374175801344)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222562455020383/79228162514264337593543950336), (-1998051486649/316912650057057350374175801344)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472922090191215/9903520314283042199192993792), (-561901642183/4951760157141521099596496896)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472896052930463/618970019642690137449562112), (-4775699476805/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886624736119559/77371252455336267181195264), (-596897096209/19342813113834066795298816)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551482485625263/9671406556917033397649408), (-2238086363785/4835703278458516698824704)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315118890270637/151115727451828646838272), (-1958047755159/302231454903657293676544)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945265626113695/37778931862957161709568), (-6362613124027/75557863725914323419136)), (2311/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299592136451005/4722366482869645213696), (-2385523871081/2361183241434822606848)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624267755882705/590295810358705651712), (-3279353977969/295147905179352825856)), (2385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826994974100177/73786976294838206464), (-8196159991891/73786976294838206464)), (373/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826611514010929/9223372036854775808), (-4608809594837/4611686018427387904)), (105/288230376151711744), by norm_num⟩
  | 6 => ⟨((1597852794907043/1152921504606846976), (-4606895477873/576460752303423488)), (841/288230376151711744), by norm_num⟩
  | 5 => ⟨((598978104384419/72057594037927936), (-8057757259625/144115188075855872)), (2947/144115188075855872), by norm_num⟩
  | 4 => ⟨((187085543140809/4503599627370496), (-12078008595729/36028797018963968)), (4429/36028797018963968), by norm_num⟩
  | 3 => ⟨((46735562687683/281474976710656), (-15082395840067/9007199254740992)), (5551/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120211914526583/2251799813685248), (-15059689327707/2251799813685248)), (5573/2251799813685248), by norm_num⟩
  | 1 => ⟨((558651414825005/562949953421312), (-22532648732119/1125899906842624)), (8415/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108446703914743/1125899906842624), (-44837047077739/1125899906842624)), (17053/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108446703914743/1125899906842624), (-44837047077739/1125899906842624)), (65052036765670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089478493757673/1125899906842624), (-44142002983163/562949953421312)), (4367/140737488355328), by norm_num⟩
  | 2 => ⟨((1047312745551055/1125899906842624), (-170856263968997/1125899906842624)), (73091/1125899906842624), by norm_num⟩
  | 3 => ⟨((118535417487769/140737488355328), (-317861191433561/1125899906842624)), (158163/1125899906842624), by norm_num⟩
  | 4 => ⟨((177237237268017/281474976710656), (-133858467527179/281474976710656)), (355729/1125899906842624), by norm_num⟩
  | 5 => ⟨((191774758856049/1125899906842624), (-1348593341927413/2251799813685248)), (98291/140737488355328), by norm_num⟩
  | 6 => ⟨((-742336756222601/2251799813685248), (-459412353391647/2251799813685248)), (2419457/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-1140962685/33554432)), (1/1073741824), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2567700857/2147483648), (-92143015127/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((648270595748207/4503599627370496), (1198204634377269/4503599627370496)), (348507/562949953421312), by norm_num⟩
  | 1 => ⟨((-13712980215/68719476736), (-50691660403/137438953472)), (15/17179869184), by norm_num⟩
  | 2 => ⟨((9505113573/68719476736), (17568390743/68719476736)), (169/274877906944), by norm_num⟩
  | 3 => ⟨((-1098073779/17179869184), (-32473281361/274877906944)), (79/274877906944), by norm_num⟩
  | 4 => ⟨((24356055807/1099511627776), (22508763419/549755813888)), (111/1099511627776), by norm_num⟩
  | 5 => ⟨((-27011730259/4398046511104), (-24963017443/2199023255552)), (125/4398046511104), by norm_num⟩
  | 6 => ⟨((24964139561/17592186044416), (46141453757/17592186044416)), (117/17592186044416), by norm_num⟩
  | 7 => ⟨((-19775797659/70368744177664), (-36551792661/70368744177664)), (47/35184372088832), by norm_num⟩
  | 8 => ⟨((27415076781/562949953421312), (50671544055/562949953421312)), (33/140737488355328), by norm_num⟩
  | 9 => ⟨((-8445636967/1125899906842624), (-487817193/35184372088832)), (165/4503599627370496), by norm_num⟩
  | 10 => ⟨((37466044491/36028797018963968), (69248842129/36028797018963968)), (185/36028797018963968), by norm_num⟩
  | 11 => ⟨((-4721724201/36028797018963968), (-34908828857/144115188075855872)), (189/288230376151711744), by norm_num⟩
  | 12 => ⟨((34910398051/2305843009213693952), (64525216797/2305843009213693952)), (177/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-29782207977/18446744073709551616), (-27523367445/9223372036854775808)), (153/18446744073709551616), by norm_num⟩
  | 14 => ⟨((47185036549/295147905179352825856), (87212546487/295147905179352825856)), (245/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-17443293359/1180591620717411303424), (-64481206087/2361183241434822606848)), (183/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((24181539223/18889465931478580854784), (22347483099/9444732965739290427392)), (1/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (1400127906995/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445030887367105/158456325028528675187087900672), (1659382156399/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891265721861851/39614081257132168796771975168), (466651187959/9903520314283042199192993792)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891135728615127/2475880078570760549798248448), (991512697317/1237940039285380274899124224)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110800101941673/9671406556917033397649408), (991376502727/77371252455336267181195264)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551063316399379/9671406556917033397649408), (1858541567893/9671406556917033397649408)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260109469678415/604462909807314587353088), (1625934540809/604462909807314587353088)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889937631389131/75557863725914323419136), (660400306425/18889465931478580854784)), (1151/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324787009592251/1180591620717411303424), (1980726409235/4722366482869645213696)), (1727/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811829468108697/295147905179352825856), (1361363953827/295147905179352825856)), (2375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456559167721625/18446744073709551616), (3402253831071/73786976294838206464)), (1485/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456440540613771/2305843009213693952), (3825946480457/9223372036854775808)), (3343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399252028579375/288230376151711744), (3823960872081/1152921504606846976)), (209/72057594037927936), by norm_num⟩
  | 5 => ⟨((299305590824783/36028797018963968), (417966621545/18014398509481984)), (183/9007199254740992), by norm_num⟩
  | 4 => ⟨((373898516257981/9007199254740992), (5011136423439/36028797018963968)), (4395/36028797018963968), by norm_num⟩
  | 3 => ⟨((373548370776653/2251799813685248), (3128057972907/4503599627370496)), (5499/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237789656950335/4503599627370496), (12488841046533/4503599627370496)), (1377/562949953421312), by norm_num⟩
  | 1 => ⟨((2230791207222267/2251799813685248), (18674864596923/2251799813685248)), (8285/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104904728319123/1125899906842624), (18558310954809/1125899906842624)), (33323/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104904728319123/1125899906842624), (18558310954809/1125899906842624)), (127117165572356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2167990316615337/2251799813685248), (72848982041709/2251799813685248)), (66503/2251799813685248), by norm_num⟩
  | 2 => ⟨((260617918288095/281474976710656), (70137623549775/1125899906842624)), (132359/2251799813685248), by norm_num⟩
  | 3 => ⟨((1921712394704245/2251799813685248), (129880969575541/1125899906842624)), (130797/1125899906842624), by norm_num⟩
  | 4 => ⟨((402511608813371/562949953421312), (13855243012313/70368744177664)), (506849/2251799813685248), by norm_num⟩
  | 5 => ⟨((531946606436379/1125899906842624), (634019688207709/2251799813685248)), (924391/2251799813685248), by norm_num⟩
  | 6 => ⟨((648270595748207/4503599627370496), (1198204634377269/4503599627370496)), (348507/562949953421312), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-92143015127/2147483648)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-53487363893/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1011212752836471/4503599627370496), (490334823770213/4503599627370496)), (1581243/4503599627370496), by norm_num⟩
  | 1 => ⟨((-49666874449/137438953472), (-6020839349/34359738368)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((79935750731/274877906944), (9690167113/68719476736)), (131/274877906944), by norm_num⟩
  | 3 => ⟨((-85767751857/549755813888), (-41588592879/549755813888)), (143/549755813888), by norm_num⟩
  | 4 => ⟨((8627366969/137438953472), (8366782263/274877906944)), (117/1099511627776), by norm_num⟩
  | 5 => ⟨((-22216338375/1099511627776), (-43090613053/4398046511104)), (153/4398046511104), by norm_num⟩
  | 6 => ⟨((1489825719/274877906944), (11558611053/4398046511104)), (21/2199023255552), by norm_num⟩
  | 7 => ⟨((-87690312963/70368744177664), (-10630209625/17592186044416)), (157/70368744177664), by norm_num⟩
  | 8 => ⟨((35283028559/140737488355328), (34217324775/281474976710656)), (1/2199023255552), by norm_num⟩
  | 9 => ⟨((-50476305625/1125899906842624), (-6118962195/281474976710656)), (93/1125899906842624), by norm_num⟩
  | 10 => ⟨((32495391981/4503599627370496), (31513887173/9007199254740992)), (61/4503599627370496), by norm_num⟩
  | 11 => ⟨((-38035866061/36028797018963968), (-36887014389/72057594037927936)), (145/72057594037927936), by norm_num⟩
  | 12 => ⟨((20405454957/144115188075855872), (39578239623/576460752303423488)), (157/576460752303423488), by norm_num⟩
  | 13 => ⟨((-80840154655/4611686018427387904), (-4899901489/576460752303423488)), (79/2305843009213693952), by norm_num⟩
  | 14 => ⟨((9293372125/4611686018427387904), (36050684451/36893488147419103232)), (147/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-31908491589/147573952589676412928), (-30944713773/295147905179352825856)), (1/2305843009213693952), by norm_num⟩
  | 16 => ⟨((12838684023/590295810358705651712), (3112724721/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (588120051351/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827683380161/633825300114114700748351602688), (348399021617/316912650057057350374175801344)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945466491201999/19807040628566084398385987584), (783801269253/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945391164535337/1237940039285380274899124224), (104083861403/309485009821345068724781056)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772448384617641/154742504910672534362390528), (832538218555/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775366155234117/4835703278458516698824704), (390181822037/4835703278458516698824704)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157477500256075/75557863725914323419136), (682677285245/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472366887793443/18889465931478580854784), (1109086463845/75557863725914323419136)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298795744688435/4722366482869645213696), (415791903909/2361183241434822606848)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811587482609663/295147905179352825856), (1143052425023/590295810358705651712)), (2371/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456408088993797/18446744073709551616), (44632899735/2305843009213693952)), (741/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825083199707987/9223372036854775808), (401502747729/2305843009213693952)), (3335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798165132524233/576460752303423488), (1605044792641/1152921504606846976)), (417/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196630496570763/144115188075855872), (1403327977877/144115188075855872)), (365/18014398509481984), by norm_num⟩
  | 4 => ⟨((747354382252011/18014398509481984), (525705356875/9007199254740992)), (1095/9007199254740992), by norm_num⟩
  | 3 => ⟨((746545612246585/4503599627370496), (2624732593895/9007199254740992)), (2739/4503599627370496), by norm_num⟩
  | 2 => ⟨((34931222064545/70368744177664), (5238099610645/4503599627370496)), (10963/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227536620607163/2251799813685248), (7828794867775/2251799813685248)), (16463/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203430004692753/2251799813685248), (1943065903601/281474976710656)), (33003/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203430004692753/2251799813685248), (1943065903601/281474976710656)), (125896462447356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155991897569337/2251799813685248), (30421245704487/2251799813685248)), (65045/2251799813685248), by norm_num⟩
  | 2 => ⟨((515962340651923/562949953421312), (1820431562517/70368744177664)), (63157/1125899906842624), by norm_num⟩
  | 3 => ⟨((945039754264653/1125899906842624), (13347888199077/281474976710656)), (119039/1125899906842624), by norm_num⟩
  | 4 => ⟨((790700375601889/1125899906842624), (179259771238205/2251799813685248)), (422249/2251799813685248), by norm_num⟩
  | 5 => ⟨((274080121967335/562949953421312), (251782183455087/2251799813685248)), (330153/1125899906842624), by norm_num⟩
  | 6 => ⟨((1011212752836471/4503599627370496), (490334823770213/4503599627370496)), (1581243/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-53487363893/1073741824)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1659352607/1073741824), (-119093119403/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((110687139331435/1125899906842624), (852137741478857/4503599627370496)), (1991911/4503599627370496), by norm_num⟩
  | 1 => ⟨((-12104780885/68719476736), (-46595027691/137438953472)), (55/68719476736), by norm_num⟩
  | 2 => ⟨((43377711547/274877906944), (20871770521/68719476736)), (199/274877906944), by norm_num⟩
  | 3 => ⟨((-25907475139/274877906944), (-24931461647/137438953472)), (15/34359738368), by norm_num⟩
  | 4 => ⟨((11332999/268435456), (89342364975/1099511627776)), (217/1099511627776), by norm_num⟩
  | 5 => ⟨((-16634681977/1099511627776), (-64032011379/2199023255552)), (157/2199023255552), by norm_num⟩
  | 6 => ⟨((19870232633/4398046511104), (76486641815/8796093022208)), (95/4398046511104), by norm_num⟩
  | 7 => ⟨((-20344387129/17592186044416), (-9788976053/4398046511104)), (197/35184372088832), by norm_num⟩
  | 8 => ⟨((9113062071/35184372088832), (17539490537/35184372088832)), (89/70368744177664), by norm_num⟩
  | 9 => ⟨((-14514146897/281474976710656), (-3491838695/35184372088832)), (143/562949953421312), by norm_num⟩
  | 10 => ⟨((41609376225/4503599627370496), (80083648599/4503599627370496)), (207/4503599627370496), by norm_num⟩
  | 11 => ⟨((-13555271611/9007199254740992), (-52178412985/18014398509481984)), (137/18014398509481984), by norm_num⟩
  | 12 => ⟨((32383715023/144115188075855872), (62327443703/144115188075855872)), (83/72057594037927936), by norm_num⟩
  | 13 => ⟨((-17853485551/576460752303423488), (-34361780753/576460752303423488)), (185/1152921504606846976), by norm_num⟩
  | 14 => ⟨((36559030623/9223372036854775808), (70363481193/9223372036854775808)), (3/144115188075855872), by norm_num⟩
  | 15 => ⟨((-4366999287/9223372036854775808), (-67239697981/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 16 => ⟨((15649224649/295147905179352825856), (60238682783/590295810358705651712)), (169/590295810358705651712), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (88871695403/633825300114114700748351602688)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444895941918833/158456325028528675187087900672), (1684270285929/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890658539925629/39614081257132168796771975168), (947271963107/19807040628566084398385987584)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472622671196743/618970019642690137449562112), (2012635382865/2475880078570760549798248448)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886078342544077/77371252455336267181195264), (503069556063/38685626227668133590597632)), (863/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550458783502527/9671406556917033397649408), (1886131429125/9671406556917033397649408)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259580607343861/604462909807314587353088), (103124104915/37778931862957161709568)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236134803123159/9444732965739290427392), (2680515678365/75557863725914323419136)), (2303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324625951019461/1180591620717411303424), (1004882384761/2361183241434822606848)), (1727/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622773391117023/590295810358705651712), (690604040273/147573952589676412928)), (297/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1825130155030635/73786976294838206464), (862876298221/18446744073709551616)), (1485/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824517903366597/9223372036854775808), (3880861158939/9223372036854775808)), (3343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797882284577679/576460752303423488), (1939129929995/576460752303423488)), (209/72057594037927936), by norm_num⟩
  | 5 => ⟨((1196135064262925/144115188075855872), (3390552881381/144115188075855872)), (183/9007199254740992), by norm_num⟩
  | 4 => ⟨((186745590246461/4503599627370496), (2539992620131/18014398509481984)), (4395/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492159612841649/9007199254740992), (6339765448429/9007199254740992)), (1375/2251799813685248), by norm_num⟩
  | 2 => ⟨((279216292233681/562949953421312), (6324463360219/2251799813685248)), (11017/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112361633672707/1125899906842624), (2362129241381/281474976710656)), (4143/562949953421312), by norm_num⟩
  | 0 => ⟨((2197757642065657/2251799813685248), (37489567724231/2251799813685248)), (33333/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197757642065657/2251799813685248), (37489567724231/2251799813685248)), (127155312545012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144388304956489/2251799813685248), (73179670291227/2251799813685248)), (66177/2251799813685248), by norm_num⟩
  | 2 => ⟨((509930535385087/562949953421312), (69688978646933/1125899906842624)), (130343/2251799813685248), by norm_num⟩
  | 3 => ⟨((459747817561699/562949953421312), (252502290662949/2251799813685248)), (126135/1125899906842624), by norm_num⟩
  | 4 => ⟨((736773194732507/1125899906842624), (412425212422891/2251799813685248)), (234311/1125899906842624), by norm_num⟩
  | 5 => ⟨((444365523502757/1125899906842624), (539770612819705/2251799813685248)), (196245/562949953421312), by norm_num⟩
  | 6 => ⟨((110687139331435/1125899906842624), (852137741478857/4503599627370496)), (1991911/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-119093119403/2147483648)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-32334768381/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-722000986465347/4503599627370496), (215384303647315/2251799813685248)), (2353781/4503599627370496), by norm_num⟩
  | 1 => ⟨((42875642309/137438953472), (-12790481641/68719476736)), (141/137438953472), by norm_num⟩
  | 2 => ⟨((-20858036879/68719476736), (49778256073/274877906944)), (69/68719476736), by norm_num⟩
  | 3 => ⟨((54117154203/274877906944), (-32288004565/274877906944)), (181/274877906944), by norm_num⟩
  | 4 => ⟨((-52653559801/549755813888), (981711809/17179869184)), (89/274877906944), by norm_num⟩
  | 5 => ⟨((1280738705/34359738368), (-24452134049/1099511627776)), (279/2199023255552), by norm_num⟩
  | 6 => ⟨((-53166985479/4398046511104), (31721103875/4398046511104)), (183/4398046511104), by norm_num⟩
  | 7 => ⟨((59118958079/17592186044416), (-4409029855/2199023255552)), (205/17592186044416), by norm_num⟩
  | 8 => ⟨((-7190011283/8796093022208), (34318303769/70368744177664)), (201/70368744177664), by norm_num⟩
  | 9 => ⟨((12436547491/70368744177664), (-29680149157/281474976710656)), (175/281474976710656), by norm_num⟩
  | 10 => ⟨((-38720646371/1125899906842624), (5775490347/281474976710656)), (137/1125899906842624), by norm_num⟩
  | 11 => ⟨((27398872273/4503599627370496), (-32694066275/9007199254740992)), (195/9007199254740992), by norm_num⟩
  | 12 => ⟨((-71087658171/72057594037927936), (42413143585/72057594037927936)), (255/72057594037927936), by norm_num⟩
  | 13 => ⟨((42563137079/288230376151711744), (-12697256393/144115188075855872)), (77/144115188075855872), by norm_num⟩
  | 14 => ⟨((-5916002887/288230376151711744), (28237394377/2305843009213693952)), (173/2305843009213693952), by norm_num⟩
  | 15 => ⟨((12279477397/4611686018427387904), (-29305297227/18446744073709551616)), (181/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-5973689923/18446744073709551616), (28512737647/147573952589676412928)), (89/73786976294838206464), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (847887376867/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779371543723299/633825300114114700748351602688), (4016347464631/633825300114114700748351602688)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890419412080849/39614081257132168796771975168), (1129425363931/9903520314283042199192993792)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118139758038697/154742504910672534362390528), (4799233423979/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771901586058661/154742504910672534362390528), (4798305967807/154742504910672534362390528)), (1731/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550219051688263/9671406556917033397649408), (4497426475027/9671406556917033397649408)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629685132944011/302231454903657293676544), (245891428413/37778931862957161709568)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944367770326691/37778931862957161709568), (3195664902835/37778931862957161709568)), (2311/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298245697051569/4722366482869645213696), (4791881063275/4722366482869645213696)), (1735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622416961733783/590295810358705651712), (6586210225089/590295810358705651712)), (2385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824682322445553/73786976294838206464), (8228823840229/73786976294838206464)), (373/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824010938929745/9223372036854775808), (578250715745/576460752303423488)), (105/288230376151711744), by norm_num⟩
  | 6 => ⟨((1595253669776937/1152921504606846976), (4622621629789/576460752303423488)), (841/288230376151711744), by norm_num⟩
  | 5 => ⟨((298920902196413/36028797018963968), (8081975042919/144115188075855872)), (737/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493278722417203/36028797018963968), (12107740485783/36028797018963968)), (2215/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491286731343897/9007199254740992), (15108044994393/9007199254740992)), (347/562949953421312), by norm_num⟩
  | 2 => ⟨((1115969307316763/2251799813685248), (15068115274461/2251799813685248)), (2787/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110960715797893/1125899906842624), (5625601495539/281474976710656)), (8417/1125899906842624), by norm_num⟩
  | 0 => ⟨((547925214246445/562949953421312), (44606093830443/1125899906842624)), (8529/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547925214246445/562949953421312), (44606093830443/1125899906842624)), (32535555125999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((532417868913111/562949953421312), (10853897122739/140737488355328)), (17279/562949953421312), by norm_num⟩
  | 2 => ⟨((1000386880228499/1125899906842624), (82121811935435/562949953421312)), (70699/1125899906842624), by norm_num⟩
  | 3 => ⟨((432453158683487/562949953421312), (145934079471035/562949953421312)), (146263/1125899906842624), by norm_num⟩
  | 4 => ⟨((1177504166380081/2251799813685248), (896842118817405/2251799813685248)), (75137/281474976710656), by norm_num⟩
  | 5 => ⟨((64636104885891/562949953421312), (468973895936313/1125899906842624)), (553727/1125899906842624), by norm_num⟩
  | 6 => ⟨((-722000986465347/4503599627370496), (215384303647315/2251799813685248)), (2353781/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-32334768381/536870912)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1925775643/1073741824), (-69107261345/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((15541932663433/2251799813685248), (-748635863846815/4503599627370496)), (925675/1125899906842624), by norm_num⟩
  | 1 => ⟨((-493141791/34359738368), (95016144707/274877906944)), (59/34359738368), by norm_num⟩
  | 2 => ⟨((4101838105/274877906944), (-98790259217/274877906944)), (247/137438953472), by norm_num⟩
  | 3 => ⟨((-1421588759/137438953472), (68476189643/274877906944)), (345/274877906944), by norm_num⟩
  | 4 => ⟨((2956110721/549755813888), (-8899514585/68719476736)), (361/549755813888), by norm_num⟩
  | 5 => ⟨((-1229411887/549755813888), (118438530105/2199023255552)), (603/2199023255552), by norm_num⟩
  | 6 => ⟨((3408653533/4398046511104), (-20523833303/1099511627776)), (105/1099511627776), by norm_num⟩
  | 7 => ⟨((-4050340433/17592186044416), (97549969291/17592186044416)), (501/17592186044416), by norm_num⟩
  | 8 => ⟨((4211223077/70368744177664), (-101424729267/70368744177664)), (523/70368744177664), by norm_num⟩
  | 9 => ⟨((-3891996537/281474976710656), (23434088377/70368744177664)), (243/140737488355328), by norm_num⟩
  | 10 => ⟨((101164741/35184372088832), (-19491926745/281474976710656)), (407/1125899906842624), by norm_num⟩
  | 11 => ⟨((-4895794385/9007199254740992), (14739026255/1125899906842624)), (309/4503599627370496), by norm_num⟩
  | 12 => ⟨((3393506075/36028797018963968), (-81730515943/36028797018963968)), (431/36028797018963968), by norm_num⟩
  | 13 => ⟨((-4342521541/288230376151711744), (52293486177/144115188075855872)), (277/144115188075855872), by norm_num⟩
  | 14 => ⟨((2580005625/1152921504606846976), (-124275711447/2305843009213693952)), (661/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-357664725/1152921504606846976), (34456543601/4611686018427387904)), (369/9223372036854775808), by norm_num⟩
  | 16 => ⟨((2974971549/73786976294838206464), (-71650368147/73786976294838206464)), (193/36893488147419103232), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-1992083331147/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222399943574483/79228162514264337593543950336), (-2358620756579/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890226274312879/39614081257132168796771975168), (-2653026103829/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945015686618531/1237940039285380274899124224), (-352290505835/309485009821345068724781056)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221462167575657/19342813113834066795298816), (-2817743453901/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550028113115321/9671406556917033397649408), (-660254434205/2417851639229258349412352)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629601867942247/302231454903657293676544), (-2310273913151/604462909807314587353088)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888465943617263/75557863725914323419136), (-3753039278885/75557863725914323419136)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298044386096789/4722366482869645213696), (-1406884207605/2361183241434822606848)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622141599095311/590295810358705651712), (-1933644600273/295147905179352825856)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824340277001305/73786976294838206464), (-4831648953033/73786976294838206464)), (5947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823629101552093/9223372036854775808), (-2716110353309/4611686018427387904)), (3347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797437766066229/576460752303423488), (-1356998176313/288230376151711744)), (6699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597678446871369/72057594037927936), (-4744740490909/144115188075855872)), (5867/144115188075855872), by norm_num⟩
  | 4 => ⟨((746398471822835/18014398509481984), (-3553806459607/18014398509481984)), (8809/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490698983797371/9007199254740992), (-8867913939567/9007199254740992)), (11029/9007199254740992), by norm_num⟩
  | 2 => ⟨((557701598639745/1125899906842624), (-2210762136191/562949953421312)), (22109/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220330755103277/2251799813685248), (-13202541949883/1125899906842624)), (33295/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188946920104297/2251799813685248), (-26157755362845/1125899906842624)), (33559/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188946920104297/2251799813685248), (-26157755362845/1125899906842624)), (128017429832076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1063316480725351/1125899906842624), (-101710529844363/2251799813685248)), (133609/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003829422768605/2251799813685248), (-192113849534115/2251799813685248)), (66109/562949953421312), by norm_num⟩
  | 3 => ⟨((883387723942329/1125899906842624), (-170958085118489/1125899906842624)), (257877/1125899906842624), by norm_num⟩
  | 4 => ⟨((1334305473123415/2251799813685248), (-536538897585931/2251799813685248)), (482977/1125899906842624), by norm_num⟩
  | 5 => ⟨((662801860944195/2251799813685248), (-317926479628255/1125899906842624)), (100317/140737488355328), by norm_num⟩
  | 6 => ⟨((15541932663433/2251799813685248), (-748635863846815/4503599627370496)), (925675/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-69107261345/1073741824)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile059Terms0
