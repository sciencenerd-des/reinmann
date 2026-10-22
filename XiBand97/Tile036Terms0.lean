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
namespace Reinmann.XiBand97.Tile036Terms0
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
  | 0 => ⟨((-20060163/33554432), (-604403261/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((829466618063691/2251799813685248), (919692806294553/2251799813685248)), (70913617/2251799813685248), by norm_num⟩
  | 1 => ⟨((-274153923/1073741824), (-75993833/268435456)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((760116075/8589934592), (842798577/8589934592)), (35/4294967296), by norm_num⟩
  | 3 => ⟨((-702496419/34359738368), (-778911277/34359738368)), (67/34359738368), by norm_num⟩
  | 4 => ⟨((121733353/34359738368), (1079800311/274877906944)), (95/274877906944), by norm_num⟩
  | 5 => ⟨((-540026435/1099511627776), (-598768433/1099511627776)), (27/549755813888), by norm_num⟩
  | 6 => ⟨((499090401/8796093022208), (553379535/8796093022208)), (51/8796093022208), by norm_num⟩
  | 7 => ⟨((-98840887/17592186044416), (-876739347/140737488355328)), (83/140737488355328), by norm_num⟩
  | 8 => ⟨((548090257/1125899906842624), (303854703/562949953421312)), (15/281474976710656), by norm_num⟩
  | 9 => ⟨((-675390607/18014398509481984), (-374428499/9007199254740992)), (19/4503599627370496), by norm_num⟩
  | 10 => ⟨((93629019/36028797018963968), (830508987/288230376151711744)), (43/144115188075855872), by norm_num⟩
  | 11 => ⟨((-755184763/4611686018427387904), (-837330855/4611686018427387904)), (89/4611686018427387904), by norm_num⟩
  | 12 => ⟨((697938919/73786976294838206464), (193464507/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-595414639/1180591620717411303424), (-660181551/1180591620717411303424)), (73/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((943337093/37778931862957161709568), (522974835/18889465931478580854784)), (59/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-174365719/151115727451828646838272), (-386665101/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((241722213/4835703278458516698824704), (536031649/9671406556917033397649408)), (63/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (1090201392555/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781047532864589/633825300114114700748351602688), (323335293593/158456325028528675187087900672)), (11541/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236538144046147/4951760157141521099596496896), (1454929646497/39614081257132168796771975168)), (51939/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892240065032707/2475880078570760549798248448), (1545768319621/2475880078570760549798248448)), (55189/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773905901655893/154742504910672534362390528), (772831044177/77371252455336267181195264)), (55195/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552098500118075/9671406556917033397649408), (724472670359/4835703278458516698824704)), (51751/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315253796363951/151115727451828646838272), (1267714310071/604462909807314587353088)), (5661/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891409288283579/75557863725914323419136), (2059824144257/75557863725914323419136)), (73603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300251666163603/4722366482869645213696), (1544682958415/4722366482869645213696)), (55211/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203147029711259/73786976294838206464), (2123638215615/590295810358705651712)), (37965/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828133017485847/73786976294838206464), (2654096519547/73786976294838206464)), (94935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827895166845745/9223372036854775808), (746309540463/2305843009213693952)), (106833/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599140636489211/1152921504606846976), (2984462702709/1152921504606846976)), (106871/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599543888644247/72057594037927936), (2610532568495/144115188075855872)), (23389/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498391099159585/36028797018963968), (61157101533/562949953421312)), (140421/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497687871444609/9007199254740992), (1222379009603/2251799813685248)), (2745/140737488355328), by norm_num⟩
  | 2 => ⟨((561193177848689/1125899906842624), (2442469493165/1125899906842624)), (175909/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120625725493779/1125899906842624), (3657984807985/562949953421312)), (66109/281474976710656), by norm_num⟩
  | 0 => ⟨((278834049939971/281474976710656), (14586206432077/1125899906842624)), (16599/35184372088832), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278834049939971/281474976710656), (14586206432077/1125899906842624)), (63320160046327103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1104682639653679/1125899906842624), (28898703964703/1125899906842624)), (266533/281474976710656), by norm_num⟩
  | 2 => ⟨((270780864233573/281474976710656), (56708232027167/1125899906842624)), (2146813/1125899906842624), by norm_num⟩
  | 3 => ⟨((519557996350903/562949953421312), (109107418761839/1125899906842624)), (1086689/281474976710656), by norm_num⟩
  | 4 => ⟨((59278005696261/70368744177664), (100697462597523/562949953421312)), (4432941/562949953421312), by norm_num⟩
  | 5 => ⟨((381469907081711/562949953421312), (678613191832369/2251799813685248)), (4527211/281474976710656), by norm_num⟩
  | 6 => ⟨((829466618063691/2251799813685248), (919692806294553/2251799813685248)), (70913617/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-604403261/33554432)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-119744563/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1680390931222785/4503599627370496), (237055164621219/2251799813685248)), (4651077/140737488355328), by norm_num⟩
  | 1 => ⟨((880288185/2147483648), (-3880735/33554432)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-483547709/2147483648), (136429541/2147483648)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((708308607/8589934592), (-199844227/8589934592)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-194539135/8589934592), (439102647/68719476736)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((341956935/68719476736), (-385922851/274877906944)), (67/137438953472), by norm_num⟩
  | 6 => ⟨((-1001808243/1099511627776), (141326529/549755813888)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((628913627/4398046511104), (-177443499/4398046511104)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-1381864479/70368744177664), (389883217/70368744177664)), (143/70368744177664), by norm_num⟩
  | 9 => ⟨((1349451821/562949953421312), (-47592277/70368744177664)), (71/281474976710656), by norm_num⟩
  | 10 => ⟨((-1186019483/4503599627370496), (167313473/2251799813685248)), (127/4503599627370496), by norm_num⟩
  | 11 => ⟨((947618603/36028797018963968), (-66840959/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1388087257/576460752303423488), (24477433/36028797018963968)), (155/576460752303423488), by norm_num⟩
  | 13 => ⟨((117305363/576460752303423488), (-132387489/2305843009213693952)), (107/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-1178268465/73786976294838206464), (332440051/73786976294838206464)), (17/9223372036854775808), by norm_num⟩
  | 15 => ⟨((1380757563/1180591620717411303424), (-389570907/1180591620717411303424)), (161/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-1516917227/18889465931478580854784), (213993693/9444732965739290427392)), (179/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (3734063913643/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890248851591109/316912650057057350374175801344), (138352822001/19807040628566084398385987584)), (23159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891686065977145/39614081257132168796771975168), (2490125004601/19807040628566084398385987584)), (26061/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472895407609809/618970019642690137449562112), (2645500188403/1237940039285380274899124224)), (55395/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773246730027403/154742504910672534362390528), (20665704951/604462909807314587353088)), (55413/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193934967983125/1208925819614629174706176), (2479576427165/4835703278458516698824704)), (25985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39389780973817/18889465931478580854784), (2169321105505/302231454903657293676544)), (45493/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890526755826753/75557863725914323419136), (3524568578335/37778931862957161709568)), (36981/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299588484025959/4722366482869645213696), (1321460138989/1180591620717411303424)), (55503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624262278821763/590295810358705651712), (3633192476503/295147905179352825856)), (4773/36893488147419103232), by norm_num⟩
  | 8 => ⟨((228373430713111/9223372036854775808), (4540255533331/36893488147419103232)), (95537/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114162631710291/576460752303423488), (10212176244585/9223372036854775808)), (53793/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597842217724919/1152921504606846976), (10207924441949/1152921504606846976)), (107719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74871602388223/9007199254740992), (8927145913593/144115188075855872)), (94405/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496665861574067/36028797018963968), (13381131211949/36028797018963968)), (70953/18014398509481984), by norm_num⟩
  | 3 => ⟨((747755155282427/4503599627370496), (16709609330737/9007199254740992)), (44477/2251799813685248), by norm_num⟩
  | 2 => ⟨((560088673811233/1125899906842624), (16684349916943/2251799813685248)), (178697/2251799813685248), by norm_num⟩
  | 1 => ⟨((139654231675755/140737488355328), (3120399222281/140737488355328)), (135011/562949953421312), by norm_num⟩
  | 0 => ⟨((277060141398829/281474976710656), (1552249191855/35184372088832)), (273985/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277060141398829/281474976710656), (1552249191855/35184372088832)), (1045169832469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1088666797791515/1125899906842624), (48892886818699/562949953421312)), (563551/562949953421312), by norm_num⟩
  | 2 => ⟨((522086080628877/562949953421312), (94552032919097/562949953421312)), (2375439/1125899906842624), by norm_num⟩
  | 3 => ⟨((234153841789187/281474976710656), (350754449714145/1125899906842624)), (5203967/1125899906842624), by norm_num⟩
  | 4 => ⟨((669881627501831/1125899906842624), (583572315272955/1125899906842624)), (2975145/281474976710656), by norm_num⟩
  | 5 => ⟨((192174716516051/2251799813685248), (1388842364917973/2251799813685248)), (52995223/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1680390931222785/4503599627370496), (237055164621219/2251799813685248)), (4651077/140737488355328), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-119744563/4194304)), (1/33554432), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-604403261/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-140172307066307/4503599627370496), (1355101776025413/4503599627370496)), (222415751/4503599627370496), by norm_num⟩
  | 1 => ⟨((46329517/1073741824), (-895771957/2147483648)), (37/536870912), by norm_num⟩
  | 2 => ⟨((-16056587/536870912), (1241803613/4294967296)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((118715499/8589934592), (-1147670231/8589934592)), (193/8589934592), by norm_num⟩
  | 4 => ⟨((-164574627/34359738368), (795504385/17179869184)), (135/17179869184), by norm_num⟩
  | 5 => ⟨((91259551/68719476736), (-1764485189/137438953472)), (151/68719476736), by norm_num⟩
  | 6 => ⟨((-42170867/137438953472), (1630730579/549755813888)), (281/549755813888), by norm_num⟩
  | 7 => ⟨((8351605/137438953472), (-645906459/1099511627776)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((-185244527/17592186044416), (447708241/4398046511104)), (313/17592186044416), by norm_num⟩
  | 9 => ⟨((7133429/4398046511104), (-1103387395/70368744177664)), (195/70368744177664), by norm_num⟩
  | 10 => ⟨((-126579615/562949953421312), (1223695779/562949953421312)), (109/281474976710656), by norm_num⟩
  | 11 => ⟨((63809675/2251799813685248), (-1233747315/4503599627370496)), (221/4503599627370496), by norm_num⟩
  | 12 => ⟨((-29486331/9007199254740992), (1140224631/36028797018963968)), (103/18014398509481984), by norm_num⟩
  | 13 => ⟨((50309827/144115188075855872), (-972730447/288230376151711744)), (177/288230376151711744), by norm_num⟩
  | 14 => ⟨((-79707691/2305843009213693952), (1541132267/4611686018427387904)), (141/2305843009213693952), by norm_num⟩
  | 15 => ⟨((117864877/36893488147419103232), (-569723459/18446744073709551616)), (105/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-81697707/295147905179352825856), (1579608837/590295810358705651712)), (293/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (2180402785111/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780121454964613/633825300114114700748351602688), (323017048771/79228162514264337593543950336)), (46227/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891263241975853/39614081257132168796771975168), (1453419143195/19807040628566084398385987584)), (104027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236391617399133/309485009821345068724781056), (96504317607/77371252455336267181195264)), (27637/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221599833481197/19342813113834066795298816), (3087713469697/154742504910672534362390528)), (110569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775530176896899/4835703278458516698824704), (2894280169791/9671406556917033397649408)), (103681/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315026673221347/151115727451828646838272), (2532043973161/604462909807314587353088)), (11343/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472483193325115/18889465931478580854784), (4113725571911/75557863725914323419136)), (36875/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299144092389607/4722366482869645213696), (3084554099481/4722366482869645213696)), (55331/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623653019378647/590295810358705651712), (4240059388031/590295810358705651712)), (38055/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28534820917095/1152921504606846976), (5298270715243/73786976294838206464)), (95183/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456438000601059/2305843009213693952), (5958075086389/9223372036854775808)), (214285/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596996691393583/1152921504606846976), (2977488154485/576460752303423488)), (214441/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197210949288169/144115188075855872), (1301779728509/36028797018963968)), (187811/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495574110557097/36028797018963968), (7803709582619/36028797018963968)), (141033/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494163591459157/9007199254740992), (1217805742189/1125899906842624)), (88299/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118857533976291/2251799813685248), (9724168078235/2251799813685248)), (88529/562949953421312), by norm_num⟩
  | 1 => ⟨((139415153073209/140737488355328), (3635147008215/281474976710656)), (133369/281474976710656), by norm_num⟩
  | 0 => ⟨((1104682639653679/1125899906842624), (14449351982351/562949953421312)), (538093/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104682639653679/1125899906842624), (14449351982351/562949953421312)), (2052661897899436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((270780864233573/281474976710656), (56708232027165/1125899906842624)), (1083529/562949953421312), by norm_num⟩
  | 2 => ⟨((519557996350903/562949953421312), (27276854690459/281474976710656)), (4387747/1125899906842624), by norm_num⟩
  | 3 => ⟨((59278005696261/70368744177664), (201394925195041/1125899906842624)), (8949489/1125899906842624), by norm_num⟩
  | 4 => ⟨((1525879628326847/2251799813685248), (21206662244761/70368744177664)), (36559227/2251799813685248), by norm_num⟩
  | 5 => ⟨((829466618063705/2251799813685248), (229923201573633/562949953421312)), (71582345/2251799813685248), by norm_num⟩
  | 6 => ⟨((-140172307066307/4503599627370496), (1355101776025413/4503599627370496)), (222415751/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-604403261/16777216)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-87711307/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-622906183161843/4503599627370496), (467698448034257/2251799813685248)), (200252399/4503599627370496), by norm_num⟩
  | 1 => ⟨((478042997/2147483648), (-717860807/2147483648)), (155/2147483648), by norm_num⟩
  | 2 => ⟨((-769380523/4294967296), (1155352399/4294967296)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((825513455/8589934592), (-619822651/4294967296)), (273/8589934592), by norm_num⟩
  | 4 => ⟨((-332153163/8589934592), (498783037/8589934592)), (111/8589934592), by norm_num⟩
  | 5 => ⟨((855327829/68719476736), (-80276033/4294967296)), (9/2147483648), by norm_num⟩
  | 6 => ⟨((-458865679/137438953472), (689062885/137438953472)), (39/34359738368), by norm_num⟩
  | 7 => ⟨((844018081/1099511627776), (-158429133/137438953472)), (289/1099511627776), by norm_num⟩
  | 8 => ⟨((-679197349/4398046511104), (1019927413/4398046511104)), (235/4398046511104), by norm_num⟩
  | 9 => ⟨((242916881/8796093022208), (-182389983/4398046511104)), (85/8796093022208), by norm_num⟩
  | 10 => ⟨((-625535421/140737488355328), (939345131/140737488355328)), (221/140737488355328), by norm_num⟩
  | 11 => ⟨((366094699/562949953421312), (-549751879/562949953421312)), (65/281474976710656), by norm_num⟩
  | 12 => ⟨((-392804459/4503599627370496), (589861011/4503599627370496)), (281/9007199254740992), by norm_num⟩
  | 13 => ⟨((778085401/72057594037927936), (-1168424215/72057594037927936)), (281/72057594037927936), by norm_num⟩
  | 14 => ⟨((-357794327/288230376151711744), (268643747/144115188075855872)), (261/576460752303423488), by norm_num⟩
  | 15 => ⟨((614237605/4611686018427387904), (-922379587/4611686018427387904)), (113/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-123572161/9223372036854775808), (742256339/36893488147419103232)), (23/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (351426187805/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779822017072729/633825300114114700748351602688), (104091451839/19807040628566084398385987584)), (5783/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1890926276707927/39614081257132168796771975168), (3746818880747/39614081257132168796771975168)), (104115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118173424160427/154742504910672534362390528), (124388429915/77371252455336267181195264)), (110647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886220186206623/77371252455336267181195264), (1989896888495/77371252455336267181195264)), (110673/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550724300182743/9671406556917033397649408), (1865190482913/4835703278458516698824704)), (103785/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157476561805553/75557863725914323419136), (3263407677509/604462909807314587353088)), (45421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944727208471299/37778931862957161709568), (1325442667113/18889465931478580854784)), (18459/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649392538473067/2361183241434822606848), (3975219614157/4722366482869645213696)), (55401/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811579485145057/295147905179352825856), (2732062985355/295147905179352825856)), (76215/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456402593451571/18446744073709551616), (853432024267/9223372036854775808)), (190653/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825055738279565/9223372036854775808), (1919293586583/2305843009213693952)), (214645/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596299393321435/1152921504606846976), (7672532568107/1152921504606846976)), (107423/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196599652805559/144115188075855872), (1677061193155/36028797018963968)), (23527/18014398509481984), by norm_num⟩
  | 4 => ⟨((93415928174571/2251799813685248), (1256490832555/4503599627370496)), (35347/4503599627370496), by norm_num⟩
  | 3 => ⟨((1493010479593833/9007199254740992), (12546641870243/9007199254740992)), (88565/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117698394657681/2251799813685248), (3129812773135/562949953421312)), (44431/281474976710656), by norm_num⟩
  | 1 => ⟨((556783772917571/562949953421312), (4677607795611/281474976710656)), (134037/281474976710656), by norm_num⟩
  | 0 => ⟨((1101115995064977/1125899906842624), (580426125239/17592186044416)), (1084227/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101115995064977/1125899906842624), (580426125239/17592186044416)), (4135997776511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075652025024137/1125899906842624), (72659132735481/1125899906842624)), (1096133/562949953421312), by norm_num⟩
  | 2 => ⟨((1022957655799543/1125899906842624), (69416422177875/562949953421312)), (4367/1099511627776), by norm_num⟩
  | 3 => ⟨((912308279487729/1125899906842624), (252278413288815/1125899906842624)), (9228715/1125899906842624), by norm_num⟩
  | 4 => ⟨((1365417999129083/2251799813685248), (408838625495301/1125899906842624)), (9545821/562949953421312), by norm_num⟩
  | 5 => ⟨((531028654630337/2251799813685248), (247906414503553/562949953421312)), (9254569/281474976710656), by norm_num⟩
  | 6 => ⟨((-622906183161843/4503599627370496), (467698448034257/2251799813685248)), (200252399/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-87711307/2097152)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1562359765/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-812622876518395/4503599627370496), (-511672819590849/4503599627370496)), (86012065/4503599627370496), by norm_num⟩
  | 1 => ⟨((694286697/2147483648), (437161741/2147483648)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-310998691/1073741824), (-783288689/4294967296)), (17/536870912), by norm_num⟩
  | 3 => ⟨((742979799/4294967296), (233910821/2147483648)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((-665620545/8589934592), (-419111929/8589934592)), (19/2147483648), by norm_num⟩
  | 5 => ⟨((238526383/8589934592), (300379107/17179869184)), (111/34359738368), by norm_num⟩
  | 6 => ⟨((-1139685081/137438953472), (-717609479/137438953472)), (135/137438953472), by norm_num⟩
  | 7 => ⟨((583440439/274877906944), (367366737/274877906944)), (35/137438953472), by norm_num⟩
  | 8 => ⟨((-1045384931/2199023255552), (-329116415/1099511627776)), (127/2199023255552), by norm_num⟩
  | 9 => ⟨((416239633/4398046511104), (262087757/4398046511104)), (103/8796093022208), by norm_num⟩
  | 10 => ⟨((-596641043/35184372088832), (-751357153/70368744177664)), (75/35184372088832), by norm_num⟩
  | 11 => ⟨((194370407/70368744177664), (489545925/281474976710656)), (99/281474976710656), by norm_num⟩
  | 12 => ⟨((-928706713/2251799813685248), (-292382849/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 13 => ⟨((512005861/9007199254740992), (644775063/18014398509481984)), (67/9007199254740992), by norm_num⟩
  | 14 => ⟨((-1048447257/144115188075855872), (-660161043/144115188075855872)), (139/144115188075855872), by norm_num⟩
  | 15 => ⟨((500950747/576460752303423488), (630853227/1152921504606846976)), (135/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-897583245/9223372036854775808), (-282584311/4611686018427387904)), (123/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-420035634711/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779576818306955/633825300114114700748351602688), (-3980196030727/633825300114114700748351602688)), (46297/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890650319014149/39614081257132168796771975168), (-2238544131541/19807040628566084398385987584)), (407/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((1890481438185153/2475880078570760549798248448), (-4756153802797/2475880078570760549798248448)), (27683/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772146862903477/154742504910672534362390528), (-4755307201611/154742504910672534362390528)), (55383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550448963938621/9671406556917033397649408), (-557150125633/1208925819614629174706176)), (51939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314892851071713/151115727451828646838272), (-1949575701165/302231454903657293676544)), (5683/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889062325202881/75557863725914323419136), (-3167217275309/37778931862957161709568)), (73911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298490728223081/4722366482869645213696), (-593668785785/590295810358705651712)), (27731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101422111654073/36893488147419103232), (-3263979414583/295147905179352825856)), (38153/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456275803366847/18446744073709551616), (-8156351954171/73786976294838206464)), (23863/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912242124327857/4611686018427387904), (-9170950876889/9223372036854775808)), (13435/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398931684544899/288230376151711744), (-4582384942761/576460752303423488)), (6725/72057594037927936), by norm_num⟩
  | 5 => ⟨((299024317872269/36028797018963968), (-4006110260177/72057594037927936)), (94285/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493898670528985/36028797018963968), (-3001106439421/9007199254740992)), (141697/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492060707393733/9007199254740992), (-14981201247641/9007199254740992)), (88797/4503599627370496), by norm_num⟩
  | 2 => ⟨((279185459346829/562949953421312), (-14944710652387/2251799813685248)), (178305/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112115870400995/1125899906842624), (-22325860555749/1125899906842624)), (134619/562949953421312), by norm_num⟩
  | 0 => ⟨((1098146023567427/1125899906842624), (-5535878888599/140737488355328)), (136405/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098146023567427/1125899906842624), (-5535878888599/140737488355328)), (520343781591319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((534667131880671/562949953421312), (-21597669034413/281474976710656)), (1107265/1125899906842624), by norm_num⟩
  | 2 => ⟨((252245428706941/281474976710656), (-164100750878583/1125899906842624)), (2273193/1125899906842624), by norm_num⟩
  | 3 => ⟨((880286993892075/1125899906842624), (-294119674439479/1125899906842624)), (2368455/562949953421312), by norm_num⟩
  | 4 => ⟨((305710483027593/562949953421312), (-919832118231215/2251799813685248)), (4940989/562949953421312), by norm_num⟩
  | 5 => ⟨((144162740677901/1125899906842624), (-999031332926701/2251799813685248)), (4701541/281474976710656), by norm_num⟩
  | 6 => ⟨((-812622876518395/4503599627370496), (-511672819590849/4503599627370496)), (86012065/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1562359765/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-848387235/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1605217095659281/9007199254740992), (-125166433537429/2251799813685248)), (67679151/4503599627370496), by norm_num⟩
  | 1 => ⟨((-372363119/1073741824), (58069857/536870912)), (1/33554432), by norm_num⟩
  | 2 => ⟨((1449170345/4294967296), (-28249681/268435456)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((-469992547/2147483648), (293180485/4294967296)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((914563267/8589934592), (-285251441/8589934592)), (41/4294967296), by norm_num⟩
  | 5 => ⟨((-1423726355/34359738368), (444058939/34359738368)), (65/17179869184), by norm_num⟩
  | 6 => ⟨((230870297/17179869184), (-72008233/17179869184)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-513431833/137438953472), (40034729/34359738368)), (97/274877906944), by norm_num⟩
  | 8 => ⟨((999092215/1099511627776), (-155807971/549755813888)), (3/34359738368), by norm_num⟩
  | 9 => ⟨((-432031929/2199023255552), (134750361/2199023255552)), (85/4398046511104), by norm_num⟩
  | 10 => ⟨((1345112505/35184372088832), (-52442419/4398046511104)), (67/17592186044416), by norm_num⟩
  | 11 => ⟨((-951806573/140737488355328), (148433797/70368744177664)), (3/4398046511104), by norm_num⟩
  | 12 => ⟨((308688345/281474976710656), (-385118443/1125899906842624)), (63/562949953421312), by norm_num⟩
  | 13 => ⟨((-739298195/4503599627370496), (461172853/9007199254740992)), (153/9007199254740992), by norm_num⟩
  | 14 => ⟨((822061635/36028797018963968), (-256400267/36028797018963968)), (43/18014398509481984), by norm_num⟩
  | 15 => ⟨((-853150975/288230376151711744), (66524251/72057594037927936)), (91/288230376151711744), by norm_num⟩
  | 16 => ⟨((830077571/2305843009213693952), (-129450215/1152921504606846976)), (45/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-393828111157/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779380050910761/633825300114114700748351602688), (-233189952303/316912650057057350374175801344)), (46123/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236303684066917/4951760157141521099596496896), (-524599846153/39614081257132168796771975168)), (25945/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890247444096841/2475880078570760549798248448), (-557291907543/2475880078570760549798248448)), (55135/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885956802829369/77371252455336267181195264), (-557184580757/154742504910672534362390528)), (110273/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550231067807139/9671406556917033397649408), (-130561634677/2417851639229258349412352)), (51693/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314845381825383/151115727451828646838272), (-456851748199/604462909807314587353088)), (90467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888755240733005/75557863725914323419136), (-371085230171/37778931862957161709568)), (147015/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162282712054539/590295810358705651712), (-556440987771/4722366482869645213696)), (27567/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202805118585915/73786976294838206464), (-764802844441/590295810358705651712)), (75815/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912357642406483/36893488147419103232), (-1866305687/144115188075855872)), (94777/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456013028090197/2305843009213693952), (-1074366758835/9223372036854775808)), (106635/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797649974652713/576460752303423488), (-536792832457/576460752303423488)), (213299/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298932459404239/36028797018963968), (-469254742395/72057594037927936)), (46667/36028797018963968), by norm_num⟩
  | 4 => ⟨((746679754442151/18014398509481984), (-1406010178025/36028797018963968)), (140033/18014398509481984), by norm_num⟩
  | 3 => ⟨((11651622525553/70368744177664), (-877223697541/4503599627370496)), (350195/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232240198146971/4503599627370496), (-437464477237/562949953421312)), (87591/562949953421312), by norm_num⟩
  | 1 => ⟨((1111261106660659/1125899906842624), (-5226685722515/2251799813685248)), (1051941/2251799813685248), by norm_num⟩
  | 0 => ⟨((548372825224005/562949953421312), (-10362175115735/2251799813685248)), (2107309/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548372825224005/562949953421312), (-10362175115735/2251799813685248)), (8038745888716887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1068322477689373/1125899906842624), (-20187710147757/2251799813685248)), (4124879/2251799813685248), by norm_num⟩
  | 2 => ⟨((2027198019096425/2251799813685248), (-9577665116079/562949953421312)), (7901835/2251799813685248), by norm_num⟩
  | 3 => ⟨((912173470518253/1125899906842624), (-34489431312473/1125899906842624)), (14496235/2251799813685248), by norm_num⟩
  | 4 => ⟨((184490405051875/281474976710656), (-55884797689919/1125899906842624)), (24377031/2251799813685248), by norm_num⟩
  | 5 => ⟨((1923667420152367/4503599627370496), (-293033763286281/4503599627370496)), (34375381/2251799813685248), by norm_num⟩
  | 6 => ⟨((1605217095659281/9007199254740992), (-125166433537429/2251799813685248)), (67679151/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-848387235/16777216)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1813209783/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-1210183601948161/9007199254740992), (441911496214567/4503599627370496)), (203000607/4503599627370496), by norm_num⟩
  | 1 => ⟨((299990899/1073741824), (-876359103/4294967296)), (405/4294967296), by norm_num⟩
  | 2 => ⟨((-311906769/1073741824), (455584381/2147483648)), (213/2147483648), by norm_num⟩
  | 3 => ⟨((432394595/2147483648), (-315787029/2147483648)), (149/2147483648), by norm_num⟩
  | 4 => ⟨((-899139283/8589934592), (328330333/4294967296)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((747883031/17179869184), (-546194987/17179869184)), (261/17179869184), by norm_num⟩
  | 6 => ⟨((-1036786029/68719476736), (757187031/68719476736)), (365/68719476736), by norm_num⟩
  | 7 => ⟨((615981697/137438953472), (-449864619/137438953472)), (437/274877906944), by norm_num⟩
  | 8 => ⟨((-640448965/549755813888), (116933397/137438953472)), (229/549755813888), by norm_num⟩
  | 9 => ⟨((295950263/1099511627776), (-864555247/4398046511104)), (213/2199023255552), by norm_num⟩
  | 10 => ⟨((-492329017/8796093022208), (359558419/8796093022208)), (357/17592186044416), by norm_num⟩
  | 11 => ⟨((744559571/70368744177664), (-543767791/70368744177664)), (17/4398046511104), by norm_num⟩
  | 12 => ⟨((-1032178735/562949953421312), (376911111/281474976710656)), (95/140737488355328), by norm_num⟩
  | 13 => ⟨((165104257/562949953421312), (-241158345/1125899906842624)), (245/2251799813685248), by norm_num⟩
  | 14 => ⟨((-784742059/18014398509481984), (573113921/18014398509481984)), (293/18014398509481984), by norm_num⟩
  | 15 => ⟨((870306793/144115188075855872), (-317801839/72057594037927936)), (327/144115188075855872), by norm_num⟩
  | 16 => ⟨((-452438025/576460752303423488), (330425173/576460752303423488)), (171/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (1635302088833/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779194504293627/633825300114114700748351602688), (3872385647389/633825300114114700748351602688)), (138871/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945110155354705/19807040628566084398385987584), (4355728238883/39614081257132168796771975168)), (156267/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945012332894479/1237940039285380274899124224), (2313556157725/1237940039285380274899124224)), (41519/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885845107951425/77371252455336267181195264), (4626157277743/154742504910672534362390528)), (41531/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550020990618889/9671406556917033397649408), (2168003909497/4835703278458516698824704)), (9737/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259197060887391/604462909807314587353088), (3792992323517/604462909807314587353088)), (136369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888454267057735/75557863725914323419136), (6161710539925/75557863725914323419136)), (110847/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324508725820871/1180591620717411303424), (4619618903291/4722366482869645213696)), (83177/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405531845639421/147573952589676412928), (1587318108057/147573952589676412928)), (228873/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824320741741295/73786976294838206464), (991566997093/9223372036854775808)), (286295/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911802350594023/4611686018427387904), (1114816151535/1152921504606846976)), (322361/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199356013429727/144115188075855872), (8911563908901/1152921504606846976)), (40339/144115188075855872), by norm_num⟩
  | 5 => ⟨((37354046911653/4503599627370496), (7789785070359/144115188075855872)), (282767/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492749078877801/36028797018963968), (5834508732045/18014398509481984)), (106235/9007199254740992), by norm_num⟩
  | 3 => ⟨((46582104093011/281474976710656), (1819860173371/1125899906842624)), (266279/4503599627370496), by norm_num⟩
  | 2 => ⟨((139414235443171/281474976710656), (3629456362649/562949953421312)), (133659/562949953421312), by norm_num⟩
  | 1 => ⟨((1109987505815771/1125899906842624), (21674202920293/1125899906842624)), (403579/562949953421312), by norm_num⟩
  | 0 => ⟨((1093943615506989/1125899906842624), (10734724150007/281474976710656)), (12775/8796093022208), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093943615506989/1125899906842624), (10734724150007/281474976710656)), (48732757601913807/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((1061256758087903/1125899906842624), (20860083346237/281474976710656)), (1651151/562949953421312), by norm_num⟩
  | 2 => ⟨((248535329506051/281474976710656), (157299271744697/1125899906842624)), (6714871/1125899906842624), by norm_num⟩
  | 3 => ⟨((427912771577383/562949953421312), (277782606404245/1125899906842624)), (13734393/1125899906842624), by norm_num⟩
  | 4 => ⟨((1164000778245037/2251799813685248), (211149719935175/562949953421312)), (13828423/562949953421312), by norm_num⟩
  | 5 => ⟨((17806604637899/140737488355328), (873180419811935/2251799813685248)), (98679345/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1210183601948161/9007199254740992), (441911496214567/4503599627370496)), (203000607/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1813209783/33554432)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile036Terms0
