/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile054Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨54,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15489/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15489/512))
  have he : value ((69/80), (15489/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-715655399/268435456), (-12550709329/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((463435118192913/9007199254740992), (842428427936193/18014398509481984)), (17464353/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1366136193/8589934592), (-9933403147/68719476736)), (13/4294967296), by norm_num⟩
  | 2 => ⟨((8445569939/34359738368), (15352285417/68719476736)), (81/17179869184), by norm_num⟩
  | 3 => ⟨((-17403743483/68719476736), (-3954547165/17179869184)), (21/4294967296), by norm_num⟩
  | 4 => ⟨((52534873/268435456), (12223673171/68719476736)), (131/34359738368), by norm_num⟩
  | 5 => ⟨((-16628482327/137438953472), (-15113557083/137438953472)), (163/68719476736), by norm_num⟩
  | 6 => ⟨((2141639367/34359738368), (15572215521/274877906944)), (169/137438953472), by norm_num⟩
  | 7 => ⟨((-15131195893/549755813888), (-13752679791/549755813888)), (301/549755813888), by norm_num⟩
  | 8 => ⟨((11692792219/1099511627776), (5313764635/549755813888)), (117/549755813888), by norm_num⟩
  | 9 => ⟨((-4015879683/1099511627776), (-14600064065/4398046511104)), (81/1099511627776), by norm_num⟩
  | 10 => ⟨((4965301835/4398046511104), (9025883569/8796093022208)), (101/4398046511104), by norm_num⟩
  | 11 => ⟨((-11162151829/35184372088832), (-10145232469/35184372088832)), (229/35184372088832), by norm_num⟩
  | 12 => ⟨((5750447529/70368744177664), (10453114753/140737488355328)), (119/70368744177664), by norm_num⟩
  | 13 => ⟨((-10938386115/562949953421312), (-1242731595/70368744177664)), (57/140737488355328), by norm_num⟩
  | 14 => ⟨((9660290243/2251799813685248), (4390098421/1125899906842624)), (203/2251799813685248), by norm_num⟩
  | 15 => ⟨((-15925529201/18014398509481984), (-7237322983/9007199254740992)), (337/18014398509481984), by norm_num⟩
  | 16 => ⟨((12306621713/72057594037927936), (5592718147/36028797018963968)), (131/36028797018963968), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (480473650249/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888928572151787/316912650057057350374175801344), (1136121191457/633825300114114700748351602688)), (2885/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944358247456757/19807040628566084398385987584), (1277842649765/39614081257132168796771975168)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944213883076301/1237940039285380274899124224), (678669381301/1237940039285380274899124224)), (3449/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770094333466413/154742504910672534362390528), (1356923785913/154742504910672534362390528)), (13797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548525931119829/9671406556917033397649408), (317918827901/2417851639229258349412352)), (1617/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257889963559921/604462909807314587353088), (556137678487/302231454903657293676544)), (1415/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471583064308001/18889465931478580854784), (903310929871/37778931862957161709568)), (18397/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296445165159409/4722366482869645213696), (1354244417073/4722366482869645213696)), (1725/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809972182734135/295147905179352825856), (116307102703/36893488147419103232)), (9489/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455399068947947/18446744073709551616), (2324384778973/73786976294838206464)), (1483/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910272795354679/4611686018427387904), (2612518847831/9223372036854775808)), (6675/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795898189883897/576460752303423488), (652376161479/288230376151711744)), (26709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149083441537143/18014398509481984), (2279930166421/144115188075855872)), (5845/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488772679206599/36028797018963968), (1706566940857/18014398509481984)), (17545/18014398509481984), by norm_num⟩
  | 3 => ⟨((92855358017821/562949953421312), (2127305314913/4503599627370496)), (5487/1125899906842624), by norm_num⟩
  | 2 => ⟨((555207741233833/1125899906842624), (2118475888505/1125899906842624)), (43947/2251799813685248), by norm_num⟩
  | 1 => ⟨((17230428221181/17592186044416), (3155729667987/562949953421312)), (33025/562949953421312), by norm_num⟩
  | 0 => ⟨((2159780838909553/2251799813685248), (24896228282063/2251799813685248)), (265249/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159780838909553/2251799813685248), (24896228282063/2251799813685248)), (1011844643599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((517811732374327/562949953421312), (47757706060663/2251799813685248)), (514685/2251799813685248), by norm_num⟩
  | 2 => ⟨((1904158184224447/2251799813685248), (43928417364995/1125899906842624)), (484333/1125899906842624), by norm_num⟩
  | 3 => ⟨((401689744482533/562949953421312), (148586308493717/2251799813685248)), (428457/562949953421312), by norm_num⟩
  | 4 => ⟨((568344598514357/1125899906842624), (106022917187765/1125899906842624)), (2671961/2251799813685248), by norm_num⟩
  | 5 => ⟨((1107646325562833/4503599627370496), (428155660631555/4503599627370496)), (3200789/2251799813685248), by norm_num⟩
  | 6 => ⟨((463435118192913/9007199254740992), (842428427936193/18014398509481984)), (17464353/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-12550709329/134217728)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-725947119/268435456), (-12731198973/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((990036493267657/18014398509481984), (-343804328986575/9007199254740992)), (966473/1125899906842624), by norm_num⟩
  | 1 => ⟨((-5920894047/34359738368), (8224460487/68719476736)), (93/34359738368), by norm_num⟩
  | 2 => ⟨((18564929037/68719476736), (-12893874143/68719476736)), (147/34359738368), by norm_num⟩
  | 3 => ⟨((-19403409205/68719476736), (13476222599/68719476736)), (155/34359738368), by norm_num⟩
  | 4 => ⟨((15209819333/68719476736), (-10563654503/68719476736)), (245/68719476736), by norm_num⟩
  | 5 => ⟨((-19076120217/137438953472), (13248911037/137438953472)), (309/137438953472), by norm_num⟩
  | 6 => ⟨((19937688201/274877906944), (-13847294641/274877906944)), (325/274877906944), by norm_num⟩
  | 7 => ⟨((-8930643719/274877906944), (12405174929/549755813888)), (293/549755813888), by norm_num⟩
  | 8 => ⟨((14000990863/1099511627776), (-9724088559/1099511627776)), (29/137438953472), by norm_num⟩
  | 9 => ⟨((-1219445163/274877906944), (3387758159/1099511627776)), (325/4398046511104), by norm_num⟩
  | 10 => ⟨((12235402417/8796093022208), (-4248918445/4398046511104)), (103/4398046511104), by norm_num⟩
  | 11 => ⟨((-13950557639/35184372088832), (4844530621/17592186044416)), (237/35184372088832), by norm_num⟩
  | 12 => ⟨((911289433/8796093022208), (-10126665161/140737488355328)), (125/70368744177664), by norm_num⟩
  | 13 => ⟨((-14066918135/562949953421312), (9769876935/562949953421312)), (243/562949953421312), by norm_num⟩
  | 14 => ⟨((6300962921/1125899906842624), (-8752397891/2251799813685248)), (219/2251799813685248), by norm_num⟩
  | 15 => ⟨((-10536870823/9007199254740992), (7318158123/9007199254740992)), (185/9007199254740992), by norm_num⟩
  | 16 => ⟨((16519148759/72057594037927936), (-11473021233/72057594037927936)), (73/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (-790743154905/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777798324011117/633825300114114700748351602688), (-934830822365/633825300114114700748351602688)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888650349700969/39614081257132168796771975168), (-1051439900909/39614081257132168796771975168)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118022345160275/154742504910672534362390528), (-34901465167/77371252455336267181195264)), (431/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770024130008333/154742504910672534362390528), (-1116500553935/154742504910672534362390528)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548460157991185/9671406556917033397649408), (-523175720839/4835703278458516698824704)), (3233/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257832454657569/604462909807314587353088), (-114398731511/75557863725914323419136)), (11317/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117889930315831/4722366482869645213696), (-1486494505659/75557863725914323419136)), (18391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162046900722491/590295810358705651712), (-1114268357899/4722366482869645213696)), (13795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809924142280475/295147905179352825856), (-1531140564107/590295810358705651712)), (18971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821476344321605/73786976294838206464), (-239057404161/9223372036854775808)), (11859/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910205450388231/4611686018427387904), (-2149502138469/9223372036854775808)), (417/144115188075855872), by norm_num⟩
  | 6 => ⟨((1591661980574027/1152921504606846976), (-268373357685/144115188075855872)), (26695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596275129716225/72057594037927936), (-468946931653/36028797018963968)), (23367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488597421143205/36028797018963968), (-1404019897323/18014398509481984)), (17533/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485467791714705/9007199254740992), (-1750099259895/4503599627370496)), (10965/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220398485263267/4503599627370496), (-108920794429/70368744177664)), (87805/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102427262857407/1125899906842624), (-10383036044507/2251799813685248)), (131923/2251799813685248), by norm_num⟩
  | 0 => ⟨((134908355895553/140737488355328), (-10237227858501/1125899906842624)), (132357/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((134908355895553/140737488355328), (-10237227858501/1125899906842624)), (504901890281295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129309021996039/140737488355328), (-39252869877331/2251799813685248)), (512315/2251799813685248), by norm_num⟩
  | 2 => ⟨((1900253263017171/2251799813685248), (-72130748867145/2251799813685248)), (119911/281474976710656), by norm_num⟩
  | 3 => ⟨((400319734991691/562949953421312), (-121739676915901/2251799813685248)), (1680509/2251799813685248), by norm_num⟩
  | 4 => ⟨((283026235186667/562949953421312), (-173140773543947/2251799813685248)), (2571765/2251799813685248), by norm_num⟩
  | 5 => ⟨((1111718601087493/4503599627370496), (-348189966057437/4503599627370496)), (5962849/4503599627370496), by norm_num⟩
  | 6 => ⟨((990036493267657/18014398509481984), (-343804328986575/9007199254740992)), (966473/1125899906842624), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-12731198973/134217728)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-3226001459/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-46206850358149/2251799813685248), (-1101582468014833/18014398509481984)), (25515365/18014398509481984), by norm_num⟩
  | 1 => ⟨((1120360243/17179869184), (6677414669/34359738368)), (311/68719476736), by norm_num⟩
  | 2 => ⟨((-7121130323/68719476736), (-10610591633/34359738368)), (31/4294967296), by norm_num⟩
  | 3 => ⟨((1885944625/17179869184), (5620171897/17179869184)), (527/68719476736), by norm_num⟩
  | 4 => ⟨((-5993633539/68719476736), (-17861208825/68719476736)), (421/68719476736), by norm_num⟩
  | 5 => ⟨((7619236011/137438953472), (22705553249/137438953472)), (537/137438953472), by norm_num⟩
  | 6 => ⟨((-2017861849/68719476736), (-24053156825/274877906944)), (571/274877906944), by norm_num⟩
  | 7 => ⟨((7328998375/549755813888), (21840636337/549755813888)), (521/549755813888), by norm_num⟩
  | 8 => ⟨((-90984185/17179869184), (-4338169873/274877906944)), (13/34359738368), by norm_num⟩
  | 9 => ⟨((8224786137/4398046511104), (24510110901/4398046511104)), (295/2199023255552), by norm_num⟩
  | 10 => ⟨((-5227762617/8796093022208), (-7789445183/4398046511104)), (377/8796093022208), by norm_num⟩
  | 11 => ⟨((6041494913/35184372088832), (4500959291/8796093022208)), (219/17592186044416), by norm_num⟩
  | 12 => ⟨((-3200032675/70368744177664), (-19072387887/140737488355328)), (233/70368744177664), by norm_num⟩
  | 13 => ⟨((1564596323/140737488355328), (1165636065/35184372088832)), (229/281474976710656), by norm_num⟩
  | 14 => ⟨((-1420677525/562949953421312), (-8467323797/1125899906842624)), (209/1125899906842624), by norm_num⟩
  | 15 => ⟨((150499655/281474976710656), (14351792441/9007199254740992)), (89/2251799813685248), by norm_num⟩
  | 16 => ⟨((-7652736081/72057594037927936), (-11402692235/36028797018963968)), (71/9007199254740992), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-1233935291793/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888868849904271/316912650057057350374175801344), (-1458692094993/316912650057057350374175801344)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888581939230647/39614081257132168796771975168), (-1640638028969/19807040628566084398385987584)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888284555059509/2475880078570760549798248448), (-108918146885/77371252455336267181195264)), (13825/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884975423174305/77371252455336267181195264), (-3484284141395/154742504910672534362390528)), (3457/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774195559468915/4835703278458516698824704), (-3265351700127/9671406556917033397649408)), (12967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628885855096251/302231454903657293676544), (-357002314743/75557863725914323419136)), (5675/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886139547321019/75557863725914323419136), (-2319424081407/37778931862957161709568)), (1153/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324075038424795/1180591620717411303424), (-3477227917015/4722366482869645213696)), (6921/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619744197487259/590295810358705651712), (-2389044697127/295147905179352825856)), (595/18446744073709551616), by norm_num⟩
  | 8 => ⟨((56917028189711/2305843009213693952), (-5967966476579/73786976294838206464)), (11907/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820261198515941/9223372036854775808), (-3353790138243/4611686018427387904)), (3351/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397877499176927/288230376151711744), (-104681415721/18014398509481984)), (13415/576460752303423488), by norm_num⟩
  | 5 => ⟨((149051839295841/18014398509481984), (-5853204174885/144115188075855872)), (23501/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488389004197677/36028797018963968), (-8761922959231/36028797018963968)), (35301/36028797018963968), by norm_num⟩
  | 3 => ⟨((371299597338551/2251799813685248), (-10921168389255/9007199254740992)), (44213/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109916603578643/2251799813685248), (-21748872371305/4503599627370496)), (5543/281474976710656), by norm_num⟩
  | 1 => ⟨((2203941018092203/2251799813685248), (-4048811405679/281474976710656)), (66845/1125899906842624), by norm_num⟩
  | 0 => ⟨((2156447855055485/2251799813685248), (-15963690630691/562949953421312)), (67507/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156447855055485/2251799813685248), (-15963690630691/562949953421312)), (257518770458030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1031661405387699/1125899906842624), (-122301693818809/2251799813685248)), (532503/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883978891628119/2251799813685248), (-14008121032739/140737488355328)), (1033709/2251799813685248), by norm_num⟩
  | 3 => ⟨((776965655292315/1125899906842624), (-187519364211057/1125899906842624)), (967747/1125899906842624), by norm_num⟩
  | 4 => ⟨((252470097072831/562949953421312), (-258808273823949/1125899906842624)), (414503/281474976710656), by norm_num⟩
  | 5 => ⟨((166962334681499/1125899906842624), (-464278215983315/2251799813685248)), (8997633/4503599627370496), by norm_num⟩
  | 6 => ⟨((-46206850358149/2251799813685248), (-1101582468014833/18014398509481984)), (25515365/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-3226001459/33554432)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-26139514713/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-560834553240885/9007199254740992), (-13563541144917/18014398509481984)), (5725737/4503599627370496), by norm_num⟩
  | 1 => ⟨((3443254061/17179869184), (166547221/68719476736)), (141/34359738368), by norm_num⟩
  | 2 => ⟨((-22166814511/68719476736), (-67011853/17179869184)), (57/8589934592), by norm_num⟩
  | 3 => ⟨((1486504653/4294967296), (143801889/34359738368)), (491/68719476736), by norm_num⟩
  | 4 => ⟨((-4784873891/17179869184), (-57860053/17179869184)), (99/17179869184), by norm_num⟩
  | 5 => ⟨((6160765957/34359738368), (297990921/137438953472)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-26440987469/274877906944), (-79932981/68719476736)), (551/274877906944), by norm_num⟩
  | 7 => ⟨((12158607907/274877906944), (147025337/274877906944)), (509/549755813888), by norm_num⟩
  | 8 => ⟨((-1223032783/68719476736), (-236628151/1099511627776)), (103/274877906944), by norm_num⟩
  | 9 => ⟨((27994955791/4398046511104), (338522949/4398046511104)), (37/274877906944), by norm_num⟩
  | 10 => ⟨((-18022457283/8796093022208), (-217932667/8796093022208)), (383/8796093022208), by norm_num⟩
  | 11 => ⟨((21095291655/35184372088832), (63772563/8796093022208)), (225/17592186044416), by norm_num⟩
  | 12 => ⟨((-22634374775/140737488355328), (-136850641/70368744177664)), (485/140737488355328), by norm_num⟩
  | 13 => ⟨((22417612853/562949953421312), (271080135/562949953421312)), (241/281474976710656), by norm_num⟩
  | 14 => ⟨((-20617003447/2251799813685248), (-249306655/2251799813685248)), (445/2251799813685248), by norm_num⟩
  | 15 => ⟨((4424238265/2251799813685248), (213996577/9007199254740992)), (3/70368744177664), by norm_num⟩
  | 16 => ⟨((-28482147189/72057594037927936), (-86103551/18014398509481984)), (155/18014398509481984), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-4076524409887/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777675591333603/633825300114114700748351602688), (-4818768098427/633825300114114700748351602688)), (11585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944255826512143/19807040628566084398385987584), (-5419784391319/39614081257132168796771975168)), (13037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944104658120207/1237940039285380274899124224), (-2878443451331/1237940039285380274899124224)), (433/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1769874978569997/154742504910672534362390528), (-5755048958961/154742504910672534362390528)), (13861/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96769957825659/604462909807314587353088), (-5393406067757/9671406556917033397649408)), (1625/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257708223653871/604462909807314587353088), (-4717278521251/604462909807314587353088)), (2845/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943017566208069/37778931862957161709568), (-1915479787283/18889465931478580854784)), (18503/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324055187699099/1180591620717411303424), (-358952460933/295147905179352825856)), (6943/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809816623529393/295147905179352825856), (-7891756328083/590295810358705651712)), (19107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821203561450795/73786976294838206464), (-4928451241921/36893488147419103232)), (23905/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820098550435699/9223372036854775808), (-5539153092967/4611686018427387904)), (13461/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591342809891527/1152921504606846976), (-691558065797/72057594037927936)), (26959/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192263335089299/144115188075855872), (-9666776375465/144115188075855872)), (11815/72057594037927936), by norm_num⟩
  | 4 => ⟨((372037947937693/9007199254740992), (-14470123316179/36028797018963968)), (35527/36028797018963968), by norm_num⟩
  | 3 => ⟨((371221052037791/2251799813685248), (-9017576835745/4503599627370496)), (5569/1125899906842624), by norm_num⟩
  | 2 => ⟨((554788047262719/1125899906842624), (-17956546523413/2251799813685248)), (22385/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101394520964069/1125899906842624), (-26738805030551/1125899906842624)), (33849/562949953421312), by norm_num⟩
  | 0 => ⟨((538407303916923/562949953421312), (-13174143708777/281474976710656)), (34395/281474976710656), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538407303916923/562949953421312), (-13174143708777/281474976710656)), (131206513524913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((128425355976903/140737488355328), (-50399188436193/562949953421312)), (276043/1125899906842624), by norm_num⟩
  | 2 => ⟨((1856996865467985/2251799813685248), (-183960472550811/1125899906842624)), (553215/1125899906842624), by norm_num⟩
  | 3 => ⟨((1471299320826991/2251799813685248), (-606828402455167/2251799813685248)), (546611/562949953421312), by norm_num⟩
  | 4 => ⟨((398898909779105/1125899906842624), (-198247244485209/562949953421312)), (2017813/1125899906842624), by norm_num⟩
  | 5 => ⟨((3397212180981/2251799813685248), (-4389855684065/17592186044416)), (11403893/4503599627370496), by norm_num⟩
  | 6 => ⟨((-560834553240885/9007199254740992), (-13563541144917/18014398509481984)), (5725737/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-26139514713/268435456)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-754332693/268435456), (-26458014235/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-418686862740739/18014398509481984), (1000354905551087/18014398509481984)), (12067169/9007199254740992), by norm_num⟩
  | 1 => ⟨((5203713295/68719476736), (-1554132869/8589934592)), (301/68719476736), by norm_num⟩
  | 2 => ⟨((-1059637517/8589934592), (632939365/2147483648)), (493/68719476736), by norm_num⟩
  | 3 => ⟨((9206403535/68719476736), (-21996560575/68719476736)), (537/68719476736), by norm_num⟩
  | 4 => ⟨((-7498837871/68719476736), (2239591183/8589934592)), (439/68719476736), by norm_num⟩
  | 5 => ⟨((9772775083/137438953472), (-182420107/1073741824)), (287/68719476736), by norm_num⟩
  | 6 => ⟨((-5306774111/137438953472), (12679302807/137438953472)), (313/137438953472), by norm_num⟩
  | 7 => ⟨((9879989919/549755813888), (-23605938617/549755813888)), (585/549755813888), by norm_num⟩
  | 8 => ⟨((-4023745119/549755813888), (19227606721/1099511627776)), (239/549755813888), by norm_num⟩
  | 9 => ⟨((2913277787/1099511627776), (-6960599877/1099511627776)), (87/549755813888), by norm_num⟩
  | 10 => ⟨((-3796696109/4398046511104), (18142645089/8796093022208)), (57/1099511627776), by norm_num⟩
  | 11 => ⟨((8996365417/35184372088832), (-21494723329/35184372088832)), (271/17592186044416), by norm_num⟩
  | 12 => ⟨((-2442585585/35184372088832), (23343961221/140737488355328)), (591/140737488355328), by norm_num⟩
  | 13 => ⟨((1224335329/70368744177664), (-23402116689/562949953421312)), (595/562949953421312), by norm_num⟩
  | 14 => ⟨((-4558860225/1125899906842624), (10892336481/1125899906842624)), (139/562949953421312), by norm_num⟩
  | 15 => ⟨((7921710249/9007199254740992), (-9463542341/4503599627370496)), (485/9007199254740992), by norm_num⟩
  | 16 => ⟨((-806553023/4503599627370496), (15416567269/36028797018963968)), (397/36028797018963968), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (2562473109099/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777631040829469/633825300114114700748351602688), (3028872702099/633825300114114700748351602688)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236057744741109/4951760157141521099596496896), (3406651218885/39614081257132168796771975168)), (13011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472039271212021/618970019642690137449562112), (3618529045537/2475880078570760549798248448)), (13827/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769823387329267/154742504910672534362390528), (3617361916421/154742504910672534362390528)), (6915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774135819007881/4835703278458516698824704), (847509292187/2417851639229258349412352)), (12969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628833588156705/302231454903657293676544), (2965043397281/604462909807314587353088)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942984851086303/37778931862957161709568), (4815873227999/75557863725914323419136)), (4613/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296172789482921/4722366482869645213696), (3609873982057/4722366482869645213696)), (3461/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404892275922265/147573952589676412928), (2480139224703/295147905179352825856)), (19045/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910563041477191/36893488147419103232), (1548851036457/18446744073709551616)), (23819/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113750943337857/576460752303423488), (870379682559/1152921504606846976)), (13407/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591263974913775/1152921504606846976), (6954555721333/1152921504606846976)), (13419/576460752303423488), by norm_num⟩
  | 5 => ⟨((596099769734383/72057594037927936), (379731624917/9007199254740992)), (23509/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488066431292169/36028797018963968), (4547263850973/18014398509481984)), (17657/18014398509481984), by norm_num⟩
  | 3 => ⟨((371198876800893/2251799813685248), (11334920523087/9007199254740992)), (44233/9007199254740992), by norm_num⟩
  | 2 => ⟨((554757113644111/1125899906842624), (11285192997109/2251799813685248)), (44369/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202736452478719/2251799813685248), (8401964375747/562949953421312)), (133791/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077024589258085/1125899906842624), (66230311730721/2251799813685248)), (67583/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077024589258085/1125899906842624), (66230311730721/2251799813685248)), (257808687450218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1029296960835921/1125899906842624), (126710507487741/2251799813685248)), (533097/2251799813685248), by norm_num⟩
  | 2 => ⟨((937417561716381/1125899906842624), (14479832917481/140737488355328)), (517355/1125899906842624), by norm_num⟩
  | 3 => ⟨((768570175582115/1125899906842624), (192893163380825/1125899906842624)), (1935901/2251799813685248), by norm_num⟩
  | 4 => ⟨((983199907827379/2251799813685248), (526696668317293/2251799813685248)), (1653165/1125899906842624), by norm_num⟩
  | 5 => ⟨((612197118186257/4503599627370496), (919883042169811/4503599627370496)), (8867959/4503599627370496), by norm_num⟩
  | 6 => ⟨((-418686862740739/18014398509481984), (1000354905551087/18014398509481984)), (12067169/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-26458014235/268435456)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-763070545/268435456), (-26764491997/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((711929975430073/18014398509481984), (771390079192993/18014398509481984)), (15465159/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8950824963/68719476736), (-9698394245/68719476736)), (49/17179869184), by norm_num⟩
  | 2 => ⟨((14750229447/68719476736), (15982162647/68719476736)), (325/68719476736), by norm_num⟩
  | 3 => ⟨((-16204783331/68719476736), (-4389550071/17179869184)), (359/68719476736), by norm_num⟩
  | 4 => ⟨((13352080577/68719476736), (14467240949/68719476736)), (149/34359738368), by norm_num⟩
  | 5 => ⟨((-8801255881/68719476736), (-4768166607/34359738368)), (99/34359738368), by norm_num⟩
  | 6 => ⟨((9669167867/137438953472), (5238366429/68719476736)), (219/137438953472), by norm_num⟩
  | 7 => ⟨((-4552571417/137438953472), (-9865600683/274877906944)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((15004532711/1099511627776), (8128852609/549755813888)), (345/1099511627776), by norm_num⟩
  | 9 => ⟨((-10989442681/2199023255552), (-2976819123/549755813888)), (127/1099511627776), by norm_num⟩
  | 10 => ⟨((7243882065/4398046511104), (7848888167/4398046511104)), (337/8796093022208), by norm_num⟩
  | 11 => ⟨((-8681692205/17592186044416), (-2351695907/4398046511104)), (51/4398046511104), by norm_num⟩
  | 12 => ⟨((9537813743/70368744177664), (10334408091/70368744177664)), (113/35184372088832), by norm_num⟩
  | 13 => ⟨((-2418082935/70368744177664), (-10480160977/281474976710656)), (231/281474976710656), by norm_num⟩
  | 14 => ⟨((9108122151/1125899906842624), (9868828831/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 15 => ⟨((-16010071875/9007199254740992), (-8673613303/4503599627370496)), (387/9007199254740992), by norm_num⟩
  | 16 => ⟨((6595823139/18014398509481984), (14293407243/36028797018963968)), (321/36028797018963968), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (1075257115453/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888792489603365/316912650057057350374175801344), (1270897922965/633825300114114700748351602688)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888410372449855/39614081257132168796771975168), (11167275037/309485009821345068724781056)), (12985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888102589557893/2475880078570760549798248448), (1518309262173/2475880078570760549798248448)), (6899/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769769245179301/154742504910672534362390528), (758907184731/77371252455336267181195264)), (13799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193527656831011/1208925819614629174706176), (1422425369817/9671406556917033397649408)), (6469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157202933176439/75557863725914323419136), (1244096846865/604462909807314587353088)), (5661/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885899373478791/75557863725914323419136), (1010336436133/37778931862957161709568)), (18401/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648060328022499/2361183241434822606848), (757321871783/2361183241434822606848)), (13803/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809749207533837/295147905179352825856), (2081237161185/590295810358705651712)), (18983/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455259803002111/18446744073709551616), (81232850297/2305843009213693952)), (11867/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819919408128173/9223372036854775808), (2921504473573/9223372036854775808)), (26709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591170839345023/1152921504606846976), (2917911028543/1152921504606846976)), (13359/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192120906085391/144115188075855872), (1274567664107/72057594037927936)), (23389/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487954181281851/36028797018963968), (953910959125/9007199254740992)), (17553/18014398509481984), by norm_num⟩
  | 3 => ⟨((46395785124797/281474976710656), (4755483809739/9007199254740992)), (2745/562949953421312), by norm_num⟩
  | 2 => ⟨((1109398646712355/2251799813685248), (9468884506927/4503599627370496)), (87955/4503599627370496), by norm_num⟩
  | 1 => ⟨((550615771845775/562949953421312), (440580377517/70368744177664)), (1033/17592186044416), by norm_num⟩
  | 0 => ⟨((538448039289939/562949953421312), (1736302076905/140737488355328)), (265621/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538448039289939/562949953421312), (1736302076905/140737488355328)), (1013263710982512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514926865763143/562949953421312), (26571696279363/1125899906842624)), (514675/2251799813685248), by norm_num⟩
  | 2 => ⟨((58835861365983/70368744177664), (97219869723677/2251799813685248)), (482917/1125899906842624), by norm_num⟩
  | 3 => ⟨((1569982670798147/2251799813685248), (162572597931819/2251799813685248)), (1698483/2251799813685248), by norm_num⟩
  | 4 => ⟨((541437058966961/1125899906842624), (28336906321379/281474976710656)), (1306829/1125899906842624), by norm_num⟩
  | 5 => ⟨((995848398108473/4503599627370496), (436064374834749/4503599627370496)), (760007/562949953421312), by norm_num⟩
  | 6 => ⟨((711929975430073/18014398509481984), (771390079192993/18014398509481984)), (15465159/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-26764491997/268435456)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile054Terms3
