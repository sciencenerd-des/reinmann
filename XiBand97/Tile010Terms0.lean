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
namespace Reinmann.XiBand97.Tile010Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (24671/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (24671/1280))
  have he : value ((69/80), (24671/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1793131449/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((217154720911825/562949953421312), (-882808565547073/2251799813685248)), (34572663/2251799813685248), by norm_num⟩
  | 1 => ⟨((-574188929/2147483648), (583568829/2147483648)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((795994875/8589934592), (-808998177/8589934592)), (37/8589934592), by norm_num⟩
  | 3 => ⟨((-735655471/34359738368), (373836537/17179869184)), (9/8589934592), by norm_num⟩
  | 4 => ⟨((1019835031/274877906944), (-1036494967/274877906944)), (53/274877906944), by norm_num⟩
  | 5 => ⟨((-565516621/1099511627776), (574754851/1099511627776)), (31/1099511627776), by norm_num⟩
  | 6 => ⟨((522648335/8796093022208), (-1062372545/17592186044416)), (15/4398046511104), by norm_num⟩
  | 7 => ⟨((-207012697/35184372088832), (420788877/70368744177664)), (25/70368744177664), by norm_num⟩
  | 8 => ⟨((573961069/1125899906842624), (-583337247/1125899906842624)), (9/281474976710656), by norm_num⟩
  | 9 => ⟨((-88408777/2251799813685248), (718824121/18014398509481984)), (23/9007199254740992), by norm_num⟩
  | 10 => ⟨((392193885/144115188075855872), (-797201461/288230376151711744)), (53/288230376151711744), by norm_num⟩
  | 11 => ⟨((-790830795/4611686018427387904), (401874869/2305843009213693952)), (7/576460752303423488), by norm_num⟩
  | 12 => ⟨((22840089/2305843009213693952), (-371411243/36893488147419103232)), (27/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-155879811/295147905179352825856), (633704999/1180591620717411303424)), (3/73786976294838206464), by norm_num⟩
  | 14 => ⟨((493932121/18889465931478580854784), (-1004001905/37778931862957161709568)), (39/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-730384335/604462909807314587353088), (742315829/604462909807314587353088)), (59/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1012527685/19342813113834066795298816), (-128633531/2417851639229258349412352)), (21/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-516811020805/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890523811475725/316912650057057350374175801344), (-1226219260295/633825300114114700748351602688)), (23081/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946152629594769/19807040628566084398385987584), (-689710835991/19807040628566084398385987584)), (1623/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892240185195823/2475880078570760549798248448), (-732773002993/1237940039285380274899124224)), (27593/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886953014658751/77371252455336267181195264), (-1465445298249/154742504910672534362390528)), (27595/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552098627766519/9671406556917033397649408), (-1373747969201/9671406556917033397649408)), (25873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261015305112235/604462909807314587353088), (-600961239857/302231454903657293676544)), (11321/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891409497654361/75557863725914323419136), (-244115428343/9444732965739290427392)), (18399/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650125918125571/2361183241434822606848), (-1464517052333/4722366482869645213696)), (27603/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812588246387749/295147905179352825856), (-1006712874441/295147905179352825856)), (37961/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228516671019219/9223372036854775808), (-2516354420893/73786976294838206464)), (47461/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827895605068803/9223372036854775808), (-44223603097/144115188075855872)), (53409/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399785282334103/288230376151711744), (-707393879855/288230376151711744)), (53427/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199088269943545/144115188075855872), (-618762930733/36028797018963968)), (46769/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498391960873657/36028797018963968), (-1855462069565/18014398509481984)), (70195/36028797018963968), by norm_num⟩
  | 3 => ⟨((748844581575677/4503599627370496), (-2317881123909/4503599627370496)), (87817/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122387968818563/2251799813685248), (-2315712033029/1125899906842624)), (87925/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120628947200965/1125899906842624), (-3468147437807/562949953421312)), (132159/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115345842216437/1125899906842624), (-3457312570895/281474976710656)), (132703/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115345842216437/1125899906842624), (-3457312570895/281474976710656)), (506221773387718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((69045052985333/70368744177664), (-27399232757761/1125899906842624)), (532357/1125899906842624), by norm_num⟩
  | 2 => ⟨((1083273411889635/1125899906842624), (-53767663459811/1125899906842624)), (1070597/1125899906842624), by norm_num⟩
  | 3 => ⟨((519846531720473/562949953421312), (-103464046655409/1125899906842624)), (2162383/1125899906842624), by norm_num⟩
  | 4 => ⟨((475289522058067/562949953421312), (-47771054500227/281474976710656)), (4391055/1125899906842624), by norm_num⟩
  | 5 => ⟨((770128264043745/1125899906842624), (-645317233580237/2251799813685248)), (4452533/562949953421312), by norm_num⟩
  | 6 => ⟨((217154720911825/562949953421312), (-882808565547073/2251799813685248)), (34572663/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1793131449/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1421023053/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-74745399760481/281474976710656), (-79506641354367/281474976710656)), (77967151/2251799813685248), by norm_num⟩
  | 1 => ⟨((78312125/268435456), (83300565/268435456)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-688277303/4294967296), (-732120195/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((1008199871/17179869184), (536210829/8589934592)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((-34613149/2147483648), (-294543903/17179869184)), (79/34359738368), by norm_num⟩
  | 5 => ⟨((486738315/137438953472), (1035486565/274877906944)), (71/137438953472), by norm_num⟩
  | 6 => ⟨((-712982259/1099511627776), (-189599711/274877906944)), (53/549755813888), by norm_num⟩
  | 7 => ⟨((223797449/2199023255552), (952212903/8796093022208)), (135/8796093022208), by norm_num⟩
  | 8 => ⟨((-983466511/70368744177664), (-1046112797/70368744177664)), (151/70368744177664), by norm_num⟩
  | 9 => ⟨((960398573/562949953421312), (255393861/140737488355328)), (75/281474976710656), by norm_num⟩
  | 10 => ⟨((-211021135/1125899906842624), (-897852269/4503599627370496)), (135/4503599627370496), by norm_num⟩
  | 11 => ⟨((5268873/281474976710656), (717375663/36028797018963968)), (55/18014398509481984), by norm_num⟩
  | 12 => ⟨((-15435863/9007199254740992), (-525411813/288230376151711744)), (41/144115188075855872), by norm_num⟩
  | 13 => ⟨((667885441/4611686018427387904), (88803673/576460752303423488)), (113/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-838568175/73786976294838206464), (-222996129/18446744073709551616)), (9/4611686018427387904), by norm_num⟩
  | 15 => ⟨((491339361/590295810358705651712), (261318707/295147905179352825856)), (43/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-134947865/2361183241434822606848), (-287087943/4722366482869645213696)), (3/295147905179352825856), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1514505958115/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222562659746481/79228162514264337593543950336), (-14028694881/2475880078570760549798248448)), (46277/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891690301116091/39614081257132168796771975168), (-4039905926843/39614081257132168796771975168)), (52073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891586394322233/2475880078570760549798248448), (-4291983063059/2475880078570760549798248448)), (55341/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443312947728309/38685626227668133590597632), (-4291513849337/154742504910672534362390528)), (55355/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775742401959053/4835703278458516698824704), (-4022795622615/9671406556917033397649408)), (51911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630238867038451/302231454903657293676544), (-3519447478175/604462909807314587353088)), (22719/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890535054156947/75557863725914323419136), (-1429541733605/18889465931478580854784)), (73865/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649797612379331/2361183241434822606848), (-4287806714751/4722366482869645213696)), (55425/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812136193506791/295147905179352825856), (-5894403873355/590295810358705651712)), (76251/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827001339742095/73786976294838206464), (-7366008744101/73786976294838206464)), (95377/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826619467817355/9223372036854775808), (-1035501787117/1152921504606846976)), (107385/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798930869236869/576460752303423488), (-8280581015353/1152921504606846976)), (107493/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197965146750103/144115188075855872), (-1810411021479/36028797018963968)), (47089/72057594037927936), by norm_num⟩
  | 4 => ⟨((187087496752095/4503599627370496), (-1356841610595/4503599627370496)), (141509/36028797018963968), by norm_num⟩
  | 3 => ⟨((373890356040773/2251799813685248), (-6777436262963/4503599627370496)), (177313/9007199254740992), by norm_num⟩
  | 2 => ⟨((70015071444153/140737488355328), (-13534536437937/2251799813685248)), (5561/70368744177664), by norm_num⟩
  | 1 => ⟨((558680577120309/562949953421312), (-20250892318473/1125899906842624)), (268529/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108621013313041/1125899906842624), (-40297705724939/1125899906842624)), (543475/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108621013313041/1125899906842624), (-40297705724939/1125899906842624)), (2073192600730514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1090164977022337/1125899906842624), (-39679267298507/562949953421312)), (1109173/1125899906842624), by norm_num⟩
  | 2 => ⟨((1049970688271819/1125899906842624), (-76839774583597/562949953421312)), (1152149/562949953421312), by norm_num⟩
  | 3 => ⟨((958185568576089/1125899906842624), (-143315601175315/562949953421312)), (4926849/1125899906842624), by norm_num⟩
  | 4 => ⟨((92810441295223/140737488355328), (-243934545093071/562949953421312)), (1361805/140737488355328), by norm_num⟩
  | 5 => ⟨((278235695549473/1125899906842624), (-643458201274069/1125899906842624)), (47620585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-74745399760481/281474976710656), (-79506641354367/281474976710656)), (77967151/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1421023053/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1793131449/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-22073186278425/4503599627370496), (-170269174466447/562949953421312)), (108575035/4503599627370496), by norm_num⟩
  | 1 => ⟨((29182371/4294967296), (112554167/268435456)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-10113839/2147483648), (-156033207/536870912)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((2336793/1073741824), (1153642427/8589934592)), (97/8589934592), by norm_num⟩
  | 4 => ⟨((-3239483/4294967296), (-1599287991/34359738368)), (137/34359738368), by norm_num⟩
  | 5 => ⟨((28741613/137438953472), (1773667139/137438953472)), (77/68719476736), by norm_num⟩
  | 6 => ⟨((-26562891/549755813888), (-819608251/274877906944)), (145/549755813888), by norm_num⟩
  | 7 => ⟨((10521139/1099511627776), (324633799/549755813888)), (117/2199023255552), by norm_num⟩
  | 8 => ⟨((-29170791/17592186044416), (-450038005/4398046511104)), (41/4398046511104), by norm_num⟩
  | 9 => ⟨((561657/2199023255552), (1109129153/70368744177664)), (103/70368744177664), by norm_num⟩
  | 10 => ⟨((-19932721/562949953421312), (-1230063593/562949953421312)), (117/562949953421312), by norm_num⟩
  | 11 => ⟨((10048225/2251799813685248), (1240167435/4503599627370496)), (119/4503599627370496), by norm_num⟩
  | 12 => ⟨((-2321633/4503599627370496), (-1146158081/36028797018963968)), (7/2251799813685248), by norm_num⟩
  | 13 => ⟨((31689519/576460752303423488), (1955584597/576460752303423488)), (97/288230376151711744), by norm_num⟩
  | 14 => ⟨((-25103429/4611686018427387904), (-1549151943/4611686018427387904)), (39/1152921504606846976), by norm_num⟩
  | 15 => ⟨((4640099/9223372036854775808), (572688161/18446744073709551616)), (117/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-6432543/147573952589676412928), (-1587828737/590295810358705651712)), (41/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-516811020805/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890060907656029/316912650057057350374175801344), (-1225012346179/316912650057057350374175801344)), (46221/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945631834313079/19807040628566084398385987584), (-2755979540631/39614081257132168796771975168)), (52007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472783354774221/618970019642690137449562112), (-1463935202801/1237940039285380274899124224)), (27633/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772799177653845/154742504910672534362390528), (-2927467835073/154742504910672534362390528)), (13819/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775530431746419/4835703278458516698824704), (-343009174605/1208925819614629174706176)), (51831/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630053585308221/302231454903657293676544), (-2400636560399/604462909807314587353088)), (45363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889933609106239/75557863725914323419136), (-3900232622739/75557863725914323419136)), (73735/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649572385636117/2361183241434822606848), (-2924472980705/4722366482869645213696)), (55319/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811827018667947/295147905179352825856), (-4020010579619/590295810358705651712)), (19023/147573952589676412928), by norm_num⟩
  | 8 => ⟨((913114968894755/36893488147419103232), (-2511651913865/36893488147419103232)), (95157/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825753750380013/9223372036854775808), (-2824433401347/4611686018427387904)), (107111/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199624832079753/144115188075855872), (-2822964962245/576460752303423488)), (6699/72057594037927936), by norm_num⟩
  | 5 => ⟨((299303228249407/36028797018963968), (-2468442778905/72057594037927936)), (46935/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495577543596057/36028797018963968), (-7398724241749/36028797018963968)), (70485/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494168734115195/9007199254740992), (-4618426498517/4503599627370496)), (176503/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118863950223423/2251799813685248), (-2304883569825/562949953421312)), (176939/2251799813685248), by norm_num⟩
  | 1 => ⟨((557667010443201/562949953421312), (-53851714043/4398046511104)), (66625/281474976710656), by norm_num⟩
  | 0 => ⟨((69045052985333/70368744177664), (-27399232757761/1125899906842624)), (537375/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((69045052985333/70368744177664), (-27399232757761/1125899906842624)), (2049922947410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1083273411889635/1125899906842624), (-53767663459811/1125899906842624)), (1080689/1125899906842624), by norm_num⟩
  | 2 => ⟨((519846531720473/562949953421312), (-103464046655409/1125899906842624)), (2182767/1125899906842624), by norm_num⟩
  | 3 => ⟨((475289522058067/562949953421312), (-47771054500227/281474976710656)), (69257/17592186044416), by norm_num⟩
  | 4 => ⟨((770128264043745/1125899906842624), (-645317233580237/2251799813685248)), (8989011/1125899906842624), by norm_num⟩
  | 5 => ⟨((217154720911825/562949953421312), (-882808565547073/2251799813685248)), (4362321/281474976710656), by norm_num⟩
  | 6 => ⟨((-22073186278425/4503599627370496), (-170269174466447/562949953421312)), (108575035/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1793131449/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1040880573/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1037169321641079/4503599627370496), (432734635131645/4503599627370496)), (12121195/562949953421312), by norm_num⟩
  | 1 => ⟨((-795965017/2147483648), (-166048891/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((320264069/1073741824), (534490761/4294967296)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((-1374520359/8589934592), (-573486463/8589934592)), (135/8589934592), by norm_num⟩
  | 4 => ⟨((1106102589/17179869184), (115373857/4294967296)), (55/8589934592), by norm_num⟩
  | 5 => ⟨((-712081377/34359738368), (-594198591/68719476736)), (9/4294967296), by norm_num⟩
  | 6 => ⟨((764033843/137438953472), (318775247/137438953472)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((-1405331467/1099511627776), (-293170839/549755813888)), (147/1099511627776), by norm_num⟩
  | 8 => ⟨((1130896871/4398046511104), (471840263/4398046511104)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((-404468511/8796093022208), (-10547189/549755813888)), (87/17592186044416), by norm_num⟩
  | 10 => ⟨((520773565/70368744177664), (217280587/70368744177664)), (57/70368744177664), by norm_num⟩
  | 11 => ⟨((-304782807/281474976710656), (-508653985/1125899906842624)), (17/140737488355328), by norm_num⟩
  | 12 => ⟨((654038673/4503599627370496), (8527573/140737488355328)), (37/2251799813685248), by norm_num⟩
  | 13 => ⟨((-647775161/36028797018963968), (-33783629/4503599627370496)), (149/72057594037927936), by norm_num⟩
  | 14 => ⟨((1191490175/576460752303423488), (248560701/288230376151711744)), (139/576460752303423488), by norm_num⟩
  | 15 => ⟨((-31960491/144115188075855872), (-213356275/2305843009213693952)), (121/4611686018427387904), by norm_num⟩
  | 16 => ⟨((823014815/36893488147419103232), (171691839/18446744073709551616)), (99/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (514880874189/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779827743939873/633825300114114700748351602688), (610025087239/633825300114114700748351602688)), (23065/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472733263518135/9903520314283042199192993792), (171548434509/9903520314283042199192993792)), (103797/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890782409683239/2475880078570760549798248448), (728977581449/2475880078570760549798248448)), (110289/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886224235125253/77371252455336267181195264), (364430717043/77371252455336267181195264)), (55147/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775366198040423/4835703278458516698824704), (683184213389/9671406556917033397649408)), (103405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259820082288883/604462909807314587353088), (597662834343/604462909807314587353088)), (45243/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472366922887787/18889465931478580854784), (970970881067/75557863725914323419136)), (18381/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298795858704601/4722366482869645213696), (364012950047/2361183241434822606848)), (110295/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623175136172737/590295810358705651712), (500353526603/295147905179352825856)), (75835/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912816295460483/36893488147419103232), (312597794297/18446744073709551616)), (189609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912541746608705/4611686018427387904), (703006509913/4611686018427387904)), (106669/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798165297504467/576460752303423488), (175645898533/144115188075855872)), (213375/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196630826234211/144115188075855872), (614285198925/72057594037927936)), (186745/144115188075855872), by norm_num⟩
  | 4 => ⟨((186838667593371/4503599627370496), (230119435417/4503599627370496)), (35025/4503599627370496), by norm_num⟩
  | 3 => ⟨((746546043761125/4503599627370496), (1148936455229/4503599627370496)), (87599/2251799813685248), by norm_num⟩
  | 2 => ⟨((558900091258681/1125899906842624), (4585796491925/4503599627370496)), (701229/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113770456215435/1125899906842624), (1713468461537/562949953421312)), (1052939/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203442810418091/2251799813685248), (3402194524115/562949953421312)), (527571/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203442810418091/2251799813685248), (3402194524115/562949953421312)), (2012523653270530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2156042020447789/2251799813685248), (13316531990535/1125899906842624)), (259715/140737488355328), by norm_num⟩
  | 2 => ⟨((258005165778539/281474976710656), (6375123215603/281474976710656)), (8055757/2251799813685248), by norm_num⟩
  | 3 => ⟨((1890783305850541/2251799813685248), (93496892196769/2251799813685248)), (7566511/1125899906842624), by norm_num⟩
  | 4 => ⟨((1583764160187971/2251799813685248), (157014279724307/2251799813685248)), (26670361/2251799813685248), by norm_num⟩
  | 5 => ⟨((1102964577918615/2251799813685248), (220866515179351/2251799813685248)), (41235629/2251799813685248), by norm_num⟩
  | 6 => ⟨((1037169321641079/4503599627370496), (432734635131645/4503599627370496)), (12121195/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1040880573/33554432)), (1/16777216), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1158794389/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-120005702909277/562949953421312), (-43699655880451/9007199254740992)), (154389191/9007199254740992), by norm_num⟩
  | 1 => ⟨((1640482747/4294967296), (18668001/2147483648)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((-91854703/268435456), (-4181071/536870912)), (61/2147483648), by norm_num⟩
  | 3 => ⟨((877768181/4294967296), (19977263/4294967296)), (37/2147483648), by norm_num⟩
  | 4 => ⟨((-786374725/8589934592), (-17897225/8589934592)), (67/8589934592), by norm_num⟩
  | 5 => ⟨((35224859/1073741824), (12827009/17179869184)), (97/34359738368), by norm_num⟩
  | 6 => ⟨((-673221063/68719476736), (-15321943/68719476736)), (59/68719476736), by norm_num⟩
  | 7 => ⟨((689285837/274877906944), (31375127/549755813888)), (61/274877906944), by norm_num⟩
  | 8 => ⟨((-617517213/1099511627776), (-7027085/549755813888)), (111/2199023255552), by norm_num⟩
  | 9 => ⟨((983504279/8796093022208), (44767453/17592186044416)), (179/17592186044416), by norm_num⟩
  | 10 => ⟨((-352440621/17592186044416), (-32085003/70368744177664)), (65/35184372088832), by norm_num⟩
  | 11 => ⟨((918529193/281474976710656), (41809897/562949953421312)), (171/562949953421312), by norm_num⟩
  | 12 => ⟨((-137148615/281474976710656), (-24971093/2251799813685248)), (13/281474976710656), by norm_num⟩
  | 13 => ⟨((1209783777/18014398509481984), (27533657/18014398509481984)), (29/4503599627370496), by norm_num⟩
  | 14 => ⟨((-309663077/36028797018963968), (-3523835/18014398509481984)), (121/144115188075855872), by norm_num⟩
  | 15 => ⟨((1183662401/1152921504606846976), (6734789/288230376151711744)), (117/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-530209579/4611686018427387904), (-6033561/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-4062633967545/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27805826715369/9903520314283042199192993792), (-2406057703153/316912650057057350374175801344)), (46337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890645695338591/39614081257132168796771975168), (-5412853502245/39614081257132168796771975168)), (3259/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((945238118831897/1237940039285380274899124224), (-2875122837275/1237940039285380274899124224)), (55421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772141338663531/154742504910672534362390528), (-5749220367631/154742504910672534362390528)), (55441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550443441177289/9671406556917033397649408), (-5388804618297/9671406556917033397649408)), (51997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629783114134597/302231454903657293676544), (-4714114465793/604462909807314587353088)), (45519/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944526635157151/37778931862957161709568), (-3829196421949/37778931862957161709568)), (37003/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298483374072187/4722366482869645213696), (-2871003328233/2361183241434822606848)), (55539/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622742760394757/590295810358705651712), (-7892353300777/590295810358705651712)), (76423/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825088060999509/73786976294838206464), (-4930541084147/36893488147419103232)), (95613/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824465320640221/9223372036854775808), (-5543861042757/4611686018427387904)), (3365/288230376151711744), by norm_num⟩
  | 6 => ⟨((1595705461446557/1152921504606846976), (-173128535207/18014398509481984)), (107825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299019004090945/36028797018963968), (-1210845365043/18014398509481984)), (47255/72057594037927936), by norm_num⟩
  | 4 => ⟨((746930761341613/18014398509481984), (-14513268723247/36028797018963968)), (35523/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492005082886983/9007199254740992), (-18112041129465/9007199254740992)), (44547/2251799813685248), by norm_num⟩
  | 2 => ⟨((139584059624339/281474976710656), (-2258462441009/281474976710656)), (22381/281474976710656), by norm_num⟩
  | 1 => ⟨((138997207557965/140737488355328), (-13495305569773/562949953421312)), (33841/140737488355328), by norm_num⟩
  | 0 => ⟨((1097733948831287/1125899906842624), (-6692121982987/140737488355328)), (550105/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1097733948831287/1125899906842624), (-6692121982987/140737488355328)), (2098484043601607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067726897680713/1125899906842624), (-104395347341963/1125899906842624)), (1125003/1125899906842624), by norm_num⟩
  | 2 => ⟨((501439929349803/562949953421312), (-198002894701927/1125899906842624)), (1171189/562949953421312), by norm_num⟩
  | 3 => ⟨((858480277687867/1125899906842624), (-11023022220601/35184372088832)), (4996753/1125899906842624), by norm_num⟩
  | 4 => ⟨((1088134382332401/2251799813685248), (-1075823908752349/2251799813685248)), (21501565/2251799813685248), by norm_num⟩
  | 5 => ⟨((11830248501147/2251799813685248), (-2079476119207631/4503599627370496)), (82651203/4503599627370496), by norm_num⟩
  | 6 => ⟨((-120005702909277/562949953421312), (-43699655880451/9007199254740992)), (154389191/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1158794389/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-314622275/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1650195146849109/9007199254740992), (161434258185915/4503599627370496)), (15420689/2251799813685248), by norm_num⟩
  | 1 => ⟨((-382796703/1073741824), (-149791985/2147483648)), (59/4294967296), by norm_num⟩
  | 2 => ⟨((1489775979/4294967296), (18217609/268435456)), (59/4294967296), by norm_num⟩
  | 3 => ⟨((-966323399/4294967296), (-189065761/4294967296)), (5/536870912), by norm_num⟩
  | 4 => ⟨((940189255/8589934592), (45988123/2147483648)), (41/8589934592), by norm_num⟩
  | 5 => ⟨((-1463619051/34359738368), (-286364017/34359738368)), (65/34359738368), by norm_num⟩
  | 6 => ⟨((949357055/68719476736), (23218277/8589934592)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((-527818151/137438953472), (-206540255/274877906944)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((1027086697/1099511627776), (200954389/1099511627776)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-888274857/4398046511104), (-347590387/8796093022208)), (89/8796093022208), by norm_num⟩
  | 10 => ⟨((86425153/2199023255552), (270551865/35184372088832)), (71/35184372088832), by norm_num⟩
  | 11 => ⟨((-244619029/35184372088832), (-95721749/70368744177664)), (13/35184372088832), by norm_num⟩
  | 12 => ⟨((634675535/562949953421312), (62088641/281474976710656)), (69/1125899906842624), by norm_num⟩
  | 13 => ⟨((-760013271/4503599627370496), (-148700205/4503599627370496)), (85/9007199254740992), by norm_num⟩
  | 14 => ⟨((105636967/4503599627370496), (165346993/36028797018963968)), (97/72057594037927936), by norm_num⟩
  | 15 => ⟨((-877056197/288230376151711744), (-171600209/288230376151711744)), (103/576460752303423488), by norm_num⟩
  | 16 => ⟨((1706672555/4611686018427387904), (83479647/1152921504606846976)), (51/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (31460344985/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779380119700127/633825300114114700748351602688), (149024127809/316912650057057350374175801344)), (11529/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472607388471117/9903520314283042199192993792), (335254743081/39614081257132168796771975168)), (51881/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890247535594575/2475880078570760549798248448), (356147180489/2475880078570760549798248448)), (13781/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((27686151607033/2417851639229258349412352), (356078593335/154742504910672534362390528)), (27563/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775115582485217/4835703278458516698824704), (166875413013/4835703278458516698824704)), (51681/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259381618362297/604462909807314587353088), (145979569251/302231454903657293676544)), (45223/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888755400029719/75557863725914323419136), (474297080321/75557863725914323419136)), (73489/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298261825809019/4722366482869645213696), (355603399961/4722366482869645213696)), (55119/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622441142648649/590295810358705651712), (244380358319/295147905179352825856)), (4737/36893488147419103232), by norm_num⟩
  | 8 => ⟨((57022360979721/2305843009213693952), (305330052103/36893488147419103232)), (94745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228006555661937/1152921504606846976), (42912063481/576460752303423488)), (26649/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398825080882521/288230376151711744), (686093868897/1152921504606846976)), (26651/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195730211433391/144115188075855872), (599771083041/144115188075855872)), (93289/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493360162145619/36028797018963968), (449267869343/18014398509481984)), (69977/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491408661330525/9007199254740992), (280302715447/2251799813685248)), (87489/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116121318447701/2251799813685248), (279569528491/562949953421312)), (175033/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222527071662951/2251799813685248), (1670104409247/1125899906842624)), (525375/2251799813685248), by norm_num⟩
  | 0 => ⟨((1096752890238373/1125899906842624), (6622144270891/2251799813685248)), (1051865/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096752890238373/1125899906842624), (6622144270891/2251799813685248)), (4012546547896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1068350687070153/1125899906842624), (12901423695899/2251799813685248)), (2055457/2251799813685248), by norm_num⟩
  | 2 => ⟨((2027412156166837/2251799813685248), (12241980646707/1125899906842624)), (3924343/2251799813685248), by norm_num⟩
  | 3 => ⟨((1825118095150045/2251799813685248), (22044180151231/1125899906842624)), (7151919/2251799813685248), by norm_num⟩
  | 4 => ⟨((369605710229811/562949953421312), (17867144247123/562949953421312)), (11873537/2251799813685248), by norm_num⟩
  | 5 => ⟨((1936785255778311/4503599627370496), (187691243219103/4503599627370496)), (32689751/4503599627370496), by norm_num⟩
  | 6 => ⟨((1650195146849109/9007199254740992), (161434258185915/4503599627370496)), (15420689/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-314622275/8388608)), (1/33554432), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1344848587/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-542541070040961/4503599627370496), (-258394584604397/2251799813685248)), (67866539/2251799813685248), by norm_num⟩
  | 1 => ⟨((134489827/536870912), (1024849765/4294967296)), (17/268435456), by norm_num⟩
  | 2 => ⟨((-279663733/1073741824), (-266389397/1073741824)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((3028877/16777216), (369294119/2147483648)), (25/536870912), by norm_num⟩
  | 4 => ⟨((-201547925/2147483648), (-191981383/2147483648)), (105/4294967296), by norm_num⟩
  | 5 => ⟨((670571405/17179869184), (638742501/17179869184)), (177/17179869184), by norm_num⟩
  | 6 => ⟨((-464804679/34359738368), (-885485127/68719476736)), (31/8589934592), by norm_num⟩
  | 7 => ⟨((552305233/137438953472), (263044937/68719476736)), (75/68719476736), by norm_num⟩
  | 8 => ⟨((-574243223/549755813888), (-546986569/549755813888)), (79/274877906944), by norm_num⟩
  | 9 => ⟨((132678357/549755813888), (505522931/2199023255552)), (295/4398046511104), by norm_num⟩
  | 10 => ⟨((-882870039/17592186044416), (-420482153/8796093022208)), (31/2199023255552), by norm_num⟩
  | 11 => ⟨((41724469/4398046511104), (635904041/70368744177664)), (95/35184372088832), by norm_num⟩
  | 12 => ⟨((-462739169/281474976710656), (-440775093/281474976710656)), (133/281474976710656), by norm_num⟩
  | 13 => ⟨((148036777/562949953421312), (564040639/2251799813685248)), (43/562949953421312), by norm_num⟩
  | 14 => ⟨((-703620169/18014398509481984), (-2618057/70368744177664)), (103/9007199254740992), by norm_num⟩
  | 15 => ⟨((390169869/72057594037927936), (23228145/4503599627370496)), (231/144115188075855872), by norm_num⟩
  | 16 => ⟨((-405667717/576460752303423488), (-386412557/576460752303423488)), (243/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-3100866134535/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779195315075331/633825300114114700748351602688), (-3671416307679/633825300114114700748351602688)), (92561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890221269252473/39614081257132168796771975168), (-2064838118283/19807040628566084398385987584)), (52077/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890025743889309/2475880078570760549798248448), (-137093010739/77371252455336267181195264)), (110691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885845680534515/77371252455336267181195264), (-4386071147895/154742504910672534362390528)), (110721/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775011067715103/4835703278458516698824704), (-4110980041363/9671406556917033397649408)), (51917/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259198133771013/604462909807314587353088), (-3596146000747/604462909807314587353088)), (45443/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888456143850217/75557863725914323419136), (-2920967318329/37778931862957161709568)), (147751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324509106867691/1180591620717411303424), (-1094968488589/1180591620717411303424)), (110865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622129667602289/590295810358705651712), (-6019764521177/590295810358705651712)), (76263/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824323881669097/73786976294838206464), (-3760431636071/36893488147419103232)), (95393/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823608623085847/9223372036854775808), (-528480582781/576460752303423488)), (214811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398713128858195/288230376151711744), (-8449089128739/1152921504606846976)), (215033/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597666951997423/72057594037927936), (-3692765346887/72057594037927936)), (188403/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492756772182619/36028797018963968), (-11063458781921/36028797018963968)), (283103/36028797018963968), by norm_num⟩
  | 3 => ⟨((372659711920161/2251799813685248), (-215677731263/140737488355328)), (354753/9007199254740992), by norm_num⟩
  | 2 => ⟨((557664119382635/1125899906842624), (-13764484928061/2251799813685248)), (356065/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110016094403425/1125899906842624), (-20549619109181/1125899906842624)), (537387/1125899906842624), by norm_num⟩
  | 0 => ⟨((547014386459279/562949953421312), (-40711506678655/1125899906842624)), (543985/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547014386459279/562949953421312), (-40711506678655/1125899906842624)), (2075138094188499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1061587732562721/1125899906842624), (-9889768936081/140737488355328)), (1096513/562949953421312), by norm_num⟩
  | 2 => ⟨((497694699689379/562949953421312), (-18649717113603/140737488355328)), (4443731/1125899906842624), by norm_num⟩
  | 3 => ⟨((430118204029779/562949953421312), (-263806480181373/1125899906842624)), (9034973/1125899906842624), by norm_num⟩
  | 4 => ⟨((1190892395835741/2251799813685248), (-201559603615617/562949953421312)), (18040143/1125899906842624), by norm_num⟩
  | 5 => ⟨((21321953022747/140737488355328), (-106597308426217/281474976710656)), (63999519/2251799813685248), by norm_num⟩
  | 6 => ⟨((-542541070040961/4503599627370496), (-258394584604397/2251799813685248)), (67866539/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1344848587/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile010Terms0
