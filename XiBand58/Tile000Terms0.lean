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
namespace Reinmann.XiBand58.Tile000Terms0
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
  | 0 => ⟨((15/16), (4561/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4561/320))
  have he : value ((15/16), (4561/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-1326005843/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1056265042848163/2251799813685248), (129104351249955/562949953421312)), (51366621/2251799813685248), by norm_num⟩
  | 1 => ⟨((21819685/67108864), (-682741677/4294967296)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-967952201/8589934592), (118310117/2147483648)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((894577785/34359738368), (-218683531/17179869184)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-1240148139/274877906944), (151579873/68719476736)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((687684149/1099511627776), (-336214917/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-1271110211/17592186044416), (621457125/17592186044416)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((125866637/17592186044416), (-30768661/8796093022208)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-1395905673/2251799813685248), (170617685/562949953421312)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((860060517/18014398509481984), (-210245631/9007199254740992)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-238459409/72057594037927936), (116584933/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((961672535/4611686018427387904), (-117542571/1152921504606846976)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-444387071/36893488147419103232), (434529609/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | 13 => ⟨((758216973/1180591620717411303424), (-92674761/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-1201270759/37778931862957161709568), (293655997/18889465931478580854784)), (91/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((1734703/1180591620717411303424), (-217116615/302231454903657293676544)), (69/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-1231262201/19342813113834066795298816), (300987539/9671406556917033397649408)), (49/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (3499931504013/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780958908328453/633825300114114700748351602688), (4151726581559/633825300114114700748351602688)), (23153/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892204952496763/39614081257132168796771975168), (4670394906457/39614081257132168796771975168)), (26053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946066497682867/1237940039285380274899124224), (4961962476635/2475880078570760549798248448)), (27689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773798148857519/154742504910672534362390528), (2480794321045/77371252455336267181195264)), (13849/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96999797261915/604462909807314587353088), (4651091969727/9671406556917033397649408)), (3247/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315231358501727/151115727451828646838272), (4069307885523/604462909807314587353088)), (11369/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891262082197487/75557863725914323419136), (6611879399471/75557863725914323419136)), (36965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650070035984683/2361183241434822606848), (4958256437611/4722366482869645213696)), (27739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625020863189375/590295810358705651712), (6816540476207/590295810358705651712)), (38165/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827935901798267/73786976294838206464), (8519080975547/73786976294838206464)), (23871/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456917357360553/2305843009213693952), (598860698193/576460752303423488)), (105/18014398509481984), by norm_num⟩
  | 6 => ⟨((1598909924107707/1152921504606846976), (9579024029797/1152921504606846976)), (26911/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198880311014215/144115188075855872), (8378550707737/144115188075855872)), (11791/36028797018963968), by norm_num⟩
  | 4 => ⟨((749034361826319/18014398509481984), (1570202934925/4503599627370496)), (8861/4503599627370496), by norm_num⟩
  | 3 => ⟨((748632682970555/4503599627370496), (3922786998843/2251799813685248)), (88855/9007199254740992), by norm_num⟩
  | 2 => ⟨((280483647546055/562949953421312), (7837386200341/1125899906842624)), (89225/2251799813685248), by norm_num⟩
  | 1 => ⟨((139984385266641/140737488355328), (11735516309435/562949953421312)), (67381/562949953421312), by norm_num⟩
  | 0 => ⟨((1113543864968069/1125899906842624), (46776443165545/1125899906842624)), (273233/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1113543864968069/1125899906842624), (46776443165545/1125899906842624)), (1042301182273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((137422507104113/140737488355328), (92526202365697/1125899906842624)), (563173/1125899906842624), by norm_num⟩
  | 2 => ⟨((1065881082274079/1125899906842624), (90346807027093/562949953421312)), (298095/281474976710656), by norm_num⟩
  | 3 => ⟨((980062519486501/1125899906842624), (171061302818823/562949953421312)), (2640361/1125899906842624), by norm_num⟩
  | 4 => ⟨((374577997425767/562949953421312), (595615188911079/1125899906842624)), (6201345/1125899906842624), by norm_num⟩
  | 5 => ⟨((366777277634631/2251799813685248), (792625857210829/1125899906842624)), (14813733/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1056265042848163/2251799813685248), (129104351249955/562949953421312)), (51366621/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-1326005843/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-1050834769/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1605944386306413/4503599627370496), (-4952830755419/281474976710656)), (129339317/4503599627370496), by norm_num⟩
  | 1 => ⟨((105161085/268435456), (83026745/4294967296)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-1848500165/8589934592), (-45607101/4294967296)), (77/4294967296), by norm_num⟩
  | 3 => ⟨((1353856665/17179869184), (66806029/17179869184)), (115/17179869184), by norm_num⟩
  | 4 => ⟨((-743681785/34359738368), (-18348481/17179869184)), (129/68719476736), by norm_num⟩
  | 5 => ⟨((1307228717/274877906944), (64505173/274877906944)), (29/68719476736), by norm_num⟩
  | 6 => ⟨((-478712511/549755813888), (-47244117/1099511627776)), (173/2199023255552), by norm_num⟩
  | 7 => ⟨((601050797/4398046511104), (59317677/8796093022208)), (111/8796093022208), by norm_num⟩
  | 8 => ⟨((-1289691/68719476736), (-65167129/70368744177664)), (31/17592186044416), by norm_num⟩
  | 9 => ⟨((1289666907/562949953421312), (31819293/281474976710656)), (123/562949953421312), by norm_num⟩
  | 10 => ⟨((-566737565/2251799813685248), (-27965653/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | 11 => ⟨((1811272301/72057594037927936), (89377193/72057594037927936)), (89/36028797018963968), by norm_num⟩
  | 12 => ⟨((-82911917/36028797018963968), (-16365147/144115188075855872)), (133/576460752303423488), by norm_num⟩
  | 13 => ⟨((896866963/4611686018427387904), (44255881/4611686018427387904)), (91/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-1126067505/73786976294838206464), (-55565777/73786976294838206464)), (29/18446744073709551616), by norm_num⟩
  | 15 => ⟨((659792853/590295810358705651712), (4069683/73786976294838206464)), (69/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-1449713073/18889465931478580854784), (-17884015/4722366482869645213696)), (77/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (-4028049941471/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780368745433873/633825300114114700748351602688), (-4775206402943/633825300114114700748351602688)), (46335/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891540901926595/39614081257132168796771975168), (-2685788132005/19807040628566084398385987584)), (26071/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891427282980035/2475880078570760549798248448), (-1426673865279/618970019642690137449562112)), (27709/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886546129064823/77371252455336267181195264), (-2853007643567/77371252455336267181195264)), (27719/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551334794313731/9671406556917033397649408), (-1337166605639/2417851639229258349412352)), (25997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260346028234991/604462909807314587353088), (-584919994809/75557863725914323419136)), (45515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890320193603625/75557863725914323419136), (-1900650867455/18889465931478580854784)), (37001/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324858336497453/1180591620717411303424), (-5700765162693/4722366482869645213696)), (3471/295147905179352825856), by norm_num⟩
  | 9 => ⟨((203006076591383/73786976294838206464), (-7836621507555/590295810358705651712)), (76417/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228339979586837/9223372036854775808), (-9792879246967/73786976294838206464)), (95605/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826300324309815/9223372036854775808), (-5506501030211/4611686018427387904)), (53835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399384883084613/288230376151711744), (-11008013940745/1152921504606846976)), (53907/576460752303423488), by norm_num⟩
  | 5 => ⟨((74854985949129/9007199254740992), (-4813197362845/72057594037927936)), (94499/144115188075855872), by norm_num⟩
  | 4 => ⟨((748132522470113/18014398509481984), (-14428342583985/36028797018963968)), (17759/4503599627370496), by norm_num⟩
  | 3 => ⟨((1495005761301955/9007199254740992), (-18015708933909/9007199254740992)), (44539/2251799813685248), by norm_num⟩
  | 2 => ⟨((1119667526062363/2251799813685248), (-4496516225923/562949953421312)), (179009/2251799813685248), by norm_num⟩
  | 1 => ⟨((279114002955377/281474976710656), (-1681547534935/70368744177664)), (135323/562949953421312), by norm_num⟩
  | 0 => ⟨((1106632874978235/1125899906842624), (-53510822246569/1125899906842624)), (137463/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1106632874978235/1125899906842624), (-53510822246569/1125899906842624)), (524379731298351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((135644041763815/140737488355328), (-105190229975651/1125899906842624)), (35411/35184372088832), by norm_num⟩
  | 2 => ⟨((518025890513831/562949953421312), (-202766556582823/1125899906842624)), (599005/281474976710656), by norm_num⟩
  | 3 => ⟨((916856827350663/1125899906842624), (-373171097721467/1125899906842624)), (5272643/1125899906842624), by norm_num⟩
  | 4 => ⟨((311470748608435/562949953421312), (-303885333533199/562949953421312)), (12082525/1125899906842624), by norm_num⟩
  | 5 => ⟨((33166225691981/2251799813685248), (-672538592473227/1125899906842624)), (26414623/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1605944386306413/4503599627370496), (-4952830755419/281474976710656)), (129339317/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-1050834769/67108864)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-1326005843/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((94258923395021/562949953421312), (-968955853188341/4503599627370496)), (37007573/2251799813685248), by norm_num⟩
  | 1 => ⟨((-249234417/1073741824), (40032209/134217728)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((345512267/2147483648), (-443971405/2147483648)), (73/4294967296), by norm_num⟩
  | 3 => ⟨((-638642277/8589934592), (820633407/8589934592)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((885346187/34359738368), (-1137639465/34359738368)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-490940171/68719476736), (315420635/34359738368)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((907450121/549755813888), (-1166042261/549755813888)), (53/274877906944), by norm_num⟩
  | 7 => ⟨((-718853135/2199023255552), (461850803/1099511627776)), (43/1099511627776), by norm_num⟩
  | 8 => ⟨((31141939/549755813888), (-160065291/2199023255552)), (61/8796093022208), by norm_num⟩
  | 9 => ⟨((-153500069/17592186044416), (788969281/70368744177664)), (77/70368744177664), by norm_num⟩
  | 10 => ⟨((5319907/4398046511104), (-218748733/140737488355328)), (11/70368744177664), by norm_num⟩
  | 11 => ⟨((-686541459/4503599627370496), (882182211/4503599627370496)), (91/4503599627370496), by norm_num⟩
  | 12 => ⟨((158624759/9007199254740992), (-815309483/36028797018963968)), (43/18014398509481984), by norm_num⟩
  | 13 => ⟨((-541293807/288230376151711744), (347771981/144115188075855872)), (75/288230376151711744), by norm_num⟩
  | 14 => ⟨((13399867/72057594037927936), (-550987813/2305843009213693952)), (121/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-634066263/36893488147419103232), (814753385/36893488147419103232)), (23/9223372036854775808), by norm_num⟩
  | 16 => ⟨((879002485/590295810358705651712), (-1129488023/590295810358705651712)), (65/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-1184687375859/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889981733818775/316912650057057350374175801344), (-701904535575/316912650057057350374175801344)), (23085/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891085674776707/39614081257132168796771975168), (-1579102046349/39614081257132168796771975168)), (51945/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890944483851087/2475880078570760549798248448), (-209696666051/309485009821345068724781056)), (55197/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443152612114773/38685626227668133590597632), (-1677322950153/154742504910672534362390528)), (55203/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193860518591209/1208925819614629174706176), (-1572224283199/9671406556917033397649408)), (51759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259952763974251/604462909807314587353088), (-687715157545/302231454903657293676544)), (45295/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889683108344085/75557863725914323419136), (-558643936033/18889465931478580854784)), (73615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162369656788167/590295810358705651712), (-104718481929/295147905179352825856)), (27611/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623396783915229/590295810358705651712), (-2303098142987/590295810358705651712)), (37973/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456477311015087/18446744073709551616), (-2877810336951/73786976294838206464)), (94957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228174271181691/1152921504606846976), (-809019118369/2305843009213693952)), (26715/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798320286865053/576460752303423488), (-1617126062625/576460752303423488)), (53451/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196901273827545/144115188075855872), (-706979845255/36028797018963968)), (93587/144115188075855872), by norm_num⟩
  | 4 => ⟨((747556723425489/18014398509481984), (-4237779521017/36028797018963968)), (140475/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493594486046947/9007199254740992), (-2645028362095/4503599627370496)), (175761/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236596980319081/4503599627370496), (-10558636544337/4503599627370496)), (352021/4503599627370496), by norm_num⟩
  | 1 => ⟨((2229015452739183/2251799813685248), (-3946088480083/562949953421312)), (529283/2251799813685248), by norm_num⟩
  | 0 => ⟨((551577697564779/562949953421312), (-31354851789577/2251799813685248)), (1063587/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((551577697564779/562949953421312), (-31354851789577/2251799813685248)), (4057262429244231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2161304103013543/2251799813685248), (-30721446644541/1125899906842624)), (2113823/2251799813685248), by norm_num⟩
  | 2 => ⟨((2072768710700253/2251799813685248), (-117947231862839/2251799813685248)), (2086551/1125899906842624), by norm_num⟩
  | 3 => ⟨((118862102897851/140737488355328), (-217139490138685/2251799813685248)), (1014975/281474976710656), by norm_num⟩
  | 4 => ⟨((1585251714421671/2251799813685248), (-366777277634629/2251799813685248)), (15281389/2251799813685248), by norm_num⟩
  | 5 => ⟨((528132521424091/1125899906842624), (-258208702499911/1125899906842624)), (13247055/1125899906842624), by norm_num⟩
  | 6 => ⟨((94258923395021/562949953421312), (-968955853188341/4503599627370496)), (37007573/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-1326005843/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1539445111/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-580696671958449/4503599627370496), (404623508986771/2251799813685248)), (89160821/4503599627370496), by norm_num⟩
  | 1 => ⟨((222824869/1073741824), (-310524185/1073741824)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((-44827849/268435456), (124942349/536870912)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((96196853/1073741824), (-1072463751/8589934592)), (125/8589934592), by norm_num⟩
  | 4 => ⟨((-619291449/17179869184), (431515955/8589934592)), (103/17179869184), by norm_num⟩
  | 5 => ⟨((398684455/34359738368), (-1111197021/68719476736)), (135/68719476736), by norm_num⟩
  | 6 => ⟨((-213885959/68719476736), (1192268409/274877906944)), (147/274877906944), by norm_num⟩
  | 7 => ⟨((786825535/1099511627776), (-274125997/274877906944)), (137/1099511627776), by norm_num⟩
  | 8 => ⟨((-633173423/4398046511104), (882377545/4398046511104)), (7/274877906944), by norm_num⟩
  | 9 => ⟨((452912583/17592186044416), (-315584861/8796093022208)), (41/8796093022208), by norm_num⟩
  | 10 => ⟨((-291573873/70368744177664), (49601/8589934592)), (107/140737488355328), by norm_num⟩
  | 11 => ⟨((170643653/281474976710656), (-951222033/1125899906842624)), (127/1125899906842624), by norm_num⟩
  | 12 => ⟨((-366187153/4503599627370496), (1020621869/9007199254740992)), (69/4503599627370496), by norm_num⟩
  | 13 => ⟨((90670075/9007199254740992), (-1010847711/72057594037927936)), (139/72057594037927936), by norm_num⟩
  | 14 => ⟨((-667098771/576460752303423488), (929655217/576460752303423488)), (65/288230376151711744), by norm_num⟩
  | 15 => ⟨((572615495/4611686018427387904), (-398992627/2305843009213693952)), (57/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-28799659/2305843009213693952), (642153861/36893488147419103232)), (47/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (2856915852967/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222454443930347/79228162514264337593543950336), (846042083357/158456325028528675187087900672)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945358260297993/19807040628566084398385987584), (1903334337573/19807040628566084398385987584)), (52061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472637984900081/618970019642690137449562112), (4043961330247/2475880078570760549798248448)), (55327/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772217546737827/154742504910672534362390528), (4043259180703/154742504910672534362390528)), (55341/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550515423752163/9671406556917033397649408), (1894904750075/4835703278458516698824704)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259629750228425/604462909807314587353088), (3315337389429/604462909807314587353088)), (45425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889157500124337/75557863725914323419136), (5386024776389/75557863725914323419136)), (36921/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298562426592351/4722366482869645213696), (4038295035767/4722366482869645213696)), (27703/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202856610835375/73786976294838206464), (2775333822639/295147905179352825856)), (76223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825227860384679/73786976294838206464), (6935352923761/73786976294838206464)), (95337/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824625536157777/9223372036854775808), (1949543240605/2305843009213693952)), (13417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595869348394703/1152921504606846976), (974131265137/144115188075855872)), (53719/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196223540816869/144115188075855872), (6813157044457/144115188075855872)), (94123/144115188075855872), by norm_num⟩
  | 4 => ⟨((747045519323023/18014398509481984), (10208215416755/36028797018963968)), (70707/18014398509481984), by norm_num⟩
  | 3 => ⟨((746153169897993/4503599627370496), (3185029213021/2251799813685248)), (177169/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116995198265435/2251799813685248), (12709903983429/2251799813685248)), (88887/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112515128315491/1125899906842624), (18989379287985/1125899906842624)), (268173/1125899906842624), by norm_num⟩
  | 0 => ⟨((549510389461709/562949953421312), (37677187331243/1125899906842624)), (542411/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((549510389461709/562949953421312), (37677187331243/1125899906842624)), (2069133762839889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((267880629247817/281474976710656), (36777702455405/562949953421312)), (1095227/1125899906842624), by norm_num⟩
  | 2 => ⟨((63435373999649/70368744177664), (140005824903865/1125899906842624)), (1113883/562949953421312), by norm_num⟩
  | 3 => ⟨((448776268439611/562949953421312), (126211174701127/562949953421312)), (1142645/281474976710656), by norm_num⟩
  | 4 => ⟨((1317849854097683/2251799813685248), (402455526808521/1125899906842624)), (18673249/2251799813685248), by norm_num⟩
  | 5 => ⟨((483544952394505/2251799813685248), (942136959177403/2251799813685248)), (17603183/1125899906842624), by norm_num⟩
  | 6 => ⟨((-580696671958449/4503599627370496), (404623508986771/2251799813685248)), (89160821/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1539445111/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-112727759/67108864), (-1713837691/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1542967139439485/9007199254740992), (-662255684649001/9007199254740992)), (36672665/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1318276397/4294967296), (17681761/134217728)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((1181017109/4294967296), (-506903403/4294967296)), (15/1073741824), by norm_num⟩
  | 3 => ⟨((-176341549/1073741824), (605499315/8589934592)), (37/4294967296), by norm_num⟩
  | 4 => ⟨((1263846561/17179869184), (-271227283/8589934592)), (17/4294967296), by norm_num⟩
  | 5 => ⟨((-905803617/34359738368), (194389621/17179869184)), (51/34359738368), by norm_num⟩
  | 6 => ⟨((1081988139/137438953472), (-464399259/137438953472)), (31/68719476736), by norm_num⟩
  | 7 => ⟨((-1107807139/549755813888), (475481011/549755813888)), (33/274877906944), by norm_num⟩
  | 8 => ⟨((496230983/1099511627776), (-212986901/1099511627776)), (61/2199023255552), by norm_num⟩
  | 9 => ⟨((-790334723/8796093022208), (169609465/4398046511104)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((1132871779/70368744177664), (-60779873/8796093022208)), (75/70368744177664), by norm_num⟩
  | 11 => ⟨((-738121359/281474976710656), (158404237/140737488355328)), (25/140737488355328), by norm_num⟩
  | 12 => ⟨((881690623/2251799813685248), (-189214861/1125899906842624)), (61/2251799813685248), by norm_num⟩
  | 13 => ⟨((-972170783/18014398509481984), (417264639/18014398509481984)), (69/18014398509481984), by norm_num⟩
  | 14 => ⟨((995369261/144115188075855872), (-427221639/144115188075855872)), (9/18014398509481984), by norm_num⟩
  | 15 => ⟨((-951179893/1152921504606846976), (102063789/288230376151711744)), (35/576460752303423488), by norm_num⟩
  | 16 => ⟨((426071395/4611686018427387904), (-365747521/9223372036854775808)), (1/144115188075855872), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (-528118447163/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779377756816083/633825300114114700748351602688), (-312703999971/316912650057057350374175801344)), (46131/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236303360837615/4951760157141521099596496896), (-703479889529/39614081257132168796771975168)), (12975/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890244690265153/2475880078570760549798248448), (-747319300851/2475880078570760549798248448)), (27573/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771910844651417/154742504910672534362390528), (-747175249765/154742504910672534362390528)), (55149/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550228471742731/9671406556917033397649408), (-350161890471/4835703278458516698824704)), (6463/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629689624064853/302231454903657293676544), (-612630336001/604462909807314587353088)), (11311/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888751522809503/75557863725914323419136), (-995237565067/75557863725914323419136)), (73527/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649129447758887/2361183241434822606848), (-746177376371/4722366482869645213696)), (55149/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202804634646147/73786976294838206464), (-256396629843/147573952589676412928)), (37919/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456177603766095/18446744073709551616), (-1281372391565/73786976294838206464)), (11851/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824046592212807/9223372036854775808), (-1440704639309/9223372036854775808)), (53337/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398823594283463/288230376151711744), (-1439656248185/1152921504606846976)), (106693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149465612943329/18014398509481984), (-1258520787521/144115188075855872)), (46689/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493351991203903/36028797018963968), (-117839177851/2251799813685248)), (140109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491398082760481/9007199254740992), (-588167285349/2251799813685248)), (175211/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232220389276917/4503599627370496), (-2346508845669/2251799813685248)), (175323/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222490988699135/2251799813685248), (-3504402104861/1125899906842624)), (526535/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193422856035875/2251799813685248), (-13895192879455/2251799813685248)), (263837/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2193422856035875/2251799813685248), (-13895192879455/2251799813685248)), (1006458284618186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((534118388295137/562949953421312), (-6767482940889/562949953421312)), (1034501/1125899906842624), by norm_num⟩
  | 2 => ⟨((2026728323938013/2251799813685248), (-25683541204575/1125899906842624)), (3975821/2251799813685248), by norm_num⟩
  | 3 => ⟨((1822981375586501/2251799813685248), (-92465698064255/2251799813685248)), (1834563/562949953421312), by norm_num⟩
  | 4 => ⟨((1472027473433331/2251799813685248), (-37428559241213/562949953421312)), (6242133/1125899906842624), by norm_num⟩
  | 5 => ⟨((952327341338121/2251799813685248), (-97869921045821/1125899906842624)), (1123893/140737488355328), by norm_num⟩
  | 6 => ⟨((1542967139439485/9007199254740992), (-662255684649001/9007199254740992)), (36672665/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-1713837691/67108864)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-122426081/67108864), (-465321129/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-311775195409723/2251799813685248), (-745911315679615/9007199254740992)), (65242593/4503599627370496), by norm_num⟩
  | 1 => ⟨((1157162699/4294967296), (346058941/2147483648)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-140733415/536870912), (-336699803/2147483648)), (61/2147483648), by norm_num⟩
  | 3 => ⟨((365139441/2147483648), (436791709/4294967296)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((-22204017/268435456), (-212489355/4294967296)), (5/536870912), by norm_num⟩
  | 5 => ⟨((276524941/8589934592), (165394077/8589934592)), (63/17179869184), by norm_num⟩
  | 6 => ⟨((-717456919/68719476736), (-107280671/17179869184)), (83/68719476736), by norm_num⟩
  | 7 => ⟨((797775257/274877906944), (59645299/34359738368)), (47/137438953472), by norm_num⟩
  | 8 => ⟨((-776199485/1099511627776), (-464257571/1099511627776)), (93/1099511627776), by norm_num⟩
  | 9 => ⟨((1342590627/8796093022208), (401512675/4398046511104)), (163/8796093022208), by norm_num⟩
  | 10 => ⟨((-1045024291/35184372088832), (-625046071/35184372088832)), (129/35184372088832), by norm_num⟩
  | 11 => ⟨((739463045/140737488355328), (442284907/140737488355328)), (93/140737488355328), by norm_num⟩
  | 12 => ⟨((-959285763/1125899906842624), (-143441115/281474976710656)), (61/562949953421312), by norm_num⟩
  | 13 => ⟨((1148728555/9007199254740992), (171768321/2251799813685248)), (37/2251799813685248), by norm_num⟩
  | 14 => ⟨((-638663587/36028797018963968), (-763990215/72057594037927936)), (167/72057594037927936), by norm_num⟩
  | 15 => ⟨((662817043/288230376151711744), (792883367/576460752303423488)), (175/576460752303423488), by norm_num⟩
  | 16 => ⟨((-1289782411/4611686018427387904), (-96429987/576460752303423488)), (43/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395399856174459/2535301200456458802993406410752), (-3390124159047/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889573224354461/316912650057057350374175801344), (-4013693196283/633825300114114700748351602688)), (23149/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945083111631869/19807040628566084398385987584), (-564332534237/4951760157141521099596496896)), (26049/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236245895565893/309485009821345068724781056), (-2397965705849/1237940039285380274899124224)), (55369/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885816338578327/77371252455336267181195264), (-4794924397519/154742504910672534362390528)), (55385/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549967008249819/9671406556917033397649408), (-4494171768585/9671406556917033397649408)), (51941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314787446639159/151115727451828646838272), (-1965665276979/302231454903657293676544)), (22733/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888377371802293/75557863725914323419136), (-3193203308089/37778931862957161709568)), (73915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297977166760345/4722366482869645213696), (-299253147209/295147905179352825856)), (27733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202755986153357/73786976294838206464), (-3290359222355/295147905179352825856)), (76311/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824221216915887/73786976294838206464), (-8221622640101/73786976294838206464)), (95459/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823492518701645/9223372036854775808), (-9243448035283/9223372036854775808)), (107489/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797367827125417/576460752303423488), (-9236103138797/1152921504606846976)), (53805/576460752303423488), by norm_num⟩
  | 5 => ⟨((597615400475113/72057594037927936), (-2018332463305/36028797018963968)), (47147/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492600423308713/36028797018963968), (-12093480552253/36028797018963968)), (141715/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490440457146895/9007199254740992), (-1885995700749/1125899906842624)), (177621/9007199254740992), by norm_num⟩
  | 2 => ⟨((557562718867619/1125899906842624), (-15044667748127/2251799813685248)), (178339/2251799813685248), by norm_num⟩
  | 1 => ⟨((554850470290457/562949953421312), (-11229430899421/562949953421312)), (269307/1125899906842624), by norm_num⟩
  | 0 => ⟨((68334693687787/70368744177664), (-44485798259245/1125899906842624)), (68229/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((68334693687787/70368744177664), (-44485798259245/1125899906842624)), (260272980273199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((264998331339101/281474976710656), (-43199909747247/562949953421312)), (1103243/1125899906842624), by norm_num⟩
  | 2 => ⟨((991314515800431/1125899906842624), (-162684500495235/1125899906842624)), (2246649/1125899906842624), by norm_num⟩
  | 3 => ⟨((849310153348223/1125899906842624), (-286475744169701/1125899906842624)), (2302719/562949953421312), by norm_num⟩
  | 4 => ⟨((70972048747153/140737488355328), (-864399248041945/2251799813685248)), (9291753/1125899906842624), by norm_num⟩
  | 5 => ⟨((240826938856207/2251799813685248), (-871810152162813/2251799813685248)), (33010147/2251799813685248), by norm_num⟩
  | 6 => ⟨((-311775195409723/2251799813685248), (-745911315679615/9007199254740992)), (65242593/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-122426081/67108864), (-465321129/16777216)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-1989008765/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-263001681126267/9007199254740992), (1254898218169591/9007199254740992)), (40725919/2251799813685248), by norm_num⟩
  | 1 => ⟨((260780631/4294967296), (-1244300597/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-271139039/4294967296), (161715647/536870912)), (173/4294967296), by norm_num⟩
  | 3 => ⟨((46984815/1073741824), (-448370979/2147483648)), (61/2147483648), by norm_num⟩
  | 4 => ⟨((-3053193/134217728), (116545155/1073741824)), (129/8589934592), by norm_num⟩
  | 5 => ⟨((162532771/17179869184), (-387758139/8589934592)), (109/17179869184), by norm_num⟩
  | 6 => ⟨((-28164783/8589934592), (1075093843/68719476736)), (153/68719476736), by norm_num⟩
  | 7 => ⟨((66933737/68719476736), (-638741371/137438953472)), (23/34359738368), by norm_num⟩
  | 8 => ⟨((-278369587/1099511627776), (1328225341/1099511627776)), (97/549755813888), by norm_num⟩
  | 9 => ⟨((128634063/2199023255552), (-1227540867/4398046511104)), (181/4398046511104), by norm_num⟩
  | 10 => ⟨((-213989611/17592186044416), (1021039789/17592186044416)), (153/17592186044416), by norm_num⟩
  | 11 => ⟨((20226313/8796093022208), (-1544140039/140737488355328)), (117/70368744177664), by norm_num⟩
  | 12 => ⟨((-224316989/562949953421312), (535158157/281474976710656)), (165/562949953421312), by norm_num⟩
  | 13 => ⟨((17940541/281474976710656), (-684818525/2251799813685248)), (213/4503599627370496), by norm_num⟩
  | 14 => ⟨((-85271557/9007199254740992), (406868597/9007199254740992)), (1/140737488355328), by norm_num⟩
  | 15 => ⟨((94569183/72057594037927936), (-902463427/144115188075855872)), (9/9007199254740992), by norm_num⟩
  | 16 => ⟨((-12290693/72057594037927936), (469154985/576460752303423488)), (19/144115188075855872), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (2315244118449/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778958003600783/633825300114114700748351602688), (342567116731/79228162514264337593543950336)), (69353/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889954522665411/39614081257132168796771975168), (192660705211/2475880078570760549798248448)), (78035/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944871307706145/1237940039285380274899124224), (1637289990237/1237940039285380274899124224)), (41463/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442852139607713/38685626227668133590597632), (3273846623555/154742504910672534362390528)), (81/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((1549757354003781/9671406556917033397649408), (3068452186507/9671406556917033397649408)), (38889/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258966795893379/604462909807314587353088), (1342058414877/302231454903657293676544)), (34037/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118005054245719/4722366482869645213696), (2180114969297/37778931862957161709568)), (110653/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297755537272985/4722366482869645213696), (3268895435807/4722366482869645213696)), (83019/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621744363832651/590295810358705651712), (2246328412551/295147905179352825856)), (14275/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823843631107001/73786976294838206464), (5612710754343/73786976294838206464)), (71411/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823070235539081/9223372036854775808), (6310025115071/9223372036854775808)), (160773/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594316492813427/1152921504606846976), (1576171307761/288230376151711744)), (160897/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149358442579283/18014398509481984), (5510596634733/144115188075855872)), (140925/144115188075855872), by norm_num⟩
  | 4 => ⟨((746031264865427/18014398509481984), (2063475033001/9007199254740992)), (105833/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489780301048855/9007199254740992), (5148204558669/4503599627370496)), (16567/562949953421312), by norm_num⟩
  | 2 => ⟨((2228967061261663/4503599627370496), (20530019600387/4503599627370496)), (265807/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217566934223443/2251799813685248), (3829797613581/281474976710656)), (801107/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091700291569593/1125899906842624), (60652254909707/2251799813685248)), (404251/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1091700291569593/1125899906842624), (60652254909707/2251799813685248)), (1542095186473655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2115445334650315/2251799813685248), (29404960408499/562949953421312)), (3222883/2251799813685248), by norm_num⟩
  | 2 => ⟨((495300970987131/562949953421312), (27624385584229/281474976710656)), (1598035/562949953421312), by norm_num⟩
  | 3 => ⟨((1721436327849589/2251799813685248), (194438385432129/1125899906842624)), (12502679/2251799813685248), by norm_num⟩
  | 4 => ⟨((624415605426357/1125899906842624), (594570260068549/2251799813685248)), (23434205/2251799813685248), by norm_num⟩
  | 5 => ⟨((66950089863231/281474976710656), (659488373083423/2251799813685248)), (9592027/562949953421312), by norm_num⟩
  | 6 => ⟨((-263001681126267/9007199254740992), (1254898218169591/9007199254740992)), (40725919/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-1989008765/67108864)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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

end Reinmann.XiBand58.Tile000Terms0
