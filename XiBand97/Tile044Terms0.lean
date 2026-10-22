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
namespace Reinmann.XiBand97.Tile044Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨44,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36127/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36127/1280))
  have he : value ((69/80), (36127/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-328221697/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((116999922995137/281474976710656), (-811020888545019/2251799813685248)), (65885481/2251799813685248), by norm_num⟩
  | 1 => ⟨((-309364955/1073741824), (268057271/1073741824)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((857741785/8589934592), (-743212567/8589934592)), (65/8589934592), by norm_num⟩
  | 3 => ⟨((-792721733/34359738368), (686874261/34359738368)), (31/17179869184), by norm_num⟩
  | 4 => ⟨((274736417/68719476736), (-952209915/274877906944)), (11/34359738368), by norm_num⟩
  | 5 => ⟨((-609384873/1099511627776), (264008647/549755813888)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((563191209/8796093022208), (-243995799/4398046511104)), (97/17592186044416), by norm_num⟩
  | 7 => ⟨((-223071085/35184372088832), (386571429/70368744177664)), (79/140737488355328), by norm_num⟩
  | 8 => ⟨((618484375/1125899906842624), (-16746931/35184372088832)), (57/1125899906842624), by norm_num⟩
  | 9 => ⟨((-762134579/18014398509481984), (660371229/18014398509481984)), (9/2251799813685248), by norm_num⟩
  | 10 => ⟨((845234295/288230376151711744), (-732375129/288230376151711744)), (41/144115188075855872), by norm_num⟩
  | 11 => ⟨((-426088559/2305843009213693952), (369195459/2305843009213693952)), (85/4611686018427387904), by norm_num⟩
  | 12 => ⟨((787578889/73786976294838206464), (-682418111/73786976294838206464)), (5/4611686018427387904), by norm_num⟩
  | 13 => ⟨((-167971719/295147905179352825856), (145543443/295147905179352825856)), (35/590295810358705651712), by norm_num⟩
  | 14 => ⟨((1064494843/37778931862957161709568), (-461179553/18889465931478580854784)), (113/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-393520853/302231454903657293676544), (681952655/604462909807314587353088)), (85/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1091071479/19342813113834066795298816), (-59086695/1208925819614629174706176)), (15/2417851639229258349412352), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-930040927253/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890523887719189/316912650057057350374175801344), (-275834408505/158456325028528675187087900672)), (46155/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892305440000687/39614081257132168796771975168), (-310296866053/9903520314283042199192993792)), (6491/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((946120194295909/1237940039285380274899124224), (-1318681144281/2475880078570760549798248448)), (55177/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221738280675743/19342813113834066795298816), (-659295272191/77371252455336267181195264)), (55181/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776049421916341/4835703278458516698824704), (-618041188801/4835703278458516698824704)), (25869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630507753825297/302231454903657293676544), (-1081475827861/604462909807314587353088)), (45275/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945704926024577/37778931862957161709568), (-439304439461/18889465931478580854784)), (73581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650126062076269/2361183241434822606848), (-1317755424843/4722366482869645213696)), (27597/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625176924549943/590295810358705651712), (-113228572059/36893488147419103232)), (593/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1828133961717449/73786976294838206464), (-283023330405/9223372036854775808)), (94899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827896346834197/9223372036854775808), (-2546680935613/9223372036854775808)), (26697/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599141963562329/1152921504606846976), (-2546019726789/1152921504606846976)), (26705/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199089103844325/144115188075855872), (-556755880757/36028797018963968)), (93505/144115188075855872), by norm_num⟩
  | 4 => ⟨((749196709734303/18014398509481984), (-1669524056917/18014398509481984)), (35083/9007199254740992), by norm_num⟩
  | 3 => ⟨((187211418697663/1125899906842624), (-4171208280297/9007199254740992)), (21943/1125899906842624), by norm_num⟩
  | 2 => ⟨((140298837412185/281474976710656), (-4167306861357/2251799813685248)), (43935/562949953421312), by norm_num⟩
  | 1 => ⟨((1120634400486469/1125899906842624), (-6241211556423/1125899906842624)), (264099/1125899906842624), by norm_num⟩
  | 0 => ⟨((139420270466743/140737488355328), (-12443457061203/1125899906842624)), (530157/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139420270466743/140737488355328), (-12443457061203/1125899906842624)), (2022388462546920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276196380580991/281474976710656), (-12326993818691/562949953421312)), (531055/562949953421312), by norm_num⟩
  | 2 => ⟨((135440906404739/140737488355328), (-48383286016455/1125899906842624)), (2130899/1125899906842624), by norm_num⟩
  | 3 => ⟨((260167523482443/281474976710656), (-46562406289101/562949953421312)), (2142275/562949953421312), by norm_num⟩
  | 4 => ⟨((477094814180601/562949953421312), (-172150662530423/1125899906842624)), (8629189/1125899906842624), by norm_num⟩
  | 5 => ⟨((1564689704491729/2251799813685248), (-145896074512243/562949953421312)), (17265129/1125899906842624), by norm_num⟩
  | 6 => ⟨((116999922995137/281474976710656), (-811020888545019/2251799813685248)), (65885481/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-328221697/16777216)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1040438163/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((400590504344535/1125899906842624), (346745674556355/2251799813685248)), (28338473/1125899906842624), by norm_num⟩
  | 1 => ⟨((-839412023/2147483648), (-363291797/2147483648)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((230547091/1073741824), (399116833/4294967296)), (69/4294967296), by norm_num⟩
  | 3 => ⟨((-675418313/8589934592), (-584632877/17179869184)), (13/2147483648), by norm_num⟩
  | 4 => ⟨((742022859/34359738368), (642284863/68719476736)), (117/68719476736), by norm_num⟩
  | 5 => ⟨((-1304312691/274877906944), (-564497635/274877906944)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((955289301/1099511627776), (413442693/1099511627776)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((-1199420075/8796093022208), (-519100827/8796093022208)), (103/8796093022208), by norm_num⟩
  | 8 => ⟨((658848817/35184372088832), (142572637/17592186044416)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((-1286790057/562949953421312), (-556913959/562949953421312)), (29/140737488355328), by norm_num⟩
  | 10 => ⟨((141368337/562949953421312), (489466015/4503599627370496)), (13/562949953421312), by norm_num⟩
  | 11 => ⟨((-903615955/36028797018963968), (-391078821/36028797018963968)), (85/36028797018963968), by norm_num⟩
  | 12 => ⟨((1323631457/576460752303423488), (572858665/576460752303423488)), (127/576460752303423488), by norm_num⟩
  | 13 => ⟨((-894866329/4611686018427387904), (-387292043/4611686018427387904)), (11/576460752303423488), by norm_num⟩
  | 14 => ⟨((1123555595/73786976294838206464), (243133599/36893488147419103232)), (113/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-329160529/295147905179352825856), (-569833727/1180591620717411303424)), (135/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((1446479209/18889465931478580854784), (626026335/18889465931478580854784)), (151/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (66506950935/1267650600228229401496703205376)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((445126986034895/158456325028528675187087900672), (630831364079/633825300114114700748351602688)), (69197/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945849099342381/19807040628566084398385987584), (177406256203/9903520314283042199192993792)), (77849/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797638964603/1237940039285380274899124224), (753903666789/2475880078570760549798248448)), (82719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773261228372151/154742504910672534362390528), (94227705095/19342813113834066795298816)), (41361/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551494239831727/9671406556917033397649408), (353310323709/4835703278458516698824704)), (19389/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260486578604039/604462909807314587353088), (618205939039/604462909807314587353088)), (33933/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890550528795653/75557863725914323419136), (251105328829/18889465931478580854784)), (55145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299607794824043/4722366482869645213696), (376586548081/2361183241434822606848)), (82725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406072809181031/147573952589676412928), (129422607947/73786976294838206464)), (28439/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456756812334821/18446744073709551616), (1293877956961/73786976294838206464)), (35553/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826651841681515/9223372036854775808), (363783546037/2305843009213693952)), (160011/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199737267626723/144115188075855872), (727268131905/576460752303423488)), (20005/144115188075855872), by norm_num⟩
  | 5 => ⟨((1198001526718467/144115188075855872), (1272046881703/144115188075855872)), (70033/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496763588174427/36028797018963968), (1906726402055/36028797018963968)), (52541/9007199254740992), by norm_num⟩
  | 3 => ⟨((1495656743824045/9007199254740992), (2381057890659/9007199254740992)), (8213/281474976710656), by norm_num⟩
  | 2 => ⟨((560180057461073/1125899906842624), (594384054557/562949953421312)), (525969/4503599627370496), by norm_num⟩
  | 1 => ⟨((558799282289499/562949953421312), (3557512369049/1125899906842624)), (789797/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218661155593591/2251799813685248), (14159860303751/2251799813685248)), (395743/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218661155593591/2251799813685248), (14159860303751/2251799813685248)), (1509639742137718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2185921142626087/2251799813685248), (3487869107373/281474976710656)), (3139261/2251799813685248), by norm_num⟩
  | 2 => ⟨((1060812030884481/1125899906842624), (27086623875473/1125899906842624)), (3086319/1125899906842624), by norm_num⟩
  | 3 => ⟨((499417609345925/562949953421312), (102083022863811/2251799813685248)), (1491075/281474976710656), by norm_num⟩
  | 4 => ⟨((1767593286334699/2251799813685248), (181124659212095/2251799813685248)), (2780789/281474976710656), by norm_num⟩
  | 5 => ⟨((42904289617185/70368744177664), (71088630895879/562949953421312)), (38504123/2251799813685248), by norm_num⟩
  | 6 => ⟨((400590504344535/1125899906842624), (346745674556355/2251799813685248)), (28338473/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1040438163/33554432)), (3/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-328221697/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((96962422588431/2251799813685248), (-168557401826803/562949953421312)), (103196137/2251799813685248), by norm_num⟩
  | 1 => ⟨((-256382865/4294967296), (1782761961/4294967296)), (275/4294967296), by norm_num⟩
  | 2 => ⟨((44427765/1073741824), (-1235716427/4294967296)), (3/67108864), by norm_num⟩
  | 3 => ⟨((-82119947/4294967296), (1142044477/8589934592)), (45/2147483648), by norm_num⟩
  | 4 => ⟨((227684839/34359738368), (-1583209819/34359738368)), (63/8589934592), by norm_num⟩
  | 5 => ⟨((-252510567/137438953472), (438958969/34359738368)), (141/68719476736), by norm_num⟩
  | 6 => ⟨((233369317/549755813888), (-405684229/137438953472)), (263/549755813888), by norm_num⟩
  | 7 => ⟨((-184867753/2199023255552), (80342537/137438953472)), (105/1099511627776), by norm_num⟩
  | 8 => ⟨((64070281/4398046511104), (-55689203/549755813888)), (147/8796093022208), by norm_num⟩
  | 9 => ⟨((-157902701/70368744177664), (1097978711/70368744177664)), (183/70368744177664), by norm_num⟩
  | 10 => ⟨((175119699/562949953421312), (-1217697357/562949953421312)), (205/562949953421312), by norm_num⟩
  | 11 => ⟨((-88279073/2251799813685248), (613849811/2251799813685248)), (209/4503599627370496), by norm_num⟩
  | 12 => ⟨((163174375/36028797018963968), (-1134635375/36028797018963968)), (195/36028797018963968), by norm_num⟩
  | 13 => ⟨((-34801187/72057594037927936), (967962229/288230376151711744)), (21/36028797018963968), by norm_num⟩
  | 14 => ⟨((220547151/4611686018427387904), (-766788903/2305843009213693952)), (67/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-81531539/18446744073709551616), (1133861475/36893488147419103232)), (25/4611686018427387904), by norm_num⟩
  | 16 => ⟨((113026713/295147905179352825856), (-1571865769/590295810358705651712)), (35/73786976294838206464), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-930040927253/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222515303157471/79228162514264337593543950336), (-1102251666927/316912650057057350374175801344)), (92417/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891264390802439/39614081257132168796771975168), (-1239899374937/19807040628566084398385987584)), (103983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891134231413999/2475880078570760549798248448), (-2634464279193/2475880078570760549798248448)), (55249/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443200010145625/38685626227668133590597632), (-2634102176497/154742504910672534362390528)), (27629/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775530863121721/4835703278458516698824704), (-617271523379/2417851639229258349412352)), (25907/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260107979255975/604462909807314587353088), (-16875513099/4722366482869645213696)), (45347/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944967511923577/37778931862957161709568), (-1754692792503/37778931862957161709568)), (147413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299145920394655/4722366482869645213696), (-1315704140233/2361183241434822606848)), (27/1152921504606846976), by norm_num⟩
  | 9 => ⟨((811827880199563/295147905179352825856), (-3617161326305/590295810358705651712)), (76057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826232305993503/73786976294838206464), (-4519914360569/73786976294838206464)), (47555/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825756709123419/9223372036854775808), (-1270697586497/2305843009213693952)), (26763/1152921504606846976), by norm_num⟩
  | 6 => ⟨((798500991573243/576460752303423488), (-1270037355105/288230376151711744)), (53559/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197216236909591/144115188075855872), (-4442160680349/144115188075855872)), (93803/72057594037927936), by norm_num⟩
  | 4 => ⟨((373895838650543/9007199254740992), (-3328651671829/18014398509481984)), (140853/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494177438950499/9007199254740992), (-2077810939259/2251799813685248)), (22041/562949953421312), by norm_num⟩
  | 2 => ⟨((1118874810851283/2251799813685248), (-8295676656131/2251799813685248)), (11045/70368744177664), by norm_num⟩
  | 1 => ⟨((557677840472697/562949953421312), (-6202317943597/562949953421312)), (532125/1125899906842624), by norm_num⟩
  | 0 => ⟨((276196380580991/281474976710656), (-24653987637383/1125899906842624)), (268031/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276196380580991/281474976710656), (-24653987637383/1125899906842624)), (1022457123876476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((135440906404739/140737488355328), (-48383286016457/1125899906842624)), (1075495/562949953421312), by norm_num⟩
  | 2 => ⟨((260167523482443/281474976710656), (-46562406289103/562949953421312)), (4324947/1125899906842624), by norm_num⟩
  | 3 => ⟨((954189628361201/1125899906842624), (-172150662530431/1125899906842624)), (8710549/1125899906842624), by norm_num⟩
  | 4 => ⟨((1564689704491721/2251799813685248), (-583584298048999/2251799813685248)), (34855825/2251799813685248), by norm_num⟩
  | 5 => ⟨((935999383961071/2251799813685248), (-202755222136263/562949953421312)), (8313335/281474976710656), by norm_num⟩
  | 6 => ⟨((96962422588431/2251799813685248), (-168557401826803/562949953421312)), (103196137/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-328221697/8388608)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1524214359/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((71709387028337/2251799813685248), (-557317351569993/2251799813685248)), (171653457/4503599627370496), by norm_num⟩
  | 1 => ⟨((-220130551/4294967296), (1710830069/4294967296)), (133/2147483648), by norm_num⟩
  | 2 => ⟨((177143227/4294967296), (-344184347/1073741824)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-95033675/4294967296), (184647779/1073741824)), (117/4294967296), by norm_num⟩
  | 4 => ⟨((9559425/1073741824), (-145107/2097152)), (95/8589934592), by norm_num⟩
  | 5 => ⟨((-196931853/68719476736), (1530532379/68719476736)), (123/34359738368), by norm_num⟩
  | 6 => ⟨((211299727/274877906944), (-410549473/68719476736)), (133/137438953472), by norm_num⟩
  | 7 => ⟨((-194327881/1099511627776), (1510294599/1099511627776)), (247/1099511627776), by norm_num⟩
  | 8 => ⟨((78189665/2199023255552), (-1215362693/4398046511104)), (201/4398046511104), by norm_num⟩
  | 9 => ⟨((-13982379/2199023255552), (869355909/17592186044416)), (145/17592186044416), by norm_num⟩
  | 10 => ⟨((72012067/70368744177664), (-34979359/4398046511104)), (189/140737488355328), by norm_num⟩
  | 11 => ⟨((-42145073/281474976710656), (1310187207/1125899906842624)), (223/1125899906842624), by norm_num⟩
  | 12 => ⟨((45219919/2251799813685248), (-702888321/4503599627370496)), (121/4503599627370496), by norm_num⟩
  | 13 => ⟨((-179147451/72057594037927936), (10877453/562949953421312)), (121/36028797018963968), by norm_num⟩
  | 14 => ⟨((82379057/288230376151711744), (-10003763/4503599627370496)), (7/18014398509481984), by norm_num⟩
  | 15 => ⟨((-141422909/4611686018427387904), (1099123059/4611686018427387904)), (97/2305843009213693952), by norm_num⟩
  | 16 => ⟨((227611391/73786976294838206464), (-884485161/36893488147419103232)), (157/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-1879447903281/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779825294517141/633825300114114700748351602688), (-1113374402347/316912650057057350374175801344)), (92419/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890930155344399/39614081257132168796771975168), (-313097570199/4951760157141521099596496896)), (103985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945389574607443/1237940039285380274899124224), (-1330475994673/1237940039285380274899124224)), (110501/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110777812921219/9671406556917033397649408), (-2660527512689/154742504910672534362390528)), (110519/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550728933398349/9671406556917033397649408), (-2493793598267/9671406556917033397649408)), (103631/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19684638076627/9444732965739290427392), (-545404630711/151115727451828646838272)), (90697/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889462013887547/75557863725914323419136), (-1772142427467/37778931862957161709568)), (73709/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324697811813045/1180591620717411303424), (-1328737099621/2361183241434822606848)), (27649/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623168221879341/590295810358705651712), (-3652825706679/590295810358705651712)), (152121/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912811544227123/36893488147419103232), (-4564230640287/73786976294838206464)), (190229/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825071622160905/9223372036854775808), (-5132283202047/9223372036854775808)), (107057/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596317249727217/1152921504606846976), (-5129189043803/1152921504606846976)), (26781/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196617493015867/144115188075855872), (-4484561103937/144115188075855872)), (93809/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494686034736317/36028797018963968), (-3359943542035/18014398509481984)), (281729/36028797018963968), by norm_num⟩
  | 3 => ⟨((46658036959261/281474976710656), (-524231091311/562949953421312)), (176345/4503599627370496), by norm_num⟩
  | 2 => ⟨((558878323099427/1125899906842624), (-523092099089/140737488355328)), (88371/562949953421312), by norm_num⟩
  | 1 => ⟨((1113683667245297/1125899906842624), (-12508714454591/1125899906842624)), (133053/281474976710656), by norm_num⟩
  | 0 => ⟨((1101462453313363/1125899906842624), (-24835827890781/1125899906842624)), (134049/140737488355328), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101462453313363/1125899906842624), (-24835827890781/1125899906842624)), (511356354296636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1077007565541585/1125899906842624), (-97187082980981/2251799813685248)), (4291087/2251799813685248), by norm_num⟩
  | 2 => ⟨((514070547889755/562949953421312), (-11620840250463/140737488355328)), (8579897/2251799813685248), by norm_num⟩
  | 3 => ⟨((232798514117189/281474976710656), (-339578702692895/2251799813685248)), (17086759/2251799813685248), by norm_num⟩
  | 4 => ⟨((744554593065851/1125899906842624), (-140427078699099/562949953421312)), (33417249/2251799813685248), by norm_num⟩
  | 5 => ⟨((105578320381295/281474976710656), (-742912408471127/2251799813685248)), (475541/17592186044416), by norm_num⟩
  | 6 => ⟨((71709387028337/2251799813685248), (-557317351569993/2251799813685248)), (171653457/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1524214359/33554432)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1696881557/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((457910560870245/2251799813685248), (-144427046223213/2251799813685248)), (9667931/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1564913909/4294967296), (493580871/4294967296)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((700987329/2147483648), (-110547275/1073741824)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-418666895/2147483648), (66024709/1073741824)), (39/4294967296), by norm_num⟩
  | 4 => ⟨((1500300747/17179869184), (-236600795/8589934592)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-268817807/8589934592), (84786343/8589934592)), (53/34359738368), by norm_num⟩
  | 6 => ⟨((642209135/68719476736), (-50638911/17179869184)), (65/137438953472), by norm_num⟩
  | 7 => ⟨((-657533885/274877906944), (207389139/274877906944)), (17/137438953472), by norm_num⟩
  | 8 => ⟨((1178142565/2199023255552), (-185795727/1099511627776)), (63/2199023255552), by norm_num⟩
  | 9 => ⟨((-469099577/4398046511104), (295912225/8796093022208)), (13/2199023255552), by norm_num⟩
  | 10 => ⟨((1344821775/70368744177664), (-424162825/70368744177664)), (19/17592186044416), by norm_num⟩
  | 11 => ⟨((-438108573/140737488355328), (276362821/281474976710656)), (51/281474976710656), by norm_num⟩
  | 12 => ⟨((8176929/17592186044416), (-165058567/1125899906842624)), (63/2251799813685248), by norm_num⟩
  | 13 => ⟨((-1154055087/18014398509481984), (181997077/9007199254740992)), (71/18014398509481984), by norm_num⟩
  | 14 => ⟨((1181593789/144115188075855872), (-23292499/9007199254740992)), (37/72057594037927936), by norm_num⟩
  | 15 => ⟨((-35285531/36028797018963968), (356134875/1152921504606846976)), (9/144115188075855872), by norm_num⟩
  | 16 => ⟨((1011570949/9223372036854775808), (-319054017/9223372036854775808)), (33/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-397985319773/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222448145595377/79228162514264337593543950336), (-235703155153/316912650057057350374175801344)), (11531/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890660192641999/39614081257132168796771975168), (-265129852231/19807040628566084398385987584)), (51891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890492543715035/2475880078570760549798248448), (-140828027609/618970019642690137449562112)), (1723/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1772158659732007/154742504910672534362390528), (-281606103797/77371252455336267181195264)), (27569/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550460757620919/9671406556917033397649408), (-527905322619/9671406556917033397649408)), (51693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259582457521699/604462909807314587353088), (-461811063157/604462909807314587353088)), (22617/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944540830840257/37778931862957161709568), (-750244110325/75557863725914323419136)), (73509/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298506432846863/4722366482869645213696), (-281254566515/2361183241434822606848)), (55135/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622777332441019/590295810358705651712), (-3020185549/2305843009213693952)), (9477/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1825135571379521/73786976294838206464), (-966035733633/73786976294838206464)), (47389/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824524669347729/9223372036854775808), (-67888000477/576460752303423488)), (106637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49867880461329/36028797018963968), (-542740369563/576460752303423488)), (106651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149517832778013/18014398509481984), (-948978118721/144115188075855872)), (11667/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493978001216869/36028797018963968), (-177729217913/4503599627370496)), (35009/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492179497377275/9007199254740992), (-887218656141/4503599627370496)), (175101/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116889964616811/2251799813685248), (-885081145261/1125899906842624)), (350371/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224822090900201/2251799813685248), (-5289162626895/2251799813685248)), (16437/70368744177664), by norm_num⟩
  | 0 => ⟨((1099026161059503/1125899906842624), (-10493332777297/2251799813685248)), (526845/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1099026161059503/1125899906842624), (-10493332777297/2251799813685248)), (2009754185203170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536384703402335/562949953421312), (-160044855687/17592186044416)), (2066901/2251799813685248), by norm_num⟩
  | 2 => ⟨((2044105833531085/2251799813685248), (-39038064846291/2251799813685248)), (3976339/2251799813685248), by norm_num⟩
  | 3 => ⟨((115930728577209/140737488355328), (-70874804764703/2251799813685248)), (7357037/2251799813685248), by norm_num⟩
  | 4 => ⟨((1525712810371103/2251799813685248), (-58382225305845/1125899906842624)), (12583655/2251799813685248), by norm_num⟩
  | 5 => ⟨((1027695991774919/2251799813685248), (-158228113362035/2251799813685248)), (18357199/2251799813685248), by norm_num⟩
  | 6 => ⟨((457910560870245/2251799813685248), (-144427046223213/2251799813685248)), (9667931/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1696881557/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1842869593/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-47122175517389/4503599627370496), (1678840702343899/9007199254740992)), (136571325/4503599627370496), by norm_num⟩
  | 1 => ⟨((43723831/2147483648), (-1557766515/4294967296)), (255/4294967296), by norm_num⟩
  | 2 => ⟨((-85082647/4294967296), (378909209/1073741824)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((55187729/4294967296), (-1966195401/8589934592)), (163/4294967296), by norm_num⟩
  | 4 => ⟨((-53695181/8589934592), (1913019793/17179869184)), (319/17179869184), by norm_num⟩
  | 5 => ⟨((41794399/17179869184), (-372256463/8589934592)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((-108437527/137438953472), (1931673679/137438953472)), (163/68719476736), by norm_num⟩
  | 7 => ⟨((60288481/274877906944), (-67122561/17179869184)), (183/274877906944), by norm_num⟩
  | 8 => ⟨((-916531/17179869184), (522457891/549755813888)), (45/274877906944), by norm_num⟩
  | 9 => ⟨((6341287/549755813888), (-1807388645/8796093022208)), (313/8796093022208), by norm_num⟩
  | 10 => ⟨((-39486639/17592186044416), (1406806363/35184372088832)), (245/35184372088832), by norm_num⟩
  | 11 => ⟨((55881783/140737488355328), (-1990922749/281474976710656)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((-566359/8796093022208), (1291385595/1125899906842624)), (57/281474976710656), by norm_num⟩
  | 13 => ⟨((86810287/9007199254740992), (-773206257/4503599627370496)), (275/9007199254740992), by norm_num⟩
  | 14 => ⟨((-48264291/36028797018963968), (859765659/36028797018963968)), (77/18014398509481984), by norm_num⟩
  | 15 => ⟨((25044793/144115188075855872), (-1784561837/576460752303423488)), (321/576460752303423488), by norm_num⟩
  | 16 => ⟨((-48734917/2305843009213693952), (1736298495/4611686018427387904)), (157/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2119185072733/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779376800346077/633825300114114700748351602688), (2509585537611/633825300114114700748351602688)), (92447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890425628472909/39614081257132168796771975168), (705715322103/9903520314283042199192993792)), (104019/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472560780120413/618970019642690137449562112), (2998776004803/2475880078570760549798248448)), (110539/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771909012998433/154742504910672534362390528), (749549430025/38685626227668133590597632)), (110559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550226476474861/9671406556917033397649408), (2810196043907/9671406556917033397649408)), (103671/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259377224338143/604462909807314587353088), (307288417761/75557863725914323419136)), (45367/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944373856683703/37778931862957161709568), (3993598072775/75557863725914323419136)), (36871/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298255583094855/4722366482869645213696), (2994191376217/4722366482869645213696)), (110649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101401986456163/36893488147419103232), (4115376964919/590295810358705651712)), (152201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912351344956499/36893488147419103232), (5141767793097/73786976294838206464)), (95169/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912018189996871/4611686018427387904), (5781116710361/9223372036854775808)), (214251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595282265861811/1152921504606846976), (2888451859123/576460752303423488)), (214403/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597856086747255/72057594037927936), (631256749463/18014398509481984)), (187773/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493328640100127/36028797018963968), (3782807311639/18014398509481984)), (281999/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491361466848509/9007199254740992), (9440468206039/9007199254740992)), (44137/1125899906842624), by norm_num⟩
  | 2 => ⟨((279015620031581/562949953421312), (18831350483121/4503599627370496)), (44249/281474976710656), by norm_num⟩
  | 1 => ⟨((277786580638569/281474976710656), (1757705367171/140737488355328)), (533233/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096403560399481/1125899906842624), (55752961831737/2251799813685248)), (2150941/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096403560399481/1125899906842624), (55752961831737/2251799813685248)), (8205188759810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2133979515883065/2251799813685248), (108584689426885/2251799813685248)), (2147847/1125899906842624), by norm_num⟩
  | 2 => ⟨((1008543901599565/1125899906842624), (51451621402409/562949953421312)), (1069519/281474976710656), by norm_num⟩
  | 3 => ⟨((447007641601405/562949953421312), (92177321762693/562949953421312)), (16892641/2251799813685248), by norm_num⟩
  | 4 => ⟨((679702242943517/1125899906842624), (585543591715169/2251799813685248)), (16179517/1125899906842624), by norm_num⟩
  | 5 => ⟨((668407222215657/2251799813685248), (706981660112411/2251799813685248)), (6987371/281474976710656), by norm_num⟩
  | 6 => ⟨((-47122175517389/4503599627370496), (1678840702343899/9007199254740992)), (136571325/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1842869593/33554432)), (1/16777216), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1969330181/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-810120870369873/9007199254740992), (-630355377497883/4503599627370496)), (50314165/1125899906842624), by norm_num⟩
  | 1 => ⟨((200819849/1073741824), (1250064047/4294967296)), (201/2147483648), by norm_num⟩
  | 2 => ⟨((-835186273/4294967296), (-1299717555/4294967296)), (421/4294967296), by norm_num⟩
  | 3 => ⟨((289453505/2147483648), (900895559/4294967296)), (147/2147483648), by norm_num⟩
  | 4 => ⟨((-601901643/8589934592), (-936679825/8589934592)), (77/2147483648), by norm_num⟩
  | 5 => ⟨((15645241/536870912), (97388547/2147483648)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((-173511275/17179869184), (-270018387/17179869184)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((824700693/274877906944), (80212493/17179869184)), (215/137438953472), by norm_num⟩
  | 8 => ⟨((-107182305/137438953472), (-83398595/68719476736)), (113/274877906944), by norm_num⟩
  | 9 => ⟨((792459867/4398046511104), (19269167/68719476736)), (105/1099511627776), by norm_num⟩
  | 10 => ⟨((-659149587/17592186044416), (-512884561/8796093022208)), (11/549755813888), by norm_num⟩
  | 11 => ⟨((498422921/70368744177664), (387823077/35184372088832)), (67/17592186044416), by norm_num⟩
  | 12 => ⟨((-690960885/562949953421312), (-537636945/281474976710656)), (187/281474976710656), by norm_num⟩
  | 13 => ⟨((110524059/562949953421312), (343995261/1125899906842624)), (241/2251799813685248), by norm_num⟩
  | 14 => ⟨((-525321873/18014398509481984), (-817506327/18014398509481984)), (289/18014398509481984), by norm_num⟩
  | 15 => ⟨((72825075/18014398509481984), (906643529/144115188075855872)), (323/144115188075855872), by norm_num⟩
  | 16 => ⟨((-605741945/1152921504606846976), (-942656109/1152921504606846976)), (169/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1395061371469/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((55599896483059/19807040628566084398385987584), (-3303497053537/633825300114114700748351602688)), (34697/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945111445872823/19807040628566084398385987584), (-3715836798583/39614081257132168796771975168)), (156167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890027568755273/2475880078570760549798248448), (-1973676457857/1237940039285380274899124224)), (41491/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771693299455441/154742504910672534362390528), (-3946538853665/154742504910672534362390528)), (166005/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775012036608141/4835703278458516698824704), (-1849507680051/4835703278458516698824704)), (155673/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259199949807715/604462909807314587353088), (-3235773766167/604462909807314587353088)), (136257/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944229660319603/37778931862957161709568), (-5256511406741/75557863725914323419136)), (221499/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649019503708273/2361183241434822606848), (-3940965512605/4722366482869645213696)), (41549/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202766691928721/73786976294838206464), (-2708261912171/295147905179352825856)), (114317/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824329196534687/73786976294838206464), (-3383600066861/36893488147419103232)), (142983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823615261573787/9223372036854775808), (-3804175807547/4611686018427387904)), (160975/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398714994182559/288230376151711744), (-7602418353081/1152921504606846976)), (322249/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195341356544717/144115188075855872), (-1661361112805/36028797018963968)), (282305/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492769794474561/36028797018963968), (-9954831748007/36028797018963968)), (212065/18014398509481984), by norm_num⟩
  | 3 => ⟨((372664585451817/2251799813685248), (-3105055555597/2251799813685248)), (265671/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115352537695017/2251799813685248), (-12385283398655/2251799813685248)), (266557/1125899906842624), by norm_num⟩
  | 1 => ⟨((277516121585705/281474976710656), (-9245354516881/562949953421312)), (201027/281474976710656), by norm_num⟩
  | 0 => ⟨((1094172921000199/1125899906842624), (-18316670682913/562949953421312)), (1626021/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094172921000199/1125899906842624), (-18316670682913/562949953421312)), (6202777866843795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((265537010013635/281474976710656), (-35601042228211/562949953421312)), (3266215/1125899906842624), by norm_num⟩
  | 2 => ⟨((498751583215889/562949953421312), (-134340813057297/1125899906842624)), (6575657/1125899906842624), by norm_num⟩
  | 3 => ⟨((867719330156305/1125899906842624), (-238041384658191/1125899906842624)), (26441491/2251799813685248), by norm_num⟩
  | 4 => ⟨((154603693206949/281474976710656), (-733824062298129/2251799813685248)), (51937055/2251799813685248), by norm_num⟩
  | 5 => ⟨((440203238571475/2251799813685248), (-50382769154663/140737488355328)), (45452507/1125899906842624), by norm_num⟩
  | 6 => ⟨((-810120870369873/9007199254740992), (-630355377497883/4503599627370496)), (50314165/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1969330181/33554432)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile044Terms0
