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
namespace Reinmann.XiBand97.Tile043Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35769/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35769/1280))
  have he : value ((69/80), (35769/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-257531989/4194304)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((94024050569895/4503599627370496), (335169883061535/2251799813685248)), (311434057/9007199254740992), by norm_num⟩
  | 1 => ⟨((-197021441/4294967296), (-87790907/268435456)), (329/4294967296), by norm_num⟩
  | 2 => ⟨((1691017/33554432), (1543170709/4294967296)), (91/1073741824), by norm_num⟩
  | 3 => ⟨((-79264941/2147483648), (-565115435/2147483648)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((174162877/8589934592), (1241685523/8589934592)), (297/8589934592), by norm_num⟩
  | 5 => ⟨((-76534991/8589934592), (-272826195/4294967296)), (263/17179869184), by norm_num⟩
  | 6 => ⟨((112109709/34359738368), (1598561123/68719476736)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-140760119/137438953472), (-1003542225/137438953472)), (123/68719476736), by norm_num⟩
  | 8 => ⟨((154640797/549755813888), (1102503821/549755813888)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((-75506791/1099511627776), (-1076643775/2199023255552)), (67/549755813888), by norm_num⟩
  | 10 => ⟨((66362151/4398046511104), (473125633/4398046511104)), (119/4398046511104), by norm_num⟩
  | 11 => ⟨((-212090981/70368744177664), (-378023007/17592186044416)), (383/70368744177664), by norm_num⟩
  | 12 => ⟨((38834293/70368744177664), (1107468589/281474976710656)), (141/140737488355328), by norm_num⟩
  | 13 => ⟨((-52509331/562949953421312), (-748725293/1125899906842624)), (3/17592186044416), by norm_num⟩
  | 14 => ⟨((65928453/4503599627370496), (940067209/9007199254740992)), (485/18014398509481984), by norm_num⟩
  | 15 => ⟨((-154516925/72057594037927936), (-1101620681/72057594037927936)), (143/36028797018963968), by norm_num⟩
  | 16 => ⟨((169754193/576460752303423488), (605127009/288230376151711744)), (79/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1864613262385/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444760813125837/158456325028528675187087900672), (2207326608169/633825300114114700748351602688)), (69313/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472512622896749/9903520314283042199192993792), (2482826597177/39614081257132168796771975168)), (155975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889844666519673/2475880078570760549798248448), (1318746473739/1237940039285380274899124224)), (41437/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771510704098639/154742504910672534362390528), (2636918986695/154742504910672534362390528)), (165775/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549853215966649/9671406556917033397649408), (308937732521/1208925819614629174706176)), (155443/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629525387715103/302231454903657293676544), (2161954599159/604462909807314587353088)), (68021/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888217522607651/75557863725914323419136), (3512033700561/75557863725914323419136)), (110561/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297858192547981/4722366482869645213696), (2633025910493/4722366482869645213696)), (165889/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101367861340805/36893488147419103232), (3618787301431/590295810358705651712)), (228175/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456005200625377/18446744073709551616), (4521050262595/73786976294838206464)), (142667/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455817525396783/2305843009213693952), (2541418404053/4611686018427387904)), (40145/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594517042794193/1152921504606846976), (2539329312141/576460752303423488)), (321361/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195043789432427/144115188075855872), (4439129602141/144115188075855872)), (281415/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492328433416387/36028797018963968), (1662327604081/9007199254740992)), (105643/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490115348584531/9007199254740992), (8295237181443/9007199254740992)), (132251/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229645118506629/4503599627370496), (16541356323899/4503599627370496)), (1060377/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218603780286503/2251799813685248), (12344767362921/1125899906842624)), (798251/1125899906842624), by norm_num⟩
  | 0 => ⟨((546388111964959/562949953421312), (24445419877059/1125899906842624)), (3216827/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546388111964959/562949953421312), (24445419877059/1125899906842624)), (12271221169478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1060096274792923/1125899906842624), (47452483943349/1125899906842624)), (6384065/2251799813685248), by norm_num⟩
  | 2 => ⟨((1992277229585395/2251799813685248), (178716424621027/2251799813685248)), (6280011/1125899906842624), by norm_num⟩
  | 3 => ⟨((1748480915206911/2251799813685248), (316238291842363/2251799813685248)), (24218609/2251799813685248), by norm_num⟩
  | 4 => ⟨((1313251220487387/2251799813685248), (245553185759919/1125899906842624)), (5551629/281474976710656), by norm_num⟩
  | 5 => ⟨((164695290734621/562949953421312), (572827156186725/2251799813685248)), (71175949/2251799813685248), by norm_num⟩
  | 6 => ⟨((94024050569895/4503599627370496), (335169883061535/2251799813685248)), (311434057/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-257531989/4194304)), (3/33554432), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-539762139/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((17911279418793/2251799813685248), (-617062547899823/4503599627370496)), (48764821/1125899906842624), by norm_num⟩
  | 1 => ⟨((-19665835/1073741824), (1355017685/4294967296)), (431/4294967296), by norm_num⟩
  | 2 => ⟨((90564517/4294967296), (-1560021761/4294967296)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((-17377709/1073741824), (1197360951/4294967296)), (3/33554432), by norm_num⟩
  | 4 => ⟨((80027307/8589934592), (-1378512739/8589934592)), (445/8589934592), by norm_num⟩
  | 5 => ⟨((-36853937/8589934592), (634828577/8589934592)), (103/4294967296), by norm_num⟩
  | 6 => ⟨((14143221/8589934592), (-974497879/34359738368)), (635/68719476736), by norm_num⟩
  | 7 => ⟨((-74436503/137438953472), (641104083/68719476736)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((85698191/549755813888), (-1476196705/549755813888)), (243/274877906944), by norm_num⟩
  | 9 => ⟨((-1370329/34359738368), (1510697123/2199023255552)), (125/549755813888), by norm_num⟩
  | 10 => ⟨((40387829/4398046511104), (-695701735/4398046511104)), (463/8796093022208), by norm_num⟩
  | 11 => ⟨((-67633755/35184372088832), (36407101/1099511627776)), (195/17592186044416), by norm_num⟩
  | 12 => ⟨((103821651/281474976710656), (-447095723/70368744177664)), (601/281474976710656), by norm_num⟩
  | 13 => ⟨((-73556365/1125899906842624), (1267047319/1125899906842624)), (107/281474976710656), by norm_num⟩
  | 14 => ⟨((96782737/9007199254740992), (-416783467/2251799813685248)), (565/9007199254740992), by norm_num⟩
  | 15 => ⟨((-59426797/36028797018963968), (1023658025/36028797018963968)), (349/36028797018963968), by norm_num⟩
  | 16 => ⟨((17104407/72057594037927936), (-1178529855/288230376151711744)), (101/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (-1970601384253/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778902828737545/633825300114114700748351602688), (-2332445444227/633825300114114700748351602688)), (184859/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889892525036031/39614081257132168796771975168), (-655885332307/9903520314283042199192993792)), (51999/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236209604735131/309485009821345068724781056), (-2786947574303/2475880078570760549798248448)), (221029/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885671443825509/77371252455336267181195264), (-1393156006519/77371252455336267181195264)), (55267/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549695901010801/9671406556917033397649408), (-652873098555/2417851639229258349412352)), (51823/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629456568909929/302231454903657293676544), (-1142190456731/302231454903657293676544)), (181421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887993885846821/75557863725914323419136), (-1855426942063/37778931862957161709568)), (294887/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297690486314765/4722366482869645213696), (-2782033846559/4722366482869645213696)), (13827/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621655220104029/590295810358705651712), (-3823499111037/590295810358705651712)), (304303/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823732652982985/73786976294838206464), (-2388339523021/36893488147419103232)), (190271/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822946005246745/9223372036854775808), (-1342515157121/2305843009213693952)), (428335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594193036494707/1152921504606846976), (-2682717334993/576460752303423488)), (53577/144115188075855872), by norm_num⟩
  | 5 => ⟨((597380192749461/72057594037927936), (-2344777740909/72057594037927936)), (93839/36028797018963968), by norm_num⟩
  | 4 => ⟨((745951765688771/18014398509481984), (-219498261865/1125899906842624)), (140917/9007199254740992), by norm_num⟩
  | 3 => ⟨((744792289686341/4503599627370496), (-8761774429583/9007199254740992)), (705697/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114292330691287/2251799813685248), (-17469178356785/4503599627370496)), (707367/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217015819739771/2251799813685248), (-26068182594771/2251799813685248)), (266309/281474976710656), by norm_num⟩
  | 0 => ⟨((2182387557683391/2251799813685248), (-51596070129443/2251799813685248)), (4294541/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182387557683391/2251799813685248), (-51596070129443/2251799813685248)), (16382373818404387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1056966358321193/1125899906842624), (-100011218396517/2251799813685248)), (8521127/2251799813685248), by norm_num⟩
  | 2 => ⟨((1980064684075479/2251799813685248), (-46944001263963/562949953421312)), (16755751/2251799813685248), by norm_num⟩
  | 3 => ⟨((431365645986247/562949953421312), (-330232406866911/2251799813685248)), (252047/17592186044416), by norm_num⟩
  | 4 => ⟨((159215290176873/281474976710656), (-31630457256457/140737488355328)), (29452381/1125899906842624), by norm_num⟩
  | 5 => ⟨((303367149301375/1125899906842624), (-572532875425393/2251799813685248)), (93115973/2251799813685248), by norm_num⟩
  | 6 => ⟨((17911279418793/2251799813685248), (-617062547899823/4503599627370496)), (48764821/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-539762139/8388608)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-562104343/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-145421583087593/2251799813685248), (978853846198655/9007199254740992)), (25508471/1125899906842624), by norm_num⟩
  | 1 => ⟨((665103391/4294967296), (-559613469/2147483648)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((-797424139/4294967296), (335473623/1073741824)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((318689929/2147483648), (-1072574153/4294967296)), (231/4294967296), by norm_num⟩
  | 4 => ⟨((-382092537/4294967296), (642980123/4294967296)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((732974311/17179869184), (-616719599/8589934592)), (271/17179869184), by norm_num⟩
  | 6 => ⟨((-146466303/8589934592), (985886007/34359738368)), (219/34359738368), by norm_num⟩
  | 7 => ⟨((401383835/68719476736), (-84430407/8589934592)), (151/68719476736), by norm_num⟩
  | 8 => ⟨((-60154775/34359738368), (809821095/274877906944)), (183/274877906944), by norm_num⟩
  | 9 => ⟨((128217645/274877906944), (-431525817/549755813888)), (197/1099511627776), by norm_num⟩
  | 10 => ⟨((-61490497/549755813888), (827802973/4398046511104)), (191/4398046511104), by norm_num⟩
  | 11 => ⟨((428938973/17592186044416), (-180453167/4398046511104)), (169/17592186044416), by norm_num⟩
  | 12 => ⟨((-342850245/70368744177664), (36058983/4398046511104)), (273/140737488355328), by norm_num⟩
  | 13 => ⟨((505919373/562949953421312), (-851354239/562949953421312)), (51/140737488355328), by norm_num⟩
  | 14 => ⟨((-693223813/4503599627370496), (1166547603/4503599627370496)), (141/2251799813685248), by norm_num⟩
  | 15 => ⟨((443274161/18014398509481984), (-745935729/18014398509481984)), (91/9007199254740992), by norm_num⟩
  | 16 => ⟨((-132865627/36028797018963968), (894337879/144115188075855872)), (55/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (10720997611/39614081257132168796771975168)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778773357727311/633825300114114700748351602688), (3248096772271/633825300114114700748351602688)), (11565/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889746741668671/39614081257132168796771975168), (1826718965023/19807040628566084398385987584)), (52053/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944760886704857/1237940039285380274899124224), (1940478861883/1237940039285380274899124224)), (27659/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771187632504359/154742504910672534362390528), (1940017652729/77371252455336267181195264)), (110663/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549550146865633/9671406556917033397649408), (3636553233457/9671406556917033397649408)), (103775/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258785400663423/604462909807314587353088), (1590502221613/302231454903657293676544)), (90831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235973241755723/9444732965739290427392), (5167295890055/75557863725914323419136)), (73827/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297534191259251/4722366482869645213696), (1936932808021/2361183241434822606848)), (110787/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405359944213581/147573952589676412928), (5323955896047/590295810358705651712)), (19051/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823462543751253/73786976294838206464), (831379060057/9223372036854775808)), (5957/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1822641027124803/9223372036854775808), (7477034603935/9223372036854775808)), (214609/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593886679632595/1152921504606846976), (7470317332041/1152921504606846976)), (53701/288230376151711744), by norm_num⟩
  | 5 => ⟨((597245388007195/72057594037927936), (1632244023941/36028797018963968)), (188175/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491496032307999/36028797018963968), (4889187203755/18014398509481984)), (17669/2251799813685248), by norm_num⟩
  | 3 => ⟨((744534914331549/4503599627370496), (12196591130495/9007199254740992)), (177077/4503599627370496), by norm_num⟩
  | 2 => ⟨((34805298680729/70368744177664), (12157086134849/2251799813685248)), (177659/1125899906842624), by norm_num⟩
  | 1 => ⟨((2215407690955837/2251799813685248), (36274155718899/2251799813685248)), (535891/1125899906842624), by norm_num⟩
  | 0 => ⟨((544753464683657/562949953421312), (71762434698401/2251799813685248)), (1083481/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544753464683657/562949953421312), (71762434698401/2251799813685248)), (4133152012351607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526573401496281/562949953421312), (34721412355133/562949953421312)), (4331955/2251799813685248), by norm_num⟩
  | 2 => ⟨((1961623544043991/2251799813685248), (259822346160339/2251799813685248)), (4319219/1125899906842624), by norm_num⟩
  | 3 => ⟨((1678861173185917/2251799813685248), (452681120585713/2251799813685248)), (17043987/2251799813685248), by norm_num⟩
  | 4 => ⟨((580347912370373/1125899906842624), (675005613347009/2251799813685248)), (2016719/140737488355328), by norm_num⟩
  | 5 => ⟨((395942043383281/2251799813685248), (347933325301337/1125899906842624)), (105219841/4503599627370496), by norm_num⟩
  | 6 => ⟨((-145421583087593/2251799813685248), (978853846198655/9007199254740992)), (25508471/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-562104343/8388608)), (1/16777216), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1165002355/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((62574220290707/562949953421312), (-84201303707875/2251799813685248)), (87220513/4503599627370496), by norm_num⟩
  | 1 => ⟨((-593151459/2147483648), (399079093/4294967296)), (209/4294967296), by norm_num⟩
  | 2 => ⟨((368481501/1073741824), (-247918573/2147483648)), (131/2147483648), by norm_num⟩
  | 3 => ⟨((-76303511/268435456), (410703007/4294967296)), (219/4294967296), by norm_num⟩
  | 4 => ⟨((1516856815/8589934592), (-127569829/2147483648)), (275/8589934592), by norm_num⟩
  | 5 => ⟨((-753849517/8589934592), (253599293/8589934592)), (69/4294967296), by norm_num⟩
  | 6 => ⟨((312207613/8589934592), (-420113713/34359738368)), (231/34359738368), by norm_num⟩
  | 7 => ⟨((-886636313/68719476736), (298269531/68719476736)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((1101604235/274877906944), (-185292985/137438953472)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((-1216614973/1099511627776), (25579765/68719476736)), (29/137438953472), by norm_num⟩
  | 10 => ⟨((604634927/2199023255552), (-101701325/1099511627776)), (233/4398046511104), by norm_num⟩
  | 11 => ⟨((-273174791/4398046511104), (367590253/17592186044416)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((905085139/70368744177664), (-304475821/70368744177664)), (89/35184372088832), by norm_num⟩
  | 13 => ⟨((-1384032049/562949953421312), (465596303/562949953421312)), (137/281474976710656), by norm_num⟩
  | 14 => ⟨((61414115/140737488355328), (-330560957/2251799813685248)), (49/562949953421312), by norm_num⟩
  | 15 => ⟨((-651128929/9007199254740992), (438086997/18014398509481984)), (131/9007199254740992), by norm_num⟩
  | 16 => ⟨((808997303/72057594037927936), (-272151323/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-211357307123/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778663186005443/633825300114114700748351602688), (-125051030263/158456325028528675187087900672)), (92249/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236202891696549/4951760157141521099596496896), (-562624556313/39614081257132168796771975168)), (12973/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889390874621943/2475880078570760549798248448), (-149414484049/618970019642690137449562112)), (55137/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771057222505203/154742504910672534362390528), (-298755503379/77371252455336267181195264)), (55139/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549428406511033/9671406556917033397649408), (-560010507065/9671406556917033397649408)), (51695/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629339698257317/302231454903657293676544), (-244926594515/302231454903657293676544)), (90471/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471903662258417/18889465931478580854784), (-795719044773/75557863725914323419136)), (147023/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162175822125431/590295810358705651712), (-596533565869/4722366482869645213696)), (220549/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621265686271045/590295810358705651712), (-204954584759/147573952589676412928)), (303279/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823246996559041/73786976294838206464), (-512075175087/36893488147419103232)), (189567/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822401373290285/9223372036854775808), (-1151313750575/9223372036854775808)), (426575/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398412641421039/288230376151711744), (-1150245476081/1152921504606846976)), (106659/288230376151711744), by norm_num⟩
  | 5 => ⟨((298572037589781/36028797018963968), (-1005264311365/144115188075855872)), (2917/1125899906842624), by norm_num⟩
  | 4 => ⟨((745600010574429/18014398509481984), (-1505498824161/36028797018963968)), (280101/18014398509481984), by norm_num⟩
  | 3 => ⟨((744356820434275/4503599627370496), (-117355319291/562949953421312)), (43781/562949953421312), by norm_num⟩
  | 2 => ⟨((2226868032204567/4503599627370496), (-3742834712191/4503599627370496)), (10951/35184372088832), by norm_num⟩
  | 1 => ⟨((2214503646508171/2251799813685248), (-2791508609443/1125899906842624)), (526111/562949953421312), by norm_num⟩
  | 0 => ⟨((1088806103599203/1125899906842624), (-11041716565853/2251799813685248)), (4216379/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088806103599203/1125899906842624), (-11041716565853/2251799813685248)), (16084209450728606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105814636192879/2251799813685248), (-5338968552199/562949953421312)), (2049071/562949953421312), by norm_num⟩
  | 2 => ⟨((1922940629923/2199023255552), (-19971363441929/1125899906842624)), (7742649/1125899906842624), by norm_num⟩
  | 3 => ⟨((1721167542862777/2251799813685248), (-69856007389615/2251799813685248)), (13815833/1125899906842624), by norm_num⟩
  | 4 => ⟨((164176330798897/281474976710656), (-53394574358817/1125899906842624)), (5494379/281474976710656), by norm_num⟩
  | 5 => ⟨((1522021267925533/4503599627370496), (-124574133093339/2251799813685248)), (110888949/4503599627370496), by norm_num⟩
  | 6 => ⟨((62574220290707/562949953421312), (-84201303707875/2251799813685248)), (87220513/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1165002355/16777216)), (1/8388608), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1202528893/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-824457150934793/9007199254740992), (-540539629377397/9007199254740992)), (89355865/2251799813685248), by norm_num⟩
  | 1 => ⟨((1008363171/4294967296), (661114109/4294967296)), (55/536870912), by norm_num⟩
  | 2 => ⟨((-646600117/2147483648), (-847862105/4294967296)), (567/4294967296), by norm_num⟩
  | 3 => ⟨((552832185/2147483648), (724907787/4294967296)), (487/4294967296), by norm_num⟩
  | 4 => ⟨((-708993279/4294967296), (-464837941/4294967296)), (157/2147483648), by norm_num⟩
  | 5 => ⟨((363706371/4294967296), (476914311/8589934592)), (81/2147483648), by norm_num⟩
  | 6 => ⟨((-621925615/17179869184), (-815507371/34359738368)), (557/34359738368), by norm_num⟩
  | 7 => ⟨((911547261/68719476736), (298819301/34359738368)), (205/34359738368), by norm_num⟩
  | 8 => ⟨((-1169036281/274877906944), (-383228187/137438953472)), (33/17179869184), by norm_num⟩
  | 9 => ⟨((166584381/137438953472), (109217877/137438953472)), (303/549755813888), by norm_num⟩
  | 10 => ⟨((-341824401/1099511627776), (-224110659/1099511627776)), (313/2199023255552), by norm_num⟩
  | 11 => ⟨((637645293/8796093022208), (836119987/17592186044416)), (293/8796093022208), by norm_num⟩
  | 12 => ⟨((-1090351923/70368744177664), (-714868475/70368744177664)), (503/70368744177664), by norm_num⟩
  | 13 => ⟨((860522297/281474976710656), (564185057/281474976710656)), (399/281474976710656), by norm_num⟩
  | 14 => ⟨((-630627461/1125899906842624), (-826917771/2251799813685248)), (587/2251799813685248), by norm_num⟩
  | 15 => ⟨((431340667/4503599627370496), (141400147/2251799813685248)), (403/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1106366967/72057594037927936), (-725368433/72057594037927936)), (519/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-3336338996547/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889274283878173/316912650057057350374175801344), (-493435847445/79228162514264337593543950336)), (185177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889493750784249/39614081257132168796771975168), (-4440047484207/39614081257132168796771975168)), (104187/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472313207678801/618970019642690137449562112), (-2358241903557/1237940039285380274899124224)), (13841/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885459266318823/77371252455336267181195264), (-294705249383/9671406556917033397649408)), (221521/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387324424726295/2417851639229258349412352), (-4419304176421/9671406556917033397649408)), (207745/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629282171021315/302231454903657293676544), (-3865616861023/604462909807314587353088)), (90923/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943713200845219/37778931862957161709568), (-3139619337563/37778931862957161709568)), (295629/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648632134645167/2361183241434822606848), (-1176834862243/1180591620717411303424)), (55459/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621068191721549/590295810358705651712), (-6469197292271/590295810358705651712)), (38151/73786976294838206464), by norm_num⟩
  | 8 => ⟨((56968668748401/2305843009213693952), (-4040703416067/36893488147419103232)), (381787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227764603949755/1152921504606846976), (-567786706871/576460752303423488)), (107473/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593361351214745/1152921504606846976), (-9075847705587/1152921504606846976)), (430369/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194029843328135/144115188075855872), (-7931541038241/144115188075855872)), (188555/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490802103075939/36028797018963968), (-185588688085/562949953421312)), (141685/9007199254740992), by norm_num⟩
  | 3 => ⟨((46506187897225/281474976710656), (-3703192166819/2251799813685248)), (177577/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112891181989535/2251799813685248), (-3690337684227/562949953421312)), (178285/562949953421312), by norm_num⟩
  | 1 => ⟨((1106370045403659/1125899906842624), (-2751716545623/140737488355328)), (1076805/1125899906842624), by norm_num⟩
  | 0 => ⟨((33961729970619/35184372088832), (-21757899524501/562949953421312)), (1091047/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((33961729970619/35184372088832), (-21757899524501/562949953421312)), (4162014009715843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((523664248094447/562949953421312), (-42003643351277/562949953421312)), (2190605/562949953421312), by norm_num⟩
  | 2 => ⟨((1935944302129693/2251799813685248), (-312579207854551/2251799813685248)), (17609451/2251799813685248), by norm_num⟩
  | 3 => ⟨((1621003144942821/2251799813685248), (-268734339852297/1125899906842624)), (35167661/2251799813685248), by norm_num⟩
  | 4 => ⟨((1038626346817003/2251799813685248), (-193453790788703/562949953421312)), (67420209/2251799813685248), by norm_num⟩
  | 5 => ⟨((426285479426025/4503599627370496), (-1427666546794423/4503599627370496)), (217062259/4503599627370496), by norm_num⟩
  | 6 => ⟨((-824457150934793/9007199254740992), (-540539629377397/9007199254740992)), (89355865/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1202528893/16777216)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1237273039/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-148194782118167/18014398509481984), (921840711038971/9007199254740992)), (610616871/18014398509481984), by norm_num⟩
  | 1 => ⟨((93244201/4294967296), (-1160044901/4294967296)), (193/2147483648), by norm_num⟩
  | 2 => ⟨((-30759599/1073741824), (1530712499/4294967296)), (511/4294967296), by norm_num⟩
  | 3 => ⟨((108235127/4294967296), (-1346546013/4294967296)), (451/4294967296), by norm_num⟩
  | 4 => ⟨((-142819353/8589934592), (888403031/4294967296)), (299/4294967296), by norm_num⟩
  | 5 => ⟨((18845423/2147483648), (-234454653/2147483648)), (633/17179869184), by norm_num⟩
  | 6 => ⟨((-33156101/8589934592), (1649971387/34359738368)), (35/2147483648), by norm_num⟩
  | 7 => ⟨((100000973/68719476736), (-311026363/17179869184)), (53/8589934592), by norm_num⟩
  | 8 => ⟨((-65977075/137438953472), (820816403/137438953472)), (281/137438953472), by norm_num⟩
  | 9 => ⟨((154770919/1099511627776), (-962747353/549755813888)), (331/549755813888), by norm_num⟩
  | 10 => ⟨((-40844933/1099511627776), (1016298183/2199023255552)), (351/2199023255552), by norm_num⟩
  | 11 => ⟨((78394269/8796093022208), (-1950595759/17592186044416)), (169/4398046511104), by norm_num⟩
  | 12 => ⟨((-137924647/70368744177664), (1715911345/70368744177664)), (597/70368744177664), by norm_num⟩
  | 13 => ⟨((55998623/140737488355328), (-174168785/35184372088832)), (487/281474976710656), by norm_num⟩
  | 14 => ⟨((-42223879/562949953421312), (525304467/562949953421312)), (369/1125899906842624), by norm_num⟩
  | 15 => ⟨((59429993/4503599627370496), (-1478729177/9007199254740992)), (261/4503599627370496), by norm_num⟩
  | 16 => ⟨((-156839159/72057594037927936), (30487899/1125899906842624)), (691/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (2150616663097/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778454938414307/633825300114114700748351602688), (2544296339053/633825300114114700748351602688)), (184901/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944694356633141/19807040628566084398385987584), (1430881055111/19807040628566084398385987584)), (104023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944570806756663/1237940039285380274899124224), (3039915881707/2475880078570760549798248448)), (110543/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770807748405057/154742504910672534362390528), (3039121473605/154742504910672534362390528)), (27641/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774597149210377/4835703278458516698824704), (1424166282865/4835703278458516698824704)), (25919/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258474326019235/604462909807314587353088), (1245723726181/302231454903657293676544)), (90739/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887280986320697/75557863725914323419136), (4047021047845/75557863725914323419136)), (36873/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297155960140505/4722366482869645213696), (758470734119/1180591620717411303424)), (1729/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1620920487928571/590295810358705651712), (4169342994597/590295810358705651712)), (152211/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822814599821799/73786976294838206464), (5208311580569/73786976294838206464)), (380707/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821913693410945/9223372036854775808), (731840471083/1152921504606846976)), (428541/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796580673665931/576460752303423488), (1462236237671/288230376151711744)), (26803/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193858358275165/144115188075855872), (5111332025777/144115188075855872)), (375589/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490551892840629/36028797018963968), (7654024325003/36028797018963968)), (564077/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487897486809861/9007199254740992), (1193107768271/1125899906842624)), (706311/9007199254740992), by norm_num⟩
  | 2 => ⟨((556304462337601/1125899906842624), (9510931151813/2251799813685248)), (708137/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105992028017201/1125899906842624), (7090909379295/562949953421312)), (2133565/2251799813685248), by norm_num⟩
  | 0 => ⟨((543099493666401/562949953421312), (3503352474237/140737488355328)), (2151947/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543099493666401/562949953421312), (3503352474237/140737488355328)), (8209026340964889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2094400630623463/2251799813685248), (108154208356441/2251799813685248)), (4259269/1125899906842624), by norm_num⟩
  | 2 => ⟨((971404438836643/1125899906842624), (12574288398643/140737488355328)), (8332245/1125899906842624), by norm_num⟩
  | 3 => ⟨((1658242199824879/2251799813685248), (173581605134443/1125899906842624)), (31733395/2251799813685248), by norm_num⟩
  | 4 => ⟨((145952411196629/281474976710656), (511307161494429/2251799813685248)), (28261093/1125899906842624), by norm_num⟩
  | 5 => ⟨((7645965749339/35184372088832), (1060506535313495/4503599627370496)), (21071277/562949953421312), by norm_num⟩
  | 6 => ⟨((-148194782118167/18014398509481984), (921840711038971/9007199254740992)), (610616871/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1237273039/16777216)), (1/8388608), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1269619067/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1676354090038447/18014398509481984), (-476547930847515/18014398509481984)), (138812103/9007199254740992), by norm_num⟩
  | 1 => ⟨((-270584287/1073741824), (76920731/1073741824)), (181/4294967296), by norm_num⟩
  | 2 => ⟨((1465511665/4294967296), (-208305201/2147483648)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((-1322893053/4294967296), (188033647/2147483648)), (225/4294967296), by norm_num⟩
  | 4 => ⟨((895615199/4294967296), (-127301139/2147483648)), (77/2147483648), by norm_num⟩
  | 5 => ⟨((-60634273/536870912), (68947575/2147483648)), (21/1073741824), by norm_num⟩
  | 6 => ⟨((218934207/4294967296), (-124475663/8589934592)), (77/8589934592), by norm_num⟩
  | 7 => ⟨((-677582655/34359738368), (6019399/1073741824)), (15/4294967296), by norm_num⟩
  | 8 => ⟨((458731961/68719476736), (-260813355/137438953472)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((-552119635/274877906944), (313909181/549755813888)), (201/549755813888), by norm_num⟩
  | 10 => ⟨((1196134151/2199023255552), (-42504091/274877906944)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((-294471939/2199023255552), (83711427/2199023255552)), (219/8796093022208), by norm_num⟩
  | 12 => ⟨((1063259725/35184372088832), (-151129831/17592186044416)), (25/4398046511104), by norm_num⟩
  | 13 => ⟨((-442978571/70368744177664), (251856719/140737488355328)), (21/17592186044416), by norm_num⟩
  | 14 => ⟨((1370980809/1125899906842624), (-97434377/281474976710656)), (131/562949953421312), by norm_num⟩
  | 15 => ⟨((-990049295/4503599627370496), (281447663/4503599627370496)), (191/4503599627370496), by norm_num⟩
  | 16 => ⟨((335137899/9007199254740992), (-11908975/1125899906842624)), (65/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-360784091521/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778366609905065/633825300114114700748351602688), (-213392623691/316912650057057350374175801344)), (46121/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889289552495187/39614081257132168796771975168), (-480036141771/39614081257132168796771975168)), (103775/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((29516195755499/38685626227668133590597632), (-254958465289/1237940039285380274899124224)), (220529/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770702970272989/154742504910672534362390528), (-31861271027/9671406556917033397649408)), (27567/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193637049365471/1208925819614629174706176), (-477773985689/9671406556917033397649408)), (25845/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258388986217139/604462909807314587353088), (-417907215791/604462909807314587353088)), (90461/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235892864927475/9444732965739290427392), (-169706858313/18889465931478580854784)), (294013/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648526471719857/2361183241434822606848), (-508882879771/4722366482869645213696)), (110261/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202597463236413/73786976294838206464), (-349663967939/295147905179352825856)), (303239/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822639919468117/73786976294838206464), (-109197660979/9223372036854775808)), (189539/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910859479449627/4611686018427387904), (-981983985271/9223372036854775808)), (426505/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592968834801939/1152921504606846976), (-122623907895/144115188075855872)), (213279/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193692403875987/144115188075855872), (-428625946047/72057594037927936)), (186649/72057594037927936), by norm_num⟩
  | 4 => ⟨((745153967616553/18014398509481984), (-1283650280385/36028797018963968)), (560067/36028797018963968), by norm_num⟩
  | 3 => ⟨((743800606271483/4503599627370496), (-100042011973/562949953421312)), (700293/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224651192413939/4503599627370496), (-3189702614365/4503599627370496)), (700611/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211198357937199/2251799813685248), (-4755554955019/2251799813685248)), (2103441/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085540544856581/1125899906842624), (-9395744601791/2251799813685248)), (2106703/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085540544856581/1125899906842624), (-9395744601791/2251799813685248)), (8036434177878951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((261652078786449/281474976710656), (-18117883574507/2251799813685248)), (254997/70368744177664), by norm_num⟩
  | 2 => ⟨((243206988083337/281474976710656), (-33683860326623/2251799813685248)), (7650897/1125899906842624), by norm_num⟩
  | 3 => ⟨((210078748670177/281474976710656), (-58208728269859/2251799813685248)), (6725165/562949953421312), by norm_num⟩
  | 4 => ⟨((1252832906348437/2251799813685248), (-86888127246811/2251799813685248)), (20772677/1125899906842624), by norm_num⟩
  | 5 => ⟨((693685440011033/2251799813685248), (-193367641873357/4503599627370496)), (6179411/281474976710656), by norm_num⟩
  | 6 => ⟨((1676354090038447/18014398509481984), (-476547930847515/18014398509481984)), (138812103/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1269619067/16777216)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile043Terms1
