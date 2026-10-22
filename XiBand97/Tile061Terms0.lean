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
namespace Reinmann.XiBand97.Tile061Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨61,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79951/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79951/2560))
  have he : value ((69/80), (79951/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/4294967296), (-23243914313/1073741824)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1166108840549073/2251799813685248), (-417180902517223/2251799813685248)), (831195/1125899906842624), by norm_num⟩
  | 1 => ⟨((98667609259/274877906944), (35298799605/274877906944)), (143/274877906944), by norm_num⟩
  | 2 => ⟨((-34195587585/274877906944), (-24467263423/549755813888)), (101/549755813888), by norm_num⟩
  | 3 => ⟨((3950429187/137438953472), (22612552877/2199023255552)), (95/2199023255552), by norm_num⟩
  | 4 => ⟨((-87623323295/17592186044416), (-1959228409/1099511627776)), (67/8796093022208), by norm_num⟩
  | 5 => ⟨((97177375189/140737488355328), (34765661383/140737488355328)), (151/140737488355328), by norm_num⟩
  | 6 => ⟨((-89810964835/1125899906842624), (-32130293557/1125899906842624)), (71/562949953421312), by norm_num⟩
  | 7 => ⟨((17786347731/2251799813685248), (25452597017/9007199254740992)), (57/4503599627370496), by norm_num⟩
  | 8 => ⟨((-98628454257/144115188075855872), (-4410598965/18014398509481984)), (161/144115188075855872), by norm_num⟩
  | 9 => ⟨((60768031103/1152921504606846976), (21740047909/1152921504606846976)), (101/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-67393903083/18446744073709551616), (-24110484661/18446744073709551616)), (57/9223372036854775808), by norm_num⟩
  | 11 => ⟨((67947482049/295147905179352825856), (12154265065/147573952589676412928)), (117/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-31398403739/2361183241434822606848), (-5616463041/1180591620717411303424)), (55/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((26786110801/37778931862957161709568), (19165713337/75557863725914323419136)), (95/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-42438210697/1208925819614629174706176), (-30364937515/2417851639229258349412352)), (153/2417851639229258349412352), by norm_num⟩
  | 15 => ⟨((3922123479/2417851639229258349412352), (22450528881/38685626227668133590597632)), (115/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-86995482601/1237940039285380274899124224), (-3890380199/154742504910672534362390528)), (81/618970019642690137449562112), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-455592690939/1267650600228229401496703205376)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((890519232422571/316912650057057350374175801344), (-4323874762659/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892294399978409/39614081257132168796771975168), (-4864069634773/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473056992410197/618970019642690137449562112), (-645969406455/309485009821345068724781056)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886946525743637/77371252455336267181195264), (-5167396434193/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48502676602611/302231454903657293676544), (-1211013174241/2417851639229258349412352)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261003141091447/604462909807314587353088), (-2119082203163/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891388213483157/75557863725914323419136), (-6886300949113/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325058636387347/1180591620717411303424), (-2582049255117/2361183241434822606848)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812575280714105/295147905179352825856), (-3549807640211/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457024430050511/18446744073709551616), (-8872987149857/73786976294838206464)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827851056613443/9223372036854775808), (-9980001360663/9223372036854775808)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799545514064021/576460752303423488), (-9977360759211/1152921504606846976)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((599519094254765/72057594037927936), (-8727214324263/144115188075855872)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498304362909749/36028797018963968), (-13084854664063/36028797018963968)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497557855429557/9007199254740992), (-8172797307903/4503599627370496)), (695/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122223990606227/2251799813685248), (-4082455151563/562949953421312)), (349/281474976710656), by norm_num⟩
  | 1 => ⟨((1120301461282871/1125899906842624), (-12227537178839/562949953421312)), (4217/1125899906842624), by norm_num⟩
  | 0 => ⟨((139295718158705/140737488355328), (-24375098696763/562949953421312)), (4277/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139295718158705/140737488355328), (-24375098696763/562949953421312)), (16315462352561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1100838915565963/1125899906842624), (-24125390596587/281474976710656)), (17675/1125899906842624), by norm_num⟩
  | 2 => ⟨((267016135087381/281474976710656), (-188707139315285/1125899906842624)), (18797/562949953421312), by norm_num⟩
  | 3 => ⟨((122696461648917/140737488355328), (-358027215010021/1125899906842624)), (83929/1125899906842624), by norm_num⟩
  | 4 => ⟨((370947495914231/562949953421312), (-624263982100297/1125899906842624)), (199719/1125899906842624), by norm_num⟩
  | 5 => ⟨((17841579275361/140737488355328), (-1645397851387653/2251799813685248)), (969351/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1166108840549073/2251799813685248), (-417180902517223/2251799813685248)), (831195/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-23243914313/1073741824)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1017427393/1073741824), (-73681465113/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-1693040351832495/4503599627370496), (-426741897894895/4503599627370496)), (4623939/4503599627370496), by norm_num⟩
  | 1 => ⟨((56762540763/137438953472), (14307369785/137438953472)), (157/137438953472), by norm_num⟩
  | 2 => ⟨((-31180012409/137438953472), (-1964781533/34359738368)), (175/274877906944), by norm_num⟩
  | 3 => ⟨((22836496529/274877906944), (11512176729/549755813888)), (259/1099511627776), by norm_num⟩
  | 4 => ⟨((-25088455717/1099511627776), (-1580927353/274877906944)), (9/137438953472), by norm_num⟩
  | 5 => ⟨((44099977207/8796093022208), (694730487/549755813888)), (255/17592186044416), by norm_num⟩
  | 6 => ⟨((-32299184593/35184372088832), (-16282441607/70368744177664)), (189/70368744177664), by norm_num⟩
  | 7 => ⟨((40553464123/281474976710656), (10221765965/281474976710656)), (15/35184372088832), by norm_num⟩
  | 8 => ⟨((-89105068067/4503599627370496), (-11229757701/2251799813685248)), (133/2251799813685248), by norm_num⟩
  | 9 => ⟨((43507521227/18014398509481984), (5483177693/9007199254740992)), (131/18014398509481984), by norm_num⟩
  | 10 => ⟨((-76476635951/288230376151711744), (-9638218231/144115188075855872)), (233/288230376151711744), by norm_num⟩
  | 11 => ⟨((61104125129/2305843009213693952), (7700847265/1152921504606846976)), (47/576460752303423488), by norm_num⟩
  | 12 => ⟨((-89506323673/36893488147419103232), (-22560654503/36893488147419103232)), (139/18446744073709551616), by norm_num⟩
  | 13 => ⟨((30256229877/147573952589676412928), (15252561401/295147905179352825856)), (95/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-75976836461/4722366482869645213696), (-9575229365/2361183241434822606848)), (15/295147905179352825856), by norm_num⟩
  | 15 => ⟨((2782302873/2361183241434822606848), (22441524581/75557863725914323419136)), (71/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-48906754033/604462909807314587353088), (-24654534681/1208925819614629174706176)), (315/1208925819614629174706176), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (-942660764543/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780497497377463/633825300114114700748351602688), (-4470660341511/633825300114114700748351602688)), (1449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945842911077703/19807040628566084398385987584), (-314314768491/2475880078570760549798248448)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472895339044447/618970019642690137449562112), (-2671415344153/1237940039285380274899124224)), (433/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886623219333693/77371252455336267181195264), (-5342245012175/154742504910672534362390528)), (1733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551479452553117/9671406556917033397649408), (-5007732230683/9671406556917033397649408)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315118179527101/151115727451828646838272), (-2190571511501/302231454903657293676544)), (1423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890526278085027/75557863725914323419136), (-3559094721165/37778931862957161709568)), (2313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324897023989189/1180591620717411303424), (-5337619661133/4722366482869645213696)), (1735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624261696885931/590295810358705651712), (-7337564763595/590295810358705651712)), (2387/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826986645816199/73786976294838206464), (-9169461085769/73786976294838206464)), (2987/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913300553956827/4611686018427387904), (-644513181417/576460752303423488)), (841/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399460273476629/288230376151711744), (-322122385097/36028797018963968)), (421/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197944515098789/144115188075855872), (-9014590499965/144115188075855872)), (2951/144115188075855872), by norm_num⟩
  | 4 => ⟨((748331948858121/18014398509481984), (-13512201009093/36028797018963968)), (4437/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495507367962033/9007199254740992), (-16873275643161/9007199254740992)), (5561/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120173674951931/2251799813685248), (-16847757754513/2251799813685248)), (5587/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117226524859099/1125899906842624), (-25207652114749/1125899906842624)), (4221/562949953421312), by norm_num⟩
  | 0 => ⟨((554109332121797/562949953421312), (-25079116971373/562949953421312)), (4283/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554109332121797/562949953421312), (-25079116971373/562949953421312)), (16338349462413699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1088580567328279/1125899906842624), (-98741088231775/1125899906842624)), (17627/562949953421312), by norm_num⟩
  | 2 => ⟨((1043838659117891/1125899906842624), (-190936386427789/1125899906842624)), (18589/281474976710656), by norm_num⟩
  | 3 => ⟨((935378390393757/1125899906842624), (-177019982304215/562949953421312)), (163093/1125899906842624), by norm_num⟩
  | 4 => ⟨((332884136556045/562949953421312), (-147065174363135/281474976710656)), (46695/140737488355328), by norm_num⟩
  | 5 => ⟨((172656103308287/2251799813685248), (-695701822697521/1125899906842624)), (52009/70368744177664), by norm_num⟩
  | 6 => ⟨((-1693040351832495/4503599627370496), (-426741897894895/4503599627370496)), (4623939/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-73681465113/2147483648)), (1/1073741824), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-2567700857/2147483648), (-23243914313/536870912)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((131646906995811/562949953421312), (864159123874085/4503599627370496)), (2247983/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5569499659/17179869184), (-9139853825/34359738368)), (97/137438953472), by norm_num⟩
  | 2 => ⟨((15441931943/68719476736), (12670527819/68719476736)), (17/34359738368), by norm_num⟩
  | 3 => ⟨((-28542750903/274877906944), (-23420108357/274877906944)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((9892163657/274877906944), (4058395519/137438953472)), (45/549755813888), by norm_num⟩
  | 5 => ⟨((-21941521115/2199023255552), (-9001809317/1099511627776)), (51/2199023255552), by norm_num⟩
  | 6 => ⟨((40556542661/17592186044416), (33277753323/17592186044416)), (3/549755813888), by norm_num⟩
  | 7 => ⟨((-64255207311/140737488355328), (-52723156323/140737488355328)), (77/70368744177664), by norm_num⟩
  | 8 => ⟨((5567289473/70368744177664), (36544907155/562949953421312)), (109/562949953421312), by norm_num⟩
  | 9 => ⟨((-54882858689/4503599627370496), (-11258221937/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 10 => ⟨((30433519009/18014398509481984), (6242883835/4503599627370496)), (153/36028797018963968), by norm_num⟩
  | 11 => ⟨((-61367004787/288230376151711744), (-50353307099/288230376151711744)), (39/72057594037927936), by norm_num⟩
  | 12 => ⟨((28357577565/1152921504606846976), (23268168565/1152921504606846976)), (73/1152921504606846976), by norm_num⟩
  | 13 => ⟨((-24191969153/9223372036854775808), (-39700345693/18446744073709551616)), (127/18446744073709551616), by norm_num⟩
  | 14 => ⟨((4791027203/18446744073709551616), (31449351639/147573952589676412928)), (51/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-14169117857/590295810358705651712), (-23252298047/1180591620717411303424)), (153/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((19642568187/9444732965739290427392), (16117264833/9444732965739290427392)), (27/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (895067328863/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445031104631319/158456325028528675187087900672), (1060802193049/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29551042981603/618970019642690137449562112), (1193275083957/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945568443005727/1237940039285380274899124224), (1267700043657/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886401430287569/77371252455336267181195264), (633762999007/77371252455336267181195264)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551064545654417/9671406556917033397649408), (1188120729777/9671406556917033397649408)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630055310917951/302231454903657293676544), (259855194773/151115727451828646838272)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889939647126631/75557863725914323419136), (844356113275/37778931862957161709568)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299149675651379/4722366482869645213696), (1266231019877/4722366482869645213696)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623661391258611/590295810358705651712), (1740575168503/590295810358705651712)), (2373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826240045134837/73786976294838206464), (271872558879/9223372036854775808)), (2967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912883189058169/4611686018427387904), (1222918995169/4611686018427387904)), (1669/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798506426991331/576460752303423488), (152785610381/72057594037927936)), (3339/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197227099274143/144115188075855872), (1068786291829/72057594037927936)), (2923/144115188075855872), by norm_num⟩
  | 4 => ⟨((747801172345475/18014398509481984), (800877231903/9007199254740992)), (4385/36028797018963968), by norm_num⟩
  | 3 => ⟨((373551471503661/2251799813685248), (3999403192781/9007199254740992)), (2743/4503599627370496), by norm_num⟩
  | 2 => ⟨((559455151562879/1125899906842624), (7983875239647/4503599627370496)), (10983/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230852932169265/2251799813685248), (11938547072195/2251799813685248)), (16503/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209993764960149/2251799813685248), (23728402960743/2251799813685248)), (8281/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209993764960149/2251799813685248), (23728402960743/2251799813685248)), (31589510204124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2168713832542431/2251799813685248), (46575741126723/2251799813685248)), (65717/2251799813685248), by norm_num⟩
  | 2 => ⟨((521932540276035/562949953421312), (44857208633093/1125899906842624)), (16163/281474976710656), by norm_num⟩
  | 3 => ⟨((1932040549287753/2251799813685248), (166355369313197/2251799813685248)), (125035/1125899906842624), by norm_num⟩
  | 4 => ⟨((1645397851387639/2251799813685248), (71366317101437/562949953421312)), (466069/2251799813685248), by norm_num⟩
  | 5 => ⟨((291527210137265/562949953421312), (417180902517179/2251799813685248)), (399643/1125899906842624), by norm_num⟩
  | 6 => ⟨((131646906995811/562949953421312), (864159123874085/4503599627370496)), (2247983/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-23243914313/536870912)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-53970697679/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((140477820631185/562949953421312), (1520916348665/4503599627370496)), (535611/2251799813685248), by norm_num⟩
  | 1 => ⟨((-110395669131/274877906944), (-149403103/274877906944)), (107/274877906944), by norm_num⟩
  | 2 => ⟨((44418743817/137438953472), (120227509/274877906944)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-11914868387/68719476736), (-128999141/549755813888)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((76704963615/1099511627776), (51904027/549755813888)), (79/1099511627776), by norm_num⟩
  | 5 => ⟨((-98761501211/4398046511104), (-66829047/2199023255552)), (13/549755813888), by norm_num⟩
  | 6 => ⟨((26491750723/4398046511104), (143409603/17592186044416)), (57/8796093022208), by norm_num⟩
  | 7 => ⟨((-97455606813/70368744177664), (-131890773/70368744177664)), (107/70368744177664), by norm_num⟩
  | 8 => ⟨((4901523387/17592186044416), (106135005/281474976710656)), (11/35184372088832), by norm_num⟩
  | 9 => ⟨((-28048702463/562949953421312), (-37959489/562949953421312)), (1/17592186044416), by norm_num⟩
  | 10 => ⟨((36114116111/4503599627370496), (97749505/9007199254740992)), (21/2251799813685248), by norm_num⟩
  | 11 => ⟨((-84543167481/72057594037927936), (-114415825/72057594037927936)), (25/18014398509481984), by norm_num⟩
  | 12 => ⟨((90711319321/576460752303423488), (30690861/144115188075855872)), (109/576460752303423488), by norm_num⟩
  | 13 => ⟨((-89842607017/4611686018427387904), (-121587779/4611686018427387904)), (109/4611686018427387904), by norm_num⟩
  | 14 => ⟨((82626341649/36893488147419103232), (13977713/4611686018427387904)), (51/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-70923715635/295147905179352825856), (-5999003/18446744073709551616)), (89/295147905179352825856), by norm_num⟩
  | 16 => ⟨((57073658417/2361183241434822606848), (77240183/2361183241434822606848)), (145/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (881439031/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827942686513/633825300114114700748351602688), (522159541/158456325028528675187087900672)), (1441/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472733322318935/9903520314283042199192993792), (587357233/9903520314283042199192993792)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890782674238283/2475880078570760549798248448), (2495914707/2475880078570760549798248448)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772448751280303/154742504910672534362390528), (1247758537/77371252455336267181195264)), (1723/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732677043261/9671406556917033397649408), (2339124861/9671406556917033397649408)), (1615/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259820345619601/604462909807314587353088), (2046311959/604462909807314587353088)), (1413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889468152236909/75557863725914323419136), (3324465345/75557863725914323419136)), (287/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649398116438907/2361183241434822606848), (311582073/590295810358705651712)), (861/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811587848599141/295147905179352825856), (1713139007/295147905179352825856)), (37/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1825633361950677/73786976294838206464), (2140580519/36893488147419103232)), (185/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1825084456434391/9223372036854775808), (4813988399/9223372036854775808)), (1665/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399082919461191/288230376151711744), (1202773225/288230376151711744)), (1665/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196631908091915/144115188075855872), (4206451203/144115188075855872)), (1457/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494711231799673/36028797018963968), (3151586255/18014398509481984)), (2185/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493094919710699/9007199254740992), (983449541/1125899906842624)), (5463/9007199254740992), by norm_num⟩
  | 2 => ⟨((17465683048159/35184372088832), (15701137489/4503599627370496)), (2731/1125899906842624), by norm_num⟩
  | 1 => ⟨((69611093648899/70368744177664), (11733376345/1125899906842624)), (8193/1125899906842624), by norm_num⟩
  | 0 => ⟨((2203484834469255/2251799813685248), (46594795181/2251799813685248)), (32773/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203484834469255/2251799813685248), (46594795181/2251799813685248)), (125019082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156206508259173/2251799813685248), (91190099513/2251799813685248)), (32071/1125899906842624), by norm_num⟩
  | 2 => ⟨((2064671321885739/2251799813685248), (87318901469/1125899906842624)), (122845/2251799813685248), by norm_num⟩
  | 3 => ⟨((1893093520574781/2251799813685248), (320250193869/2251799813685248)), (225293/2251799813685248), by norm_num⟩
  | 4 => ⟨((1591528231462483/2251799813685248), (538470216839/2251799813685248)), (189437/1125899906842624), by norm_num⟩
  | 5 => ⟨((1124861013931133/2251799813685248), (1522321028171/4503599627370496)), (535743/2251799813685248), by norm_num⟩
  | 6 => ⟨((140477820631185/562949953421312), (1520916348665/4503599627370496)), (535611/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-53970697679/1073741824)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1659352607/1073741824), (-120169293739/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((797691136252019/4503599627370496), (534653033856207/4503599627370496)), (1495247/4503599627370496), by norm_num⟩
  | 1 => ⟨((-10904469657/34359738368), (-29234913213/137438953472)), (83/137438953472), by norm_num⟩
  | 2 => ⟨((78152747059/274877906944), (52381932581/274877906944)), (151/274877906944), by norm_num⟩
  | 3 => ⟨((-46676974863/274877906944), (-31285274573/274877906944)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((41816955853/549755813888), (14013921741/274877906944)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((-59940741299/2199023255552), (-40175323169/2199023255552)), (61/1099511627776), by norm_num⟩
  | 6 => ⟨((71599593877/8796093022208), (47989677145/8796093022208)), (37/2199023255552), by norm_num⟩
  | 7 => ⟨((-73308143041/35184372088832), (-6141854175/4398046511104)), (153/35184372088832), by norm_num⟩
  | 8 => ⟨((65675279733/140737488355328), (44018901507/140737488355328)), (139/140737488355328), by norm_num⟩
  | 9 => ⟨((-52299690825/562949953421312), (-17526951911/281474976710656)), (7/35184372088832), by norm_num⟩
  | 10 => ⟨((74966773019/4503599627370496), (50246531285/4503599627370496)), (163/4503599627370496), by norm_num⟩
  | 11 => ⟨((-12211129585/4503599627370496), (-16369036041/9007199254740992)), (27/4503599627370496), by norm_num⟩
  | 12 => ⟨((911641961/2251799813685248), (39105833771/144115188075855872)), (131/144115188075855872), by norm_num⟩
  | 13 => ⟨((-64332528883/1152921504606846976), (-21559460911/576460752303423488)), (73/576460752303423488), by norm_num⟩
  | 14 => ⟨((65867667317/9223372036854775808), (5518481177/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-62943475537/73786976294838206464), (-10546976965/18446744073709551616)), (147/73786976294838206464), by norm_num⟩
  | 16 => ⟨((1762180755/18446744073709551616), (37795291697/590295810358705651712)), (67/295147905179352825856), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (384582899101/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896209994613/158456325028528675187087900672), (455531388885/316912650057057350374175801344)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659808430713/39614081257132168796771975168), (512402762159/19807040628566084398385987584)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236311513945605/309485009821345068724781056), (1088684178717/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886079100340463/77371252455336267181195264), (1088491074031/154742504910672534362390528)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460298691873/9671406556917033397649408), (15941488349/151115727451828646838272)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259582027405353/604462909807314587353088), (223129567977/151115727451828646838272)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889080909236117/75557863725914323419136), (1449957785359/75557863725914323419136)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298505821728725/4722366482869645213696), (1087132093629/4722366482869645213696)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622776416188791/590295810358705651712), (747130218349/295147905179352825856)), (593/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825134312223001/73786976294838206464), (933503309709/36893488147419103232)), (1483/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824523096436971/9223372036854775808), (2099257010305/9223372036854775808)), (3337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797885203329993/576460752303423488), (2097851095139/1152921504606846976)), (3337/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196140895897729/144115188075855872), (229254907949/18014398509481984)), (1461/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493974914138145/36028797018963968), (2747901028465/36028797018963968)), (137/1125899906842624), by norm_num⟩
  | 3 => ⟨((1492174874734043/9007199254740992), (857339203071/2251799813685248)), (2741/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233768400492001/4503599627370496), (1710545586809/1125899906842624)), (5487/2251799813685248), by norm_num⟩
  | 1 => ⟨((69524972401027/70368744177664), (2555510044863/562949953421312)), (16487/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197983815706679/2251799813685248), (20279714930225/2251799813685248)), (33075/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197983815706679/2251799813685248), (20279714930225/2251799813685248)), (126171120650481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((536317833174187/562949953421312), (4948761978405/281474976710656)), (32583/1125899906842624), by norm_num⟩
  | 2 => ⟨((2043086462323483/2251799813685248), (37717161676951/1125899906842624)), (126459/2251799813685248), by norm_num⟩
  | 3 => ⟨((925595590259759/1125899906842624), (68442516027507/1125899906842624)), (118975/1125899906842624), by norm_num⟩
  | 4 => ⟨((1513532088474065/2251799813685248), (225064734924783/2251799813685248)), (420165/2251799813685248), by norm_num⟩
  | 5 => ⟨((497407725660071/1125899906842624), (37818936681485/281474976710656)), (648813/2251799813685248), by norm_num⟩
  | 6 => ⟨((797691136252019/4503599627370496), (534653033856207/4503599627370496)), (1495247/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-120169293739/2147483648)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-130507834509/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-24665238097493/281474976710656), (742363307999229/4503599627370496)), (2327405/4503599627370496), by norm_num⟩
  | 1 => ⟨((46871422991/274877906944), (-88169695759/274877906944)), (139/137438953472), by norm_num⟩
  | 2 => ⟨((-45603788849/274877906944), (21446288227/68719476736)), (17/17179869184), by norm_num⟩
  | 3 => ⟨((7395072963/68719476736), (-27821699947/137438953472)), (89/137438953472), by norm_num⟩
  | 4 => ⟨((-28780295063/549755813888), (54138528291/549755813888)), (175/549755813888), by norm_num⟩
  | 5 => ⟨((44803094605/2199023255552), (-84278969325/2199023255552)), (137/1099511627776), by norm_num⟩
  | 6 => ⟨((-29060932167/4398046511104), (427081515/34359738368)), (179/4398046511104), by norm_num⟩
  | 7 => ⟨((32314264483/17592186044416), (-30393133879/8796093022208)), (201/17592186044416), by norm_num⟩
  | 8 => ⟨((-3930040951/8796093022208), (59142307677/70368744177664)), (197/70368744177664), by norm_num⟩
  | 9 => ⟨((27191134481/281474976710656), (-51149162999/281474976710656)), (43/70368744177664), by norm_num⟩
  | 10 => ⟨((-42329203641/2251799813685248), (19906335079/562949953421312)), (135/1125899906842624), by norm_num⟩
  | 11 => ⟨((29952300715/9007199254740992), (-28171592335/4503599627370496)), (3/140737488355328), by norm_num⟩
  | 12 => ⟨((-19428161983/36028797018963968), (36546258293/36028797018963968)), (251/72057594037927936), by norm_num⟩
  | 13 => ⟨((46529793945/576460752303423488), (-43763529183/288230376151711744)), (303/576460752303423488), by norm_num⟩
  | 14 => ⟨((-25869370935/2305843009213693952), (48662797483/2305843009213693952)), (85/1152921504606846976), by norm_num⟩
  | 15 => ⟨((6711929527/4611686018427387904), (-12625790867/4611686018427387904)), (89/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-26121623573/147573952589676412928), (6142163647/18446744073709551616)), (175/147573952589676412928), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (1341303678431/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779374772082773/633825300114114700748351602688), (3176802589085/633825300114114700748351602688)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472605807470943/9903520314283042199192993792), (3573364078807/39614081257132168796771975168)), (1627/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118140026417089/154742504910672534362390528), (3796048050249/2475880078570760549798248448)), (865/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442976536828895/38685626227668133590597632), (948828854479/38685626227668133590597632)), (865/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550223611622481/9671406556917033397649408), (3557329883033/9671406556917033397649408)), (811/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629687269710577/302231454903657293676544), (3111885439445/604462909807314587353088)), (355/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((118046438532897/4722366482869645213696), (5055354939029/75557863725914323419136)), (577/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298251768564383/4722366482869645213696), (947559976781/1180591620717411303424)), (433/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811213032197185/295147905179352825856), (325594146275/36893488147419103232)), (1191/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824694831116373/73786976294838206464), (6508773417239/73786976294838206464)), (2979/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824026563539739/9223372036854775808), (3659047902167/4611686018427387904)), (1677/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595271232028351/1152921504606846976), (3656377434361/576460752303423488)), (3357/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195701151750143/144115188075855872), (6392654609195/144115188075855872)), (735/36028797018963968), by norm_num⟩
  | 4 => ⟨((186663672403465/4503599627370496), (4788488373567/18014398509481984)), (4417/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491332629850717/9007199254740992), (186722294349/140737488355328)), (5533/9007199254740992), by norm_num⟩
  | 2 => ⟨((139503316101611/281474976710656), (11918765629057/2251799813685248)), (5551/2251799813685248), by norm_num⟩
  | 1 => ⟨((555537352146479/562949953421312), (4449900094405/281474976710656)), (4185/562949953421312), by norm_num⟩
  | 0 => ⟨((274047531103611/281474976710656), (17642819864655/562949953421312)), (16917/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274047531103611/281474976710656), (17642819864655/562949953421312)), (64533237937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66634903844323/70368744177664), (68709073639389/1125899906842624)), (17001/562949953421312), by norm_num⟩
  | 2 => ⟨((1005393926553933/1125899906842624), (16265824297055/140737488355328)), (68547/1125899906842624), by norm_num⟩
  | 3 => ⟨((110343291946649/140737488355328), (116199039429805/562949953421312)), (69133/562949953421312), by norm_num⟩
  | 4 => ⟨((161033903081145/281474976710656), (91104258584971/281474976710656)), (273891/1125899906842624), by norm_num⟩
  | 5 => ⟨((62641206032873/281474976710656), (833942655575117/2251799813685248)), (981379/2251799813685248), by norm_num⟩
  | 6 => ⟨((-24665238097493/281474976710656), (742363307999229/4503599627370496)), (2327405/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-130507834509/2147483648)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1925775643/1073741824), (-17432935735/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-385294593811865/4503599627370496), (-1285254744088795/9007199254740992)), (8360383/9007199254740992), by norm_num⟩
  | 1 => ⟨((6112652467/34359738368), (40780824379/137438953472)), (267/137438953472), by norm_num⟩
  | 2 => ⟨((-50843613879/274877906944), (-42400670159/137438953472)), (279/137438953472), by norm_num⟩
  | 3 => ⟨((17621053805/137438953472), (58779809949/274877906944)), (389/274877906944), by norm_num⟩
  | 4 => ⟨((-18320975645/274877906944), (-30557294655/274877906944)), (407/549755813888), by norm_num⟩
  | 5 => ⟨((476217473/17179869184), (25416843163/549755813888)), (341/1099511627776), by norm_num⟩
  | 6 => ⟨((-42251366239/4398046511104), (-70470452709/4398046511104)), (475/4398046511104), by norm_num⟩
  | 7 => ⟨((50205283515/17592186044416), (41868339093/8796093022208)), (71/2199023255552), by norm_num⟩
  | 8 => ⟨((-13049869019/17592186044416), (-10882845449/8796093022208)), (297/35184372088832), by norm_num⟩
  | 9 => ⟨((48242559559/281474976710656), (80463078821/281474976710656)), (69/35184372088832), by norm_num⟩
  | 10 => ⟨((-20063516485/562949953421312), (-66927307469/1125899906842624)), (461/1125899906842624), by norm_num⟩
  | 11 => ⟨((15171239873/2251799813685248), (197686681/17592186044416)), (351/4503599627370496), by norm_num⟩
  | 12 => ⟨((-21031804287/18014398509481984), (-17539323593/9007199254740992)), (489/36028797018963968), by norm_num⟩
  | 13 => ⟨((13456740779/72057594037927936), (44888613037/144115188075855872)), (315/144115188075855872), by norm_num⟩
  | 14 => ⟨((-31980006619/1152921504606846976), (-53338998113/1152921504606846976)), (47/144115188075855872), by norm_num⟩
  | 15 => ⟨((8866740569/2305843009213693952), (29577420925/4611686018427387904)), (419/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-36875737357/73786976294838206464), (-61504517767/73786976294838206464)), (219/36893488147419103232), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-1374837099931/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779196855454445/633825300114114700748351602688), (-1627803049255/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118138943147401/2475880078570760549798248448), (-1830984240409/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890027792140607/2475880078570760549798248448), (-486266045027/309485009821345068724781056)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771693536736517/154742504910672534362390528), (-1944663075311/77371252455336267181195264)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387506077605841/2417851639229258349412352), (-3645391045559/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259200172110817/604462909807314587353088), (-3188865087001/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944229854756361/37778931862957161709568), (-5180308423883/75557863725914323419136)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298039323229319/4722366482869645213696), (-1941916973407/2361183241434822606848)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622134008892001/590295810358705651712), (-5338001518239/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824329847128159/73786976294838206464), (-833637207085/9223372036854775808)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((7123500289807/36028797018963968), (-7498055652753/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594860890065571/1152921504606846976), (-7492209070977/1152921504606846976)), (6713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298835567201987/36028797018963968), (-3274554439267/72057594037927936)), (2941/72057594037927936), by norm_num⟩
  | 4 => ⟨((746385694262819/18014398509481984), (-9810523571279/36028797018963968)), (2209/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490660728070601/9007199254740992), (-12240178757483/9007199254740992)), (11069/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115355512112793/2251799813685248), (-12205752936719/2251799813685248)), (11105/2251799813685248), by norm_num⟩
  | 1 => ⟨((277517602496889/281474976710656), (-18222697117231/1125899906842624)), (4187/281474976710656), by norm_num⟩
  | 0 => ⟨((1094190566263851/1125899906842624), (-36102460073205/1125899906842624)), (8465/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094190566263851/1125899906842624), (-36102460073205/1125899906842624)), (32291413427257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((132777079073495/140737488355328), (-70171373122851/1125899906842624)), (67985/1125899906842624), by norm_num⟩
  | 2 => ⟨((997762008961231/1125899906842624), (-132404664410451/1125899906842624)), (136755/1125899906842624), by norm_num⟩
  | 3 => ⟨((217159186492723/281474976710656), (-469343120663301/2251799813685248)), (274547/1125899906842624), by norm_num⟩
  | 4 => ⟨((1242488876624763/2251799813685248), (-362100288488415/1125899906842624)), (538077/1125899906842624), by norm_num⟩
  | 5 => ⟨((452665519664693/2251799813685248), (-12487388364165/35184372088832)), (469949/562949953421312), by norm_num⟩
  | 6 => ⟨((-385294593811865/4503599627370496), (-1285254744088795/9007199254740992)), (8360383/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-17432935735/268435456)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile061Terms0
