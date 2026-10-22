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
namespace Reinmann.XiBand97.Tile060Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨60,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79593/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79593/2560))
  have he : value ((69/80), (79593/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/4294967296), (-92559336189/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1120259815477465/2251799813685248), (-4125619029503/17592186044416)), (843377/1125899906842624), by norm_num⟩
  | 1 => ⟨((23697049945/68719476736), (2792637889/17179869184)), (73/137438953472), by norm_num⟩
  | 2 => ⟨((-16425543357/137438953472), (-30971345265/549755813888)), (103/549755813888), by norm_num⟩
  | 3 => ⟨((60721701691/2199023255552), (28623600865/2199023255552)), (97/2199023255552), by norm_num⟩
  | 4 => ⟨((-21044538163/4398046511104), (-19840368237/8796093022208)), (137/17592186044416), by norm_num⟩
  | 5 => ⟨((93356558681/140737488355328), (44007344975/140737488355328)), (77/70368744177664), by norm_num⟩
  | 6 => ⟨((-43139890291/562949953421312), (-40671422791/1125899906842624)), (9/70368744177664), by norm_num⟩
  | 7 => ⟨((17087024757/2251799813685248), (16109304021/4503599627370496)), (29/2251799813685248), by norm_num⟩
  | 8 => ⟨((-23687646069/36028797018963968), (-11166118663/36028797018963968)), (41/36028797018963968), by norm_num⟩
  | 9 => ⟨((7297344483/144115188075855872), (859973741/36028797018963968)), (103/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-64744112051/18446744073709551616), (-30519724745/18446744073709551616)), (29/4611686018427387904), by norm_num⟩
  | 11 => ⟨((65275925419/295147905179352825856), (15385208115/147573952589676412928)), (119/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-60327764883/4722366482869645213696), (-14218951503/2361183241434822606848)), (7/295147905179352825856), by norm_num⟩
  | 13 => ⟨((51465870939/75557863725914323419136), (12130247563/37778931862957161709568)), (97/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-20384813335/604462909807314587353088), (-19218392909/1208925819614629174706176)), (39/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((7535827141/4835703278458516698824704), (28418506367/38685626227668133590597632)), (117/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-83574997375/1237940039285380274899124224), (-4924551891/154742504910672534362390528)), (41/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-3518476382827/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1781039142918575/633825300114114700748351602688), (-2087041168747/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59134225125093/1237940039285380274899124224), (-4695564973325/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946114437042903/1237940039285380274899124224), (-2494365155115/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773894012370939/154742504910672534362390528), (-4988384188027/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388021653016703/2417851639229258349412352), (-4676242228893/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630502020859499/302231454903657293676544), (-511417973307/75557863725914323419136)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472847447341921/18889465931478580854784), (-6647742886069/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((325058956438763/1180591620717411303424), (-4985202283957/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406288120346359/147573952589676412928), (-856708668537/73786976294838206464)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828100359571725/73786976294838206464), (-2141402372751/18446744073709551616)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827854354967079/9223372036854775808), (-2408569272335/2305843009213693952)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399773684398383/288230376151711744), (-1203966429825/144115188075855872)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599520948247071/72057594037927936), (-8424896116229/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((749155424271387/18014398509481984), (-12631593815183/36028797018963968)), (277/4503599627370496), by norm_num⟩
  | 3 => ⟨((1497567577178847/9007199254740992), (-7889700444475/4503599627370496)), (1389/4503599627370496), by norm_num⟩
  | 2 => ⟨((17534939547221/35184372088832), (-15764207416391/2251799813685248)), (1395/1125899906842624), by norm_num⟩
  | 1 => ⟨((70020356663873/70368744177664), (-23608130487039/1125899906842624)), (4213/1125899906842624), by norm_num⟩
  | 0 => ⟨((557219151281167/562949953421312), (-23531180156615/562949953421312)), (8541/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557219151281167/562949953421312), (-23531180156615/562949953421312)), (32581333640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101126180866675/1125899906842624), (-93166535716543/1125899906842624)), (17623/1125899906842624), by norm_num⟩
  | 2 => ⟨((534594085804855/562949953421312), (-91116546892543/562949953421312)), (9347/281474976710656), by norm_num⟩
  | 3 => ⟨((985837585644971/1125899906842624), (-43263496862979/140737488355328)), (41557/562949953421312), by norm_num⟩
  | 4 => ⟨((756803522053561/1125899906842624), (-151526014114573/281474976710656)), (98325/562949953421312), by norm_num⟩
  | 5 => ⟨((364844943123683/2251799813685248), (-50926117174231/70368744177664)), (952185/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1120259815477465/2251799813685248), (-4125619029503/17592186044416)), (843377/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-92559336189/4294967296)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1017427393/1073741824), (-18337884619/536870912)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-401948591473209/1125899906842624), (-85100267823741/562949953421312)), (2377673/2251799813685248), by norm_num⟩
  | 1 => ⟨((13476124939/34359738368), (22825244141/137438953472)), (81/68719476736), by norm_num⟩
  | 2 => ⟨((-29610072923/137438953472), (-25076093705/274877906944)), (45/68719476736), by norm_num⟩
  | 3 => ⟨((86746639951/1099511627776), (1147871029/34359738368)), (133/549755813888), by norm_num⟩
  | 4 => ⟨((-95300924651/4398046511104), (-5044260873/549755813888)), (295/4398046511104), by norm_num⟩
  | 5 => ⟨((41879506777/8796093022208), (35466796687/17592186044416)), (131/8796093022208), by norm_num⟩
  | 6 => ⟨((-30672893859/35184372088832), (-25976172453/70368744177664)), (97/35184372088832), by norm_num⟩
  | 7 => ⟨((77023127137/562949953421312), (16307281297/281474976710656)), (123/281474976710656), by norm_num⟩
  | 8 => ⟨((-661082453/35184372088832), (-35830759255/4503599627370496)), (273/4503599627370496), by norm_num⟩
  | 9 => ⟨((41316881447/18014398509481984), (2186895135/2251799813685248)), (269/36028797018963968), by norm_num⟩
  | 10 => ⟨((-72625973899/288230376151711744), (-3844079791/36028797018963968)), (239/288230376151711744), by norm_num⟩
  | 11 => ⟨((58027481747/2305843009213693952), (383923027/36028797018963968)), (193/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-84999606037/36893488147419103232), (-35992111391/36893488147419103232)), (285/36893488147419103232), by norm_num⟩
  | 13 => ⟨((57465607215/295147905179352825856), (24333154381/295147905179352825856)), (97/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-4509458733/295147905179352825856), (-15275829957/2361183241434822606848)), (123/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((21137692925/18889465931478580854784), (17901028811/37778931862957161709568)), (291/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-46444258403/604462909807314587353088), (-39332580463/1208925819614629174706176)), (161/604462909807314587353088), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (-3570517538431/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890249299397875/316912650057057350374175801344), (-4233381657045/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891687127032047/39614081257132168796771975168), (-1190531239343/9903520314283042199192993792)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472895705990469/618970019642690137449562112), (-632408170945/309485009821345068724781056)), (433/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773247997959739/154742504910672534362390528), (-5058711211547/154742504910672534362390528)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775740505794275/4835703278458516698824704), (-4741952819777/9671406556917033397649408)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630237089715521/302231454903657293676544), (-4148619607285/604462909807314587353088)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472632208713315/18889465931478580854784), (-6740401921779/75557863725914323419136)), (289/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299590172818469/4722366482869645213696), (-5054334260335/4722366482869645213696)), (1735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406066202820297/147573952589676412928), (-3474068633721/295147905179352825856)), (2387/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826990926650643/73786976294838206464), (-8682811899967/73786976294838206464)), (2985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826606456766587/9223372036854775808), (-2441229229267/2305843009213693952)), (1681/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597847108352097/1152921504606846976), (-9760855976971/1152921504606846976)), (1683/576460752303423488), by norm_num⟩
  | 5 => ⟨((299487631443273/36028797018963968), (-2134044126995/36028797018963968)), (2949/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496674407900421/36028797018963968), (-12795110054733/36028797018963968)), (4433/36028797018963968), by norm_num⟩
  | 3 => ⟨((186940389527561/1125899906842624), (-7988922461893/4503599627370496)), (1389/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120193330435273/2251799813685248), (-3988434323785/562949953421312)), (1395/562949953421312), by norm_num⟩
  | 1 => ⟨((558632873036695/562949953421312), (-23870184740029/1125899906842624)), (2107/281474976710656), by norm_num⟩
  | 0 => ⟨((69270992343813/70368744177664), (-47497777360421/1125899906842624)), (4273/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((69270992343813/70368744177664), (-47497777360421/1125899906842624)), (16300202489757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1089042081849233/1125899906842624), (-93513624843861/1125899906842624)), (17547/562949953421312), by norm_num⟩
  | 2 => ⟨((522811952844237/562949953421312), (-180904664903683/1125899906842624)), (73721/1125899906842624), by norm_num⟩
  | 3 => ⟨((471002283558921/562949953421312), (-336012537392089/1125899906842624)), (160621/1125899906842624), by norm_num⟩
  | 4 => ⟨((687865923497635/1125899906842624), (-281130980568103/562949953421312)), (364645/1125899906842624), by norm_num⟩
  | 5 => ⟨((69731338822497/562949953421312), (-687025268932025/1125899906842624)), (404879/562949953421312), by norm_num⟩
  | 6 => ⟨((-401948591473209/1125899906842624), (-85100267823741/562949953421312)), (2377673/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-18337884619/536870912)), (1/1073741824), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-2567700857/2147483648), (-92559336189/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((54185232684935/281474976710656), (1050867743452095/4503599627370496)), (2522655/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4584758455/17179869184), (-694662107/2147483648)), (27/34359738368), by norm_num⟩
  | 2 => ⟨((25423299173/137438953472), (15408098589/68719476736)), (19/34359738368), by norm_num⟩
  | 3 => ⟨((-23496117523/274877906944), (-14240106793/137438953472)), (71/274877906944), by norm_num⟩
  | 4 => ⟨((16286267615/549755813888), (19740979749/549755813888)), (25/274877906944), by norm_num⟩
  | 5 => ⟨((-36124097533/4398046511104), (-21893447127/2199023255552)), (113/4398046511104), by norm_num⟩
  | 6 => ⟨((8346438785/4398046511104), (40467683063/17592186044416)), (53/8796093022208), by norm_num⟩
  | 7 => ⟨((-26447133767/70368744177664), (-64114423815/140737488355328)), (85/70368744177664), by norm_num⟩
  | 8 => ⟨((36663512409/562949953421312), (11110183025/140737488355328)), (15/70368744177664), by norm_num⟩
  | 9 => ⟨((-45179040455/4503599627370496), (-54762610057/4503599627370496)), (75/2251799813685248), by norm_num⟩
  | 10 => ⟨((50105159219/36028797018963968), (30366839009/18014398509481984)), (169/36028797018963968), by norm_num⟩
  | 11 => ⟨((-25258363523/144115188075855872), (-61232549357/288230376151711744)), (43/72057594037927936), by norm_num⟩
  | 12 => ⟨((46687369231/2305843009213693952), (56590891927/2305843009213693952)), (161/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-4978648977/2305843009213693952), (-24138964421/9223372036854775808)), (35/4611686018427387904), by norm_num⟩
  | 14 => ⟨((31551419441/147573952589676412928), (38244240297/147573952589676412928)), (113/147573952589676412928), by norm_num⟩
  | 15 => ⟨((-11663881295/590295810358705651712), (-14138073245/590295810358705651712)), (169/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((4042393217/2361183241434822606848), (39199062433/18889465931478580854784)), (119/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (143449702279/1267650600228229401496703205376)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780124031806109/633825300114114700748351602688), (1360092175083/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891266292948245/39614081257132168796771975168), (1529940041699/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891136370984777/2475880078570760549798248448), (812681432767/1237940039285380274899124224)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443200578364875/38685626227668133590597632), (1625139666333/154742504910672534362390528)), (863/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48470749957859/302231454903657293676544), (1523331323625/9671406556917033397649408)), (809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39378440910637/18889465931478580854784), (666338917321/302231454903657293676544)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944969375074437/37778931862957161709568), (2165157053481/75557863725914323419136)), (2301/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81196809192583/295147905179352825856), (1623479000819/4722366482869645213696)), (1727/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623660298796075/590295810358705651712), (2231652002957/590295810358705651712)), (1187/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913119271818253/36893488147419103232), (2788617847889/73786976294838206464)), (371/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912882251099757/4611686018427387904), (3135893192823/9223372036854775808)), (835/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597010744890223/1152921504606846976), (3134266514849/1152921504606846976)), (3341/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197224991823235/144115188075855872), (2740654121915/144115188075855872)), (1463/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495598660342683/36028797018963968), (2053662680093/18014398509481984)), (2195/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494200366867335/9007199254740992), (5127764260635/9007199254740992)), (1373/2251799813685248), by norm_num⟩
  | 2 => ⟨((559451708541649/1125899906842624), (1279546523835/562949953421312)), (1375/562949953421312), by norm_num⟩
  | 1 => ⟨((2230825465231713/2251799813685248), (15306740863213/2251799813685248)), (2067/281474976710656), by norm_num⟩
  | 0 => ⟨((1104955874742749/1125899906842624), (30422652016997/2251799813685248)), (33223/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104955874742749/1125899906842624), (30422652016997/2251799813685248)), (126735695845793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2168391867289147/2251799813685248), (59713457416839/2251799813685248)), (66109/2251799813685248), by norm_num⟩
  | 2 => ⟨((1043244955562859/1125899906842624), (115003273953099/2251799813685248)), (32707/562949953421312), by norm_num⟩
  | 3 => ⟨((481860595448133/562949953421312), (53280307021801/562949953421312)), (63953/562949953421312), by norm_num⟩
  | 4 => ⟨((1629635749575385/2251799813685248), (364844943123677/2251799813685248)), (30397/140737488355328), by norm_num⟩
  | 5 => ⟨((1120259815477457/2251799813685248), (528079235776373/2251799813685248)), (861551/2251799813685248), by norm_num⟩
  | 6 => ⟨((54185232684935/281474976710656), (1050867743452095/4503599627370496)), (2522655/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-92559336189/2147483648)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-26864515393/536870912)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1095138672122079/4503599627370496), (126145510942355/2251799813685248)), (1320177/4503599627370496), by norm_num⟩
  | 1 => ⟨((-107577984515/274877906944), (-387236343/4294967296)), (33/68719476736), by norm_num⟩
  | 2 => ⟨((86570043411/274877906944), (1246465703/17179869184)), (27/68719476736), by norm_num⟩
  | 3 => ⟨((-46443036649/274877906944), (-668703053/17179869184)), (59/274877906944), by norm_num⟩
  | 4 => ⟨((4671698997/68719476736), (17219776731/1099511627776)), (97/1099511627776), by norm_num⟩
  | 5 => ⟨((-6015047585/274877906944), (-5542832303/1099511627776)), (127/4398046511104), by norm_num⟩
  | 6 => ⟨((51631176685/8796093022208), (23788918535/17592186044416)), (69/8796093022208), by norm_num⟩
  | 7 => ⟨((-94968197967/70368744177664), (-21878164221/70368744177664)), (129/70368744177664), by norm_num⟩
  | 8 => ⟨((38211354571/140737488355328), (4401443369/70368744177664)), (105/281474976710656), by norm_num⟩
  | 9 => ⟨((-109331204857/2251799813685248), (-25187021609/2251799813685248)), (19/281474976710656), by norm_num⟩
  | 10 => ⟨((17596178611/2251799813685248), (1013423687/562949953421312)), (25/2251799813685248), by norm_num⟩
  | 11 => ⟨((-82385329369/72057594037927936), (-9489701837/36028797018963968)), (119/72057594037927936), by norm_num⟩
  | 12 => ⟨((11049506043/72057594037927936), (2545514319/72057594037927936)), (65/288230376151711744), by norm_num⟩
  | 13 => ⟨((-5471844289/288230376151711744), (-10084547081/2305843009213693952)), (131/4611686018427387904), by norm_num⟩
  | 14 => ⟨((40258713827/18446744073709551616), (18549088459/36893488147419103232)), (123/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-69113493695/295147905179352825856), (-7960961655/147573952589676412928)), (27/73786976294838206464), by norm_num⟩
  | 16 => ⟨((55616938507/2361183241434822606848), (12812673507/2361183241434822606848)), (11/295147905179352825856), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (294941464707/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889913938736227/316912650057057350374175801344), (349443340699/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945466606049629/19807040628566084398385987584), (196537695919/19807040628566084398385987584)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890782587430601/2475880078570760549798248448), (208791726747/1237940039285380274899124224)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772448659066737/154742504910672534362390528), (417516924645/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550732584851733/9671406556917033397649408), (391351444833/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259820259213453/604462909807314587353088), (342361858949/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889468001072953/75557863725914323419136), (69525697213/9444732965739290427392)), (1149/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649398055050481/2361183241434822606848), (208519165565/2361183241434822606848)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623175513109731/590295810358705651712), (573239512203/590295810358705651712)), (1185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228204138619193/9223372036854775808), (716267217171/73786976294838206464)), (1481/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912542070187403/4611686018427387904), (805412820667/9223372036854775808)), (833/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199541415316807/144115188075855872), (402464178103/576460752303423488)), (833/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196631553102263/144115188075855872), (351883839603/72057594037927936)), (2917/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494710611288565/36028797018963968), (263640807055/9007199254740992)), (4375/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493093990383875/9007199254740992), (658150858487/4503599627370496)), (2735/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235605111878965/4503599627370496), (2626905229613/4503599627370496)), (10943/4503599627370496), by norm_num⟩
  | 1 => ⟨((139221898453625/140737488355328), (3926142914023/2251799813685248)), (2053/281474976710656), by norm_num⟩
  | 0 => ⟨((1101735522526165/1125899906842624), (3897804608617/1125899906842624)), (4111/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101735522526165/1125899906842624), (3897804608617/1125899906842624)), (15682221532726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1078076267116077/1125899906842624), (7628297632997/1125899906842624)), (64593/2251799813685248), by norm_num⟩
  | 2 => ⟨((2064464593577067/2251799813685248), (14608557273433/1125899906842624)), (124575/2251799813685248), by norm_num⟩
  | 3 => ⟨((473083840807451/562949953421312), (13393219535305/562949953421312)), (28957/281474976710656), by norm_num⟩
  | 4 => ⟨((99311200198397/140737488355328), (90041620219089/2251799813685248)), (400375/2251799813685248), by norm_num⟩
  | 5 => ⟨((279415092702009/562949953421312), (127075471876963/2251799813685248)), (597069/2251799813685248), by norm_num⟩
  | 6 => ⟨((1095138672122079/4503599627370496), (126145510942355/2251799813685248)), (1320177/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-26864515393/536870912)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1659352607/1073741824), (-119631206571/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((640212303259149/4503599627370496), (715746618729237/4503599627370496)), (874129/2251799813685248), by norm_num⟩
  | 1 => ⟨((-35006910909/137438953472), (-39137139333/137438953472)), (97/137438953472), by norm_num⟩
  | 2 => ⟨((31361982055/137438953472), (35062169999/137438953472)), (11/17179869184), by norm_num⟩
  | 3 => ⟨((-37462085547/274877906944), (-41881983405/274877906944)), (107/274877906944), by norm_num⟩
  | 4 => ⟨((16780761629/274877906944), (18760610089/274877906944)), (97/549755813888), by norm_num⟩
  | 5 => ⟨((-48107341679/2199023255552), (-53783201241/2199023255552)), (141/2199023255552), by norm_num⟩
  | 6 => ⟨((897883177/137438953472), (32122186703/4398046511104)), (85/4398046511104), by norm_num⟩
  | 7 => ⟨((-29417886805/17592186044416), (-32888704113/17592186044416)), (11/2199023255552), by norm_num⟩
  | 8 => ⟨((52709777247/140737488355328), (58928647025/140737488355328)), (5/4398046511104), by norm_num⟩
  | 9 => ⟨((-20987387223/281474976710656), (-23463546959/281474976710656)), (129/562949953421312), by norm_num⟩
  | 10 => ⟨((30083479833/2251799813685248), (67265651913/4503599627370496)), (187/4503599627370496), by norm_num⟩
  | 11 => ⟨((-9800429065/4503599627370496), (-21913430685/9007199254740992)), (31/4503599627370496), by norm_num⟩
  | 12 => ⟨((23413348773/72057594037927936), (52351462577/144115188075855872)), (75/72057594037927936), by norm_num⟩
  | 13 => ⟨((-25816054997/576460752303423488), (-14430958277/288230376151711744)), (167/1152921504606846976), by norm_num⟩
  | 14 => ⟨((52864183999/9223372036854775808), (3693829449/576460752303423488)), (173/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-50517281207/73786976294838206464), (-14119368305/18446744073709551616)), (167/73786976294838206464), by norm_num⟩
  | 16 => ⟨((45257408481/590295810358705651712), (6324627965/73786976294838206464)), (151/590295810358705651712), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (1095556462325/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896095923159/158456325028528675187087900672), (648833265925/316912650057057350374175801344)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472664817164287/9903520314283042199192993792), (1459674922055/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890491504442919/2475880078570760549798248448), (1550660013291/2475880078570760549798248448)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443039388941625/38685626227668133590597632), (1550384910633/154742504910672534362390528)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550459653949081/9671406556917033397649408), (726596809739/4835703278458516698824704)), (809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259581423141295/604462909807314587353088), (1271252252923/604462909807314587353088)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889079852138511/75557863725914323419136), (516309313061/18889465931478580854784)), (2301/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298504963178509/4722366482869645213696), (387112221675/1180591620717411303424)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622775128960993/590295810358705651712), (16627648735/4611686018427387904)), (1187/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825132543255281/73786976294838206464), (2659257014243/73786976294838206464)), (371/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824520886682239/9223372036854775808), (2990060607133/9223372036854775808)), (3339/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595767922685071/1152921504606846976), (2988057379033/1152921504606846976)), (3341/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196138414419729/144115188075855872), (2612298209343/144115188075855872)), (731/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493970577164121/36028797018963968), (489243425293/4503599627370496)), (4389/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492168380484013/9007199254740992), (4884568586439/9007199254740992)), (5491/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233752204042765/4503599627370496), (1218197106329/562949953421312)), (2749/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112383420605765/1125899906842624), (3639898166875/562949953421312)), (8265/1125899906842624), by norm_num⟩
  | 0 => ⟨((274735946684861/281474976710656), (3610607837573/281474976710656)), (8301/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274735946684861/281474976710656), (3610607837573/281474976710656)), (31665804149436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2144895572424447/2251799813685248), (28193305819383/1125899906842624)), (65671/2251799813685248), by norm_num⟩
  | 2 => ⟨((2041654652733047/2251799813685248), (419606688451/8796093022208)), (32099/562949953421312), by norm_num⟩
  | 3 => ⟨((230749575690561/281474976710656), (97394598446259/1125899906842624)), (122539/1125899906842624), by norm_num⟩
  | 4 => ⟨((748237169197341/1125899906842624), (4990177663539/35184372088832)), (444225/2251799813685248), by norm_num⟩
  | 5 => ⟨((474606437084225/1125899906842624), (212244026940779/1125899906842624)), (716445/2251799813685248), by norm_num⟩
  | 6 => ⟨((640212303259149/4503599627370496), (715746618729237/4503599627370496)), (874129/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-119631206571/2147483648)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-129923454017/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-289826117842647/2251799813685248), (304487398406127/2251799813685248)), (2374105/4503599627370496), by norm_num⟩
  | 1 => ⟨((34422337901/137438953472), (-18081821253/68719476736)), (71/68719476736), by norm_num⟩
  | 2 => ⟨((-16745694169/68719476736), (70371198979/274877906944)), (139/137438953472), by norm_num⟩
  | 3 => ⟨((43447488315/274877906944), (-45645343431/274877906944)), (91/137438953472), by norm_num⟩
  | 4 => ⟨((-42272454231/549755813888), (5551358565/68719476736)), (179/549755813888), by norm_num⟩
  | 5 => ⟨((65806718171/2199023255552), (-69135647825/2199023255552)), (281/2199023255552), by norm_num⟩
  | 6 => ⟨((-10671163397/1099511627776), (11210979897/1099511627776)), (23/549755813888), by norm_num⟩
  | 7 => ⟨((47463143215/17592186044416), (-49864136143/17592186044416)), (207/17592186044416), by norm_num⟩
  | 8 => ⟨((-11544876511/17592186044416), (48515564297/70368744177664)), (203/70368744177664), by norm_num⟩
  | 9 => ⟨((39938297551/281474976710656), (-20979317545/140737488355328)), (177/281474976710656), by norm_num⟩
  | 10 => ⟨((-3885816927/140737488355328), (32659093545/1125899906842624)), (139/1125899906842624), by norm_num⟩
  | 11 => ⟨((21996947187/4503599627370496), (-23109695123/4503599627370496)), (99/4503599627370496), by norm_num⟩
  | 12 => ⟨((-14268027593/18014398509481984), (29979593521/36028797018963968)), (259/72057594037927936), by norm_num⟩
  | 13 => ⟨((34171445785/288230376151711744), (-8975014661/72057594037927936)), (157/288230376151711744), by norm_num⟩
  | 14 => ⟨((-37996893235/2305843009213693952), (39919021981/2305843009213693952)), (11/144115188075855872), by norm_num⟩
  | 15 => ⟨((39433888095/18446744073709551616), (-10357177335/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-19183700765/73786976294838206464), (40308272983/147573952589676412928)), (181/147573952589676412928), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (1518539215931/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444843313025531/158456325028528675187087900672), (3596575026499/633825300114114700748351602688)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890421432380547/39614081257132168796771975168), (4045533410303/39614081257132168796771975168)), (407/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890238400938937/2475880078570760549798248448), (4297641496553/2475880078570760549798248448)), (865/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885951999888013/77371252455336267181195264), (2148405773513/77371252455336267181195264)), (1731/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550221464705397/9671406556917033397649408), (2013689543161/4835703278458516698824704)), (1623/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259372527347663/604462909807314587353088), (3523075054017/604462909807314587353088)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888739496720073/75557863725914323419136), (5723344072299/75557863725914323419136)), (2309/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649124454980615/2361183241434822606848), (4291061971981/4722366482869645213696)), (1733/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811210889329103/295147905179352825856), (5897860697473/590295810358705651712)), (149/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912344470876091/36893488147419103232), (7368802248527/73786976294838206464)), (1491/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28500300111211/144115188075855872), (8285058601549/9223372036854775808)), (3357/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797631481657475/576460752303423488), (2069751318793/288230376151711744)), (105/36028797018963968), by norm_num⟩
  | 5 => ⟨((149461611513747/18014398509481984), (7237321805469/144115188075855872)), (23/1125899906842624), by norm_num⟩
  | 4 => ⟨((1493294945261785/36028797018963968), (10842372555163/36028797018963968)), (4423/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491311019684439/9007199254740992), (13529160263583/9007199254740992)), (2771/4503599627370496), by norm_num⟩
  | 2 => ⟨((278999896853947/562949953421312), (13493476881213/2251799813685248)), (2781/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111021035194949/1125899906842624), (20151093932969/1125899906842624)), (8393/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096030183942967/1125899906842624), (39946227867057/1125899906842624)), (16987/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096030183942967/1125899906842624), (39946227867057/1125899906842624)), (64800266746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065535626836975/1125899906842624), (77772937382573/1125899906842624)), (34279/1125899906842624), by norm_num⟩
  | 2 => ⟨((1003035470032777/1125899906842624), (73603199610599/562949953421312)), (69619/1125899906842624), by norm_num⟩
  | 3 => ⟨((218583025051667/281474976710656), (65571210609979/281474976710656)), (142249/1125899906842624), by norm_num⟩
  | 4 => ⟨((1235746230460093/2251799813685248), (407361357344745/1125899906842624)), (574413/2251799813685248), by norm_num⟩
  | 5 => ⟨((383380280528785/2251799813685248), (894209616173703/2251799813685248)), (32691/70368744177664), by norm_num⟩
  | 6 => ⟨((-289826117842647/2251799813685248), (304487398406127/2251799813685248)), (2374105/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-129923454017/2147483648)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1925775643/1073741824), (-69419502143/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-184866871699709/4503599627370496), (-1452234282847335/9007199254740992)), (7987481/9007199254740992), by norm_num⟩
  | 1 => ⟨((23463125775/274877906944), (11519761261/34359738368)), (255/137438953472), by norm_num⟩
  | 2 => ⟨((-24395099217/274877906944), (-47909340233/137438953472)), (533/274877906944), by norm_num⟩
  | 3 => ⟨((8454697121/137438953472), (33208224105/137438953472)), (93/68719476736), by norm_num⟩
  | 4 => ⟨((-549407763/17179869184), (-34527280365/274877906944)), (389/549755813888), by norm_num⟩
  | 5 => ⟨((14623504969/1099511627776), (28718984445/549755813888)), (325/1099511627776), by norm_num⟩
  | 6 => ⟨((-10136241239/2199023255552), (-79625932387/4398046511104)), (453/4398046511104), by norm_num⟩
  | 7 => ⟨((24088824125/17592186044416), (47307849029/8796093022208)), (541/17592186044416), by norm_num⟩
  | 8 => ⟨((-6261412697/17592186044416), (-98373906519/70368744177664)), (565/70368744177664), by norm_num⟩
  | 9 => ⟨((23147096305/281474976710656), (90916794593/281474976710656)), (525/281474976710656), by norm_num⟩
  | 10 => ⟨((-9626606725/562949953421312), (-37811231903/562949953421312)), (439/1125899906842624), by norm_num⟩
  | 11 => ⟨((3639630169/1125899906842624), (57182724627/4503599627370496)), (167/2251799813685248), by norm_num⟩
  | 12 => ⟨((-20182395119/36028797018963968), (-619313193/281474976710656)), (233/18014398509481984), by norm_num⟩
  | 13 => ⟨((3228316217/36028797018963968), (3170032199/9007199254740992)), (599/288230376151711744), by norm_num⟩
  | 14 => ⟨((-15344216803/1152921504606846976), (-15067192327/288230376151711744)), (179/576460752303423488), by norm_num⟩
  | 15 => ⟨((2127160123/1152921504606846976), (66840204035/9223372036854775808)), (399/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-8846610251/36893488147419103232), (-69495148463/73786976294838206464)), (417/73786976294838206464), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-2370878766111/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779198309595991/633825300114114700748351602688), (-2807113428263/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890224809510791/39614081257132168796771975168), (-3157497866733/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890029725725477/2475880078570760549798248448), (-3354226881439/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442923897651343/38685626227668133590597632), (-1676767782327/77371252455336267181195264)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775013181828313/4835703278458516698824704), (-785801300207/2417851639229258349412352)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157400262042729/75557863725914323419136), (-85924072165/18889465931478580854784)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888463075566995/75557863725914323419136), (-1116668841939/18889465931478580854784)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162255257110393/590295810358705651712), (-3348802506985/4722366482869645213696)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622138107159225/590295810358705651712), (-4602647512555/590295810358705651712)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912167739324983/36893488147419103232), (-5750376531981/73786976294838206464)), (5953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823623108201747/9223372036854775808), (-3232571306419/4611686018427387904)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594868795919149/1152921504606846976), (-6460106423481/1152921504606846976)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195350165406007/144115188075855872), (-5646930903819/144115188075855872)), (2937/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492785186762993/36028797018963968), (-8459080663291/36028797018963968)), (8823/36028797018963968), by norm_num⟩
  | 3 => ⟨((372670345961831/2251799813685248), (-5277034017679/4503599627370496)), (11049/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115381259158117/2251799813685248), (-10524433182427/2251799813685248)), (1385/281474976710656), by norm_num⟩
  | 1 => ⟨((1110121686404541/1125899906842624), (-31425400660683/2251799813685248)), (33395/2251799813685248), by norm_num⟩
  | 0 => ⟨((273585827404981/281474976710656), (-31130429072781/1125899906842624)), (67419/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273585827404981/281474976710656), (-31130429072781/1125899906842624)), (257183083541106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2125620880547589/2251799813685248), (-60515817746057/1125899906842624)), (33697/562949953421312), by norm_num⟩
  | 2 => ⟨((2000007035998235/2251799813685248), (-57124831888991/562949953421312)), (268961/2251799813685248), by norm_num⟩
  | 3 => ⟨((438295644372579/562949953421312), (-101474442811343/562949953421312)), (532359/2251799813685248), by norm_num⟩
  | 4 => ⟨((1291809392484579/2251799813685248), (-19751225676921/70368744177664)), (510439/1125899906842624), by norm_num⟩
  | 5 => ⟨((563681514261977/2251799813685248), (-45323422956985/140737488355328)), (436099/562949953421312), by norm_num⟩
  | 6 => ⟨((-184866871699709/4503599627370496), (-1452234282847335/9007199254740992)), (7987481/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-69419502143/1073741824)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile060Terms0
