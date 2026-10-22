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
namespace Reinmann.XiBand97.Tile053Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨53,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77087/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77087/2560))
  have he : value ((69/80), (77087/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-5602818047/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-540673782637527/2251799813685248), (-557117939693741/1125899906842624)), (6709149/2251799813685248), by norm_num⟩
  | 1 => ⟨((2859241547/17179869184), (11784812291/34359738368)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((-1981875217/34359738368), (-8168609413/68719476736)), (51/68719476736), by norm_num⟩
  | 3 => ⟨((7326566501/549755813888), (235918691/8589934592)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((-10156777827/4398046511104), (-20931376065/4398046511104)), (135/4398046511104), by norm_num⟩
  | 5 => ⟨((1408028383/4398046511104), (2901704861/4398046511104)), (77/17592186044416), by norm_num⟩
  | 6 => ⟨((-2602589077/70368744177664), (-21453957795/281474976710656)), (145/281474976710656), by norm_num⟩
  | 7 => ⟨((2061688321/562949953421312), (8497571633/1125899906842624)), (117/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1429053447/4503599627370496), (-5890067819/9007199254740992)), (83/18014398509481984), by norm_num⟩
  | 9 => ⟨((7043871059/288230376151711744), (7258104715/144115188075855872)), (13/36028797018963968), by norm_num⟩
  | 10 => ⟨((-976487873/576460752303423488), (-8049495711/2305843009213693952)), (117/4611686018427387904), by norm_num⟩
  | 11 => ⟨((7876070587/73786976294838206464), (16231229839/73786976294838206464)), (15/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-1819758707/295147905179352825856), (-117194075/9223372036854775808)), (113/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((3104887673/9444732965739290427392), (6398640653/9444732965739290427392)), (49/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-2459593299/151115727451828646838272), (-20275198757/604462909807314587353088)), (79/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((3637035009/4835703278458516698824704), (7495304989/4835703278458516698824704)), (119/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-10084002249/309485009821345068724781056), (-20781398083/309485009821345068724781056)), (21/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-2634620371247/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781043220103293/633825300114114700748351602688), (-3125535362779/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892300038518689/39614081257132168796771975168), (-1758013714159/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892234312433701/2475880078570760549798248448), (-3735549895231/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773899790081175/154742504910672534362390528), (-3735291912173/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776046194587727/4835703278458516698824704), (-437695248851/1208925819614629174706176)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261009457118829/604462909807314587353088), (-3063592486555/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891399265037611/75557863725914323419136), (-2488911697469/37778931862957161709568)), (2307/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300243523536291/4722366482869645213696), (-1866458641601/2361183241434822606848)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406291006488679/147573952589676412928), (-5132029274549/590295810358705651712)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914058114967427/36893488147419103232), (-400871128871/4611686018427387904)), (1489/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228484273473299/1152921504606846976), (-7214168951883/9223372036854775808)), (6705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599117042446815/1152921504606846976), (-7212278412345/1152921504606846976)), (6711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149883024062415/18014398509481984), (-1577153731825/36028797018963968)), (5879/144115188075855872), by norm_num⟩
  | 4 => ⟨((749174923304553/18014398509481984), (-9458660463483/36028797018963968)), (69/281474976710656), by norm_num⟩
  | 3 => ⟨((23400406786043/140737488355328), (-11815856961295/9007199254740992)), (5531/4503599627370496), by norm_num⟩
  | 2 => ⟨((140288641536027/281474976710656), (-2951158396093/562949953421312)), (11097/2251799813685248), by norm_num⟩
  | 1 => ⟨((560235748975095/562949953421312), (-8839410270259/562949953421312)), (4183/281474976710656), by norm_num⟩
  | 0 => ⟨((139359326891871/140737488355328), (-17622347410163/562949953421312)), (33811/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139359326891871/140737488355328), (-17622347410163/562949953421312)), (128978733543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102854002751887/1125899906842624), (-69799127497135/1125899906842624)), (34539/562949953421312), by norm_num⟩
  | 2 => ⟨((537976344888279/562949953421312), (-68370417903911/562949953421312)), (71947/562949953421312), by norm_num⟩
  | 3 => ⟨((505807011590415/562949953421312), (-65337366668015/281474976710656)), (154987/562949953421312), by norm_num⟩
  | 4 => ⟨((26508223065667/35184372088832), (-117410430460779/281474976710656)), (350463/562949953421312), by norm_num⟩
  | 5 => ⟨((443189489166127/1125899906842624), (-176916153173483/281474976710656)), (820459/562949953421312), by norm_num⟩
  | 6 => ⟨((-540673782637527/2251799813685248), (-557117939693741/1125899906842624)), (6709149/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-5602818047/268435456)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-17760513005/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-82645354337173/2251799813685248), (-869076128376563/2251799813685248)), (17708681/4503599627370496), by norm_num⟩
  | 1 => ⟨((2770849667/68719476736), (7284375873/17179869184)), (75/17179869184), by norm_num⟩
  | 2 => ⟨((-1522044747/68719476736), (-8002704849/34359738368)), (167/68719476736), by norm_num⟩
  | 3 => ⟨((557379021/68719476736), (5861246593/68719476736)), (247/274877906944), by norm_num⟩
  | 4 => ⟨((-306171721/137438953472), (-3219618767/137438953472)), (137/549755813888), by norm_num⟩
  | 5 => ⟨((2152729697/4398046511104), (11318760775/2199023255552)), (243/4398046511104), by norm_num⟩
  | 6 => ⟨((-788338433/8796093022208), (-259061035/274877906944)), (45/4398046511104), by norm_num⟩
  | 7 => ⟨((61862735/4398046511104), (20817015703/140737488355328)), (57/35184372088832), by norm_num⟩
  | 8 => ⟨((-543705287/281474976710656), (-1429364329/70368744177664)), (253/1125899906842624), by norm_num⟩
  | 9 => ⟨((2123809101/9007199254740992), (22333400417/9007199254740992)), (249/9007199254740992), by norm_num⟩
  | 10 => ⟨((-933297111/36028797018963968), (-4907149629/18014398509481984)), (221/72057594037927936), by norm_num⟩
  | 11 => ⟨((2982783055/1152921504606846976), (31366137511/1152921504606846976)), (89/288230376151711744), by norm_num⟩
  | 12 => ⟨((-1092307373/4611686018427387904), (-11486408039/4611686018427387904)), (263/9223372036854775808), by norm_num⟩
  | 13 => ⟨((2953901053/147573952589676412928), (31062422213/147573952589676412928)), (359/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-927197713/590295810358705651712), (-19500319291/1180591620717411303424)), (57/295147905179352825856), by norm_num⟩
  | 15 => ⟨((2173079043/18889465931478580854784), (11425754883/9444732965739290427392)), (269/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-2387371341/302231454903657293676544), (-25104949443/302231454903657293676544)), (149/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1084819451029/5070602400912917605986812821504)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890252313649017/316912650057057350374175801344), (-2572430867945/633825300114114700748351602688)), (5779/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472923567285773/9903520314283042199192993792), (-1446866800747/19807040628566084398385987584)), (3251/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891590857762569/2475880078570760549798248448), (-3074293932449/2475880078570760549798248448)), (3455/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773256532627497/154742504910672534362390528), (-3073958646115/154742504910672534362390528)), (6911/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775744772427363/4835703278458516698824704), (-720369996953/2417851639229258349412352)), (6481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260482177878659/604462909807314587353088), (-157558671567/37778931862957161709568)), (709/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1890542829157193/75557863725914323419136), (-4095857499941/75557863725914323419136)), (2305/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649800770198321/2361183241434822606848), (-3071308656507/4722366482869645213696)), (6917/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101517616109885/36893488147419103232), (-2111049818215/295147905179352825856)), (4757/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913507178803767/36893488147419103232), (-5276199887561/73786976294838206464)), (11899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826635733535369/9223372036854775808), (-2966882977649/4611686018427387904)), (13393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199735003538815/144115188075855872), (-5931317288077/1152921504606846976)), (13403/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598991712606937/72057594037927936), (-2593573925475/72057594037927936)), (11739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496731935730775/36028797018963968), (-1943803041061/9007199254740992)), (17629/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495609315518277/9007199254740992), (-4854686629755/4503599627370496)), (22075/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120300917626479/2251799813685248), (-9694910117845/2251799813685248)), (22131/2251799813685248), by norm_num⟩
  | 1 => ⟨((279370108518817/281474976710656), (-14506206658977/1125899906842624)), (8335/281474976710656), by norm_num⟩
  | 0 => ⟨((1108977505517279/1125899906842624), (-7216944049421/281474976710656)), (67253/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108977505517279/1125899906842624), (-7216944049421/281474976710656)), (256549839500045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((68223080476089/70368744177664), (-3554236287233/70368744177664)), (67967/562949953421312), by norm_num⟩
  | 2 => ⟨((527706574082621/562949953421312), (-13783446107421/140737488355328)), (277311/1125899906842624), by norm_num⟩
  | 3 => ⟨((978539894960583/1125899906842624), (-206728575574277/1125899906842624)), (574219/1125899906842624), by norm_num⟩
  | 4 => ⟨((812508835386527/1125899906842624), (-89835764883885/281474976710656)), (302249/281474976710656), by norm_num⟩
  | 5 => ⟨((943322172632591/2251799813685248), (-1037283719566961/2251799813685248)), (5033359/2251799813685248), by norm_num⟩
  | 6 => ⟨((-82645354337173/2251799813685248), (-869076128376563/2251799813685248)), (17708681/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-17760513005/536870912)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-5602818047/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-421526571729051/2251799813685248), (1070145088382245/4503599627370496)), (3803475/1125899906842624), by norm_num⟩
  | 1 => ⟨((8916624595/34359738368), (-11318482221/34359738368)), (163/34359738368), by norm_num⟩
  | 2 => ⟨((-12361066397/68719476736), (980671755/4294967296)), (57/17179869184), by norm_num⟩
  | 3 => ⟨((1428006387/17179869184), (-7250665195/68719476736)), (213/137438953472), by norm_num⟩
  | 4 => ⟨((-989818601/34359738368), (5025778137/137438953472)), (149/274877906944), by norm_num⟩
  | 5 => ⟨((8781951649/1099511627776), (-11147532627/1099511627776)), (167/1099511627776), by norm_num⟩
  | 6 => ⟨((-8116246701/4398046511104), (2575626937/1099511627776)), (39/1099511627776), by norm_num⟩
  | 7 => ⟨((12858865183/35184372088832), (-2040329771/4398046511104)), (249/35184372088832), by norm_num⟩
  | 8 => ⟨((-8913086147/140737488355328), (5656995313/70368744177664)), (87/70368744177664), by norm_num⟩
  | 9 => ⟨((10983254281/1125899906842624), (-6970898403/562949953421312)), (27/140737488355328), by norm_num⟩
  | 10 => ⟨((-12180818781/9007199254740992), (15461947437/9007199254740992)), (121/4503599627370496), by norm_num⟩
  | 11 => ⟨((12280873011/72057594037927936), (-15588953123/72057594037927936)), (123/36028797018963968), by norm_num⟩
  | 12 => ⟨((-5674968335/288230376151711744), (7203625937/288230376151711744)), (229/576460752303423488), by norm_num⟩
  | 13 => ⟨((9682678895/4611686018427387904), (-12290887405/4611686018427387904)), (99/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-7670310373/36893488147419103232), (4868225115/18446744073709551616)), (79/18446744073709551616), by norm_num⟩
  | 15 => ⟨((2835548805/147573952589676412928), (-7198712561/295147905179352825856)), (59/147573952589676412928), by norm_num⟩
  | 16 => ⟨((-3930905319/2361183241434822606848), (9979534631/4722366482869645213696)), (165/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (182206852587/633825300114114700748351602688)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222514830931751/79228162514264337593543950336), (3455122046449/633825300114114700748351602688)), (5785/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945629958945641/19807040628566084398385987584), (1943292395571/19807040628566084398385987584)), (6509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945564600105063/1237940039285380274899124224), (4128990844287/2475880078570760549798248448)), (6917/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772794695909355/154742504910672534362390528), (4128422101641/154742504910672534362390528)), (6919/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387764095668495/2417851639229258349412352), (3869791413825/9671406556917033397649408)), (6489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630051485416135/302231454903657293676544), (3385463161033/604462909807314587353088)), (5679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889926261450981/75557863725914323419136), (687530560477/9444732965739290427392)), (577/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1299138803146453/4722366482869645213696), (4124191812795/4722366482869645213696)), (6927/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811822544187209/295147905179352825856), (2834576198329/295147905179352825856)), (4765/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913108819105801/36893488147419103232), (7084023342805/73786976294838206464)), (11919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825738383773603/9223372036854775808), (3983101229377/4611686018427387904)), (3355/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596981380021077/1152921504606846976), (7962047384137/1152921504606846976)), (13433/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197195649898937/144115188075855872), (6962116563175/144115188075855872)), (11769/144115188075855872), by norm_num⟩
  | 4 => ⟨((186943420448351/4503599627370496), (2608455990901/9007199254740992)), (8841/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494123524921003/9007199254740992), (13025913504217/9007199254740992)), (22153/9007199254740992), by norm_num⟩
  | 2 => ⟨((559403772573755/1125899906842624), (13001359096157/2251799813685248)), (11115/1125899906842624), by norm_num⟩
  | 1 => ⟨((557610764955063/562949953421312), (9720318218419/562949953421312)), (33537/1125899906842624), by norm_num⟩
  | 0 => ⟨((552192485081371/562949953421312), (9658892482639/281474976710656)), (33923/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552192485081371/562949953421312), (9658892482639/281474976710656)), (129405977489280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1081955374233613/1125899906842624), (75794557732283/1125899906842624)), (34439/281474976710656), by norm_num⟩
  | 2 => ⟨((517311800885507/562949953421312), (36418125882111/281474976710656)), (283307/1125899906842624), by norm_num⟩
  | 3 => ⟨((232974865856357/281474976710656), (267725770938653/1125899906842624)), (296995/562949953421312), by norm_num⟩
  | 4 => ⟨((707664612693919/1125899906842624), (443189489166133/1125899906842624)), (316443/281474976710656), by norm_num⟩
  | 5 => ⟨((135168445659371/562949953421312), (1114235879387477/2251799813685248)), (2587653/1125899906842624), by norm_num⟩
  | 6 => ⟨((-421526571729051/2251799813685248), (1070145088382245/4503599627370496)), (3803475/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-5602818047/134217728)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-26018681267/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-32178396138593/562949953421312), (1093942742334113/4503599627370496)), (5928995/2251799813685248), by norm_num⟩
  | 1 => ⟨((6321915369/68719476736), (-6716281599/17179869184)), (147/34359738368), by norm_num⟩
  | 2 => ⟨((-5087365137/68719476736), (2702359559/8589934592)), (119/34359738368), by norm_num⟩
  | 3 => ⟨((5458532217/137438953472), (-5799039903/34359738368)), (257/137438953472), by norm_num⟩
  | 4 => ⟨((-1098146087/68719476736), (18666389351/274877906944)), (13/17179869184), by norm_num⟩
  | 5 => ⟨((5655673427/1099511627776), (-24033915767/1099511627776)), (135/549755813888), by norm_num⟩
  | 6 => ⟨((-6068303489/4398046511104), (25787396813/4398046511104)), (73/1099511627776), by norm_num⟩
  | 7 => ⟨((2790445057/8796093022208), (-23716122339/17592186044416)), (135/8796093022208), by norm_num⟩
  | 8 => ⟨((-4491048067/70368744177664), (9542406607/35184372088832)), (219/70368744177664), by norm_num⟩
  | 9 => ⟨((401559057/35184372088832), (-13651476417/281474976710656)), (79/140737488355328), by norm_num⟩
  | 10 => ⟨((-4136219971/2251799813685248), (17576962965/2251799813685248)), (205/2251799813685248), by norm_num⟩
  | 11 => ⟨((4841446717/18014398509481984), (-10286920211/9007199254740992)), (121/9007199254740992), by norm_num⟩
  | 12 => ⟨((-1298667983/36028797018963968), (11037439593/72057594037927936)), (131/72057594037927936), by norm_num⟩
  | 13 => ⟨((5144924277/1152921504606846976), (-21863475369/1152921504606846976)), (131/576460752303423488), by norm_num⟩
  | 14 => ⟨((-2365838911/4611686018427387904), (10053687473/4611686018427387904)), (243/9223372036854775808), by norm_num⟩
  | 15 => ⟨((4061515561/73786976294838206464), (-8629752415/36893488147419103232)), (211/73786976294838206464), by norm_num⟩
  | 16 => ⟨((-3268378563/590295810358705651712), (27778101423/1180591620717411303424)), (171/590295810358705651712), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (2347191572431/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779823812383497/633825300114114700748351602688), (1390463129941/316912650057057350374175801344)), (5781/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945464200669047/19807040628566084398385987584), (3128149981147/39614081257132168796771975168)), (813/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((14771696690043/19342813113834066795298816), (1661593885867/1237940039285380274899124224)), (27/9671406556917033397649408), by norm_num⟩
  | 14 => ⟨((443110727747641/38685626227668133590597632), (3322657269817/154742504910672534362390528)), (6913/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550726838151163/9671406556917033397649408), (3114427585221/9671406556917033397649408)), (3241/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259814873142949/604462909807314587353088), (1362280295739/302231454903657293676544)), (2837/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944729289185733/37778931862957161709568), (1106588609991/18889465931478580854784)), (9223/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649394228447285/2361183241434822606848), (1659420750395/2361183241434822606848)), (865/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623164038091215/590295810358705651712), (4561905266647/590295810358705651712)), (4759/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825617338585915/73786976294838206464), (5700129304637/73786976294838206464)), (93/576460752303423488), by norm_num⟩
  | 7 => ⟨((1825064439084861/9223372036854775808), (6409549262229/9223372036854775808)), (1675/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1596309174621391/1152921504606846976), (6405680022755/1152921504606846976)), (6705/576460752303423488), by norm_num⟩
  | 5 => ⟨((299152356306377/36028797018963968), (2800309262899/72057594037927936)), (5873/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494671932554753/36028797018963968), (4196114152685/18014398509481984)), (8821/18014398509481984), by norm_num⟩
  | 3 => ⟨((746518031153105/4503599627370496), (5237534591669/4503599627370496)), (22093/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117730303207375/2251799813685248), (10452260709145/2251799813685248)), (22155/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113631153558451/1125899906842624), (7810712693877/562949953421312)), (8347/281474976710656), by norm_num⟩
  | 0 => ⟨((1101305772376099/1125899906842624), (31015322146503/1125899906842624)), (16849/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101305772376099/1125899906842624), (31015322146503/1125899906842624)), (64273835302257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1076394488262857/1125899906842624), (60675648171667/1125899906842624)), (67781/562949953421312), by norm_num⟩
  | 2 => ⟨((1025795946036117/1125899906842624), (116015522990691/1125899906842624)), (273815/1125899906842624), by norm_num⟩
  | 3 => ⟨((461318859259187/562949953421312), (26425140555977/140737488355328)), (277685/562949953421312), by norm_num⟩
  | 4 => ⟨((716378000666919/1125899906842624), (692944905554611/2251799813685248)), (2237539/2251799813685248), by norm_num⟩
  | 5 => ⟨((698382292984707/2251799813685248), (881802161980153/2251799813685248)), (2112239/1125899906842624), by norm_num⟩
  | 6 => ⟨((-32178396138593/562949953421312), (1093942742334113/4503599627370496)), (5928995/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-26018681267/536870912)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-28966149099/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-820385205181589/4503599627370496), (249566188048479/2251799813685248)), (5369249/2251799813685248), by norm_num⟩
  | 1 => ⟨((11214698485/34359738368), (-6823159495/34359738368)), (37/8589934592), by norm_num⟩
  | 2 => ⟨((-20094042205/68719476736), (12225460635/68719476736)), (267/68719476736), by norm_num⟩
  | 3 => ⟨((3000307533/17179869184), (-7301694953/68719476736)), (161/68719476736), by norm_num⟩
  | 4 => ⟨((-5375829433/68719476736), (6541440537/137438953472)), (73/68719476736), by norm_num⟩
  | 5 => ⟨((15411509267/549755813888), (-2344137605/137438953472)), (211/549755813888), by norm_num⟩
  | 6 => ⟨((-9204572555/1099511627776), (11200348669/2199023255552)), (127/1099511627776), by norm_num⟩
  | 7 => ⟨((18848434327/8796093022208), (-1433452199/1099511627776)), (131/4398046511104), by norm_num⟩
  | 8 => ⟨((-16885930343/35184372088832), (10273606205/35184372088832)), (59/8796093022208), by norm_num⟩
  | 9 => ⟨((6723450131/70368744177664), (-1022657289/17592186044416)), (95/70368744177664), by norm_num⟩
  | 10 => ⟨((-19274888701/1125899906842624), (11727077641/1125899906842624)), (137/562949953421312), by norm_num⟩
  | 11 => ⟨((6279266245/2251799813685248), (-7640764513/4503599627370496)), (45/1125899906842624), by norm_num⟩
  | 12 => ⟨((-15001246339/36028797018963968), (4563470723/18014398509481984)), (217/36028797018963968), by norm_num⟩
  | 13 => ⟨((8270346209/144115188075855872), (-5031779619/144115188075855872)), (241/288230376151711744), by norm_num⟩
  | 14 => ⟨((-8467697791/1152921504606846976), (5151850731/1152921504606846976)), (249/2305843009213693952), by norm_num⟩
  | 15 => ⟨((8091774773/9223372036854775808), (-4923134577/9223372036854775808)), (15/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-14498514073/147573952589676412928), (8821072997/147573952589676412928)), (217/147573952589676412928), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (3380291110581/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779576717208833/633825300114114700748351602688), (2001946404841/316912650057057350374175801344)), (1447/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945325099708927/19807040628566084398385987584), (1125935779717/9903520314283042199192993792)), (6513/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890481303667837/2475880078570760549798248448), (299029379787/154742504910672534362390528)), (3461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772146720012783/154742504910672534362390528), (2391809198639/77371252455336267181195264)), (1731/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775224410543065/4835703278458516698824704), (4483737353255/9671406556917033397649408)), (6493/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39361602200101/18889465931478580854784), (245147831671/37778931862957161709568)), (1421/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889062090987725/75557863725914323419136), (3186073507223/37778931862957161709568)), (1155/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298490537999369/4722366482869645213696), (4777625764343/4722366482869645213696)), (3467/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811376750631387/295147905179352825856), (3283411594043/295147905179352825856)), (2385/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825102821530495/73786976294838206464), (1025613843783/9223372036854775808)), (11933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824483759059179/9223372036854775808), (576596857623/576460752303423488)), (13437/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797863093914883/576460752303423488), (4609665718831/576460752303423488)), (3363/288230376151711744), by norm_num⟩
  | 5 => ⟨((598048360848523/72057594037927936), (4029959932981/72057594037927936)), (11787/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493897709647867/36028797018963968), (6037945303355/18014398509481984)), (17715/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492059268581631/9007199254740992), (3767596172291/2251799813685248)), (11101/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116740043263265/2251799813685248), (15033672021281/2251799813685248)), (5573/562949953421312), by norm_num⟩
  | 1 => ⟨((139014036915415/140737488355328), (22458745193597/1125899906842624)), (33661/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098135364166089/1125899906842624), (1392204920343/35184372088832)), (68219/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098135364166089/1125899906842624), (1392204920343/35184372088832)), (260234837058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1069292677391861/1125899906842624), (86903893202059/1125899906842624)), (138473/1125899906842624), by norm_num⟩
  | 2 => ⟨((504411864841261/562949953421312), (20633649597325/140737488355328)), (17775/70368744177664), by norm_num⟩
  | 3 => ⟨((879720721021313/1125899906842624), (295809106542829/1125899906842624)), (593047/1125899906842624), by norm_num⟩
  | 4 => ⟨((152412642391429/281474976710656), (462260275377929/1125899906842624)), (619189/562949953421312), by norm_num⟩
  | 5 => ⟨((280645293278999/2251799813685248), (1001215964080015/2251799813685248)), (4715983/2251799813685248), by norm_num⟩
  | 6 => ⟨((-820385205181589/4503599627370496), (249566188048479/2251799813685248)), (5369249/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-28966149099/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-31458197643/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-385247465840509/4503599627370496), (-373641341245515/2251799813685248)), (9294251/4503599627370496), by norm_num⟩
  | 1 => ⟨((5719428663/34359738368), (22188491151/68719476736)), (139/34359738368), by norm_num⟩
  | 2 => ⟨((-5564747141/34359738368), (-10794202531/34359738368)), (17/4294967296), by norm_num⟩
  | 3 => ⟨((3609499313/34359738368), (14003032171/68719476736)), (89/34359738368), by norm_num⟩
  | 4 => ⟨((-3511880673/68719476736), (-6812160605/68719476736)), (175/137438953472), by norm_num⟩
  | 5 => ⟨((5467043395/274877906944), (21209363933/549755813888)), (275/549755813888), by norm_num⟩
  | 6 => ⟨((-886531269/137438953472), (-6878586089/549755813888)), (45/274877906944), by norm_num⟩
  | 7 => ⟨((7886218029/4398046511104), (7648634561/2199023255552)), (101/2199023255552), by norm_num⟩
  | 8 => ⟨((-3836467925/8796093022208), (-14883555619/17592186044416)), (99/8796093022208), by norm_num⟩
  | 9 => ⟨((6635930553/70368744177664), (6436013763/35184372088832)), (173/70368744177664), by norm_num⟩
  | 10 => ⟨((-10330339689/562949953421312), (-10019123601/281474976710656)), (271/562949953421312), by norm_num⟩
  | 11 => ⟨((7309786489/2251799813685248), (14179137673/2251799813685248)), (193/2251799813685248), by norm_num⟩
  | 12 => ⟨((-9482791811/18014398509481984), (-9197109301/9007199254740992)), (63/4503599627370496), by norm_num⟩
  | 13 => ⟨((5677741793/72057594037927936), (22026767177/144115188075855872)), (19/9007199254740992), by norm_num⟩
  | 14 => ⟨((-6313357359/576460752303423488), (-6123158543/288230376151711744)), (85/288230376151711744), by norm_num⟩
  | 15 => ⟨((3276060309/2305843009213693952), (12709457443/4611686018427387904)), (89/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-1593729751/9223372036854775808), (-6182865557/18446744073709551616)), (175/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-2666174426419/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779374837978155/633825300114114700748351602688), (-1578671175849/316912650057057350374175801344)), (5783/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890423307810529/39614081257132168796771975168), (-887868686053/9903520314283042199192993792)), (6507/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890240510321307/2475880078570760549798248448), (-3772794637429/2475880078570760549798248448)), (6915/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442976560104369/38685626227668133590597632), (-943016628099/38685626227668133590597632)), (6917/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775111852348701/4835703278458516698824704), (-1767769411849/4835703278458516698824704)), (3243/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629687313325119/302231454903657293676544), (-3092823052775/604462909807314587353088)), (5677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944371584559975/37778931862957161709568), (-5024387543801/75557863725914323419136)), (2307/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298251892492975/4722366482869645213696), (-941755555579/1180591620717411303424)), (1731/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101401640637081/36893488147419103232), (-5177594801511/590295810358705651712)), (9525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824695086437253/73786976294838206464), (-6468903164745/73786976294838206464)), (11913/73786976294838206464), by norm_num⟩
  | 7 => ⟨((7125105009617/36028797018963968), (-7273268137901/9223372036854775808)), (13411/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595271590501249/1152921504606846976), (-3633980086385/576460752303423488)), (13423/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195701509829991/144115188075855872), (-3176748178499/72057594037927936)), (11759/144115188075855872), by norm_num⟩
  | 4 => ⟨((746655002491809/18014398509481984), (-4759156809761/18014398509481984)), (69/140737488355328), by norm_num⟩
  | 3 => ⟨((1491333566718207/9007199254740992), (-1484628493801/1125899906842624)), (22127/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116027696809087/2251799813685248), (-11845761937481/2251799813685248)), (11099/1125899906842624), by norm_num⟩
  | 1 => ⟨((34721157219773/35184372088832), (-8845291698463/562949953421312)), (523/17592186044416), by norm_num⟩
  | 0 => ⟨((1096197058453945/1125899906842624), (-35069563324615/1125899906842624)), (16913/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096197058453945/1125899906842624), (-35069563324615/1125899906842624)), (64517975927257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((533092732931141/562949953421312), (-8536094532931/140737488355328)), (67975/562949953421312), by norm_num⟩
  | 2 => ⟨((125687026717887/140737488355328), (-32333460091527/281474976710656)), (68493/281474976710656), by norm_num⟩
  | 3 => ⟨((110388963923997/140737488355328), (-231005768819471/1125899906842624)), (1104581/2251799813685248), by norm_num⟩
  | 4 => ⟨((1290563442015351/2251799813685248), (-362383722751471/1125899906842624)), (546511/562949953421312), by norm_num⟩
  | 5 => ⟨((253189946298893/1125899906842624), (-830765118146237/2251799813685248)), (1956481/1125899906842624), by norm_num⟩
  | 6 => ⟨((-385247465840509/4503599627370496), (-373641341245515/2251799813685248)), (9294251/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-31458197643/536870912)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-481443911/268435456), (-16808454141/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((731952624108415/4503599627370496), (5006559987321/140737488355328)), (7019423/4503599627370496), by norm_num⟩
  | 1 => ⟨((-11612340493/34359738368), (-5083422275/68719476736)), (225/68719476736), by norm_num⟩
  | 2 => ⟨((24147183217/68719476736), (2642669863/34359738368)), (237/68719476736), by norm_num⟩
  | 3 => ⟨((-16737551965/68719476736), (-3663518329/68719476736)), (167/68719476736), by norm_num⟩
  | 4 => ⟨((17402380431/137438953472), (3809036101/137438953472)), (175/137438953472), by norm_num⟩
  | 5 => ⟨((-14474893117/274877906944), (-3168267161/274877906944)), (147/274877906944), by norm_num⟩
  | 6 => ⟨((10033231353/549755813888), (1098037725/274877906944)), (103/549755813888), by norm_num⟩
  | 7 => ⟨((-23844020655/4398046511104), (-5218983451/4398046511104)), (31/549755813888), by norm_num⟩
  | 8 => ⟨((24791123535/17592186044416), (5426285497/17592186044416)), (261/17592186044416), by norm_num⟩
  | 9 => ⟨((-22911863175/70368744177664), (-2507476329/35184372088832)), (61/17592186044416), by norm_num⟩
  | 10 => ⟨((19057552033/281474976710656), (4171320355/281474976710656)), (103/140737488355328), by norm_num⟩
  | 11 => ⟨((-14410569229/1125899906842624), (-1577093969/562949953421312)), (79/562949953421312), by norm_num⟩
  | 12 => ⟨((19977290863/9007199254740992), (546579119/1125899906842624)), (221/9007199254740992), by norm_num⟩
  | 13 => ⟨((-3195508347/9007199254740992), (-2797733725/36028797018963968)), (143/36028797018963968), by norm_num⟩
  | 14 => ⟨((7594140347/144115188075855872), (415551695/36028797018963968)), (43/72057594037927936), by norm_num⟩
  | 15 => ⟨((-16844342305/2305843009213693952), (-1843446309/1152921504606846976)), (193/2305843009213693952), by norm_num⟩
  | 16 => ⟨((8756706283/9223372036854775808), (3833338835/18446744073709551616)), (203/18446744073709551616), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (280689270145/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779202464618407/633825300114114700748351602688), (332335263471/633825300114114700748351602688)), (5765/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945114860883821/19807040628566084398385987584), (186909144689/19807040628566084398385987584)), (12971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472508812678295/618970019642690137449562112), (49638659083/309485009821345068724781056)), (13783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771701459292333/154742504910672534362390528), (397027556059/154742504910672534362390528)), (6891/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550032230530135/9671406556917033397649408), (372126533613/9671406556917033397649408)), (6461/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259207594609523/604462909807314587353088), (325523943385/604462909807314587353088)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888472693684295/75557863725914323419136), (528813764285/75557863725914323419136)), (9187/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162256233499295/590295810358705651712), (396468066585/4722366482869645213696)), (13781/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811074908756447/295147905179352825856), (272456265325/295147905179352825856)), (9475/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824351570132557/73786976294838206464), (170198564391/18446744073709551616)), (23689/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823643207183493/9223372036854775808), (765417533285/9223372036854775808)), (6663/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199361423269071/144115188075855872), (764822977015/1152921504606846976)), (13327/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195372729260273/144115188075855872), (668551849819/144115188075855872)), (23325/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492824614215829/36028797018963968), (1001492814863/36028797018963968)), (17497/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490740406594773/9007199254740992), (156191665329/1125899906842624)), (5469/1125899906842624), by norm_num⟩
  | 2 => ⟨((2230909661359517/4503599627370496), (1246041235623/2251799813685248)), (87533/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220536420162041/2251799813685248), (3720711873793/2251799813685248)), (8211/140737488355328), by norm_num⟩
  | 0 => ⟨((547389896701919/562949953421312), (1843016814357/562949953421312)), (131531/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547389896701919/562949953421312), (1843016814357/562949953421312)), (501750950339889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((532253889496487/562949953421312), (14336603493785/2251799813685248)), (513305/2251799813685248), by norm_num⟩
  | 2 => ⟨((2012835102126011/2251799813685248), (27109738353687/2251799813685248)), (977169/2251799813685248), by norm_num⟩
  | 3 => ⟨((899451671018575/1125899906842624), (48465616380391/2251799813685248)), (885235/1125899906842624), by norm_num⟩
  | 4 => ⟨((1436053195478813/2251799813685248), (38717899677721/1125899906842624)), (181561/140737488355328), by norm_num⟩
  | 5 => ⟨((1826319075724475/4503599627370496), (98767151887137/2251799813685248)), (7810019/4503599627370496), by norm_num⟩
  | 6 => ⟨((731952624108415/4503599627370496), (5006559987321/140737488355328)), (7019423/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-16808454141/268435456)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile053Terms0
