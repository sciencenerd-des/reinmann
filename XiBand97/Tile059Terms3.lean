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
namespace Reinmann.XiBand97.Tile059Terms3
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
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2862621597/1073741824), (-102726368773/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((22961397466135/2251799813685248), (-619481968837811/9007199254740992)), (3029999/9007199254740992), by norm_num⟩
  | 1 => ⟨((-8663898237/274877906944), (116872867723/549755813888)), (287/274877906944), by norm_num⟩
  | 2 => ⟨((13390238631/274877906944), (-90314748945/274877906944)), (223/137438953472), by norm_num⟩
  | 3 => ⟨((-6898299345/137438953472), (93055574385/274877906944)), (231/137438953472), by norm_num⟩
  | 4 => ⟨((5330734033/137438953472), (-71909682737/274877906944)), (359/274877906944), by norm_num⟩
  | 5 => ⟨((-13182020163/549755813888), (88910352859/549755813888)), (223/274877906944), by norm_num⟩
  | 6 => ⟨((13582061315/1099511627776), (-45804279205/549755813888)), (461/1099511627776), by norm_num⟩
  | 7 => ⟨((-2998766295/549755813888), (40452277591/1099511627776)), (409/2199023255552), by norm_num⟩
  | 8 => ⟨((4634656963/2199023255552), (-62519853685/4398046511104)), (159/2199023255552), by norm_num⟩
  | 9 => ⟨((-6367076191/8796093022208), (85889565297/17592186044416)), (439/17592186044416), by norm_num⟩
  | 10 => ⟨((1968090281/8796093022208), (-53097658527/35184372088832)), (545/70368744177664), by norm_num⟩
  | 11 => ⟨((-17697310867/281474976710656), (14920646971/35184372088832)), (615/281474976710656), by norm_num⟩
  | 12 => ⟨((9117189867/562949953421312), (-15373451073/140737488355328)), (159/281474976710656), by norm_num⟩
  | 13 => ⟨((-2167816995/562949953421312), (116972282883/4503599627370496)), (607/4503599627370496), by norm_num⟩
  | 14 => ⟨((15316147115/18014398509481984), (-103304654931/18014398509481984)), (269/9007199254740992), by norm_num⟩
  | 15 => ⟨((-12624762921/72057594037927936), (85151753073/72057594037927936)), (223/36028797018963968), by norm_num⟩
  | 16 => ⟨((4877959769/144115188075855872), (-16450480233/72057594037927936)), (173/144115188075855872), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (-1854406593643/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888927629257109/316912650057057350374175801344), (-1096225894761/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888714270267913/39614081257132168796771975168), (-616484721591/9903520314283042199192993792)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944212632137451/1237940039285380274899124224), (-1309673789821/1237940039285380274899124224)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770091676305909/154742504910672534362390528), (-2618546386159/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548523275178613/9671406556917033397649408), (-2454036283197/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157235934363731/75557863725914323419136), (-268303893443/75557863725914323419136)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886327904682499/75557863725914323419136), (-871589122577/18889465931478580854784)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296441631137697/4722366482869645213696), (-2613373259495/4722366482869645213696)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619939068675835/590295810358705651712), (-1795562106317/295147905179352825856)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821588999586433/73786976294838206464), (-560688962155/9223372036854775808)), (5945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910268252884299/4611686018427387904), (-5041538497573/9223372036854775808)), (6691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591786173376947/1152921504606846976), (-5035716782641/1152921504606846976)), (837/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192657343590391/144115188075855872), (-549963872487/18014398509481984)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((744377444344811/18014398509481984), (-6586504596343/36028797018963968)), (2201/9007199254740992), by norm_num⟩
  | 3 => ⟨((371414780444091/2251799813685248), (-8210318605875/9007199254740992)), (11021/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110382362660243/2251799813685248), (-4088096252861/1125899906842624)), (5523/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102681579978417/1125899906842624), (-12179295131073/1125899906842624)), (33261/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159389994630523/2251799813685248), (-12010269713199/562949953421312)), (16755/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159389994630523/2251799813685248), (-12010269713199/562949953421312)), (63915254833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1034873787476147/1125899906842624), (-46069559281207/1125899906842624)), (16425/281474976710656), by norm_num⟩
  | 2 => ⟨((1898643645348949/2251799813685248), (-169379814354541/2251799813685248)), (252307/2251799813685248), by norm_num⟩
  | 3 => ⟨((794066628121019/1125899906842624), (-142815496395447/1125899906842624)), (57929/281474976710656), by norm_num⟩
  | 4 => ⟨((541918104954681/1125899906842624), (-201447782306307/1125899906842624)), (771261/2251799813685248), by norm_num⟩
  | 5 => ⟨((449585299622767/2251799813685248), (-96960839743649/562949953421312)), (2036875/4503599627370496), by norm_num⟩
  | 6 => ⟨((22961397466135/2251799813685248), (-619481968837811/9007199254740992)), (3029999/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-102726368773/1073741824)), (1/536870912), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1451894239/536870912), (-26050914859/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1135524430376329/18014398509481984), (-404428222466107/18014398509481984)), (3343633/9007199254740992), by norm_num⟩
  | 1 => ⟨((13581963667/68719476736), (2418675141/34359738368)), (161/137438953472), by norm_num⟩
  | 2 => ⟨((-42586168519/137438953472), (-30334967659/274877906944)), (507/274877906944), by norm_num⟩
  | 3 => ⟨((22254780845/68719476736), (31705038545/274877906944)), (133/68719476736), by norm_num⟩
  | 4 => ⟨((-8722467077/34359738368), (-24852741243/274877906944)), (419/274877906944), by norm_num⟩
  | 5 => ⟨((21879396055/137438953472), (31170250567/549755813888)), (33/34359738368), by norm_num⟩
  | 6 => ⟨((-45735146519/549755813888), (-32578046787/1099511627776)), (277/549755813888), by norm_num⟩
  | 7 => ⟨((81944164215/2199023255552), (7296305519/549755813888)), (499/2199023255552), by norm_num⟩
  | 8 => ⟨((-64233863231/4398046511104), (-22877523753/4398046511104)), (393/4398046511104), by norm_num⟩
  | 9 => ⟨((89513291835/17592186044416), (3985130189/2199023255552)), (275/8796093022208), by norm_num⟩
  | 10 => ⟨((-1754177555/1099511627776), (-4998141063/8796093022208)), (347/35184372088832), by norm_num⟩
  | 11 => ⟨((64002485265/140737488355328), (22795116209/140737488355328)), (199/70368744177664), by norm_num⟩
  | 12 => ⟨((-66893140785/562949953421312), (-23824651675/562949953421312)), (209/281474976710656), by norm_num⟩
  | 13 => ⟨((1008380077/35184372088832), (22985248469/2251799813685248)), (405/2251799813685248), by norm_num⟩
  | 14 => ⟨((-3613451313/562949953421312), (-5147865259/2251799813685248)), (365/9007199254740992), by norm_num⟩
  | 15 => ⟨((96682288567/72057594037927936), (34434350387/72057594037927936)), (613/72057594037927936), by norm_num⟩
  | 16 => ⟨((-37893344573/144115188075855872), (-26992176617/288230376151711744)), (241/144115188075855872), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (-3646584178519/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888894411818463/316912650057057350374175801344), (-538882199813/79228162514264337593543950336)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472159785819419/9903520314283042199192993792), (-4848785027139/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888344919719593/2475880078570760549798248448), (-1287602676461/618970019642690137449562112)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110625671564551/9671406556917033397649408), (-5148809761525/154742504910672534362390528)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193555847406609/1208925819614629174706176), (-4825308604243/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257819918714421/604462909807314587353088), (-4220444993939/604462909807314587353088)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943108480197037/37778931862957161709568), (-6855036638891/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324089351100213/1180591620717411303424), (-5138490401447/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809910802094739/295147905179352825856), (-7060897342715/590295810358705651712)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910719847020949/36893488147419103232), (-2204833703321/18446744073709551616)), (5971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820365140726619/9223372036854775808), (-4956212766671/4611686018427387904)), (1681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198951321630213/144115188075855872), (-4950388290787/576460752303423488)), (1683/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192498942441023/144115188075855872), (-8650086419505/144115188075855872)), (5899/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488507819812727/36028797018963968), (-12948973407913/36028797018963968)), (8867/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485333795747913/9007199254740992), (-8070255393681/4503599627370496)), (11117/9007199254740992), by norm_num⟩
  | 2 => ⟨((277508114117827/562949953421312), (-16072086684063/2251799813685248)), (11165/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102095809934335/1125899906842624), (-23937541873841/1125899906842624)), (4217/281474976710656), by norm_num⟩
  | 0 => ⟨((2156566073028661/2251799813685248), (-94391129246135/2251799813685248)), (34223/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156566073028661/2251799813685248), (-94391129246135/2251799813685248)), (130550388816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2061403288981145/2251799813685248), (-180798226991533/2251799813685248)), (68421/1125899906842624), by norm_num⟩
  | 2 => ⟨((1872588982072099/2251799813685248), (-82755593436247/562949953421312)), (272519/2251799813685248), by norm_num⟩
  | 3 => ⟨((1508577122714373/2251799813685248), (-137638533880095/562949953421312)), (533375/2251799813685248), by norm_num⟩
  | 4 => ⟨((876052598925351/2251799813685248), (-737679582895575/2251799813685248)), (487739/1125899906842624), by norm_num⟩
  | 5 => ⟨((99163783434829/2251799813685248), (-1147963707683597/4503599627370496)), (2796271/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1135524430376329/18014398509481984), (-404428222466107/18014398509481984)), (3343633/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-26050914859/268435456)), (1/536870912), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-105618067265/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-162983964014211/4503599627370496), (480912738110143/9007199254740992)), (413429/1125899906842624), by norm_num⟩
  | 1 => ⟨((31614490425/274877906944), (-23321023093/137438953472)), (323/274877906944), by norm_num⟩
  | 2 => ⟨((-50236276195/274877906944), (4632216673/17179869184)), (515/274877906944), by norm_num⟩
  | 3 => ⟨((1663058229/8589934592), (-39257157175/137438953472)), (547/274877906944), by norm_num⟩
  | 4 => ⟨((-21141154299/137438953472), (15595169841/68719476736)), (109/68719476736), by norm_num⟩
  | 5 => ⟨((26875090559/274877906944), (-79299662797/549755813888)), (139/137438953472), by norm_num⟩
  | 6 => ⟨((-28470161497/549755813888), (10500774879/137438953472)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((25851344513/1099511627776), (-76278920745/2199023255552)), (135/549755813888), by norm_num⟩
  | 8 => ⟨((-41078482225/4398046511104), (30302314531/2199023255552)), (431/4398046511104), by norm_num⟩
  | 9 => ⟨((7252757099/2199023255552), (-2675066299/549755813888)), (153/4398046511104), by norm_num⟩
  | 10 => ⟨((-18439721983/17592186044416), (54409630067/35184372088832)), (391/35184372088832), by norm_num⟩
  | 11 => ⟨((42619948421/140737488355328), (-7859851511/17592186044416)), (227/70368744177664), by norm_num⟩
  | 12 => ⟨((-5643687097/70368744177664), (16652687467/140737488355328)), (483/562949953421312), by norm_num⟩
  | 13 => ⟨((22075004795/1125899906842624), (-65136168849/2251799813685248)), (237/1125899906842624), by norm_num⟩
  | 14 => ⟨((-40088887739/9007199254740992), (14786160779/2251799813685248)), (27/562949953421312), by norm_num⟩
  | 15 => ⟨((33974571529/36028797018963968), (-783186915/562949953421312)), (23/2251799813685248), by norm_num⟩
  | 16 => ⟨((-53986508591/288230376151711744), (79648325603/288230376151711744)), (587/288230376151711744), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (2822075033443/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777736295086797/633825300114114700748351602688), (3336105685719/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236072535300521/4951760157141521099596496896), (1876111326117/19807040628566084398385987584)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888282691785461/2475880078570760549798248448), (3985621162931/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769948867451125/154742504910672534362390528), (3984366783535/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193548642621867/1208925819614629174706176), (1867005762631/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257769856844837/604462909807314587353088), (3265928249343/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943068152973339/37778931862957161709568), (5304637274245/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162037190242689/590295810358705651712), (3976294900973/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619740253101809/590295810358705651712), (5463860011489/590295810358705651712)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14229214717341/576460752303423488), (1706127568363/18446744073709551616)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820254433613281/9223372036854775808), (3835135966697/4611686018427387904)), (6709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591502397058591/1152921504606846976), (3830576370197/576460752303423488)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192407128283263/144115188075855872), (3346630592061/72057594037927936)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((744187879513375/18014398509481984), (5009712948977/18014398509481984)), (4419/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485178582429267/9007199254740992), (12488532386311/9007199254740992)), (11073/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219783902221057/4503599627370496), (24870075717241/4503599627370496)), (5555/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203843043215725/2251799813685248), (18519276373167/1125899906842624)), (33517/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156157090511339/2251799813685248), (18254080550519/562949953421312)), (33895/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156157090511339/2251799813685248), (18254080550519/562949953421312)), (129299168113326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062209077126911/2251799813685248), (139830068270067/2251799813685248)), (134219/2251799813685248), by norm_num⟩
  | 2 => ⟨((1879897939446191/2251799813685248), (64028523825545/562949953421312)), (262507/2251799813685248), by norm_num⟩
  | 3 => ⟨((1540288711208851/2251799813685248), (427629807139679/2251799813685248)), (498019/2251799813685248), by norm_num⟩
  | 4 => ⟨((15193555177339/35184372088832), (73127433499039/281474976710656)), (435235/1125899906842624), by norm_num⟩
  | 5 => ⟨((267914460924933/2251799813685248), (1010508363692531/4503599627370496)), (1204083/2251799813685248), by norm_num⟩
  | 6 => ⟨((-162983964014211/4503599627370496), (480912738110143/9007199254740992)), (413429/1125899906842624), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-105618067265/1073741824)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-53487363893/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((694664763132185/18014398509481984), (440388016681473/9007199254740992)), (2155489/9007199254740992), by norm_num⟩
  | 1 => ⟨((-17059628391/137438953472), (-10815081333/68719476736)), (107/137438953472), by norm_num⟩
  | 2 => ⟨((54912825409/274877906944), (34812403847/137438953472)), (173/137438953472), by norm_num⟩
  | 3 => ⟨((-7364898591/34359738368), (-37352268383/137438953472)), (373/274877906944), by norm_num⟩
  | 4 => ⟨((47413388055/274877906944), (60116156851/274877906944)), (151/137438953472), by norm_num⟩
  | 5 => ⟨((-30523561717/274877906944), (-19350644397/137438953472)), (49/68719476736), by norm_num⟩
  | 6 => ⟨((8187629575/137438953472), (10381220241/137438953472)), (53/137438953472), by norm_num⟩
  | 7 => ⟨((-60239915205/2199023255552), (-76379105981/2199023255552)), (49/274877906944), by norm_num⟩
  | 8 => ⟨((48476201687/4398046511104), (30731857221/2199023255552)), (317/4398046511104), by norm_num⟩
  | 9 => ⟨((-34675305265/8796093022208), (-5495668459/1099511627776)), (57/2199023255552), by norm_num⟩
  | 10 => ⟨((44646200735/35184372088832), (28303798951/17592186044416)), (37/4398046511104), by norm_num⟩
  | 11 => ⟨((-6532298919/17592186044416), (-16564802581/35184372088832)), (87/35184372088832), by norm_num⟩
  | 12 => ⟨((56071090857/562949953421312), (4443336881/35184372088832)), (375/562949953421312), by norm_num⟩
  | 13 => ⟨((-13883529141/562949953421312), (-17603138053/562949953421312)), (373/2251799813685248), by norm_num⟩
  | 14 => ⟨((51073550075/9007199254740992), (8094616503/1125899906842624)), (345/9007199254740992), by norm_num⟩
  | 15 => ⟨((-43839844167/36028797018963968), (-55585206129/36028797018963968)), (149/18014398509481984), by norm_num⟩
  | 16 => ⟨((35278753639/144115188075855872), (44730469057/144115188075855872)), (121/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (588120051351/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888843506291161/316912650057057350374175801344), (695203525489/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888525122860883/39614081257132168796771975168), (1563834326705/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((14751753628037/19342813113834066795298816), (1661103643795/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442472766657689/38685626227668133590597632), (1660574798781/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193541925696539/1208925819614629174706176), (1556227206015/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314430822704109/151115727451828646838272), (1361137396273/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943030741802753/37778931862957161709568), (2210796176857/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648121072911385/2361183241434822606848), (828588550757/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619665312814243/590295810358705651712), (142320280845/36893488147419103232)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821247608372473/73786976294838206464), (2844166385593/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910076771952911/4611686018427387904), (3196611163629/9223372036854775808)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((198925573501423/144115188075855872), (3192770518235/1152921504606846976)), (6683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192325001428313/144115188075855872), (2789359492301/144115188075855872)), (2925/72057594037927936), by norm_num⟩
  | 4 => ⟨((744129728356401/18014398509481984), (521928103933/4503599627370496)), (8781/36028797018963968), by norm_num⟩
  | 3 => ⟨((742522602135047/4503599627370496), (5204239551289/9007199254740992)), (5493/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109776464466115/2251799813685248), (5181744617133/2251799813685248)), (22003/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101792643647737/1125899906842624), (15433228914635/2251799813685248)), (33083/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077995948784669/1125899906842624), (30421245704487/2251799813685248)), (66485/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077995948784669/1125899906842624), (30421245704487/2251799813685248)), (253620156295012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1031924681303847/1125899906842624), (1820431562517/70368744177664)), (64555/1125899906842624), by norm_num⟩
  | 2 => ⟨((945039754264655/1125899906842624), (13347888199077/281474976710656)), (60837/562949953421312), by norm_num⟩
  | 3 => ⟨((1581400751203785/2251799813685248), (179259771238205/2251799813685248)), (431595/2251799813685248), by norm_num⟩
  | 4 => ⟨((548160243934675/1125899906842624), (15736386465943/140737488355328)), (674921/2251799813685248), by norm_num⟩
  | 5 => ⟨((505606376418245/2251799813685248), (490334823770219/4503599627370496)), (808121/2251799813685248), by norm_num⟩
  | 6 => ⟨((694664763132185/18014398509481984), (440388016681473/9007199254740992)), (2155489/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-53487363893/536870912)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-3017330773/1073741824), (-108278172013/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((516218099799579/9007199254740992), (-331789266943009/18014398509481984)), (1398489/9007199254740992), by norm_num⟩
  | 1 => ⟨((-51327160761/274877906944), (32989546569/549755813888)), (35/68719476736), by norm_num⟩
  | 2 => ⟨((83614422391/274877906944), (-26870781867/274877906944)), (115/137438953472), by norm_num⟩
  | 3 => ⟨((-45403976687/137438953472), (911954181/8589934592)), (63/68719476736), by norm_num⟩
  | 4 => ⟨((18491317407/68719476736), (-371404345/4294967296)), (207/274877906944), by norm_num⟩
  | 5 => ⟨((-96394395563/549755813888), (30977822993/549755813888)), (17/34359738368), by norm_num⟩
  | 6 => ⟨((52343707745/549755813888), (-4205364077/137438953472)), (149/549755813888), by norm_num⟩
  | 7 => ⟨((-97451915995/2199023255552), (3914709183/274877906944)), (279/2199023255552), by norm_num⟩
  | 8 => ⟨((19844234383/1099511627776), (-25509000873/4398046511104)), (229/4398046511104), by norm_num⟩
  | 9 => ⟨((-28735302819/4398046511104), (9234531937/4398046511104)), (167/8796093022208), by norm_num⟩
  | 10 => ⟨((74897912507/35184372088832), (-24069597227/35184372088832)), (55/8796093022208), by norm_num⟩
  | 11 => ⟨((-88736228889/140737488355328), (28516753235/140737488355328)), (263/140737488355328), by norm_num⟩
  | 12 => ⟨((96370400047/562949953421312), (-30970111663/562949953421312)), (9/17592186044416), by norm_num⟩
  | 13 => ⟨((-3019077565/70368744177664), (3880908215/281474976710656)), (291/2251799813685248), by norm_num⟩
  | 14 => ⟨((89933222057/9007199254740992), (-3612678177/1125899906842624)), (273/9007199254740992), by norm_num⟩
  | 15 => ⟨((-19534074629/9007199254740992), (3138787803/4503599627370496)), (15/2251799813685248), by norm_num⟩
  | 16 => ⟨((31821950461/72057594037927936), (-20452947349/144115188075855872)), (197/144115188075855872), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-405035393903/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444408960135409/158456325028528675187087900672), (-59844562057/79228162514264337593543950336)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944233809036185/19807040628566084398385987584), (-538471232383/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472040862559667/618970019642690137449562112), (-571961799729/2475880078570760549798248448)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769830147648229/154742504910672534362390528), (-571777531783/154742504910672534362390528)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548278395064861/9671406556917033397649408), (-535845735037/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1257673507574523/604462909807314587353088), (-234334705675/302231454903657293676544)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942990387469399/37778931862957161709568), (-761221230747/75557863725914323419136)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296181779602835/4722366482869645213696), (-285297690319/2361183241434822606848)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619582577498029/590295810358705651712), (-392024070777/295147905179352825856)), (4739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821144590980277/73786976294838206464), (-122410008967/9223372036854775808)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820038200774407/9223372036854775808), (-550309249725/4611686018427387904)), (3333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591289932712269/1152921504606846976), (-1099280616215/1152921504606846976)), (6667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596112724923749/72057594037927936), (-480183804247/72057594037927936)), (5835/144115188075855872), by norm_num⟩
  | 4 => ⟨((744055833975507/18014398509481984), (-359387753143/9007199254740992)), (8753/36028797018963968), by norm_num⟩
  | 3 => ⟨((185607893707459/1125899906842624), (-895850164719/4503599627370496)), (5473/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109598409495517/2251799813685248), (-891933571927/1125899906842624)), (10951/2251799813685248), by norm_num⟩
  | 1 => ⟨((550767741164725/562949953421312), (-5312606253913/2251799813685248)), (32881/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155041691324041/2251799813685248), (-654390753703/140737488355328)), (65877/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2155041691324041/2251799813685248), (-654390753703/140737488355328)), (251300820357512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1031196253979205/1125899906842624), (-20040706610969/2251799813685248)), (63353/1125899906842624), by norm_num⟩
  | 2 => ⟨((472184649931319/562949953421312), (-36710015621693/2251799813685248)), (234353/2251799813685248), by norm_num⟩
  | 3 => ⟨((791807924304167/1125899906842624), (-61582404510227/2251799813685248)), (200389/1125899906842624), by norm_num⟩
  | 4 => ⟨((556010074297005/1125899906842624), (-86617710140229/2251799813685248)), (292815/1125899906842624), by norm_num⟩
  | 5 => ⟨((272911955960599/1125899906842624), (-42774956421803/1125899906842624)), (623465/2251799813685248), by norm_num⟩
  | 6 => ⟨((516218099799579/9007199254740992), (-331789266943009/18014398509481984)), (1398489/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-108278172013/1073741824)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-3052282179/1073741824), (-3422888055/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((12021684923413/2251799813685248), (-522646536415429/9007199254740992)), (1297431/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1209152599/68719476736), (105136579749/549755813888)), (131/137438953472), by norm_num⟩
  | 2 => ⟨((7970339425/274877906944), (-21657063469/68719476736)), (433/274877906944), by norm_num⟩
  | 3 => ⟨((-8756312837/274877906944), (47585432127/137438953472)), (239/137438953472), by norm_num⟩
  | 4 => ⟨((7214844665/274877906944), (-78416910745/274877906944)), (99/68719476736), by norm_num⟩
  | 5 => ⟨((-2377895103/137438953472), (103379738141/549755813888)), (131/137438953472), by norm_num⟩
  | 6 => ⟨((10449539125/1099511627776), (-113574250721/1099511627776)), (289/549755813888), by norm_num⟩
  | 7 => ⟨((-9839993223/2199023255552), (53474600365/1099511627776)), (273/1099511627776), by norm_num⟩
  | 8 => ⟨((4053876553/2199023255552), (-88121779639/4398046511104)), (113/1099511627776), by norm_num⟩
  | 9 => ⟨((-5938184797/8796093022208), (64541113341/8796093022208)), (333/8796093022208), by norm_num⟩
  | 10 => ⟨((1957128837/8796093022208), (-85086792289/35184372088832)), (441/35184372088832), by norm_num⟩
  | 11 => ⟨((-9382367087/140737488355328), (25493835167/35184372088832)), (265/70368744177664), by norm_num⟩
  | 12 => ⟨((10307583779/562949953421312), (-112031362399/562949953421312)), (585/562949953421312), by norm_num⟩
  | 13 => ⟨((-1306619793/281474976710656), (113611413645/2251799813685248)), (595/2251799813685248), by norm_num⟩
  | 14 => ⟨((9843212991/9007199254740992), (-106984195855/9007199254740992)), (281/4503599627370496), by norm_num⟩
  | 15 => ⟨((-4325549901/18014398509481984), (5876707613/2251799813685248)), (31/2251799813685248), by norm_num⟩
  | 16 => ⟨((7128153415/144115188075855872), (-77474678407/144115188075855872)), (205/72057594037927936), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (-1926625674001/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888791531602055/316912650057057350374175801344), (-17790400229/4951760157141521099596496896)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944204056576667/19807040628566084398385987584), (-2561189608013/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472025012190787/618970019642690137449562112), (-2720475003535/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442441636689745/38685626227668133590597632), (-2719587858757/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548218557547669/9671406556917033397649408), (-318583924895/1208925819614629174706176)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257620938281515/604462909807314587353088), (-139321604715/37778931862957161709568)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471473738450723/18889465931478580854784), (-3620596741027/75557863725914323419136)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1296117067683019/4722366482869645213696), (-1356952043835/2361183241434822606848)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619493037114297/590295810358705651712), (-3729111654081/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910515912386923/36893488147419103232), (-2328816393507/36893488147419103232)), (5947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909955092624989/4611686018427387904), (-654334506491/1152921504606846976)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198895059867459/144115188075855872), (-5228232113369/1152921504606846976)), (6697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298027641204205/36028797018963968), (-2283731712385/72057594037927936)), (5865/144115188075855872), by norm_num⟩
  | 4 => ⟨((743968063519961/18014398509481984), (-854592518477/4503599627370496)), (8807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484638128387727/9007199254740992), (-8520683675511/9007199254740992)), (5513/4503599627370496), by norm_num⟩
  | 2 => ⟨((554682525916491/1125899906842624), (-2120732659751/562949953421312)), (22101/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101164801031935/1125899906842624), (-12630394689095/1125899906842624)), (33281/2251799813685248), by norm_num⟩
  | 0 => ⟨((538349036822535/562949953421312), (-777720764237/35184372088832)), (67079/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538349036822535/562949953421312), (-777720764237/35184372088832)), (255886086470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32159257918157/35184372088832), (-95197998312841/2251799813685248)), (131261/2251799813685248), by norm_num⟩
  | 2 => ⟨((29331354956035/35184372088832), (-43506488808517/562949953421312)), (125525/1125899906842624), by norm_num⟩
  | 3 => ⟨((48483717401321/70368744177664), (-145076258619767/1125899906842624)), (457379/2251799813685248), by norm_num⟩
  | 4 => ⟨((1031574146221435/2251799813685248), (-199913652197715/1125899906842624)), (748135/2251799813685248), by norm_num⟩
  | 5 => ⟨((401582476522385/2251799813685248), (-732661061007415/4503599627370496)), (1902269/4503599627370496), by norm_num⟩
  | 6 => ⟨((12021684923413/2251799813685248), (-522646536415429/9007199254740992)), (1297431/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-3422888055/33554432)), (1/536870912), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile059Terms3
