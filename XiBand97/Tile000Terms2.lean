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
namespace Reinmann.XiBand97.Tile000Terms2
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
  | 0 => ⟨((69/80), (18227/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (18227/1280))
  have he : value ((69/80), (18227/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-662385127/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-86439819775963/4503599627370496), (-805872048061687/9007199254740992)), (281503789/18014398509481984), by norm_num⟩
  | 1 => ⟨((28569945/536870912), (266355485/1073741824)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((-316850829/4294967296), (-369247107/1073741824)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((292832345/4294967296), (1365027153/4294967296)), (245/4294967296), by norm_num⟩
  | 4 => ⟨((-101487957/2147483648), (-946164723/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((56276873/2147483648), (65583141/536870912)), (3/134217728), by norm_num⟩
  | 6 => ⟨((-104021749/8589934592), (-484893539/8589934592)), (179/17179869184), by norm_num⟩
  | 7 => ⟨((329610889/68719476736), (384117245/17179869184)), (143/34359738368), by norm_num⟩
  | 8 => ⟨((-114234429/68719476736), (-532499571/68719476736)), (25/17179869184), by norm_num⟩
  | 9 => ⟨((281533413/549755813888), (1312357605/549755813888)), (31/68719476736), by norm_num⟩
  | 10 => ⟨((-156115273/1099511627776), (-727725579/1099511627776)), (277/2199023255552), by norm_num⟩
  | 11 => ⟨((314795233/8796093022208), (91712897/549755813888)), (281/8796093022208), by norm_num⟩
  | 12 => ⟨((-290932571/35184372088832), (-678085717/17592186044416)), (131/17592186044416), by norm_num⟩
  | 13 => ⟨((248195805/140737488355328), (144619447/17592186044416)), (113/70368744177664), by norm_num⟩
  | 14 => ⟨((-98306413/281474976710656), (-7160183/4398046511104)), (181/562949953421312), by norm_num⟩
  | 15 => ⟨((290734135/4503599627370496), (1355246431/4503599627370496)), (135/2251799813685248), by norm_num⟩
  | 16 => ⟨((-100760773/9007199254740992), (-939385243/18014398509481984)), (189/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-290176016697/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778276897473383/633825300114114700748351602688), (-1372914870913/316912650057057350374175801344)), (92471/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889188427002459/39614081257132168796771975168), (-3088411757993/39614081257132168796771975168)), (104047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888928817949065/2475880078570760549798248448), (-1640318299175/1237940039285380274899124224)), (55285/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442648740636473/38685626227668133590597632), (-3279735883089/154742504910672534362390528)), (110593/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774497411007663/4835703278458516698824704), (-3073795666343/9671406556917033397649408)), (103705/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629149897265587/302231454903657293676544), (-168038425347/37778931862957161709568)), (45383/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117937337009501/4722366482869645213696), (-4367206487461/75557863725914323419136)), (147539/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296943281637787/4722366482869645213696), (-1636918524199/2361183241434822606848)), (55347/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620628082929219/590295810358705651712), (-562372439829/73786976294838206464)), (38067/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822449135687641/73786976294838206464), (-2809953501549/36893488147419103232)), (5951/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1821502604496181/9223372036854775808), (-3158575048561/4611686018427387904)), (214369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592750331703271/1152921504606846976), (-3155299474041/576460752303423488)), (214535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596749401360257/72057594037927936), (-2757205764823/72057594037927936)), (187905/144115188075855872), by norm_num⟩
  | 4 => ⟨((745006363713981/18014398509481984), (-8256910912465/36028797018963968)), (282231/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487223827665961/9007199254740992), (-10295444548689/9007199254740992)), (353445/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223871438912849/4503599627370496), (-10256987467715/2251799813685248)), (354431/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209966762143445/2251799813685248), (-15289632264443/1125899906842624)), (1068237/2251799813685248), by norm_num⟩
  | 0 => ⟨((135523311521605/140737488355328), (-7549406975423/281474976710656)), (2156333/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135523311521605/140737488355328), (-7549406975423/281474976710656)), (8225757607466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521604294458537/562949953421312), (-116315349411437/2251799813685248)), (4268557/2251799813685248), by norm_num⟩
  | 2 => ⟨((1927172812200653/2251799813685248), (-215545219946203/2251799813685248)), (8351089/2251799813685248), by norm_num⟩
  | 3 => ⟨((1628712856246979/2251799813685248), (-92235749633603/562949953421312)), (3973273/562949953421312), by norm_num⟩
  | 4 => ⟨((34924655277999/70368744177664), (-266854185386881/1125899906842624)), (14099357/1125899906842624), by norm_num⟩
  | 5 => ⟨((856346530010627/4503599627370496), (-529768751342093/2251799813685248)), (82715101/4503599627370496), by norm_num⟩
  | 6 => ⟨((-86439819775963/4503599627370496), (-805872048061687/9007199254740992)), (281503789/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-662385127/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-81995171/33554432), (-84608581/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-687884634839289/9007199254740992), (-186198192125695/4503599627370496)), (282557033/18014398509481984), by norm_num⟩
  | 1 => ⟨((929319347/4294967296), (125775147/1073741824)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-1316479987/4294967296), (-356347825/2147483648)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((310822389/1073741824), (336536471/2147483648)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-220156535/1073741824), (-238369905/2147483648)), (47/1073741824), by norm_num⟩
  | 5 => ⟨((249500173/2147483648), (540282237/8589934592)), (215/8589934592), by norm_num⟩
  | 6 => ⟨((-942516293/17179869184), (-127561237/4294967296)), (205/17179869184), by norm_num⟩
  | 7 => ⟨((190739267/8589934592), (206518971/17179869184)), (21/4294967296), by norm_num⟩
  | 8 => ⟨((-1080810073/137438953472), (-36569519/8589934592)), (15/8589934592), by norm_num⟩
  | 9 => ⟨((680481227/274877906944), (736776883/549755813888)), (19/34359738368), by norm_num⟩
  | 10 => ⟨((-771179397/1099511627776), (-417489219/1099511627776)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((794514821/4398046511104), (430122191/4398046511104)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((-750343331/17592186044416), (-203104655/8796093022208)), (173/17592186044416), by norm_num⟩
  | 13 => ⟨((1308235531/140737488355328), (88529049/17592186044416)), (19/8796093022208), by norm_num⟩
  | 14 => ⟨((-1059002961/562949953421312), (-35831669/35184372088832)), (31/70368744177664), by norm_num⟩
  | 15 => ⟨((400050843/1125899906842624), (433146721/2251799813685248)), (189/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1133429387/18014398509481984), (-613598535/18014398509481984)), (135/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-430741674283/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778191473999611/633825300114114700748351602688), (-254724958565/39614081257132168796771975168)), (46301/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889092076097963/39614081257132168796771975168), (-4584057217075/39614081257132168796771975168)), (52101/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888826112282855/2475880078570760549798248448), (-1217336166441/618970019642690137449562112)), (55373/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885245941413683/77371252455336267181195264), (-4867976771933/154742504910672534362390528)), (110779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548897787663795/9671406556917033397649408), (-285142198159/604462909807314587353088)), (103891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314553623178169/151115727451828646838272), (-3990538096361/604462909807314587353088)), (90941/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886858033523155/75557863725914323419136), (-6481901433167/75557863725914323419136)), (147845/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648419056570747/2361183241434822606848), (-4859044270825/4722366482869645213696)), (55471/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620482422179067/590295810358705651712), (-6677316936727/590295810358705651712)), (152641/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822265481113469/73786976294838206464), (-8340845385787/73786976294838206464)), (190945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910646913238585/4611686018427387904), (-9375479235235/9223372036854775808)), (107505/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796269425700991/576460752303423488), (-9365520840777/1152921504606846976)), (26907/144115188075855872), by norm_num⟩
  | 5 => ⟨((596655362811943/72057594037927936), (-4091818162123/72057594037927936)), (188627/144115188075855872), by norm_num⟩
  | 4 => ⟨((11638473192745/281474976710656), (-6126543813533/18014398509481984)), (283495/36028797018963968), by norm_num⟩
  | 3 => ⟨((185856637491735/1125899906842624), (-7638633484565/4503599627370496)), (355343/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111549289892711/2251799813685248), (-3804681763065/562949953421312)), (356807/2251799813685248), by norm_num⟩
  | 1 => ⟨((552182401749489/562949953421312), (-22682087272593/1125899906842624)), (538879/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082795524312725/1125899906842624), (-44782242052299/1125899906842624)), (1092495/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082795524312725/1125899906842624), (-44782242052299/1125899906842624)), (4167537693503951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079120339481545/2251799813685248), (-172271126298961/2251799813685248)), (4376493/2251799813685248), by norm_num⟩
  | 2 => ⟨((238312927452441/281474976710656), (-318120998515749/2251799813685248)), (1093925/281474976710656), by norm_num⟩
  | 3 => ⟨((1569213345631003/2251799813685248), (-269339560220707/1125899906842624)), (4322893/562949953421312), by norm_num⟩
  | 4 => ⟨((964675152784493/2251799813685248), (-750779407363067/2251799813685248)), (4046627/281474976710656), by norm_num⟩
  | 5 => ⟨((325897914769643/4503599627370496), (-643270538618717/2251799813685248)), (98648981/4503599627370496), by norm_num⟩
  | 6 => ⟨((-687884634839289/9007199254740992), (-186198192125695/4503599627370496)), (282557033/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-84608581/2097152)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83649375/33554432), (-1381048151/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-176829830910977/2251799813685248), (465247170789299/18014398509481984)), (262328507/18014398509481984), by norm_num⟩
  | 1 => ⟨((974853419/4294967296), (-20038147/268435456)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-1408844395/4294967296), (463341553/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((678680675/2147483648), (-111602445/1073741824)), (259/4294967296), by norm_num⟩
  | 4 => ⟨((-61301233/268435456), (322572555/4294967296)), (189/4294967296), by norm_num⟩
  | 5 => ⟨((1133973457/8589934592), (-372941841/8589934592)), (55/2147483648), by norm_num⟩
  | 6 => ⟨((-136566869/2147483648), (179656761/8589934592)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((902237763/34359738368), (-296728473/34359738368)), (89/17179869184), by norm_num⟩
  | 8 => ⟨((-1303901275/137438953472), (428827799/137438953472)), (259/137438953472), by norm_num⟩
  | 9 => ⟨((418751047/137438953472), (-275438169/274877906944)), (21/34359738368), by norm_num⟩
  | 10 => ⟨((-30258655/34359738368), (159223741/549755813888)), (49/274877906944), by norm_num⟩
  | 11 => ⟨((254425489/1099511627776), (-334702403/4398046511104)), (13/274877906944), by norm_num⟩
  | 12 => ⟨((-980512331/17592186044416), (161235729/8796093022208)), (101/8796093022208), by norm_num⟩
  | 13 => ⟨((218003473/17592186044416), (-286788429/70368744177664)), (91/35184372088832), by norm_num⟩
  | 14 => ⟨((-1440253901/562949953421312), (473671529/562949953421312)), (303/562949953421312), by norm_num⟩
  | 15 => ⟨((1110098453/2251799813685248), (-45636227/281474976710656)), (59/562949953421312), by norm_num⟩
  | 16 => ⟨((-1604298609/18014398509481984), (527622647/18014398509481984)), (343/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (3678386319935/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778114283626739/633825300114114700748351602688), (2175086782595/316912650057057350374175801344)), (23157/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889005187914935/39614081257132168796771975168), (611607913097/4951760157141521099596496896)), (104235/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944366862769189/1237940039285380274899124224), (2598671364191/1237940039285380274899124224)), (110781/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442599854907951/38685626227668133590597632), (5195852864105/154742504910672534362390528)), (110817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548811022273509/9671406556917033397649408), (4869529428623/9671406556917033397649408)), (51965/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258138491947125/604462909807314587353088), (4259256010869/604462909807314587353088)), (90977/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886734380514759/75557863725914323419136), (3459162576523/37778931862957161709568)), (36977/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296745240793827/4722366482869645213696), (2593074783655/2361183241434822606848)), (55497/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810177253809681/295147905179352825856), (7126741485999/590295810358705651712)), (152719/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911052632977281/36893488147419103232), (8902108342471/73786976294838206464)), (191051/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821113142806025/9223372036854775808), (1250773547379/1152921504606846976)), (107571/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49761175541317/36028797018963968), (1249417584647/144115188075855872)), (107703/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193151528809043/144115188075855872), (8733728619239/144115188075855872)), (23597/18014398509481984), by norm_num⟩
  | 4 => ⟨((744742272493379/18014398509481984), (13076226975393/36028797018963968)), (283757/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486550932930505/9007199254740992), (16302695075805/9007199254740992)), (44467/1125899906842624), by norm_num⟩
  | 2 => ⟨((555621970775789/1125899906842624), (16238915761627/2251799813685248)), (89325/562949953421312), by norm_num⟩
  | 1 => ⟨((275974728502301/281474976710656), (24199288584097/1125899906842624)), (539867/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081832793307461/1125899906842624), (47764419841587/1125899906842624)), (547737/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1081832793307461/1125899906842624), (47764419841587/1125899906842624)), (2089450838329124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((129683014646067/140737488355328), (11473736569275/140737488355328)), (17173/8796093022208), by norm_num⟩
  | 2 => ⟨((948491427654455/1125899906842624), (84580093900877/562949953421312)), (4409385/1125899906842624), by norm_num⟩
  | 3 => ⟨((773621894720177/1125899906842624), (142505552274469/562949953421312)), (17508329/2251799813685248), by norm_num⟩
  | 4 => ⟨((918837461715027/2251799813685248), (391670395169967/1125899906842624)), (8231147/562949953421312), by norm_num⟩
  | 5 => ⟨((204849015297733/4503599627370496), (1278555685242445/4503599627370496)), (12444161/562949953421312), by norm_num⟩
  | 6 => ⟨((-176829830910977/2251799813685248), (465247170789299/18014398509481984)), (262328507/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1381048151/33554432)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-703441001/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-660308166196853/18014398509481984), (1258638480578165/18014398509481984)), (255068965/18014398509481984), by norm_num⟩
  | 1 => ⟨((463542247/4294967296), (-13805867/67108864)), (181/4294967296), by norm_num⟩
  | 2 => ⟨((-341217965/2147483648), (650408527/2147483648)), (269/4294967296), by norm_num⟩
  | 3 => ⟨((83724623/536870912), (-1276725479/4294967296)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-493044087/4294967296), (469905033/2147483648)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((580695291/8589934592), (-276721339/2147483648)), (59/2147483648), by norm_num⟩
  | 6 => ⟨((-569940617/17179869184), (1086385463/17179869184)), (117/8589934592), by norm_num⟩
  | 7 => ⟨((239736481/17179869184), (-456970815/17179869184)), (199/34359738368), by norm_num⟩
  | 8 => ⟨((-705889439/137438953472), (168190335/17179869184)), (295/137438953472), by norm_num⟩
  | 9 => ⟨((230938709/137438953472), (-880402095/274877906944)), (195/274877906944), by norm_num⟩
  | 10 => ⟨((-543987949/1099511627776), (518458049/549755813888)), (29/137438953472), by norm_num⟩
  | 11 => ⟨((291225331/2199023255552), (-1110231337/4398046511104)), (125/2199023255552), by norm_num⟩
  | 12 => ⟨((-285831739/8796093022208), (1089669475/17592186044416)), (31/2199023255552), by norm_num⟩
  | 13 => ⟨((258958189/35184372088832), (-987220085/70368744177664)), (227/70368744177664), by norm_num⟩
  | 14 => ⟨((-108926655/70368744177664), (830516943/281474976710656)), (193/281474976710656), by norm_num⟩
  | 15 => ⟨((85527437/281474976710656), (-1304216779/2251799813685248)), (153/1125899906842624), by norm_num⟩
  | 16 => ⟨((-503660639/9007199254740992), (120005835/1125899906842624)), (227/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (2675494204463/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444511806283717/158456325028528675187087900672), (49435603285/9903520314283042199192993792)), (2891/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888930029090193/39614081257132168796771975168), (3558572618319/39614081257132168796771975168)), (3253/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((59020445053413/77371252455336267181195264), (3780003236979/2475880078570760549798248448)), (110625/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885160177199141/77371252455336267181195264), (3778900900165/154742504910672534362390528)), (110651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548737343050429/9671406556917033397649408), (3541548717953/9671406556917033397649408)), (103763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258074466695371/604462909807314587353088), (3097684653591/604462909807314587353088)), (90821/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886631171333945/75557863725914323419136), (5031543774817/75557863725914323419136)), (36909/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296668561005231/4722366482869645213696), (1885869559835/2361183241434822606848)), (27693/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810125126495611/295147905179352825856), (1295756245315/147573952589676412928)), (76193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821976715252925/73786976294838206464), (6474109559365/73786976294838206464)), (190593/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910485474786439/4611686018427387904), (7276954252327/9223372036854775808)), (107285/4611686018427387904), by norm_num⟩
  | 6 => ⟨((3109801661711/2251799813685248), (7268937307451/1152921504606846976)), (107381/576460752303423488), by norm_num⟩
  | 5 => ⟨((18641143041599/2251799813685248), (793913804549/18014398509481984)), (47033/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489313755719021/36028797018963968), (9508969612545/36028797018963968)), (141315/18014398509481984), by norm_num⟩
  | 3 => ⟨((46448414053119/281474976710656), (5927385745029/4503599627370496)), (88511/2251799813685248), by norm_num⟩
  | 2 => ⟨((277764967107329/562949953421312), (11807715692961/2251799813685248)), (355181/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207332996560027/2251799813685248), (2199287630655/140737488355328)), (1071245/2251799813685248), by norm_num⟩
  | 0 => ⟨((540770378530123/562949953421312), (69443420659397/2251799813685248)), (270675/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((540770378530123/562949953421312), (69443420659397/2251799813685248)), (1032543183446788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1037858520915185/1125899906842624), (66707430470829/1125899906842624)), (4293731/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905498742182905/2251799813685248), (122982291235209/1125899906842624)), (1053093/281474976710656), by norm_num⟩
  | 3 => ⟨((792794026123375/1125899906842624), (104069020627523/562949953421312)), (1006169/140737488355328), by norm_num⟩
  | 4 => ⟨((1039525663130233/2251799813685248), (586235400547327/2251799813685248)), (28623699/2251799813685248), by norm_num⟩
  | 5 => ⟨((654535678502791/4503599627370496), (270630959200159/1125899906842624)), (20665823/1125899906842624), by norm_num⟩
  | 6 => ⟨((-660308166196853/18014398509481984), (1258638480578165/18014398509481984)), (255068965/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-703441001/16777216)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-1431390445/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((332811752568529/18014398509481984), (82403980484773/1125899906842624)), (202662607/18014398509481984), by norm_num⟩
  | 1 => ⟨((-118853439/2147483648), (-941697173/4294967296)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((356053083/4294967296), (1410536307/4294967296)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((-355546571/4294967296), (-1408529713/4294967296)), (7/134217728), by norm_num⟩
  | 4 => ⟨((33285073/536870912), (65930905/268435456)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((-39885267/1073741824), (-9875567/67108864)), (205/8589934592), by norm_num⟩
  | 6 => ⟨((159314109/8589934592), (1262274337/17179869184)), (207/17179869184), by norm_num⟩
  | 7 => ⟨((-136360691/17179869184), (-1080410277/34359738368)), (179/34359738368), by norm_num⟩
  | 8 => ⟨((408500123/137438953472), (101144373/8589934592)), (135/68719476736), by norm_num⟩
  | 9 => ⟨((-271946001/274877906944), (-1077338533/274877906944)), (91/137438953472), by norm_num⟩
  | 10 => ⟨((325870965/1099511627776), (1290967125/1099511627776)), (55/274877906944), by norm_num⟩
  | 11 => ⟨((-354989879/4398046511104), (-43947635/137438953472)), (121/2199023255552), by norm_num⟩
  | 12 => ⟨((354484879/17592186044416), (702161859/8796093022208)), (61/4398046511104), by norm_num⟩
  | 13 => ⟨((-326751321/70368744177664), (-647227367/35184372088832)), (227/70368744177664), by norm_num⟩
  | 14 => ⟨((279674137/281474976710656), (1107954235/281474976710656)), (49/70368744177664), by norm_num⟩
  | 15 => ⟨((-6981907/35184372088832), (-885102469/1125899906842624)), (79/562949953421312), by norm_num⟩
  | 16 => ⟨((167327393/4503599627370496), (165720627/1125899906842624)), (119/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1724055557271/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777982218182473/633825300114114700748351602688), (2038615490541/633825300114114700748351602688)), (92401/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857086282493/39614081257132168796771975168), (2292928696803/39614081257132168796771975168)), (25991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((59018030980201/77371252455336267181195264), (304449334485/309485009821345068724781056)), (110477/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885121693294171/77371252455336267181195264), (2434872664897/154742504910672534362390528)), (55247/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((6049474553509/37778931862957161709568), (570481565851/2417851639229258349412352)), (51803/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258011891232723/604462909807314587353088), (1995918931909/604462909807314587353088)), (45337/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886530047653731/75557863725914323419136), (3241931647157/75557863725914323419136)), (147377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648296604490971/2361183241434822606848), (2430192356379/4722366482869645213696)), (55281/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620147440415751/590295810358705651712), (3339474112971/590295810358705651712)), (152071/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910924696243013/36893488147419103232), (2085642121101/36893488147419103232)), (11885/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455207337239409/2305843009213693952), (4688492991975/9223372036854775808)), (214029/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592078892839883/1152921504606846976), (1170811509785/288230376151711744)), (214153/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596456666829109/72057594037927936), (4091944705221/144115188075855872)), (187523/144115188075855872), by norm_num⟩
  | 4 => ⟨((744569297096923/18014398509481984), (6126143985565/36028797018963968)), (281563/36028797018963968), by norm_num⟩
  | 3 => ⟨((371534565713667/2251799813685248), (7637117739433/9007199254740992)), (176221/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221721529085733/4503599627370496), (950794437005/281474976710656)), (706353/4503599627370496), by norm_num⟩
  | 1 => ⟨((68962332776751/70368744177664), (22665821788407/2251799813685248)), (1063217/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081118991118055/1125899906842624), (44722053297405/2251799813685248)), (535315/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081118991118055/1125899906842624), (44722053297405/2251799813685248)), (2042064668895530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1037675063602827/1125899906842624), (42943303261483/1125899906842624)), (1049311/562949953421312), by norm_num⟩
  | 2 => ⟨((1909451104481483/2251799813685248), (158313166818313/2251799813685248)), (8056879/2251799813685248), by norm_num⟩
  | 3 => ⟨((804010294256921/1125899906842624), (67122141452811/562949953421312)), (7398405/1125899906842624), by norm_num⟩
  | 4 => ⟨((279070555898933/562949953421312), (383457835799769/2251799813685248)), (24661473/2251799813685248), by norm_num⟩
  | 5 => ⟨((488074510087517/2251799813685248), (760364510202601/4503599627370496)), (65699979/4503599627370496), by norm_num⟩
  | 6 => ⟨((332811752568529/18014398509481984), (82403980484773/1125899906842624)), (202662607/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1431390445/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-88110603/33554432), (-1454702867/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1054434721846351/18014398509481984), (766824606653999/18014398509481984)), (135588493/18014398509481984), by norm_num⟩
  | 1 => ⟨((-191345821/1073741824), (-556615525/4294967296)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((1165113291/4294967296), (211828557/1073741824)), (77/2147483648), by norm_num⟩
  | 3 => ⟨((-1182404519/4294967296), (-214972265/1073741824)), (79/2147483648), by norm_num⟩
  | 4 => ⟨((56247767/268435456), (163621971/1073741824)), (61/2147483648), by norm_num⟩
  | 5 => ⟨((-136998071/1073741824), (-797041219/8589934592)), (151/8589934592), by norm_num⟩
  | 6 => ⟨((556124935/8589934592), (404434979/8589934592)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((-967505625/34359738368), (-21987703/1073741824)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((368199073/34359738368), (535536441/68719476736)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((-996435857/274877906944), (-724645649/274877906944)), (147/274877906944), by norm_num⟩
  | 10 => ⟨((606734265/549755813888), (882479975/1099511627776)), (181/1099511627776), by norm_num⟩
  | 11 => ⟨((-167928735/549755813888), (-488496379/2199023255552)), (51/1099511627776), by norm_num⟩
  | 12 => ⟨((85210467/1099511627776), (247873031/4398046511104)), (105/8796093022208), by norm_num⟩
  | 13 => ⟨((-638585055/35184372088832), (-58050385/4398046511104)), (25/8796093022208), by norm_num⟩
  | 14 => ⟨((1110963731/281474976710656), (807934627/281474976710656)), (11/17592186044416), by norm_num⟩
  | 15 => ⟨((-901961069/1125899906842624), (-655940027/1125899906842624)), (145/1125899906842624), by norm_num⟩
  | 16 => ⟨((343255089/2251799813685248), (499256033/4503599627370496)), (7/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (819047464735/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777919128678793/633825300114114700748351602688), (30263068929/19807040628566084398385987584)), (11537/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888786221797983/39614081257132168796771975168), (1089223789441/39614081257132168796771975168)), (103839/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472125461229459/618970019642690137449562112), (578495218857/1237940039285380274899124224)), (431/9671406556917033397649408), by norm_num⟩
  | 14 => ⟨((1770168405417833/154742504910672534362390528), (72290127633/9671406556917033397649408)), (13793/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548595366330175/9671406556917033397649408), (1083981889875/9671406556917033397649408)), (3233/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((628975356059931/302231454903657293676544), (237028573249/151115727451828646838272)), (90533/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943215480019605/37778931862957161709568), (96249536605/4722366482869645213696)), (147131/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296519180351857/4722366482869645213696), (1154388289443/4722366482869645213696)), (110363/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810023058489751/295147905179352825856), (1586299556731/590295810358705651712)), (37943/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821723436078625/73786976294838206464), (1981399074525/73786976294838206464)), (189749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820688605960387/9223372036854775808), (1113523587437/4611686018427387904)), (106757/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198992418105661/144115188075855872), (2224516469655/1152921504606846976)), (213573/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298198142544919/36028797018963968), (971804339145/72057594037927936)), (2921/2251799813685248), by norm_num⟩
  | 4 => ⟨((372240030655849/9007199254740992), (727434016317/9007199254740992)), (280549/36028797018963968), by norm_num⟩
  | 3 => ⟨((742959916726299/4503599627370496), (3627256782429/9007199254740992)), (350921/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110649287705277/2251799813685248), (3612429474523/2251799813685248)), (175637/1125899906842624), by norm_num⟩
  | 1 => ⟨((551548679881221/562949953421312), (5381724765291/1125899906842624)), (527801/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080587283407227/1125899906842624), (21233322672513/2251799813685248)), (1059193/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080587283407227/1125899906842624), (21233322672513/2251799813685248)), (4040500645164107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073996376529909/2251799813685248), (10189386429893/562949953421312)), (1026553/562949953421312), by norm_num⟩
  | 2 => ⟨((1909494692287565/2251799813685248), (75078611895169/2251799813685248)), (1928153/562949953421312), by norm_num⟩
  | 3 => ⟨((1616721504187469/2251799813685248), (127331221937993/2251799813685248)), (13594677/2251799813685248), by norm_num⟩
  | 4 => ⟨((1153555110110269/2251799813685248), (182839632022809/2251799813685248)), (21058563/2251799813685248), by norm_num⟩
  | 5 => ⟨((288049375690331/1125899906842624), (23416334632497/281474976710656)), (24995609/2251799813685248), by norm_num⟩
  | 6 => ⟨((1054434721846351/18014398509481984), (766824606653999/18014398509481984)), (135588493/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1454702867/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile000Terms2
