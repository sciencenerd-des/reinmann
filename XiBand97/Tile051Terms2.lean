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
namespace Reinmann.XiBand97.Tile051Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨51,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76371/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76371/2560))
  have he : value ((69/80), (76371/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-2775388957/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((211583387767707/4503599627370496), (-707281427597467/9007199254740992)), (13464019/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4475660055/34359738368), (3740311641/17179869184)), (287/68719476736), by norm_num⟩
  | 2 => ⟨((12409164593/68719476736), (-20740691747/68719476736)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((-2867125817/17179869184), (19168469343/68719476736)), (93/17179869184), by norm_num⟩
  | 4 => ⟨((3974680353/34359738368), (-13286570481/68719476736)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((-8816123137/137438953472), (14735278189/137438953472)), (145/68719476736), by norm_num⟩
  | 6 => ⟨((8147827861/274877906944), (-13618288709/274877906944)), (135/137438953472), by norm_num⟩
  | 7 => ⟨((-3227225091/274877906944), (2696993835/137438953472)), (27/68719476736), by norm_num⟩
  | 8 => ⟨((2236941973/549755813888), (-7477654691/1099511627776)), (301/2199023255552), by norm_num⟩
  | 9 => ⟨((-11025991265/8796093022208), (2303606785/1099511627776)), (373/8796093022208), by norm_num⟩
  | 10 => ⟨((12228215613/35184372088832), (-20438253417/35184372088832)), (13/1099511627776), by norm_num⟩
  | 11 => ⟨((-3082164791/35184372088832), (20606134883/140737488355328)), (211/70368744177664), by norm_num⟩
  | 12 => ⟨((11394100453/562949953421312), (-4761028099/140737488355328)), (49/70368744177664), by norm_num⟩
  | 13 => ⟨((-9720355205/2251799813685248), (8123306347/1125899906842624)), (21/140737488355328), by norm_num⟩
  | 14 => ⟨((1925039087/2251799813685248), (-12870050037/9007199254740992)), (67/2251799813685248), by norm_num⟩
  | 15 => ⟨((-711645555/4503599627370496), (4757780745/18014398509481984)), (199/36028797018963968), by norm_num⟩
  | 16 => ⟨((246637555/9007199254740992), (-13191369237/288230376151711744)), (139/144115188075855872), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-1343809941197/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778279583727849/633825300114114700748351602688), (-1589497878713/633825300114114700748351602688)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889191598109285/39614081257132168796771975168), (-446953364775/9903520314283042199192993792)), (6495/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888932384344243/2475880078570760549798248448), (-7418314429/9671406556917033397649408)), (13803/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770598750452553/154742504910672534362390528), (-1898567487519/154742504910672534362390528)), (13805/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548998608361155/9671406556917033397649408), (-1779353640261/9671406556917033397649408)), (809/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629151671286411/302231454903657293676544), (-1556381269629/604462909807314587353088)), (177/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((471750899477891/18889465931478580854784), (-2528082831547/75557863725914323419136)), (9205/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296948320713039/4722366482869645213696), (-1895155437191/4722366482869645213696)), (13811/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405158909028277/147573952589676412928), (-1302183105409/295147905179352825856)), (9497/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28475929882815/1152921504606846976), (-1626625238731/36893488147419103232)), (23749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821515562300535/9223372036854775808), (-3656874183333/9223372036854775808)), (3341/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592764891086411/1152921504606846976), (-1826543523671/576460752303423488)), (6685/288230376151711744), by norm_num⟩
  | 5 => ⟨((4662161482219/562949953421312), (-199512225585/9007199254740992)), (11705/72057594037927936), by norm_num⟩
  | 4 => ⟨((745019057901005/18014398509481984), (-4779794712583/36028797018963968)), (35143/36028797018963968), by norm_num⟩
  | 3 => ⟨((371815452154251/2251799813685248), (-5959898551453/9007199254740992)), (43975/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223966036497091/4503599627370496), (-5937686968637/2251799813685248)), (44047/2251799813685248), by norm_num⟩
  | 1 => ⟨((552538724069861/562949953421312), (-17702391821927/2251799813685248)), (33125/562949953421312), by norm_num⟩
  | 0 => ⟨((2168932104902907/2251799813685248), (-8741108270605/562949953421312)), (66611/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168932104902907/2251799813685248), (-8741108270605/562949953421312)), (254100801708030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2088571077906289/2251799813685248), (-67355438064523/2251799813685248)), (521553/2251799813685248), by norm_num⟩
  | 2 => ⟨((967579881201391/1125899906842624), (-124945937934903/2251799813685248)), (124837/281474976710656), by norm_num⟩
  | 3 => ⟨((1656111611677051/2251799813685248), (-107376486176891/1125899906842624)), (456839/562949953421312), by norm_num⟩
  | 4 => ⟨((299381278789565/562949953421312), (-157942499593337/1125899906842624)), (94889/70368744177664), by norm_num⟩
  | 5 => ⟨((1185081427411595/4503599627370496), (-335980328028097/2251799813685248)), (8163055/4503599627370496), by norm_num⟩
  | 6 => ⟨((211583387767707/4503599627370496), (-707281427597467/9007199254740992)), (13464019/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-2775388957/33554432)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-354509351/4194304)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-93369989706885/1125899906842624), (-464393078951167/18014398509481984)), (8578893/4503599627370496), by norm_num⟩
  | 1 => ⟨((1009128955/4294967296), (2509545647/34359738368)), (373/68719476736), by norm_num⟩
  | 2 => ⟨((-11436310485/34359738368), (-7110078215/68719476736)), (531/68719476736), by norm_num⟩
  | 3 => ⟨((10800502491/34359738368), (1678697373/17179869184)), (63/8589934592), by norm_num⟩
  | 4 => ⟨((-7650031945/34359738368), (-2378053899/34359738368)), (359/68719476736), by norm_num⟩
  | 5 => ⟨((17339338071/137438953472), (168438351/4294967296)), (409/137438953472), by norm_num⟩
  | 6 => ⟨((-511729625/8589934592), (-5090365693/274877906944)), (97/68719476736), by norm_num⟩
  | 7 => ⟨((13255672705/549755813888), (4120597717/549755813888)), (79/137438953472), by norm_num⟩
  | 8 => ⟨((-4694518599/549755813888), (-5837266219/2199023255552)), (225/1099511627776), by norm_num⟩
  | 9 => ⟨((23645462647/8796093022208), (3675160121/4398046511104)), (569/8796093022208), by norm_num⟩
  | 10 => ⟨((-3349632015/4398046511104), (-4165005079/17592186044416)), (81/4398046511104), by norm_num⟩
  | 11 => ⟨((13803959451/70368744177664), (4291035625/70368744177664)), (21/4398046511104), by norm_num⟩
  | 12 => ⟨((-6518260353/140737488355328), (-4052473131/281474976710656)), (637/562949953421312), by norm_num⟩
  | 13 => ⟨((22729381185/2251799813685248), (7065551355/2251799813685248)), (279/1125899906842624), by norm_num⟩
  | 14 => ⟨((-9199598011/4503599627370496), (-178734057/281474976710656)), (227/4503599627370496), by norm_num⟩
  | 15 => ⟨((13901026051/36028797018963968), (540151163/4503599627370496)), (345/36028797018963968), by norm_num⟩
  | 16 => ⟨((-4923071563/72057594037927936), (-6121453931/288230376151711744)), (491/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-462460800375/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222273764331437/79228162514264337593543950336), (-4375719936055/633825300114114700748351602688)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236136308950357/4951760157141521099596496896), (-2460808034281/19807040628566084398385987584)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118051519237873/154742504910672534362390528), (-5227910956497/2475880078570760549798248448)), (13849/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13831952861627/1208925819614629174706176), (-5226441780085/154742504910672534362390528)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774447935965981/4835703278458516698824704), (-2449114246769/4835703278458516698824704)), (203/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((314553174392931/151115727451828646838272), (-4284389621111/604462909807314587353088)), (11373/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886854893741511/75557863725914323419136), (-6959208326597/75557863725914323419136)), (9245/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648417781838203/2361183241434822606848), (-2608423906695/2361183241434822606848)), (3469/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810239300396893/295147905179352825856), (-896126218271/73786976294838206464)), (4773/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822260231277173/73786976294838206464), (-559689420783/4611686018427387904)), (23883/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455321817757861/2305843009213693952), (-10065845468929/9223372036854775808)), (26895/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592531485938503/1152921504606846976), (-10055146549377/1152921504606846976)), (1683/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193303371918245/144115188075855872), (-4393112746745/72057594037927936)), (1475/9007199254740992), by norm_num⟩
  | 4 => ⟨((372427931529415/9007199254740992), (-13155304151659/36028797018963968)), (35473/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486833888903853/9007199254740992), (-8201059350501/4503599627370496)), (5559/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111525368363583/2251799813685248), (-4084799480211/562949953421312)), (44669/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104317236635447/1125899906842624), (-24351833049971/1125899906842624)), (67495/1125899906842624), by norm_num⟩
  | 0 => ⟨((541327100288775/562949953421312), (-48077843720971/1125899906842624)), (17121/140737488355328), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541327100288775/562949953421312), (-48077843720971/1125899906842624)), (65311432421636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1039016551881527/1125899906842624), (-92462356809655/1125899906842624)), (275113/1125899906842624), by norm_num⟩
  | 2 => ⟨((1902489024375921/2251799813685248), (-42663614486219/281474976710656)), (552953/1125899906842624), by norm_num⟩
  | 3 => ⟨((194454047963977/281474976710656), (-576726636582501/2251799813685248)), (2203953/2251799813685248), by norm_num⟩
  | 4 => ⟨((231745567170665/562949953421312), (-796851147215113/2251799813685248)), (4174101/2251799813685248), by norm_num⟩
  | 5 => ⟨((12452504340677/281474976710656), (-656067985936067/2251799813685248)), (99857/35184372088832), by norm_num⟩
  | 6 => ⟨((-93369989706885/1125899906842624), (-464393078951167/18014398509481984)), (8578893/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-354509351/4194304)), (1/134217728), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-23146327601/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-247550936906713/18014398509481984), (1468460406672359/18014398509481984)), (15758667/9007199254740992), by norm_num⟩
  | 1 => ⟨((1364735101/34359738368), (-16191087673/68719476736)), (349/68719476736), by norm_num⟩
  | 2 => ⟨((-3944591793/68719476736), (11699565635/34359738368)), (253/34359738368), by norm_num⟩
  | 3 => ⟨((950111393/17179869184), (-22544062727/68719476736)), (245/34359738368), by norm_num⟩
  | 4 => ⟨((-2746175137/68719476736), (8145090277/34359738368)), (89/17179869184), by norm_num⟩
  | 5 => ⟨((3174986823/137438953472), (-9416935561/68719476736)), (413/137438953472), by norm_num⟩
  | 6 => ⟨((-1529482041/137438953472), (567050929/8589934592)), (25/17179869184), by norm_num⟩
  | 7 => ⟨((2526155255/549755813888), (-468282283/17179869184)), (83/137438953472), by norm_num⟩
  | 8 => ⟨((-3650763903/2199023255552), (2707019771/274877906944)), (241/1099511627776), by norm_num⟩
  | 9 => ⟨((4689806613/8796093022208), (-13909855101/4398046511104)), (311/4398046511104), by norm_num⟩
  | 10 => ⟨((-2711056917/17592186044416), (2010232617/2199023255552)), (361/17592186044416), by norm_num⟩
  | 11 => ⟨((2849440853/70368744177664), (-8451373939/35184372088832)), (381/70368744177664), by norm_num⟩
  | 12 => ⟨((-343164307/35184372088832), (16285075033/281474976710656)), (369/281474976710656), by norm_num⟩
  | 13 => ⟨((1220766057/562949953421312), (-1810381575/140737488355328)), (659/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4032534553/9007199254740992), (23920803545/9007199254740992)), (273/4503599627370496), by norm_num⟩
  | 15 => ⟨((3108139729/36028797018963968), (-18437337331/36028797018963968)), (423/36028797018963968), by norm_num⟩
  | 16 => ⟨((-2245919823/144115188075855872), (6661344889/72057594037927936)), (307/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (2263684575039/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889060292881605/316912650057057350374175801344), (2677103474667/633825300114114700748351602688)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944506312837007/19807040628566084398385987584), (3011086266779/39614081257132168796771975168)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888742090298629/2475880078570760549798248448), (199904079475/154742504910672534362390528)), (13821/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221301037974135/19342813113834066795298816), (799387493851/38685626227668133590597632)), (27/302231454903657293676544), by norm_num⟩
  | 13 => ⟨((1548819902615065/9671406556917033397649408), (2996730911061/9671406556917033397649408)), (12963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258146813210347/604462909807314587353088), (327645963309/75557863725914323419136)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886748934614717/75557863725914323419136), (4257576065581/75557863725914323419136)), (18441/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296757058399777/4722366482869645213696), (3191589017553/4722366482869645213696)), (3459/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620372220734819/590295810358705651712), (2192923808235/295147905179352825856)), (2379/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822129599899543/73786976294838206464), (5478431034517/73786976294838206464)), (23801/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821143527877039/9223372036854775808), (3078952977513/4611686018427387904)), (26793/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796195878034513/576460752303423488), (1537812673043/288230376151711744)), (26813/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193185612039325/144115188075855872), (5374865340521/144115188075855872)), (5871/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489544065881113/36028797018963968), (8047360351647/36028797018963968)), (4409/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486639965138921/9007199254740992), (10033105322091/9007199254740992)), (44169/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222709593386327/4503599627370496), (2498513523859/562949953421312)), (88579/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208238644779853/2251799813685248), (29787545197809/2251799813685248)), (133471/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164975066204449/2251799813685248), (58800447497845/2251799813685248)), (269365/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164975066204449/2251799813685248), (58800447497845/2251799813685248)), (1027545937545012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079962666395213/2251799813685248), (56533223753207/1125899906842624)), (266013/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915561341568301/2251799813685248), (6527389452151/70368744177664)), (518141/1125899906842624), by norm_num⟩
  | 3 => ⟨((1610154621517459/2251799813685248), (177687054700487/1125899906842624)), (1955341/2251799813685248), by norm_num⟩
  | 4 => ⟨((1095260392408147/2251799813685248), (254111072015397/1125899906842624)), (1706759/1125899906842624), by norm_num⟩
  | 5 => ⟨((418023651025297/2251799813685248), (988783428293653/4503599627370496)), (9722919/4503599627370496), by norm_num⟩
  | 6 => ⟨((-247550936906713/18014398509481984), (1468460406672359/18014398509481984)), (15758667/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-23146327601/268435456)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-11789651111/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1410266694171589/18014398509481984), (88495106358033/9007199254740992)), (12424395/18014398509481984), by norm_num⟩
  | 1 => ⟨((-247504963/1073741824), (-496994859/17179869184)), (141/68719476736), by norm_num⟩
  | 2 => ⟨((23320424339/68719476736), (2926742071/68719476736)), (105/34359738368), by norm_num⟩
  | 3 => ⟨((-22888522145/68719476736), (-718134453/17179869184)), (13/4294967296), by norm_num⟩
  | 4 => ⟨((16848464195/68719476736), (528625769/17179869184)), (155/68719476736), by norm_num⟩
  | 5 => ⟨((-9921854943/68719476736), (-2490410111/137438953472)), (185/137438953472), by norm_num⟩
  | 6 => ⟨((9738098813/137438953472), (611071717/68719476736)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-16384707273/549755813888), (-2056301009/549755813888)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((12060942689/1099511627776), (1513663211/1099511627776)), (29/274877906944), by norm_num⟩
  | 9 => ⟨((-1972928321/549755813888), (-990419769/2199023255552)), (77/2199023255552), by norm_num⟩
  | 10 => ⟨((18589334565/17592186044416), (2332984459/17592186044416)), (183/17592186044416), by norm_num⟩
  | 11 => ⟨((-9951847507/35184372088832), (-156121145/4398046511104)), (99/35184372088832), by norm_num⟩
  | 12 => ⟨((19535071809/281474976710656), (612918913/70368744177664)), (49/70368744177664), by norm_num⟩
  | 13 => ⟨((-17698408275/1125899906842624), (-2221172109/1125899906842624)), (179/1125899906842624), by norm_num⟩
  | 14 => ⟨((3722277371/1125899906842624), (1868601639/4503599627370496)), (19/562949953421312), by norm_num⟩
  | 15 => ⟨((-1461335811/2251799813685248), (-2934391201/36028797018963968)), (241/36028797018963968), by norm_num⟩
  | 16 => ⟨((8605628247/72057594037927936), (1080016979/72057594037927936)), (179/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (81314547771/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889026285912741/316912650057057350374175801344), (192315392023/633825300114114700748351602688)), (11529/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888936338505317/39614081257132168796771975168), (216307398265/39614081257132168796771975168)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944330668745545/1237940039285380274899124224), (229767106343/2475880078570760549798248448)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442581972683981/38685626227668133590597632), (114850098363/77371252455336267181195264)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548744876092981/9671406556917033397649408), (215272870523/9671406556917033397649408)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081525423293/604462909807314587353088), (47073182205/151115727451828646838272)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471660879278101/18889465931478580854784), (152921281777/37778931862957161709568)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296678585395813/4722366482869645213696), (114632753915/2361183241434822606848)), (13779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132639057223/295147905179352825856), (78762755635/147573952589676412928)), (18945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910998678092403/36893488147419103232), (98382604459/18446744073709551616)), (11841/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820996722843909/9223372036854775808), (221166224947/4611686018427387904)), (26643/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592247407412655/1152921504606846976), (441846387087/1152921504606846976)), (26645/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149132757931063/18014398509481984), (193034744463/72057594037927936)), (5829/36028797018963968), by norm_num⟩
  | 4 => ⟨((372341059661145/9007199254740992), (289006916727/18014398509481984)), (17489/18014398509481984), by norm_num⟩
  | 3 => ⟨((371606189902111/2251799813685248), (720613133955/9007199254740992)), (2733/562949953421312), by norm_num⟩
  | 2 => ⟨((2222307762843743/4503599627370496), (358882481725/1125899906842624)), (43737/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207706809731461/2251799813685248), (2139110342429/2251799813685248)), (131261/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164191812455943/2251799813685248), (4221819048823/2251799813685248)), (262725/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164191812455943/2251799813685248), (4221819048823/2251799813685248)), (1002216347701262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079984352463375/2251799813685248), (63399467753/17592186044416)), (505993/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921249404513849/2251799813685248), (14991872021795/2251799813685248)), (469209/1125899906842624), by norm_num⟩
  | 3 => ⟨((1639121957327783/2251799813685248), (12791157108803/1125899906842624)), (197/274877906944), by norm_num⟩
  | 4 => ⟨((596426538422475/1125899906842624), (18621785426259/1125899906842624)), (149133/140737488355328), by norm_num⟩
  | 5 => ⟨((315638932628341/1125899906842624), (9864577617895/562949953421312)), (5213907/4503599627370496), by norm_num⟩
  | 6 => ⟨((1410266694171589/18014398509481984), (88495106358033/9007199254740992)), (12424395/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-11789651111/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-23990063015/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((111972966080303/9007199254740992), (-1341252545878507/18014398509481984)), (13056645/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2559211947/68719476736), (15327581553/68719476736)), (75/17179869184), by norm_num⟩
  | 2 => ⟨((239584807/4294967296), (-22958665367/68719476736)), (451/68719476736), by norm_num⟩
  | 3 => ⟨((-478487959/8589934592), (22926004933/68719476736)), (453/68719476736), by norm_num⟩
  | 4 => ⟨((2866843643/68719476736), (-4292510805/17179869184)), (341/68719476736), by norm_num⟩
  | 5 => ⟨((-1717659205/68719476736), (20574741045/137438953472)), (205/68719476736), by norm_num⟩
  | 6 => ⟨((1715215705/137438953472), (-20545471923/274877906944)), (411/274877906944), by norm_num⟩
  | 7 => ⟨((-1468093441/274877906944), (2198169047/68719476736)), (353/549755813888), by norm_num⟩
  | 8 => ⟨((2199007451/1099511627776), (-26340503827/2199023255552)), (531/2199023255552), by norm_num⟩
  | 9 => ⟨((-2927838929/4398046511104), (17535354981/4398046511104)), (355/4398046511104), by norm_num⟩
  | 10 => ⟨((3508408629/17592186044416), (-10506245769/8796093022208)), (427/17592186044416), by norm_num⟩
  | 11 => ⟨((-3821910167/70368744177664), (22890108745/70368744177664)), (467/70368744177664), by norm_num⟩
  | 12 => ⟨((3816473211/281474976710656), (-11428772919/140737488355328)), (469/281474976710656), by norm_num⟩
  | 13 => ⟨((-439735845/140737488355328), (21069257773/1125899906842624)), (217/562949953421312), by norm_num⟩
  | 14 => ⟨((752760493/1125899906842624), (-18033672997/4503599627370496)), (373/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1202703415/9007199254740992), (14406414989/18014398509481984)), (299/18014398509481984), by norm_num⟩
  | 16 => ⟨((900744359/36028797018963968), (-5394720291/36028797018963968)), (225/72057594037927936), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-915315708411/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888990967085293/316912650057057350374175801344), (-541159121597/158456325028528675187087900672)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888856751167969/39614081257132168796771975168), (-1217335085057/19807040628566084398385987584)), (12999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944288307243359/1237940039285380274899124224), (-161634703501/154742504910672534362390528)), (13813/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770242986311585/154742504910672534362390528), (-2585388555371/154742504910672534362390528)), (13815/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774332542799587/4835703278458516698824704), (-1211493720779/4835703278458516698824704)), (6477/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629005758164241/302231454903657293676544), (-2119300008917/604462909807314587353088)), (11337/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886529391948591/75557863725914323419136), (-107573029805/2361183241434822606848)), (9213/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648296338287545/2361183241434822606848), (-161276158951/295147905179352825856)), (27/9223372036854775808), by norm_num⟩
  | 9 => ⟨((405036660605985/147573952589676412928), (-1772954383473/295147905179352825856)), (9507/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455462074062925/18446744073709551616), (-276821133551/4611686018427387904)), (23777/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455206995042557/2305843009213693952), (-2489159170035/4611686018427387904)), (13381/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592077355022183/1152921504606846976), (-2486373146303/576460752303423488)), (13389/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192911798422657/144115188075855872), (-4344892052333/144115188075855872)), (11725/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489135913332797/36028797018963968), (-3252417574267/18014398509481984)), (35211/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486134253143299/9007199254740992), (-8109206447501/9007199254740992)), (44079/9007199254740992), by norm_num⟩
  | 2 => ⟨((555427886309075/1125899906842624), (-4038267672057/1125899906842624)), (2761/140737488355328), by norm_num⟩
  | 1 => ⟨((2206774802031625/2251799813685248), (-1504177817005/140737488355328)), (133015/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162179043223383/2251799813685248), (-1483943840587/70368744177664)), (66999/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162179043223383/2251799813685248), (-1483943840587/70368744177664)), (255580904247093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((518780937707035/562949953421312), (-91192540407907/2251799813685248)), (131491/562949953421312), by norm_num⟩
  | 2 => ⟨((477154149727821/562949953421312), (-168075159566785/2251799813685248)), (1011995/2251799813685248), by norm_num⟩
  | 3 => ⟨((1605190674769953/2251799813685248), (-284919678440535/2251799813685248)), (933299/1125899906842624), by norm_num⟩
  | 4 => ⟨((1108205917790599/2251799813685248), (-406208765194549/2251799813685248)), (1566781/1125899906842624), by norm_num⟩
  | 5 => ⟨((7376840772297/35184372088832), (-399825024152821/2251799813685248)), (2107431/1125899906842624), by norm_num⟩
  | 6 => ⟨((111972966080303/9007199254740992), (-1341252545878507/18014398509481984)), (13056645/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-23990063015/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-12190389271/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-626376398241871/9007199254740992), (-90299143675925/4503599627370496)), (3570467/2251799813685248), by norm_num⟩
  | 1 => ⟨((14549385063/68719476736), (4194912247/68719476736)), (167/34359738368), by norm_num⟩
  | 2 => ⟨((-692123895/2147483648), (-3192876115/34359738368)), (255/34359738368), by norm_num⟩
  | 3 => ⟨((87799447/268435456), (3240260991/34359738368)), (519/68719476736), by norm_num⟩
  | 4 => ⟨((-8553836365/34359738368), (-2466261823/34359738368)), (397/68719476736), by norm_num⟩
  | 5 => ⟨((10416938697/68719476736), (3003435783/68719476736)), (485/137438953472), by norm_num⟩
  | 6 => ⟨((-2642883633/34359738368), (-6096018421/274877906944)), (247/137438953472), by norm_num⟩
  | 7 => ⟨((18391585191/549755813888), (5302704247/549755813888)), (27/34359738368), by norm_num⟩
  | 8 => ⟨((-13998398445/1099511627776), (-4036050515/1099511627776)), (165/549755813888), by norm_num⟩
  | 9 => ⟨((9470764035/2199023255552), (2730632523/2199023255552)), (449/4398046511104), by norm_num⟩
  | 10 => ⟨((-11533581443/8796093022208), (-1662694397/4398046511104)), (549/17592186044416), by norm_num⟩
  | 11 => ⟨((25537634539/70368744177664), (7363069671/70368744177664)), (305/35184372088832), by norm_num⟩
  | 12 => ⟨((-25916633787/281474976710656), (-934042951/35184372088832)), (621/281474976710656), by norm_num⟩
  | 13 => ⟨((24278084023/1125899906842624), (3499956581/562949953421312)), (73/140737488355328), by norm_num⟩
  | 14 => ⟨((-5279655111/1125899906842624), (-3044484669/2251799813685248)), (255/2251799813685248), by norm_num⟩
  | 15 => ⟨((8572815173/9007199254740992), (4943467673/18014398509481984)), (13/562949953421312), by norm_num⟩
  | 16 => ⟨((-26100128149/144115188075855872), (-7525249125/144115188075855872)), (159/36028797018963968), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (-3726620140207/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777909220043529/633825300114114700748351602688), (-1101562163657/158456325028528675187087900672)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888774531522045/39614081257132168796771975168), (-4955879618617/39614081257132168796771975168)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888488697812577/2475880078570760549798248448), (-5264209170209/2475880078570760549798248448)), (6925/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770154442238779/154742504910672534362390528), (-2631309966115/77371252455336267181195264)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548581409470821/9671406556917033397649408), (-4932018035123/9671406556917033397649408)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257937634275931/604462909807314587353088), (-4313828094369/604462909807314587353088)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943204043614561/37778931862957161709568), (-875850903707/9444732965739290427392)), (18491/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648250304382447/2361183241434822606848), (-5252338414921/4722366482869645213696)), (13877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810009140792383/295147905179352825856), (-7217470787251/590295810358705651712)), (19093/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821685198111607/73786976294838206464), (-2253774982187/18446744073709551616)), (23885/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227580107750919/1152921504606846976), (-10132727180077/9223372036854775808)), (26897/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795942853197519/576460752303423488), (-10121159793411/1152921504606846976)), (26931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596369511745351/72057594037927936), (-8843012393455/144115188075855872)), (11801/72057594037927936), by norm_num⟩
  | 4 => ⟨((93054163879955/2251799813685248), (-6619270480223/18014398509481984)), (35477/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485779994208311/9007199254740992), (-16502776628317/9007199254740992)), (22239/4503599627370496), by norm_num⟩
  | 2 => ⟨((555237603607187/1125899906842624), (-8217399952697/1125899906842624)), (11169/562949953421312), by norm_num⟩
  | 1 => ⟨((1102751347744491/1125899906842624), (-24482687611097/1125899906842624)), (33755/562949953421312), by norm_num⟩
  | 0 => ⟨((1079559945182805/1125899906842624), (-48289906236643/1125899906842624)), (17127/140737488355328), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079559945182805/1125899906842624), (-48289906236643/1125899906842624)), (65334320605230287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2066112188356963/2251799813685248), (-46302382843167/562949953421312)), (274507/1125899906842624), by norm_num⟩
  | 2 => ⟨((1880503310565513/2251799813685248), (-339873613847309/2251799813685248)), (274449/562949953421312), by norm_num⟩
  | 3 => ⟨((759565438914361/1125899906842624), (-283832271469877/1125899906842624)), (2164955/2251799813685248), by norm_num⟩
  | 4 => ⟨((881746049801919/2251799813685248), (-382963321245237/1125899906842624)), (2006315/1125899906842624), by norm_num⟩
  | 5 => ⟨((169493285775031/4503599627370496), (-1199667550107403/4503599627370496)), (5872193/2251799813685248), by norm_num⟩
  | 6 => ⟨((-626376398241871/9007199254740992), (-90299143675925/4503599627370496)), (3570467/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-12190389271/134217728)), (1/134217728), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile051Terms2
