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
namespace Reinmann.XiBand97.Tile061Terms3
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
  | 0 => ⟨((-2862621597/1073741824), (-103654646429/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-823372769836851/18014398509481984), (-943838635711669/18014398509481984)), (7175201/18014398509481984), by norm_num⟩
  | 1 => ⟨((38834841713/274877906944), (22258341157/137438953472)), (85/68719476736), by norm_num⟩
  | 2 => ⟨((-30010036101/137438953472), (-34400738729/137438953472)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((30920765205/137438953472), (35444714613/137438953472)), (273/137438953472), by norm_num⟩
  | 4 => ⟨((-23894349485/137438953472), (-6847569851/34359738368)), (53/34359738368), by norm_num⟩
  | 5 => ⟨((59086758923/549755813888), (33865806579/274877906944)), (263/274877906944), by norm_num⟩
  | 6 => ⟨((-60879893421/1099511627776), (-69787097235/1099511627776)), (17/34359738368), by norm_num⟩
  | 7 => ⟨((53766381463/2199023255552), (61632822929/2199023255552)), (241/1099511627776), by norm_num⟩
  | 8 => ⟨((-10387135479/1099511627776), (-47627418049/4398046511104)), (375/4398046511104), by norm_num⟩
  | 9 => ⟨((7134905941/2199023255552), (32715193585/8796093022208)), (517/17592186044416), by norm_num⟩
  | 10 => ⟨((-35286875463/35184372088832), (-40449620897/35184372088832)), (321/35184372088832), by norm_num⟩
  | 11 => ⟨((39662992765/140737488355328), (45465998333/140737488355328)), (363/140737488355328), by norm_num⟩
  | 12 => ⟨((-40866664821/562949953421312), (-46845777011/562949953421312)), (47/70368744177664), by norm_num⟩
  | 13 => ⟨((19433937829/1125899906842624), (44554549385/2251799813685248)), (359/2251799813685248), by norm_num⟩
  | 14 => ⟨((-34326358209/9007199254740992), (-9837143117/2251799813685248)), (319/9007199254740992), by norm_num⟩
  | 15 => ⟨((28294461465/36028797018963968), (64868324255/72057594037927936)), (33/4503599627370496), by norm_num⟩
  | 16 => ⟨((-5466211349/36028797018963968), (-25063843019/144115188075855872)), (205/144115188075855872), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (-2980548150813/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111115698533617/39614081257132168796771975168), (-880970245335/158456325028528675187087900672)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944354727401879/19807040628566084398385987584), (-3963441835553/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944209924366327/1237940039285380274899124224), (-2105005369885/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770085924641703/154742504910672534362390528), (-1052180415477/38685626227668133590597632)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96782345384757/604462909807314587353088), (-1972153667977/4835703278458516698824704)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314470522001699/151115727451828646838272), (-1724950086293/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943159241605193/37778931862957161709568), (-5603522391695/75557863725914323419136)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648216990723143/2361183241434822606848), (-2100199044541/2361183241434822606848)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404981900832087/147573952589676412928), (-721487905817/73786976294838206464)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910786624827711/36893488147419103232), (-1802354045775/18446744073709551616)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910258420358819/4611686018427387904), (-1012885892003/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591764080911201/1152921504606846976), (-505857038773/72057594037927936)), (3359/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192635289472007/144115188075855872), (-1767865826603/36028797018963968)), (2943/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488716380131123/36028797018963968), (-10586152205963/36028797018963968)), (2211/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485601530904119/9007199254740992), (-13195927765091/9007199254740992)), (11081/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110310674263941/2251799813685248), (-26281817150797/4503599627370496)), (695/140737488355328), by norm_num⟩
  | 1 => ⟨((551269550395237/562949953421312), (-39148500678953/2251799813685248)), (16779/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079272026979563/1125899906842624), (-77205319023045/2251799813685248)), (33957/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079272026979563/1125899906842624), (-77205319023045/2251799813685248)), (129535679343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066503311402833/2251799813685248), (-148015894928487/2251799813685248)), (134861/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886725100991257/2251799813685248), (-33958984181345/281474976710656)), (265257/2251799813685248), by norm_num⟩
  | 3 => ⟨((774031061442631/1125899906842624), (-113813434870573/562949953421312)), (254255/1125899906842624), by norm_num⟩
  | 4 => ⟨((972218025640809/2251799813685248), (-625953573769077/2251799813685248)), (452397/1125899906842624), by norm_num⟩
  | 5 => ⟨((245754533552859/2251799813685248), (-1081025664775447/4503599627370496)), (1284321/2251799813685248), by norm_num⟩
  | 6 => ⟨((-823372769836851/18014398509481984), (-943838635711669/18014398509481984)), (7175201/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-103654646429/1073741824)), (1/536870912), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1451894239/536870912), (-105145286497/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1037082589394521/18014398509481984), (19198735052615/562949953421312)), (6857377/18014398509481984), by norm_num⟩
  | 1 => ⟨((49618018501/274877906944), (-7348330409/68719476736)), (165/137438953472), by norm_num⟩
  | 2 => ⟨((-4861781563/17179869184), (11520323747/68719476736)), (65/34359738368), by norm_num⟩
  | 3 => ⟨((40650901253/137438953472), (-48162544633/274877906944)), (273/137438953472), by norm_num⟩
  | 4 => ⟨((-15932583219/68719476736), (18876672515/137438953472)), (215/137438953472), by norm_num⟩
  | 5 => ⟨((79930436045/549755813888), (-23675078995/274877906944)), (541/549755813888), by norm_num⟩
  | 6 => ⟨((-83540473299/1099511627776), (12372178875/274877906944)), (71/137438953472), by norm_num⟩
  | 7 => ⟨((4677511979/137438953472), (-44334737487/2199023255552)), (511/2199023255552), by norm_num⟩
  | 8 => ⟨((-58665247021/4398046511104), (34752828239/4398046511104)), (201/2199023255552), by norm_num⟩
  | 9 => ⟨((40876565047/8796093022208), (-48429907525/17592186044416)), (281/8796093022208), by norm_num⟩
  | 10 => ⟨((-51267293309/35184372088832), (30370338985/35184372088832)), (177/17592186044416), by norm_num⟩
  | 11 => ⟨((14613481967/35184372088832), (-34627644445/140737488355328)), (405/140737488355328), by norm_num⟩
  | 12 => ⟨((-61093984243/562949953421312), (9047898239/140737488355328)), (425/562949953421312), by norm_num⟩
  | 13 => ⟨((58941487453/2251799813685248), (-17458235443/1125899906842624)), (103/562949953421312), by norm_num⟩
  | 14 => ⟨((-52803055139/9007199254740992), (1955007009/562949953421312)), (371/9007199254740992), by norm_num⟩
  | 15 => ⟨((44150313059/36028797018963968), (-26154296187/36028797018963968)), (39/4503599627370496), by norm_num⟩
  | 16 => ⟨((-34608262807/144115188075855872), (1281353819/9007199254740992)), (491/288230376151711744), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (3395629795679/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888895074277595/316912650057057350374175801344), (1003593700003/158456325028528675187087900672)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944320353060433/19807040628566084398385987584), (4515099721897/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888346677299061/2475880078570760549798248448), (2397984205503/1237940039285380274899124224)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((13828223528801/1208925819614629174706176), (2397239068141/77371252455336267181195264)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548448645035589/9671406556917033397649408), (2246620145467/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257821666960631/604462909807314587353088), (3930002804105/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943110008987769/37778931862957161709568), (6383288548651/75557863725914323419136)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648179943476397/2361183241434822606848), (2392436120495/2361183241434822606848)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809912662493143/295147905179352825856), (6574985841361/590295810358705651712)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455361201303759/18446744073709551616), (8212415631221/73786976294838206464)), (5967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227546440289339/1152921504606846976), (2307571988733/2305843009213693952)), (6719/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591617742191843/1152921504606846976), (9219447103663/1152921504606846976)), (6727/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596253049466845/72057594037927936), (8054832200111/144115188075855872)), (5895/144115188075855872), by norm_num⟩
  | 4 => ⟨((744260157615815/18014398509481984), (12057910118675/36028797018963968)), (8859/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485352482079855/9007199254740992), (3757465744305/2251799813685248)), (11103/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110055715195267/2251799813685248), (29932420449151/4503599627370496)), (22295/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204284061240553/2251799813685248), (44581306332127/2251799813685248)), (8417/562949953421312), by norm_num⟩
  | 0 => ⟨((1078420220438095/1125899906842624), (87898948910815/2251799813685248)), (34123/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078420220438095/1125899906842624), (87898948910815/2251799813685248)), (130168919089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515613603166917/562949953421312), (84192212189185/1125899906842624)), (136065/2251799813685248), by norm_num⟩
  | 2 => ⟨((938219477655067/1125899906842624), (308451219307381/2251799813685248)), (134799/1125899906842624), by norm_num⟩
  | 3 => ⟨((760698392790621/1125899906842624), (514068684261985/2251799813685248)), (65397/281474976710656), by norm_num⟩
  | 4 => ⟨((910552329997077/2251799813685248), (694646512581587/2251799813685248)), (236457/562949953421312), by norm_num⟩
  | 5 => ⟨((38477195676439/562949953421312), (1123567018189511/4503599627370496)), (2696941/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1037082589394521/18014398509481984), (19198735052615/562949953421312)), (6857377/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-105145286497/1073741824)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-13321559437/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((335805400995215/18014398509481984), (139046043396003/2251799813685248)), (5327991/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8142148139/137438953472), (-26971179859/137438953472)), (65/68719476736), by norm_num⟩
  | 2 => ⟨((3234523135/34359738368), (21428965365/68719476736)), (415/274877906944), by norm_num⟩
  | 3 => ⟨((-27411969703/274877906944), (-45401603639/137438953472)), (221/137438953472), by norm_num⟩
  | 4 => ⟨((5444794707/68719476736), (36072185087/137438953472)), (353/274877906944), by norm_num⟩
  | 5 => ⟨((-13843080539/274877906944), (-22927869197/137438953472)), (451/549755813888), by norm_num⟩
  | 6 => ⟨((29329370087/1099511627776), (97154670031/1099511627776)), (15/34359738368), by norm_num⟩
  | 7 => ⟨((-3328939891/274877906944), (-22054483659/549755813888)), (219/1099511627776), by norm_num⟩
  | 8 => ⟨((21159100343/4398046511104), (70090336269/4398046511104)), (175/2199023255552), by norm_num⟩
  | 9 => ⟨((-1867909997/1099511627776), (-99000382955/17592186044416)), (497/17592186044416), by norm_num⟩
  | 10 => ⟨((9498109633/17592186044416), (62925709251/35184372088832)), (159/17592186044416), by norm_num⟩
  | 11 => ⟨((-686034175/4398046511104), (-1136257337/2199023255552)), (369/140737488355328), by norm_num⟩
  | 12 => ⟨((11628018867/281474976710656), (77036522285/562949953421312)), (393/562949953421312), by norm_num⟩
  | 13 => ⟨((-11370606123/1125899906842624), (-4708196437/140737488355328)), (193/1125899906842624), by norm_num⟩
  | 14 => ⟨((20649370481/9007199254740992), (68401836437/9007199254740992)), (11/281474976710656), by norm_num⟩
  | 15 => ⟨((-17499949587/36028797018963968), (-57969258211/36028797018963968)), (75/9007199254740992), by norm_num⟩
  | 16 => ⟨((6951972727/72057594037927936), (46057355775/144115188075855872)), (479/288230376151711744), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (832116563229/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444435047333353/158456325028528675187087900672), (1967367107445/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888584875549343/39614081257132168796771975168), (2212764321781/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888287857263171/2475880078570760549798248448), (2350404870913/2475880078570760549798248448)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769954353467731/154742504910672534362390528), (2349665850505/154742504910672534362390528)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548394624401679/9671406556917033397649408), (2202026830983/9671406556917033397649408)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314443748701751/151115727451828646838272), (1925988916817/604462909807314587353088)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886145291882643/75557863725914323419136), (97758177157/2361183241434822606848)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296304817863435/4722366482869645213696), (2344910450423/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((404937796994171/147573952589676412928), (805540952217/147573952589676412928)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455338626161611/18446744073709551616), (1006143765127/18446744073709551616)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113767074233017/576460752303423488), (4523347485637/9223372036854775808)), (209/288230376151711744), by norm_num⟩
  | 6 => ⟨((795761732666839/576460752303423488), (2258989489869/576460752303423488)), (1673/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192428158978453/144115188075855872), (1973600013115/72057594037927936)), (1465/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488412478327153/36028797018963968), (738594602657/4503599627370496)), (4399/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485233492893521/9007199254740992), (7364915196807/9007199254740992)), (2753/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219920590233995/4503599627370496), (14666916751953/4503599627370496)), (22067/4503599627370496), by norm_num⟩
  | 1 => ⟨((551028665251021/562949953421312), (21843715373581/2251799813685248)), (33211/2251799813685248), by norm_num⟩
  | 0 => ⟨((539240799003765/562949953421312), (10766131230433/562949953421312)), (33435/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539240799003765/562949953421312), (10766131230433/562949953421312)), (127544407371139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032648561251463/1125899906842624), (20625411447661/562949953421312)), (65333/1125899906842624), by norm_num⟩
  | 2 => ⟨((1891218596244171/2251799813685248), (151337086554169/2251799813685248)), (249263/2251799813685248), by norm_num⟩
  | 3 => ⟨((789103197232481/1125899906842624), (127103444388447/1125899906842624)), (226101/1125899906842624), by norm_num⟩
  | 4 => ⟨((1077411174156703/2251799813685248), (89082283191097/562949953421312)), (183991/562949953421312), by norm_num⟩
  | 5 => ⟨((459119137082233/2251799813685248), (681966464309481/4503599627370496)), (468595/1125899906842624), by norm_num⟩
  | 6 => ⟨((335805400995215/18014398509481984), (139046043396003/2251799813685248)), (5327991/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-13321559437/134217728)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-53970697679/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((280436750383433/4503599627370496), (6072440726825/36028797018963968)), (2188711/18014398509481984), by norm_num⟩
  | 1 => ⟨((-110191781765/549755813888), (-298254893/549755813888)), (217/549755813888), by norm_num⟩
  | 2 => ⟨((44336707803/137438953472), (120005683/137438953472)), (11/17179869184), by norm_num⟩
  | 3 => ⟨((-95142904601/274877906944), (-257522261/274877906944)), (191/274877906944), by norm_num⟩
  | 4 => ⟨((38281649441/137438953472), (207233045/274877906944)), (155/274877906944), by norm_num⟩
  | 5 => ⟨((-49289550369/274877906944), (-266822975/549755813888)), (101/274877906944), by norm_num⟩
  | 6 => ⟨((105771294735/1099511627776), (35786251/137438953472)), (219/1099511627776), by norm_num⟩
  | 7 => ⟨((-12159452271/274877906944), (-263294853/2199023255552)), (203/2199023255552), by norm_num⟩
  | 8 => ⟨((39139766959/2199023255552), (211878359/4398046511104)), (165/4398046511104), by norm_num⟩
  | 9 => ⟨((-55993799847/8796093022208), (-75778903/4398046511104)), (119/8796093022208), by norm_num⟩
  | 10 => ⟨((18023708867/8796093022208), (195138303/35184372088832)), (155/35184372088832), by norm_num⟩
  | 11 => ⟨((-84387026541/140737488355328), (-114204721/70368744177664)), (183/140737488355328), by norm_num⟩
  | 12 => ⟨((90543786555/562949953421312), (245073877/562949953421312)), (99/281474976710656), by norm_num⟩
  | 13 => ⟨((-89676678657/2251799813685248), (-121363443/1125899906842624)), (99/1125899906842624), by norm_num⟩
  | 14 => ⟨((82473740853/9007199254740992), (223230773/9007199254740992)), (23/1125899906842624), by norm_num⟩
  | 15 => ⟨((-70792728165/36028797018963968), (-11975869/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 16 => ⟨((56968250317/144115188075855872), (154195341/144115188075855872)), (65/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (881439031/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777688049807731/633825300114114700748351602688), (2083858629/316912650057057350374175801344)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888526346129645/39614081257132168796771975168), (4687564781/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888225840083757/2475880078570760549798248448), (4979128093/2475880078570760549798248448)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769892527685997/154742504910672534362390528), (4977543293/154742504910672534362390528)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387084216482445/2417851639229258349412352), (1166190925/2417851639229258349412352)), (3229/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724659160591/604462909807314587353088), (254999119/37778931862957161709568)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235757984590845/9444732965739290427392), (6626824427/75557863725914323419136)), (4591/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296244088846321/4722366482869645213696), (2483680721/2361183241434822606848)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619668224923467/590295810358705651712), (6825645251/590295810358705651712)), (4735/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910625804291963/36893488147419103232), (8525347055/73786976294838206464)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227519817283561/1152921504606846976), (9581798935/9223372036854775808)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99463137410317/72057594037927936), (4785145951/576460752303423488)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74520662616705/9007199254740992), (4180539335/72057594037927936)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((372067308691473/9007199254740992), (12515811109/36028797018963968)), (8739/36028797018963968), by norm_num⟩
  | 3 => ⟨((742529913013433/4503599627370496), (1949963307/1125899906842624)), (10925/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219589325176061/4503599627370496), (7766164539/1125899906842624)), (21849/4503599627370496), by norm_num⟩
  | 1 => ⟨((550914401815233/562949953421312), (23130778607/1125899906842624)), (32775/2251799813685248), by norm_num⟩
  | 0 => ⟨((539051627064793/562949953421312), (11398762439/281474976710656)), (8195/281474976710656), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((539051627064793/562949953421312), (11398762439/281474976710656)), (31261445165538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2064671321885737/2251799813685248), (21829725367/281474976710656)), (15695/281474976710656), by norm_num⟩
  | 2 => ⟨((946546760287389/1125899906842624), (320250193865/2251799813685248)), (1799/17592186044416), by norm_num⟩
  | 3 => ⟨((795764115731239/1125899906842624), (4206798569/17592186044416)), (387247/2251799813685248), by norm_num⟩
  | 4 => ⟨((562430506965563/1125899906842624), (1522321028151/4503599627370496)), (547583/2251799813685248), by norm_num⟩
  | 5 => ⟨((561911282524733/2251799813685248), (1520916348645/4503599627370496)), (2189793/9007199254740992), by norm_num⟩
  | 6 => ⟨((280436750383433/4503599627370496), (6072440726825/36028797018963968)), (2188711/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-53970697679/536870912)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-3017330773/1073741824), (-54628309021/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((370431885666995/18014398509481984), (-509604955328767/9007199254740992)), (4865487/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1150992245/17179869184), (50669620993/274877906944)), (61/68719476736), by norm_num⟩
  | 2 => ⟨((15000175395/137438953472), (-41271629185/137438953472)), (399/274877906944), by norm_num⟩
  | 3 => ⟨((-32581346349/274877906944), (89644634777/274877906944)), (109/68719476736), by norm_num⟩
  | 4 => ⟨((3317286617/34359738368), (-73017718555/274877906944)), (357/274877906944), by norm_num⟩
  | 5 => ⟨((-4323216017/68719476736), (95159510415/549755813888)), (467/549755813888), by norm_num⟩
  | 6 => ⟨((18780606851/549755813888), (-6459143155/68719476736)), (255/549755813888), by norm_num⟩
  | 7 => ⟨((-34965160093/2199023255552), (96203483209/2199023255552)), (477/2199023255552), by norm_num⟩
  | 8 => ⟨((28479966763/4398046511104), (-78360058897/4398046511104)), (391/4398046511104), by norm_num⟩
  | 9 => ⟨((-10310053457/4398046511104), (56734363691/8796093022208)), (285/8796093022208), by norm_num⟩
  | 10 => ⟨((6718229895/8796093022208), (-73938413571/35184372088832)), (373/35184372088832), by norm_num⟩
  | 11 => ⟨((-31838024091/140737488355328), (10949931331/17592186044416)), (111/35184372088832), by norm_num⟩
  | 12 => ⟨((34577118689/562949953421312), (-11891977787/70368744177664)), (121/140737488355328), by norm_num⟩
  | 13 => ⟨((-34663258675/2251799813685248), (95372828697/2251799813685248)), (61/281474976710656), by norm_num⟩
  | 14 => ⟨((4033437253/1125899906842624), (-22195277357/2251799813685248)), (57/1125899906842624), by norm_num⟩
  | 15 => ⟨((-28034832961/36028797018963968), (77135313405/36028797018963968)), (199/18014398509481984), by norm_num⟩
  | 16 => ⟨((11417524027/72057594037927936), (-62828574391/144115188075855872)), (163/72057594037927936), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-796019397431/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444408515840583/158456325028528675187087900672), (-940904087795/316912650057057350374175801344)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236058190287875/4951760157141521099596496896), (-2116521779667/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118010068333435/154742504910672534362390528), (-2248159981221/2475880078570760549798248448)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769827644514567/154742504910672534362390528), (-1123717691975/77371252455336267181195264)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12095905415167/75557863725914323419136), (-1053100548885/4835703278458516698824704)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257671163306357/604462909807314587353088), (-921078367321/302231454903657293676544)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942988337519055/37778931862957161709568), (-2992063135997/75557863725914323419136)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296178450839889/4722366482869645213696), (-560696682323/1180591620717411303424)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619577588561347/590295810358705651712), (-770446157047/147573952589676412928)), (297/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821137738023545/73786976294838206464), (-3849162524383/73786976294838206464)), (2971/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820029644814167/9223372036854775808), (-2163046460135/4611686018427387904)), (6687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591280321312983/1152921504606846976), (-270051885841/72057594037927936)), (6691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298053963997781/36028797018963968), (-3774813918565/144115188075855872)), (2929/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488094918099591/36028797018963968), (-2825208075413/18014398509481984)), (8795/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484838103491537/9007199254740992), (-7042407378005/9007199254740992)), (43/35184372088832), by norm_num⟩
  | 2 => ⟨((2219134477869509/4503599627370496), (-14023157787645/4503599627370496)), (22057/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202947101990997/2251799813685248), (-5220306914471/562949953421312)), (33193/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154674178031779/2251799813685248), (-41152205846661/2251799813685248)), (33407/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154674178031779/2251799813685248), (-41152205846661/2251799813685248)), (127437595847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060985741816735/2251799813685248), (-78754421035087/2251799813685248)), (130307/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883586606305745/2251799813685248), (-144161783717985/2251799813685248)), (123823/1125899906842624), by norm_num⟩
  | 3 => ⟨((97897131611503/140737488355328), (-241177038298039/2251799813685248)), (111503/562949953421312), by norm_num⟩
  | 4 => ⟨((1063726360730191/2251799813685248), (-335525957381373/2251799813685248)), (716033/2251799813685248), by norm_num⟩
  | 5 => ⟨((904997057236665/4503599627370496), (-633995621469909/4503599627370496)), (222469/562949953421312), by norm_num⟩
  | 6 => ⟨((370431885666995/18014398509481984), (-509604955328767/9007199254740992)), (4865487/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-54628309021/536870912)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-3052282179/1073741824), (-110522197669/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-774652469812099/18014398509481984), (-708378780921371/18014398509481984)), (1510461/4503599627370496), by norm_num⟩
  | 1 => ⟨((38957644171/274877906944), (1113272143/8589934592)), (153/137438953472), by norm_num⟩
  | 2 => ⟨((-2006219373/8589934592), (-58706613933/274877906944)), (253/137438953472), by norm_num⟩
  | 3 => ⟨((35264916111/137438953472), (64495807493/274877906944)), (279/137438953472), by norm_num⟩
  | 4 => ⟨((-29056852649/137438953472), (-26570957505/137438953472)), (231/137438953472), by norm_num⟩
  | 5 => ⟨((9576664617/68719476736), (8757354131/68719476736)), (153/137438953472), by norm_num⟩
  | 6 => ⟨((-42084165731/549755813888), (-19241873729/274877906944)), (169/274877906944), by norm_num⟩
  | 7 => ⟨((39629298541/1099511627776), (36238901033/1099511627776)), (5/17179869184), by norm_num⟩
  | 8 => ⟨((-65305851553/4398046511104), (-14929688251/1099511627776)), (529/4398046511104), by norm_num⟩
  | 9 => ⟨((11957635173/2199023255552), (43738503943/8796093022208)), (389/8796093022208), by norm_num⟩
  | 10 => ⟨((-31528331867/17592186044416), (-450484293/274877906944)), (515/35184372088832), by norm_num⟩
  | 11 => ⟨((18893134271/35184372088832), (17276773707/35184372088832)), (155/35184372088832), by norm_num⟩
  | 12 => ⟨((-41512458963/281474976710656), (-18980475903/140737488355328)), (171/140737488355328), by norm_num⟩
  | 13 => ⟨((5262242025/140737488355328), (38496339825/1125899906842624)), (87/281474976710656), by norm_num⟩
  | 14 => ⟨((-19821132873/2251799813685248), (-18125379429/2251799813685248)), (329/4503599627370496), by norm_num⟩
  | 15 => ⟨((69682368479/36028797018963968), (7965105831/4503599627370496)), (145/9007199254740992), by norm_num⟩
  | 16 => ⟨((-7176928717/18014398509481984), (-52503378879/144115188075855872)), (15/4503599627370496), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (-3127378790025/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888789256795699/316912650057057350374175801344), (-1848199445255/316912650057057350374175801344)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472100687094471/9903520314283042199192993792), (-4157418648683/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472023503895751/618970019642690137449562112), (-4415975434827/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769760139295711/154742504910672534362390528), (-551816727835/19342813113834066795298816)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548212153222025/9671406556917033397649408), (-1034273563897/2417851639229258349412352)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257614937558331/604462909807314587353088), (-1809213421753/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885884459197889/75557863725914323419136), (-5877074906641/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296108547056869/4722366482869645213696), (-2202648636161/2361183241434822606848)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809740133544031/295147905179352825856), (-6053209055989/590295810358705651712)), (149/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821014283706887/73786976294838206464), (-7560403271119/73786976294838206464)), (5963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56871508920925/288230376151711744), (-2124265399067/2305843009213693952)), (6715/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591135878156401/1152921504606846976), (-8486581212511/1152921504606846976)), (6721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192086009558925/144115188075855872), (-1853495372137/36028797018963968)), (2945/72057594037927936), by norm_num⟩
  | 4 => ⟨((743946628800613/18014398509481984), (-11097451465517/36028797018963968)), (8849/36028797018963968), by norm_num⟩
  | 3 => ⟨((371143507082939/2251799813685248), (-1728841003885/1125899906842624)), (11089/9007199254740992), by norm_num⟩
  | 2 => ⟨((554642641495483/1125899906842624), (-13769248520031/2251799813685248)), (5565/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101006328236235/1125899906842624), (-10250349072217/562949953421312)), (16799/1125899906842624), by norm_num⟩
  | 0 => ⟨((1076227953195891/1125899906842624), (-20195918696633/562949953421312)), (34017/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076227953195891/1125899906842624), (-20195918696633/562949953421312)), (129764561179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1027298341249339/1125899906842624), (-9652462048221/140737488355328)), (134947/2251799813685248), by norm_num⟩
  | 2 => ⟨((1864071564525697/2251799813685248), (-281828484137055/2251799813685248)), (264769/2251799813685248), by norm_num⟩
  | 3 => ⟨((1507831860792969/2251799813685248), (-466603167972993/2251799813685248)), (126159/562949953421312), by norm_num⟩
  | 4 => ⟨((912975652438399/2251799813685248), (-624886030046501/2251799813685248)), (221239/562949953421312), by norm_num⟩
  | 5 => ⟨((393500335780711/4503599627370496), (-126677719643219/562949953421312)), (2417515/4503599627370496), by norm_num⟩
  | 6 => ⟨((-774652469812099/18014398509481984), (-708378780921371/18014398509481984)), (1510461/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-110522197669/1073741824)), (1/536870912), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile061Terms3
