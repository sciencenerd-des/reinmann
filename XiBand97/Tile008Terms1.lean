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
namespace Reinmann.XiBand97.Tile008Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11709/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11709/640))
  have he : value ((69/80), (11709/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-674425801/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-67776727960127/562949953421312), (-810432214415791/9007199254740992)), (245039207/9007199254740992), by norm_num⟩
  | 1 => ⟨((1136174717/4294967296), (849104681/4294967296)), (259/4294967296), by norm_num⟩
  | 2 => ⟨((-624107753/2147483648), (-466418419/2147483648)), (9/134217728), by norm_num⟩
  | 3 => ⟨((914203263/4294967296), (683217343/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-1004354939/8589934592), (-750590969/8589934592)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((882717343/17179869184), (329843385/8589934592)), (209/17179869184), by norm_num⟩
  | 6 => ⟨((-323254707/17179869184), (-483159995/34359738368)), (155/34359738368), by norm_num⟩
  | 7 => ⟨((811729357/137438953472), (303317433/68719476736)), (197/137438953472), by norm_num⟩
  | 8 => ⟨((-891775847/549755813888), (-666456519/549755813888)), (219/549755813888), by norm_num⟩
  | 9 => ⟨((435429291/1099511627776), (325412143/1099511627776)), (27/274877906944), by norm_num⟩
  | 10 => ⟨((-47836797/549755813888), (-572002847/8796093022208)), (3/137438953472), by norm_num⟩
  | 11 => ⟨((1223077075/70368744177664), (457024987/35184372088832)), (155/35184372088832), by norm_num⟩
  | 12 => ⟨((-447895835/140737488355328), (-669457689/281474976710656)), (229/281474976710656), by norm_num⟩
  | 13 => ⟨((605617069/1125899906842624), (226299829/562949953421312)), (39/281474976710656), by norm_num⟩
  | 14 => ⟨((-760386691/9007199254740992), (-35516539/562949953421312)), (99/4503599627370496), by norm_num⟩
  | 15 => ⟨((891061507/72057594037927936), (332961333/36028797018963968)), (117/36028797018963968), by norm_num⟩
  | 16 => ⟨((-489465561/288230376151711744), (-91448853/72057594037927936)), (65/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3256266588831/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889518954902013/316912650057057350374175801344), (-3854763896523/633825300114114700748351602688)), (92579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945022088397293/19807040628566084398385987584), (-1083967536037/9903520314283042199192993792)), (6511/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944918782082319/1237940039285380274899124224), (-4605969311191/2475880078570760549798248448)), (110715/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442875790009869/38685626227668133590597632), (-575620632095/19342813113834066795298816)), (110747/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549845674374203/9671406556917033397649408), (-1079021963119/2417851639229258349412352)), (103859/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629521853903773/302231454903657293676544), (-1887755065517/302231454903657293676544)), (90911/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888205159507101/75557863725914323419136), (-6133204141111/75557863725914323419136)), (147793/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40557754763717/147573952589676412928), (-4598153577437/4722366482869645213696)), (27725/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25341730154361/9223372036854775808), (-1579904694439/147573952589676412928)), (76289/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824000120540327/73786976294838206464), (-7895260923101/73786976294838206464)), (190857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823244270054947/9223372036854775808), (-8876309221665/9223372036854775808)), (53725/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797244005534249/576460752303423488), (-4434493805575/576460752303423488)), (215133/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597507396808863/72057594037927936), (-1938032709881/36028797018963968)), (188503/144115188075855872), by norm_num⟩
  | 4 => ⟨((746138885737157/18014398509481984), (-5805869181781/18014398509481984)), (141639/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490039516973475/9007199254740992), (-14485891355795/9007199254740992)), (355015/9007199254740992), by norm_num⟩
  | 2 => ⟨((557364025823065/1125899906842624), (-7221379251563/1125899906842624)), (89099/562949953421312), by norm_num⟩
  | 1 => ⟨((1109113719160273/1125899906842624), (-21556444513757/1125899906842624)), (538049/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092215921712281/1125899906842624), (-10670738311175/281474976710656)), (68123/70368744177664), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092215921712281/1125899906842624), (-10670738311175/281474976710656)), (259868622094607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1057921559372337/1125899906842624), (-41405990742371/562949953421312)), (2197361/1125899906842624), by norm_num⟩
  | 2 => ⟨((987956562343733/1125899906842624), (-155624101315957/1125899906842624)), (4452623/1125899906842624), by norm_num⟩
  | 3 => ⟨((1690806265073603/2251799813685248), (-273114601430439/1125899906842624)), (18090183/2251799813685248), by norm_num⟩
  | 4 => ⟨((1137072429082283/2251799813685248), (-205073238027283/562949953421312)), (4492893/281474976710656), by norm_num⟩
  | 5 => ⟨((275358927525801/2251799813685248), (-1656865755019879/4503599627370496)), (124973573/4503599627370496), by norm_num⟩
  | 6 => ⟨((-67776727960127/562949953421312), (-810432214415791/9007199254740992)), (245039207/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-674425801/16777216)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-353382811/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-347552224490749/9007199254740992), (1186341070322109/9007199254740992)), (416051/17592186044416), by norm_num⟩
  | 1 => ⟨((381597791/4294967296), (-651276413/2147483648)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((-439330693/4294967296), (46863105/134217728)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((21074923/268435456), (-1151000395/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-97053607/2147483648), (5176321/33554432)), (247/8589934592), by norm_num⟩
  | 5 => ⟨((178779351/8589934592), (-305124341/4294967296)), (115/8589934592), by norm_num⟩
  | 6 => ⟨((-137218223/17179869184), (468383173/17179869184)), (179/34359738368), by norm_num⟩
  | 7 => ⟨((361093297/137438953472), (-616281207/68719476736)), (119/68719476736), by norm_num⟩
  | 8 => ⟨((-415724021/549755813888), (1419039921/549755813888)), (277/549755813888), by norm_num⟩
  | 9 => ⟨((425439971/2199023255552), (-181525565/274877906944)), (143/1099511627776), by norm_num⟩
  | 10 => ⟨((-195922347/4398046511104), (20898903/137438953472)), (133/4398046511104), by norm_num⟩
  | 11 => ⟨((41011625/4398046511104), (-279979651/8796093022208)), (225/35184372088832), by norm_num⟩
  | 12 => ⟨((-62955171/35184372088832), (429784647/70368744177664)), (175/140737488355328), by norm_num⟩
  | 13 => ⟨((356823725/1125899906842624), (-304497145/281474976710656)), (125/562949953421312), by norm_num⟩
  | 14 => ⟨((-469495423/9007199254740992), (1602584199/9007199254740992)), (331/9007199254740992), by norm_num⟩
  | 15 => ⟨((288280843/36028797018963968), (-984023063/36028797018963968)), (205/36028797018963968), by norm_num⟩
  | 16 => ⟨((-165947793/144115188075855872), (566449209/144115188075855872)), (119/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1208682481249/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444725339750065/158456325028528675187087900672), (1430622128501/316912650057057350374175801344)), (46241/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889890788276991/39614081257132168796771975168), (804583271963/9903520314283042199192993792)), (26015/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889674884539679/2475880078570760549798248448), (3418785392005/2475880078570760549798248448)), (110585/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885670406430399/77371252455336267181195264), (3418005348305/154742504910672534362390528)), (110609/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549693826934283/9671406556917033397649408), (400443924611/1208925819614629174706176)), (12965/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((78681949633173/37778931862957161709568), (2802279056711/604462909807314587353088)), (90781/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471997621476219/18889465931478580854784), (2276075308149/37778931862957161709568)), (147565/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324421931320003/1180591620717411303424), (3412754646017/4722366482869645213696)), (110715/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621651081031275/590295810358705651712), (4690331177409/590295810358705651712)), (38075/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823726965783131/73786976294838206464), (5859605685513/73786976294838206464)), (190475/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455734725569673/2305843009213693952), (3293754892759/4611686018427387904)), (107211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594185053940445/1152921504606846976), (1645457486503/288230376151711744)), (214595/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298688103322113/36028797018963968), (5752716090271/144115188075855872)), (187965/144115188075855872), by norm_num⟩
  | 4 => ⟨((372972400812925/9007199254740992), (8616315675293/36028797018963968)), (8823/1125899906842624), by norm_num⟩
  | 3 => ⟨((1489563733596273/9007199254740992), (10748093752891/9007199254740992)), (176801/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228532709075711/4503599627370496), (10714695401469/2251799813685248)), (709251/4503599627370496), by norm_num⟩
  | 1 => ⟨((69278512510797/70368744177664), (15988732330625/1125899906842624)), (1069009/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182079717586837/2251799813685248), (63290663150505/2251799813685248)), (2158613/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182079717586837/2251799813685248), (63290663150505/2251799813685248)), (8234455117232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112739399367767/2251799813685248), (61331061284403/1125899906842624)), (4304901/2251799813685248), by norm_num⟩
  | 2 => ⟨((987792464119461/1125899906842624), (57543547518345/562949953421312)), (267097/70368744177664), by norm_num⟩
  | 3 => ⟨((1709723762969895/2251799813685248), (403880183322665/2251799813685248)), (8372349/1125899906842624), by norm_num⟩
  | 4 => ⟨((306425567495959/562949953421312), (306654056289889/1125899906842624)), (15717055/1125899906842624), by norm_num⟩
  | 5 => ⟨((500132918940181/2251799813685248), (333836578731333/1125899906842624)), (51343513/2251799813685248), by norm_num⟩
  | 6 => ⟨((-347552224490749/9007199254740992), (1186341070322109/9007199254740992)), (416051/17592186044416), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-353382811/8388608)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-736020549/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((282876162078613/2251799813685248), (127322709301693/9007199254740992)), (78105409/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1293768715/4294967296), (-145581495/4294967296)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((1551160943/4294967296), (174544589/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-619920249/2147483648), (-139513215/4294967296)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((1486503835/8589934592), (167269039/8589934592)), (113/8589934592), by norm_num⟩
  | 5 => ⟨((-89112013/1073741824), (-160437455/17179869184)), (111/17179869184), by norm_num⟩
  | 6 => ⟨((1139633465/34359738368), (128237405/34359738368)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((-195194407/17179869184), (-87857105/68719476736)), (63/68719476736), by norm_num⟩
  | 8 => ⟨((1872222983/549755813888), (210672137/549755813888)), (77/274877906944), by norm_num⟩
  | 9 => ⟨((-997643253/1099511627776), (-56129969/549755813888)), (21/274877906944), by norm_num⟩
  | 10 => ⟨((59806101/274877906944), (53837515/2199023255552)), (41/2199023255552), by norm_num⟩
  | 11 => ⟨((-104297285/2199023255552), (-187777051/35184372088832)), (145/35184372088832), by norm_num⟩
  | 12 => ⟨((1333834489/140737488355328), (150089901/140737488355328)), (59/70368744177664), by norm_num⟩
  | 13 => ⟨((-492060833/281474976710656), (-27684605/140737488355328)), (89/562949953421312), by norm_num⟩
  | 14 => ⟨((674234483/2251799813685248), (18967081/562949953421312)), (31/1125899906842624), by norm_num⟩
  | 15 => ⟨((-421027/8796093022208), (-97026291/18014398509481984)), (161/36028797018963968), by norm_num⟩
  | 16 => ⟨((1033808541/144115188075855872), (58164721/72057594037927936)), (49/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (9122659935/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444694747246047/158456325028528675187087900672), (43185233555/158456325028528675187087900672)), (46109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889753394665667/39614081257132168796771975168), (48574621303/9903520314283042199192993792)), (51873/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118095578500795/154742504910672534362390528), (206398599091/2475880078570760549798248448)), (13779/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885597790125843/77371252455336267181195264), (103174816707/77371252455336267181195264)), (110233/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549558091780895/9671406556917033397649408), (193400771727/9671406556917033397649408)), (103345/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258792846013465/604462909807314587353088), (84586842077/302231454903657293676544)), (90429/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943899478697345/37778931862957161709568), (274809792705/75557863725914323419136)), (146949/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297544767094937/4722366482869645213696), (25752765031/590295810358705651712)), (55107/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621455630751101/590295810358705651712), (141570999729/295147905179352825856)), (151549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911742163425757/36893488147419103232), (353720004173/73786976294838206464)), (94721/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822668232004889/9223372036854775808), (99412476953/2305843009213693952)), (106565/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593917252155985/1152921504606846976), (24830865617/72057594037927936)), (213141/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149315163421187/18014398509481984), (347231983633/144115188075855872)), (186511/144115188075855872), by norm_num⟩
  | 4 => ⟨((745774684830495/18014398509481984), (520048779629/36028797018963968)), (17487/2251799813685248), by norm_num⟩
  | 3 => ⟨((372287412482737/2251799813685248), (40541549707/562949953421312)), (349783/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113869011653939/2251799813685248), (1293150689543/4503599627370496)), (174925/1125899906842624), by norm_num⟩
  | 1 => ⟨((553950893773971/562949953421312), (482328108027/562949953421312)), (1049893/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180191888983933/2251799813685248), (954292934815/562949953421312)), (262649/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180191888983933/2251799813685248), (954292934815/562949953421312)), (1001926423192882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2110854647515145/2251799813685248), (7391569014453/2251799813685248)), (4075871/2251799813685248), by norm_num⟩
  | 2 => ⟨((1978707290303823/2251799813685248), (6928914245291/1125899906842624)), (3834133/1125899906842624), by norm_num⟩
  | 3 => ⟨((217331180901227/281474976710656), (12177186486759/1125899906842624)), (3392735/562949953421312), by norm_num⟩
  | 4 => ⟨((335543677820745/562949953421312), (9402193936203/562949953421312)), (21250219/2251799813685248), by norm_num⟩
  | 5 => ⟨((1598737618375281/4503599627370496), (5604133571313/281474976710656)), (52084029/4503599627370496), by norm_num⟩
  | 6 => ⟨((282876162078613/2251799813685248), (127322709301693/9007199254740992)), (78105409/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-736020549/16777216)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1525456409/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((47969891428601/4503599627370496), (-4109200051083/35184372088832)), (165318583/9007199254740992), by norm_num⟩
  | 1 => ⟨((-14209831/536870912), (311614335/1073741824)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((70620207/2147483648), (-774332533/2147483648)), (31/536870912), by norm_num⟩
  | 3 => ⟨((-29247437/1073741824), (1282762707/4294967296)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((145354301/8589934592), (-796886395/4294967296)), (259/8589934592), by norm_num⟩
  | 5 => ⟨((-36119187/4294967296), (1584150641/17179869184)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((119670411/34359738368), (-1312155487/34359738368)), (217/34359738368), by norm_num⟩
  | 7 => ⟨((-5310175/4294967296), (1863190797/137438953472)), (155/68719476736), by norm_num⟩
  | 8 => ⟨((105562313/274877906944), (-144682975/34359738368)), (97/137438953472), by norm_num⟩
  | 9 => ⟨((-58291665/549755813888), (1278306441/1099511627776)), (217/1099511627776), by norm_num⟩
  | 10 => ⟨((115879477/4398046511104), (-635294435/2199023255552)), (217/4398046511104), by norm_num⟩
  | 11 => ⟨((-6544311/1099511627776), (1148107175/17592186044416)), (99/8796093022208), by norm_num⟩
  | 12 => ⟨((86730677/70368744177664), (-1901959435/140737488355328)), (331/140737488355328), by norm_num⟩
  | 13 => ⟨((-66313119/281474976710656), (727106407/281474976710656)), (1/2199023255552), by norm_num⟩
  | 14 => ⟨((23540273/562949953421312), (-129056539/281474976710656)), (23/281474976710656), by norm_num⟩
  | 15 => ⟨((-62395073/9007199254740992), (1368292061/18014398509481984)), (123/9007199254740992), by norm_num⟩
  | 16 => ⟨((38761483/36028797018963968), (-425009755/36028797018963968)), (77/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-963832671475/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778660534176895/633825300114114700748351602688), (-2281033387673/633825300114114700748351602688)), (92425/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889620001176821/39614081257132168796771975168), (-1282839771523/19807040628566084398385987584)), (103993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472346837913427/618970019642690137449562112), (-2725438254451/2475880078570760549798248448)), (27627/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442763370144863/38685626227668133590597632), (-85148989471/4835703278458516698824704)), (110527/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549424665966111/9671406556917033397649408), (-2553757377585/9671406556917033397649408)), (103639/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157334486402539/75557863725914323419136), (-2233825620197/604462909807314587353088)), (90705/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887608517700365/75557863725914323419136), (-3628631943345/75557863725914323419136)), (18429/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297401598042259/4722366482869645213696), (-2720306574327/4722366482869645213696)), (110607/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202657277829239/73786976294838206464), (-3738525423177/590295810358705651712)), (76069/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911618370930137/36893488147419103232), (-4670314145581/73786976294838206464)), (47563/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455597141652763/2305843009213693952), (-2625098648241/4611686018427387904)), (1673/72057594037927936), by norm_num⟩
  | 6 => ⟨((1593636174234627/1152921504606846976), (-1311329600817/288230376151711744)), (214281/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194273778967943/144115188075855872), (-4584170005655/144115188075855872)), (46913/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491174916284011/36028797018963968), (-6865300698411/36028797018963968)), (70447/9007199254740992), by norm_num⟩
  | 3 => ⟨((744338036778497/4503599627370496), (-133788824893/140737488355328)), (352779/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226774428184971/4503599627370496), (-17067662062845/4503599627370496)), (88399/562949953421312), by norm_num⟩
  | 1 => ⟨((1107158689244667/1125899906842624), (-397791073205/35184372088832)), (1064889/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177058083988219/2251799813685248), (-50348221277199/2251799813685248)), (2146239/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177058083988219/2251799813685248), (-50348221277199/2251799813685248)), (8187252053267668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051835720227751/1125899906842624), (-24338531666935/562949953421312)), (4245979/2251799813685248), by norm_num⟩
  | 2 => ⟨((1961078279059731/2251799813685248), (-90949956846403/1125899906842624)), (129695/35184372088832), by norm_num⟩
  | 3 => ⟨((1693196888474103/2251799813685248), (-316830978968775/2251799813685248)), (15798695/2251799813685248), by norm_num⟩
  | 4 => ⟨((307146956080481/562949953421312), (-238234866395241/1125899906842624)), (28204833/2251799813685248), by norm_num⟩
  | 5 => ⟨((1139004122846861/4503599627370496), (-1039852492760053/4503599627370496)), (10678317/562949953421312), by norm_num⟩
  | 6 => ⟨((47969891428601/4503599627370496), (-4109200051083/35184372088832)), (165318583/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1525456409/33554432)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1574593733/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-966722447071665/9007199254740992), (-96644186300507/4503599627370496)), (84247661/4503599627370496), by norm_num⟩
  | 1 => ⟨((591181307/2147483648), (14775243/268435456)), (13/268435456), by norm_num⟩
  | 2 => ⟨((-758175057/2147483648), (-18948875/268435456)), (269/4294967296), by norm_num⟩
  | 3 => ⟨((648226875/2147483648), (64803873/1073741824)), (29/536870912), by norm_num⟩
  | 4 => ⟨((-1662669107/8589934592), (-332437305/8589934592)), (75/2147483648), by norm_num⟩
  | 5 => ⟨((1705864823/17179869184), (341073941/17179869184)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((-1458485627/34359738368), (-145806231/17179869184)), (267/34359738368), by norm_num⟩
  | 7 => ⟨((534420253/34359738368), (26713257/8589934592)), (99/34359738368), by norm_num⟩
  | 8 => ⟨((-1370760885/274877906944), (-137036303/137438953472)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((390659139/274877906944), (156218301/549755813888)), (147/549755813888), by norm_num⟩
  | 10 => ⟨((-400808363/1099511627776), (-320553625/4398046511104)), (19/274877906944), by norm_num⟩
  | 11 => ⟨((1495350041/17592186044416), (298983205/17592186044416)), (143/8796093022208), by norm_num⟩
  | 12 => ⟨((-639249521/35184372088832), (-255625593/70368744177664)), (247/70368744177664), by norm_num⟩
  | 13 => ⟨((1009010861/281474976710656), (12608975/17592186044416)), (197/281474976710656), by norm_num⟩
  | 14 => ⟨((-739446217/1125899906842624), (-147846319/1125899906842624)), (291/2251799813685248), by norm_num⟩
  | 15 => ⟨((1011542453/9007199254740992), (202249771/9007199254740992)), (201/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1297277583/72057594037927936), (-129690105/36028797018963968)), (65/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-3835218143151/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444636471384855/158456325028528675187087900672), (-2268875095199/316912650057057350374175801344)), (92647/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889490583035785/39614081257132168796771975168), (-1275988812553/9903520314283042199192993792)), (104257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889249268048531/2475880078570760549798248448), (-677715677111/309485009821345068724781056)), (55403/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221364343573733/19342813113834066795298816), (-169385783127/4835703278458516698824704)), (110843/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193661739537939/1208925819614629174706176), (-5080107072193/9671406556917033397649408)), (25989/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157320099673715/75557863725914323419136), (-4443627499403/604462909807314587353088)), (91001/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887420201619395/75557863725914323419136), (-1804536519453/18889465931478580854784)), (147951/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81078702163211/295147905179352825856), (-2705602510701/2361183241434822606848)), (27757/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405265161184831/147573952589676412928), (-3718250231113/295147905179352825856)), (76385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822987031029075/73786976294838206464), (-4644883772265/36893488147419103232)), (191121/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56940746334819/288230376151711744), (-10442936344319/9223372036854775808)), (215231/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593346800577319/1152921504606846976), (-10432875150203/1152921504606846976)), (215505/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149251914218597/18014398509481984), (-1139681550329/18014398509481984)), (47219/36028797018963968), by norm_num⟩
  | 4 => ⟨((372694180914203/9007199254740992), (-13653565650933/36028797018963968)), (70983/9007199254740992), by norm_num⟩
  | 3 => ⟨((744080019091053/4503599627370496), (-17027415427601/9007199254740992)), (355997/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112843879174753/2251799813685248), (-8484082622941/1125899906842624)), (357625/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106275935000957/1125899906842624), (-25304341303543/1125899906842624)), (270259/562949953421312), by norm_num⟩
  | 0 => ⟨((543247749138633/562949953421312), (-25009188559821/562949953421312)), (1097417/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543247749138633/562949953421312), (-25009188559821/562949953421312)), (4186313633445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046248092364161/1125899906842624), (-24133913344049/281474976710656)), (1107763/562949953421312), by norm_num⟩
  | 2 => ⟨((481977097523013/562949953421312), (-179412472771597/1125899906842624)), (1124375/281474976710656), by norm_num⟩
  | 3 => ⟨((796712788862675/1125899906842624), (-614425508771041/2251799813685248)), (18269091/2251799813685248), by norm_num⟩
  | 4 => ⟨((959892772343457/2251799813685248), (-869563373557981/2251799813685248)), (17912531/1125899906842624), by norm_num⟩
  | 5 => ⟨((146774746813057/4503599627370496), (-1482703022355913/4503599627370496)), (1819111/70368744177664), by norm_num⟩
  | 6 => ⟨((-966722447071665/9007199254740992), (-96644186300507/4503599627370496)), (84247661/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1574593733/33554432)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1620087787/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-92648922682401/2251799813685248), (847313138044757/9007199254740992)), (163667617/9007199254740992), by norm_num⟩
  | 1 => ⟨((233178919/2147483648), (-1066259359/4294967296)), (13/268435456), by norm_num⟩
  | 2 => ⟨((-615372535/4294967296), (351739947/1073741824)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((270667233/2147483648), (-1237682513/4294967296)), (123/2147483648), by norm_num⟩
  | 4 => ⟨((-89288293/1073741824), (816578777/4294967296)), (41/1073741824), by norm_num⟩
  | 5 => ⟨((188509539/4294967296), (-430999641/4294967296)), (175/8589934592), by norm_num⟩
  | 6 => ⟨((-20728645/1073741824), (189572127/4294967296)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((500151611/68719476736), (-1143523911/68719476736)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((-164991097/68719476736), (377228145/68719476736)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((387040857/549755813888), (-884912623/549755813888)), (47/137438953472), by norm_num⟩
  | 10 => ⟨((-102142301/549755813888), (934134057/2199023255552)), (25/274877906944), by norm_num⟩
  | 11 => ⟨((392086383/8796093022208), (-896448483/8796093022208)), (97/4398046511104), by norm_num⟩
  | 12 => ⟨((-172456407/17592186044416), (197148245/8796093022208)), (43/8796093022208), by norm_num⟩
  | 13 => ⟨((280075289/140737488355328), (-1280702821/281474976710656)), (141/140737488355328), by norm_num⟩
  | 14 => ⟨((-422362711/1125899906842624), (965670905/1125899906842624)), (215/1125899906842624), by norm_num⟩
  | 15 => ⟨((594474351/9007199254740992), (-10618587/70368744177664)), (305/9007199254740992), by norm_num⟩
  | 16 => ⟨((-392212973/36028797018963968), (896737915/36028797018963968)), (203/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (645803571825/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889226701577109/316912650057057350374175801344), (382010353527/79228162514264337593543950336)), (92501/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944693450191417/19807040628566084398385987584), (3437404025815/39614081257132168796771975168)), (104083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889139574623551/2475880078570760549798248448), (1825696493529/1237940039285380274899124224)), (110611/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770805582840105/154742504910672534362390528), (1825219173429/77371252455336267181195264)), (27659/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549192133705329/9671406556917033397649408), (1710635954893/4835703278458516698824704)), (25937/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258472297500817/604462909807314587353088), (2992599178429/604462909807314587353088)), (45403/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471819359554327/18889465931478580854784), (4861073530151/75557863725914323419136)), (73805/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648576539498407/2361183241434822606848), (3644143162201/4722366482869645213696)), (3461/147573952589676412928), by norm_num⟩
  | 9 => ⟨((50653630286547/18446744073709551616), (2503998653751/295147905179352825856)), (152355/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227851083291173/9223372036854775808), (390996837389/4611686018427387904)), (190551/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910953141871103/4611686018427387904), (7032381493703/9223372036854775808)), (214517/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593153021341697/1152921504606846976), (7025434573673/1152921504606846976)), (107351/576460752303423488), by norm_num⟩
  | 5 => ⟨((596925022315677/72057594037927936), (1534861728457/36028797018963968)), (188073/144115188075855872), by norm_num⟩
  | 4 => ⟨((745268685854311/18014398509481984), (9193571054267/36028797018963968)), (282525/36028797018963968), by norm_num⟩
  | 3 => ⟨((185984470064331/1125899906842624), (11464704053001/9007199254740992)), (353885/9007199254740992), by norm_num⟩
  | 2 => ⟨((278145465891645/562949953421312), (22847784864563/4503599627370496)), (709961/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211876390608051/2251799813685248), (8517041228567/562949953421312)), (535219/1125899906842624), by norm_num⟩
  | 0 => ⟨((2172077862563687/2251799813685248), (67325550892819/2251799813685248)), (2162939/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172077862563687/2251799813685248), (67325550892819/2251799813685248)), (8250957497603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093165423760463/2251799813685248), (64941980095411/1125899906842624)), (4302065/2251799813685248), by norm_num⟩
  | 2 => ⟨((969107382811411/1125899906842624), (120733918228537/1125899906842624)), (2123569/562949953421312), by norm_num⟩
  | 3 => ⟨((1642406105177883/2251799813685248), (415682178495389/2251799813685248)), (16444469/2251799813685248), by norm_num⟩
  | 4 => ⟨((560597377587271/1125899906842624), (606376236133661/2251799813685248)), (15029831/1125899906842624), by norm_num⟩
  | 5 => ⟨((197483260696191/1125899906842624), (150960545312171/562949953421312)), (11530821/562949953421312), by norm_num⟩
  | 6 => ⟨((-92648922682401/2251799813685248), (847313138044757/9007199254740992)), (163667617/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1620087787/33554432)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-415610435/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((654620613551785/9007199254740992), (575140933779687/9007199254740992)), (47846567/4503599627370496), by norm_num⟩
  | 1 => ⟨((-845310919/4294967296), (-742678891/4294967296)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((572286101/2147483648), (251401465/1073741824)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-1033186327/4294967296), (-907743717/4294967296)), (159/4294967296), by norm_num⟩
  | 4 => ⟨((349740055/2147483648), (614553889/4294967296)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-757690901/8589934592), (-665697113/8589934592)), (15/1073741824), by norm_num⟩
  | 6 => ⟨((683954999/17179869184), (600913733/17179869184)), (55/8589934592), by norm_num⟩
  | 7 => ⟨((-1058391127/68719476736), (-929888317/68719476736)), (43/17179869184), by norm_num⟩
  | 8 => ⟨((179136019/34359738368), (629546061/137438953472)), (59/68719476736), by norm_num⟩
  | 9 => ⟨((-862416591/549755813888), (-757707705/549755813888)), (9/34359738368), by norm_num⟩
  | 10 => ⟨((934186969/2199023255552), (820764201/2199023255552)), (79/1099511627776), by norm_num⟩
  | 11 => ⟨((-114992055/1099511627776), (-202060969/2199023255552)), (79/4398046511104), by norm_num⟩
  | 12 => ⟨((415205677/17592186044416), (364794165/17592186044416)), (145/35184372088832), by norm_num⟩
  | 13 => ⟨((-345968559/70368744177664), (-607926715/140737488355328)), (61/70368744177664), by norm_num⟩
  | 14 => ⟨((1070743115/1125899906842624), (940740607/1125899906842624)), (191/1125899906842624), by norm_num⟩
  | 15 => ⟨((-773233629/4503599627370496), (-84919093/562949953421312)), (35/1125899906842624), by norm_num⟩
  | 16 => ⟨((523488871/18014398509481984), (919860667/36028797018963968)), (3/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (938997731171/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778366046469993/633825300114114700748351602688), (1110776191099/633825300114114700748351602688)), (46155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944644443635771/19807040628566084398385987584), (624684839903/19807040628566084398385987584)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889035780199037/2475880078570760549798248448), (663569546891/1237940039285380274899124224)), (110355/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770702175644589/154742504910672534362390528), (663391763835/77371252455336267181195264)), (27591/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549095600614735/9671406556917033397649408), (1243481898819/9671406556917033397649408)), (25869/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258388241891591/604462909807314587353088), (543834575043/302231454903657293676544)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887141617528073/75557863725914323419136), (883377423635/37778931862957161709568)), (36791/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297051886287915/4722366482869645213696), (82777960381/295147905179352825856)), (110389/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620778121274501/590295810358705651712), (56878444155/18446744073709551616)), (151811/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455659435605949/18446744073709551616), (568407853943/18446744073709551616)), (94901/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910858120148523/4611686018427387904), (638941442889/2305843009213693952)), (106791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592965780087317/1152921504606846976), (2553181296373/1152921504606846976)), (213649/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193689353796405/144115188075855872), (2231129518315/144115188075855872)), (46755/36028797018963968), by norm_num⟩
  | 4 => ⟨((745151304003049/18014398509481984), (835223645323/9007199254740992)), (280681/36028797018963968), by norm_num⟩
  | 3 => ⟨((371898310621397/2251799813685248), (4165987934865/9007199254740992)), (175559/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224631339825601/4503599627370496), (2075415388901/1125899906842624)), (10985/70368744177664), by norm_num⟩
  | 1 => ⟨((1105579434842093/1125899906842624), (12376973860047/2251799813685248)), (264145/562949953421312), by norm_num⟩
  | 0 => ⟨((1085481852198561/1125899906842624), (24453472494429/2251799813685248)), (2121291/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085481852198561/1125899906842624), (24453472494429/2251799813685248)), (8092082985884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523190983147419/562949953421312), (5893907720975/281474976710656)), (2068177/1125899906842624), by norm_num⟩
  | 2 => ⟨((485993205241665/562949953421312), (43821151153865/1125899906842624)), (7861665/2251799813685248), by norm_num⟩
  | 3 => ⟨((837407733268075/1125899906842624), (151322735367261/2251799813685248)), (7092939/1125899906842624), by norm_num⟩
  | 4 => ⟨((1235504266321317/2251799813685248), (7034308070243/70368744177664)), (23008595/2251799813685248), by norm_num⟩
  | 5 => ⟨((327693815707173/1125899906842624), (247010735603331/2251799813685248)), (59696965/4503599627370496), by norm_num⟩
  | 6 => ⟨((654620613551785/9007199254740992), (575140933779687/9007199254740992)), (47846567/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-415610435/8388608)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile008Terms1
