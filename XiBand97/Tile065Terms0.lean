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
namespace Reinmann.XiBand97.Tile065Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨65,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81383/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81383/2560))
  have he : value ((69/80), (81383/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/4294967296), (-1478764711/67108864)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1237279328243149/2251799813685248), (13669302592569/562949953421312)), (1543899/2251799813685248), by norm_num⟩
  | 1 => ⟨((104689535881/274877906944), (-1156596503/68719476736)), (133/274877906944), by norm_num⟩
  | 2 => ⟨((-36282628315/274877906944), (801691605/137438953472)), (47/274877906944), by norm_num⟩
  | 3 => ⟨((33532268693/1099511627776), (-1481840735/1099511627776)), (89/2199023255552), by norm_num⟩
  | 4 => ⟨((-92971190009/17592186044416), (2054267455/8796093022208)), (125/17592186044416), by norm_num⟩
  | 5 => ⟨((103108349165/140737488355328), (-4556511023/140737488355328)), (141/140737488355328), by norm_num⟩
  | 6 => ⟨((-5955771793/70368744177664), (2105555179/562949953421312)), (133/1125899906842624), by norm_num⟩
  | 7 => ⟨((75487568939/9007199254740992), (-3335907739/9007199254740992)), (107/9007199254740992), by norm_num⟩
  | 8 => ⟨((-104647991155/144115188075855872), (578068761/18014398509481984)), (151/144115188075855872), by norm_num⟩
  | 9 => ⟨((128953706703/2305843009213693952), (-2849327871/1152921504606846976)), (47/576460752303423488), by norm_num⟩
  | 10 => ⟨((-71507118579/18446744073709551616), (98750179/576460752303423488)), (53/9223372036854775808), by norm_num⟩
  | 11 => ⟨((36047241915/147573952589676412928), (-1592981135/147573952589676412928)), (109/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-33314725467/2361183241434822606848), (2944454353/4722366482869645213696)), (51/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((113683731833/151115727451828646838272), (-5023852881/151115727451828646838272)), (11/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-45028318969/1208925819614629174706176), (1989868263/1208925819614629174706176)), (71/1208925819614629174706176), by norm_num⟩
  | 15 => ⟨((66584004989/38685626227668133590597632), (-2942446029/38685626227668133590597632)), (107/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-92305030657/1237940039285380274899124224), (2039548169/618970019642690137449562112)), (75/618970019642690137449562112), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (4034748277635/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1781036219466553/633825300114114700748351602688), (1196638096259/158456325028528675187087900672)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473072934381019/9903520314283042199192993792), (5384544192873/39614081257132168796771975168)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892224974658177/2475880078570760549798248448), (5720724530121/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773889869614119/154742504910672534362390528), (1430081578047/38685626227668133590597632)), (217/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552082469743601/9671406556917033397649408), (1340595627171/2417851639229258349412352)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261000158752075/604462909807314587353088), (2345830473095/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472845748774649/18889465931478580854784), (7623153786325/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300230306277659/4722366482869645213696), (1429167193303/1180591620717411303424)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625144203687073/590295810358705651712), (982410786257/73786976294838206464)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228511122525771/9223372036854775808), (9822405587431/73786976294838206464)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827840134470587/9223372036854775808), (11047861816269/9223372036854775808)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599078744646461/1152921504606846976), (11044925471949/1152921504606846976)), (1685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299756477487705/36028797018963968), (4830499245859/72057594037927936)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((749141443269971/18014398509481984), (7242427697647/18014398509481984)), (2221/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497525663169281/9007199254740992), (18094400769683/9007199254740992)), (2785/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122183789472607/2251799813685248), (2259601182681/281474976710656)), (1399/1125899906842624), by norm_num⟩
  | 1 => ⟨((4375863973809/4398046511104), (27070926529083/1125899906842624)), (2115/562949953421312), by norm_num⟩
  | 0 => ⟨((1114125489619789/1125899906842624), (53962851627143/1125899906842624)), (8593/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114125489619789/1125899906842624), (53962851627143/1125899906842624)), (32779697898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((549943920298191/562949953421312), (53398519819555/562949953421312)), (17831/1125899906842624), by norm_num⟩
  | 2 => ⟨((1064346525773003/1125899906842624), (208659339248291/1125899906842624)), (19111/562949953421312), by norm_num⟩
  | 3 => ⟨((483744070165283/562949953421312), (98625926447497/281474976710656)), (86433/1125899906842624), by norm_num⟩
  | 4 => ⟨((693134552241637/1125899906842624), (338997857934473/562949953421312)), (52279/281474976710656), by norm_num⟩
  | 5 => ⟨((36872401620105/2251799813685248), (1669570284479143/2251799813685248)), (509327/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1237279328243149/2251799813685248), (13669302592569/562949953421312)), (1543899/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-1478764711/67108864)), (1/2147483648), by norm_num⟩, -4, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1017427393/1073741824), (-37500585829/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-407333490296325/1125899906842624), (313753535151349/2251799813685248)), (2365817/2251799813685248), by norm_num⟩
  | 1 => ⟨((27313328737/68719476736), (-5259605245/34359738368)), (161/137438953472), by norm_num⟩
  | 2 => ⟨((-30006758595/137438953472), (23113067823/274877906944)), (179/274877906944), by norm_num⟩
  | 3 => ⟨((87908783295/1099511627776), (-8464100113/274877906944)), (265/1099511627776), by norm_num⟩
  | 4 => ⟨((-48288834805/2199023255552), (37195057587/4398046511104)), (147/2199023255552), by norm_num⟩
  | 5 => ⟨((21220282929/4398046511104), (-16345178937/8796093022208)), (261/17592186044416), by norm_num⟩
  | 6 => ⟨((-62167636253/70368744177664), (23942685921/70368744177664)), (193/70368744177664), by norm_num⟩
  | 7 => ⟨((78055004737/562949953421312), (-30061404545/562949953421312)), (245/562949953421312), by norm_num⟩
  | 8 => ⟨((-21438046849/1125899906842624), (1032057139/140737488355328)), (17/281474976710656), by norm_num⟩
  | 9 => ⟨((20935201523/9007199254740992), (-16125591545/18014398509481984)), (67/9007199254740992), by norm_num⟩
  | 10 => ⟨((-73598942909/288230376151711744), (28345236853/288230376151711744)), (119/144115188075855872), by norm_num⟩
  | 11 => ⟨((58804874991/2305843009213693952), (-22647582205/2305843009213693952)), (3/36028797018963968), by norm_num⟩
  | 12 => ⟨((-43069172199/18446744073709551616), (8293637373/9223372036854775808)), (71/9223372036854775808), by norm_num⟩
  | 13 => ⟨((58235473035/295147905179352825856), (-11214143921/147573952589676412928)), (97/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-9139743759/590295810358705651712), (28159991585/4722366482869645213696)), (123/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((21420874259/18889465931478580854784), (-16499686829/37778931862957161709568)), (291/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-23533235695/302231454903657293676544), (36253517419/1208925819614629174706176)), (161/604462909807314587353088), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (1806702624283/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445124591953243/158456325028528675187087900672), (4284231440989/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945843426690607/19807040628566084398385987584), (4819325180715/39614081257132168796771975168)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118223907259183/154742504910672534362390528), (5120034614443/2475880078570760549798248448)), (433/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443311917738551/38685626227668133590597632), (1279868427419/38685626227668133590597632)), (1733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551480684636873/9671406556917033397649408), (1199727620915/2417851639229258349412352)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260473872971089/604462909807314587353088), (32800393567/4722366482869645213696)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236316037332859/9444732965739290427392), (6821363428945/75557863725914323419136)), (289/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((40612179289725/147573952589676412928), (5115043566367/4722366482869645213696)), (1735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624264158148363/590295810358705651712), (3515796657451/295147905179352825856)), (2387/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826990028898815/73786976294838206464), (8787103027739/73786976294838206464)), (1493/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913302667517909/4611686018427387904), (9882204559071/9223372036854775808)), (1681/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798922923518315/576460752303423488), (9878093629443/1152921504606846976)), (1683/576460752303423488), by norm_num⟩
  | 5 => ⟨((299487316311983/36028797018963968), (4319351509257/72057594037927936)), (1475/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496672203761635/36028797018963968), (12948786457767/36028797018963968)), (4433/36028797018963968), by norm_num⟩
  | 3 => ⟨((747759906788957/4503599627370496), (16169740938157/9007199254740992)), (2779/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120189208383337/2251799813685248), (4036332968083/562949953421312)), (5581/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117257520769055/1125899906842624), (24156815329699/1125899906842624)), (8431/1125899906842624), by norm_num⟩
  | 0 => ⟨((138538911987967/140737488355328), (6008493444557/140737488355328)), (8551/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138538911987967/140737488355328), (6008493444557/140737488355328)), (32619478465843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((17014770162881/17592186044416), (23658519253779/281474976710656)), (35131/1125899906842624), by norm_num⟩
  | 2 => ⟨((1045249431013089/1125899906842624), (183055939258859/1125899906842624)), (73863/1125899906842624), by norm_num⟩
  | 3 => ⟨((470306858406763/562949953421312), (339886547980031/1125899906842624)), (161163/1125899906842624), by norm_num⟩
  | 4 => ⟨((683214639316509/1125899906842624), (283952372006993/562949953421312)), (366587/1125899906842624), by norm_num⟩
  | 5 => ⟨((256268686454313/2251799813685248), (344613968337315/562949953421312)), (203679/281474976710656), by norm_num⟩
  | 6 => ⟨((-407333490296325/1125899906842624), (313753535151349/2251799813685248)), (2365817/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-37500585829/1073741824)), (1/1073741824), by norm_num⟩, -6, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-2567700857/2147483648), (-1478764711/33554432)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((678510820312869/2251799813685248), (-15021535597003/562949953421312)), (1408655/4503599627370496), by norm_num⟩
  | 1 => ⟨((-57410627695/137438953472), (1271012579/34359738368)), (61/137438953472), by norm_num⟩
  | 2 => ⟨((39794014721/137438953472), (-7047990285/274877906944)), (87/274877906944), by norm_num⟩
  | 3 => ⟨((-73554957619/549755813888), (3256863063/274877906944)), (41/274877906944), by norm_num⟩
  | 4 => ⟨((101968822979/2199023255552), (-4514970899/1099511627776)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((-28271760861/2199023255552), (10014525917/8796093022208)), (131/8796093022208), by norm_num⟩
  | 6 => ⟨((26128655107/8796093022208), (-9255387205/35184372088832)), (123/35184372088832), by norm_num⟩
  | 7 => ⟨((-41396579701/70368744177664), (7331823481/140737488355328)), (99/140737488355328), by norm_num⟩
  | 8 => ⟨((57387845009/562949953421312), (-2541016387/281474976710656)), (139/1125899906842624), by norm_num⟩
  | 9 => ⟨((-70716840829/4503599627370496), (6262394113/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 10 => ⟨((39213743071/18014398509481984), (-6945217317/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 11 => ⟨((-79071695851/288230376151711744), (7002265893/288230376151711744)), (101/288230376151711744), by norm_num⟩
  | 12 => ⟨((73077764055/2305843009213693952), (-6471467815/2305843009213693952)), (95/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-31171474533/9223372036854775808), (5520836517/18446744073709551616)), (41/9223372036854775808), by norm_num⟩
  | 14 => ⟨((98772204281/295147905179352825856), (-4373431161/147573952589676412928)), (33/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-73027919909/2361183241434822606848), (6467053821/2361183241434822606848)), (99/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((50619096787/18889465931478580854784), (-8965240245/37778931862957161709568)), (139/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (-115053828615/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890062504608355/316912650057057350374175801344), (-136357735087/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945633725099749/19807040628566084398385987584), (-153386128817/39614081257132168796771975168)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891137672685711/2475880078570760549798248448), (-162952878289/2475880078570760549798248448)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772803696263527/154742504910672534362390528), (-10183157101/9671406556917033397649408)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775532690585357/4835703278458516698824704), (-152723598391/9671406556917033397649408)), (1615/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260111404949625/604462909807314587353088), (-66804697675/302231454903657293676544)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889941017210129/75557863725914323419136), (-217070740489/75557863725914323419136)), (2297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649575394250825/2361183241434822606848), (-81382052325/2361183241434822606848)), (1723/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623663059934719/590295810358705651712), (-111868684209/295147905179352825856)), (2369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456560584647751/18446744073709551616), (-279576831311/73786976294838206464)), (2961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825769243476983/9223372036854775808), (-39299191443/1152921504606846976)), (3331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199627009438445/144115188075855872), (-314230609753/1152921504606846976)), (3331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197230318293365/144115188075855872), (-274768610319/144115188075855872)), (2915/144115188075855872), by norm_num⟩
  | 4 => ⟨((93475498271327/2251799813685248), (-411786853359/36028797018963968)), (1093/9007199254740992), by norm_num⟩
  | 3 => ⟨((186776789529299/1125899906842624), (-514093597155/9007199254740992)), (5465/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118920821227817/2251799813685248), (-1026269839705/4503599627370496)), (10931/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230894886739969/2251799813685248), (-1534620300257/2251799813685248)), (16401/2251799813685248), by norm_num⟩
  | 0 => ⟨((2210119040870143/2251799813685248), (-3050156231733/2251799813685248)), (2051/140737488355328), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210119040870143/2251799813685248), (-3050156231733/2251799813685248)), (7823944628667787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2169205646824201/2251799813685248), (-2993697896417/1125899906842624)), (64507/2251799813685248), by norm_num⟩
  | 2 => ⟨((522406261505639/562949953421312), (-11535566069997/2251799813685248)), (62313/1125899906842624), by norm_num⟩
  | 3 => ⟨((969535510471123/1125899906842624), (-21409547716823/2251799813685248)), (232579/2251799813685248), by norm_num⟩
  | 4 => ⟨((1669570284479145/2251799813685248), (-36872401620133/2251799813685248)), (101245/562949953421312), by norm_num⟩
  | 5 => ⟨((1237279328243151/2251799813685248), (-54677210370317/2251799813685248)), (613799/2251799813685248), by norm_num⟩
  | 6 => ⟨((678510820312869/2251799813685248), (-15021535597003/562949953421312)), (1408655/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-1478764711/33554432)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-109874730503/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((349762509225997/2251799813685248), (-879570474413857/4503599627370496)), (2108017/4503599627370496), by norm_num⟩
  | 1 => ⟨((-17178986899/68719476736), (43201112921/137438953472)), (53/68719476736), by norm_num⟩
  | 2 => ⟨((55297025625/274877906944), (-69529508995/274877906944)), (173/274877906944), by norm_num⟩
  | 3 => ⟨((-59331419657/549755813888), (74602285207/549755813888)), (47/137438953472), by norm_num⟩
  | 4 => ⟨((47745118097/1099511627776), (-60033873083/1099511627776)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((-1876045/134217728), (9662079137/549755813888)), (101/2199023255552), by norm_num⟩
  | 6 => ⟨((4122457359/1099511627776), (-1295876373/274877906944)), (55/4398046511104), by norm_num⟩
  | 7 => ⟨((-60661386661/70368744177664), (9534320295/8796093022208)), (205/70368744177664), by norm_num⟩
  | 8 => ⟨((48815367757/281474976710656), (-61379586209/281474976710656)), (167/281474976710656), by norm_num⟩
  | 9 => ⟨((-34917912701/1125899906842624), (5488146283/140737488355328)), (121/1125899906842624), by norm_num⟩
  | 10 => ⟨((44958570019/9007199254740992), (-14132529115/2251799813685248)), (79/4503599627370496), by norm_num⟩
  | 11 => ⟨((-52624019693/72057594037927936), (66168518273/72057594037927936)), (187/72057594037927936), by norm_num⟩
  | 12 => ⟨((56463394933/576460752303423488), (-70996081279/576460752303423488)), (203/576460752303423488), by norm_num⟩
  | 13 => ⟨((-27961331837/2305843009213693952), (70316175289/4611686018427387904)), (203/4611686018427387904), by norm_num⟩
  | 14 => ⟨((25715444309/18446744073709551616), (-32334148105/18446744073709551616)), (189/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-11036642935/73786976294838206464), (27754562041/147573952589676412928)), (41/73786976294838206464), by norm_num⟩
  | 16 => ⟨((35525583131/2361183241434822606848), (-5583655549/295147905179352825856)), (67/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (-585475734561/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779826914760415/633825300114114700748351602688), (-1387330172695/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945466036396943/19807040628566084398385987584), (-195069197351/4951760157141521099596496896)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945390652973465/1237940039285380274899124224), (-1657853242809/2475880078570760549798248448)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886223648889853/77371252455336267181195264), (-1657588991039/154742504910672534362390528)), (863/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550731223890149/9671406556917033397649408), (-1553708962949/9671406556917033397649408)), (809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((19684671619651/9444732965739290427392), (-169901835525/75557863725914323419136)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889465769541511/75557863725914323419136), (-1104098875049/37778931862957161709568)), (2301/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649397148814719/2361183241434822606848), (-827844043761/2361183241434822606848)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811586397767807/295147905179352825856), (-2275823484657/590295810358705651712)), (1187/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228203671766215/9223372036854775808), (-710914576181/18446744073709551616)), (371/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912539737302243/4611686018427387904), (-3197574801293/9223372036854775808)), (835/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798163038667397/576460752303423488), (-3195649792129/1152921504606846976)), (3341/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196626312639077/144115188075855872), (-2794029280031/144115188075855872)), (2925/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494701451125555/36028797018963968), (-1046679677539/9007199254740992)), (4391/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493080271410741/9007199254740992), (-5225836839557/9007199254740992)), (5493/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117785444394601/2251799813685248), (-10429019286695/4503599627370496)), (11001/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227482151681185/2251799813685248), (-15586998719885/2251799813685248)), (4135/562949953421312), by norm_num⟩
  | 0 => ⟨((2203267484354779/2251799813685248), (-30948510336291/2251799813685248)), (33233/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203267484354779/2251799813685248), (-30948510336291/2251799813685248)), (126773842818450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155355803755921/2251799813685248), (-15140743439705/562949953421312)), (16487/562949953421312), by norm_num⟩
  | 2 => ⟨((2061413602924587/2251799813685248), (-115938154173803/2251799813685248)), (129795/2251799813685248), by norm_num⟩
  | 3 => ⟨((235144369904977/281474976710656), (-212271523125059/2251799813685248)), (251009/2251799813685248), by norm_num⟩
  | 4 => ⟨((387876928480715/562949953421312), (-88665880955595/562949953421312)), (466711/2251799813685248), by norm_num⟩
  | 5 => ⟨((506570334842145/1125899906842624), (-488731893228943/2251799813685248)), (98769/281474976710656), by norm_num⟩
  | 6 => ⟨((349762509225997/2251799813685248), (-879570474413857/4503599627370496)), (2108017/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-109874730503/2147483648)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1659352607/1073741824), (-61160821205/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((220005224410443/1125899906842624), (-192177154717013/2251799813685248)), (1314565/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3007480195/8589934592), (656767343/4294967296)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((43109448943/137438953472), (-37656611389/274877906944)), (135/274877906944), by norm_num⟩
  | 3 => ⟨((-6436813613/34359738368), (5622632503/68719476736)), (41/137438953472), by norm_num⟩
  | 4 => ⟨((46132886971/549755813888), (-40297620117/1099511627776)), (149/1099511627776), by norm_num⟩
  | 5 => ⟨((-33063614829/1099511627776), (28881456973/2199023255552)), (109/2199023255552), by norm_num⟩
  | 6 => ⟨((19747348319/2199023255552), (-17249541339/4398046511104)), (33/2199023255552), by norm_num⟩
  | 7 => ⟨((-40437140963/17592186044416), (2207644931/2199023255552)), (137/35184372088832), by norm_num⟩
  | 8 => ⟨((72453630229/140737488355328), (-15822274839/70368744177664)), (125/140737488355328), by norm_num⟩
  | 9 => ⟨((-57697545797/562949953421312), (3149967863/70368744177664)), (101/562949953421312), by norm_num⟩
  | 10 => ⟨((41352049613/2251799813685248), (-4515187797/562949953421312)), (147/4503599627370496), by norm_num⟩
  | 11 => ⟨((-53885764703/18014398509481984), (2941865633/2251799813685248)), (49/9007199254740992), by norm_num⟩
  | 12 => ⟨((64366886109/144115188075855872), (-28112616561/144115188075855872)), (119/144115188075855872), by norm_num⟩
  | 13 => ⟨((-70972293963/1152921504606846976), (7749391835/288230376151711744)), (133/1152921504606846976), by norm_num⟩
  | 14 => ⟨((72665874149/9223372036854775808), (-7934312115/2305843009213693952)), (69/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-34719938159/36893488147419103232), (15164137455/36893488147419103232)), (67/36893488147419103232), by norm_num⟩
  | 16 => ⟨((62209777967/590295810358705651712), (-13585243439/295147905179352825856)), (61/295147905179352825856), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (-536396857685/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792533903419/316912650057057350374175801344), (-317676118915/316912650057057350374175801344)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118166254871589/2475880078570760549798248448), (-357336828247/19807040628566084398385987584)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890492414707423/2475880078570760549798248448), (-759221038035/2475880078570760549798248448)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772158522693733/154742504910672534362390528), (-759086385187/154742504910672534362390528)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460620618997/9671406556917033397649408), (-355750225245/4835703278458516698824704)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259582329121023/604462909807314587353088), (-622419895713/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889081437056583/75557863725914323419136), (-63197767959/4722366482869645213696)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298506250412335/4722366482869645213696), (-758138756627/4722366482869645213696)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622777058915933/590295810358705651712), (-1042059942577/590295810358705651712)), (2371/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825135195488373/73786976294838206464), (-651001957625/36893488147419103232)), (2963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824524199792447/9223372036854775808), (-182996210251/1152921504606846976)), (3335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24933931983391/18014398509481984), (-731494704303/576460752303423488)), (3335/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196142134928479/144115188075855872), (-1279013790475/144115188075855872)), (2919/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493977079640707/36028797018963968), (-1916318963601/36028797018963968)), (1095/9007199254740992), by norm_num⟩
  | 3 => ⟨((93261132337039/562949953421312), (-597887637585/2251799813685248)), (5477/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233776487587567/4503599627370496), (-4771576051551/4503599627370496)), (10959/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224815232501259/2251799813685248), (-7128619289821/2251799813685248)), (2057/281474976710656), by norm_num⟩
  | 0 => ⟨((549507967751449/562949953421312), (-14142665551659/2251799813685248)), (4123/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549507967751449/562949953421312), (-14142665551659/2251799813685248)), (15727997899913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2145458962029927/2251799813685248), (-27609940665771/2251799813685248)), (8101/281474976710656), by norm_num⟩
  | 2 => ⟨((2043801505338545/2251799813685248), (-26306066055467/1125899906842624)), (125085/2251799813685248), by norm_num⟩
  | 3 => ⟨((1853786704932345/2251799813685248), (-23876179879289/562949953421312)), (58227/562949953421312), by norm_num⟩
  | 4 => ⟨((380518283097805/562949953421312), (-78623942600585/1125899906842624)), (403239/2251799813685248), by norm_num⟩
  | 5 => ⟨((508921732077945/1125899906842624), (-106289546582001/1125899906842624)), (601447/2251799813685248), by norm_num⟩
  | 6 => ⟨((220005224410443/1125899906842624), (-192177154717013/2251799813685248)), (1314565/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-61160821205/1073741824)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-132845356479/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((118659349636471/1125899906842624), (346974911697185/2251799813685248)), (1646197/4503599627370496), by norm_num⟩
  | 1 => ⟨((-28186087981/137438953472), (-20604919499/68719476736)), (25/34359738368), by norm_num⟩
  | 2 => ⟨((6855949333/34359738368), (80190643947/274877906944)), (49/68719476736), by norm_num⟩
  | 3 => ⟨((-35576163703/274877906944), (-13003648993/68719476736)), (129/274877906944), by norm_num⟩
  | 4 => ⟨((34614009007/549755813888), (12651966275/137438953472)), (127/549755813888), by norm_num⟩
  | 5 => ⟨((-53884601141/2199023255552), (-1230979479/34359738368)), (199/2199023255552), by norm_num⟩
  | 6 => ⟨((17475765373/2199023255552), (25550671589/2199023255552)), (131/4398046511104), by norm_num⟩
  | 7 => ⟨((-38864307659/17592186044416), (-56822069897/17592186044416)), (147/17592186044416), by norm_num⟩
  | 8 => ⟨((37813225355/70368744177664), (55285321251/70368744177664)), (145/70368744177664), by norm_num⟩
  | 9 => ⟨((-16351364219/140737488355328), (-23906726159/140737488355328)), (127/281474976710656), by norm_num⟩
  | 10 => ⟨((50909256935/2251799813685248), (74432545701/2251799813685248)), (25/281474976710656), by norm_num⟩
  | 11 => ⟨((-36023578091/9007199254740992), (-13167186009/2251799813685248)), (143/9007199254740992), by norm_num⟩
  | 12 => ⟨((5841553851/9007199254740992), (17081440593/18014398509481984)), (47/18014398509481984), by norm_num⟩
  | 13 => ⟨((-27980649661/288230376151711744), (-40909475213/288230376151711744)), (57/144115188075855872), by norm_num⟩
  | 14 => ⟨((31113045801/2305843009213693952), (45489236005/2305843009213693952)), (1/18014398509481984), by norm_num⟩
  | 15 => ⟨((-16144851091/9223372036854775808), (-23604790937/9223372036854775808)), (135/18446744073709551616), by norm_num⟩
  | 16 => ⟨((31416429593/147573952589676412928), (45932802251/147573952589676412928)), (133/147573952589676412928), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (632361527825/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779378968023647/633825300114114700748351602688), (187214104749/79228162514264337593543950336)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945214095965989/19807040628566084398385987584), (26323076349/618970019642690137449562112)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890246003735069/2475880078570760549798248448), (894831306727/1237940039285380274899124224)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771912075668173/154742504910672534362390528), (447329449387/38685626227668133590597632)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550229538259375/9671406556917033397649408), (104819946997/604462909807314587353088)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629690046910373/302231454903657293676544), (733556534405/302231454903657293676544)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236094091635203/9444732965739290427392), (1191686166037/37778931862957161709568)), (1151/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324564914962579/1180591620717411303424), (893464422381/2361183241434822606848)), (1727/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622437895348705/590295810358705651712), (307006484897/73786976294838206464)), (2375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824711088973811/73786976294838206464), (3068602580725/73786976294838206464)), (2969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912023435655597/4611686018427387904), (431271043613/1152921504606846976)), (3341/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595294058275593/1152921504606846976), (3447658001721/1152921504606846976)), (1671/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195723953019441/144115188075855872), (1506939401943/72057594037927936)), (1463/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493349225294295/36028797018963968), (282198736817/2251799813685248)), (549/4503599627370496), by norm_num⟩
  | 3 => ⟨((1491392286755367/9007199254740992), (2817059911413/4503599627370496)), (5495/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116100903858931/2251799813685248), (2809681028627/1125899906842624)), (11007/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222445734315805/2251799813685248), (16784469334691/2251799813685248)), (2069/281474976710656), by norm_num⟩
  | 0 => ⟨((2193263368123085/2251799813685248), (33275501330897/2251799813685248)), (33271/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193263368123085/2251799813685248), (33275501330897/2251799813685248)), (126918801314543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1067878439667113/1125899906842624), (8102622808813/281474976710656)), (65797/2251799813685248), by norm_num⟩
  | 2 => ⟨((505957019376061/562949953421312), (122961071757095/2251799813685248)), (128601/2251799813685248), by norm_num⟩
  | 3 => ⟨((453055444507785/562949953421312), (221025037793885/2251799813685248)), (245209/2251799813685248), by norm_num⟩
  | 4 => ⟨((718379956729755/1125899906842624), (355756657004699/2251799813685248)), (110705/562949953421312), by norm_num⟩
  | 5 => ⟨((215129719585263/562949953421312), (226990383702981/1125899906842624)), (705003/2251799813685248), by norm_num⟩
  | 6 => ⟨((118659349636471/1125899906842624), (346974911697185/2251799813685248)), (1646197/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-132845356479/2147483648)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1925775643/1073741824), (-4436294133/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1485428791738805/9007199254740992), (197961506254913/9007199254740992)), (7818171/9007199254740992), by norm_num⟩
  | 1 => ⟨((5891537355/17179869184), (-12562542107/274877906944)), (499/274877906944), by norm_num⟩
  | 2 => ⟨((-98008860163/274877906944), (13061535963/274877906944)), (521/274877906944), by norm_num⟩
  | 3 => ⟨((16983641273/68719476736), (-9053566827/274877906944)), (363/274877906944), by norm_num⟩
  | 4 => ⟨((-4414561149/34359738368), (1176647685/68719476736)), (95/137438953472), by norm_num⟩
  | 5 => ⟨((29375429893/549755813888), (-15659328487/2199023255552)), (635/2199023255552), by norm_num⟩
  | 6 => ⟨((-81445985633/4398046511104), (5427109695/2199023255552)), (443/4398046511104), by norm_num⟩
  | 7 => ⟨((96778380531/17592186044416), (-6448775629/8796093022208)), (529/17592186044416), by norm_num⟩
  | 8 => ⟨((-100622492407/70368744177664), (419057873/2199023255552)), (69/8796093022208), by norm_num⟩
  | 9 => ⟨((46497464609/140737488355328), (-3098333687/70368744177664)), (513/281474976710656), by norm_num⟩
  | 10 => ⟨((-77351007593/1125899906842624), (5154243023/562949953421312)), (107/281474976710656), by norm_num⟩
  | 11 => ⟨((116979562531/9007199254740992), (-15589741175/9007199254740992)), (325/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1266938343/562949953421312), (10805985141/36028797018963968)), (453/36028797018963968), by norm_num⟩
  | 13 => ⟨((103759723173/288230376151711744), (-3456986831/72057594037927936)), (291/144115188075855872), by norm_num⟩
  | 14 => ⟨((-61646365349/1152921504606846976), (2053886293/288230376151711744)), (87/288230376151711744), by norm_num⟩
  | 15 => ⟨((34184003467/4611686018427387904), (-2277832789/2305843009213693952)), (97/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-71083636871/73786976294838206464), (9473240253/73786976294838206464)), (203/36893488147419103232), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (979923612255/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222398875669479/79228162514264337593543950336), (580113325479/79228162514264337593543950336)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945108087052677/19807040628566084398385987584), (5220163995389/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890020013244801/2475880078570760549798248448), (5545405611625/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771685273936753/154742504910672534362390528), (693032440307/19342813113834066795298816)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387504012546333/2417851639229258349412352), (5196525607249/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259192430859193/604462909807314587353088), (1136435559687/151115727451828646838272)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888446167764749/75557863725914323419136), (3692274035051/37778931862957161709568)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649014162830287/2361183241434822606848), (5536413427661/4722366482869645213696)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622117521465001/590295810358705651712), (1902330608825/147573952589676412928)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824307191418197/73786976294838206464), (2376696050587/18446744073709551616)), (5975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911793888150755/4611686018427387904), (2672109474901/2305843009213693952)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398707271209107/288230376151711744), (333752202871/36028797018963968)), (6737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195310500936953/144115188075855872), (9335649050689/144115188075855872)), (5905/144115188075855872), by norm_num⟩
  | 4 => ⟨((746357939387133/18014398509481984), (3496162529129/9007199254740992)), (8877/36028797018963968), by norm_num⟩
  | 3 => ⟨((93161101962907/562949953421312), (4361968937677/2251799813685248)), (5565/4503599627370496), by norm_num⟩
  | 2 => ⟨((278812983757667/562949953421312), (17398478999857/2251799813685248)), (5591/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109864136313551/1125899906842624), (12987128959417/562949953421312)), (16903/1125899906842624), by norm_num⟩
  | 0 => ⟨((546788071186617/562949953421312), (25727435532037/562949953421312)), (17163/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546788071186617/562949953421312), (25727435532037/562949953421312)), (65471651317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1059828825066681/1125899906842624), (99955278551111/1125899906842624)), (17455/281474976710656), by norm_num⟩
  | 2 => ⟨((494380572360949/562949953421312), (94089612035863/562949953421312)), (143843/1125899906842624), by norm_num⟩
  | 3 => ⟨((836874730349565/1125899906842624), (165258300382865/562949953421312)), (300729/1125899906842624), by norm_num⟩
  | 4 => ⟨((1050036663691721/2251799813685248), (245671031199879/562949953421312)), (623623/1125899906842624), by norm_num⟩
  | 5 => ⟨((121599535741845/4503599627370496), (916470774707625/2251799813685248)), (4503603/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1485428791738805/9007199254740992), (197961506254913/9007199254740992)), (7818171/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-4436294133/67108864)), (1/536870912), by norm_num⟩, -11, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile065Terms0
