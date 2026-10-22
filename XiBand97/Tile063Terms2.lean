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
namespace Reinmann.XiBand97.Tile063Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨63,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80667/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80667/2560))
  have he : value ((69/80), (80667/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2567700857/1073741824), (-46904149689/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((42550118707465/562949953421312), (232285336579311/4503599627370496)), (2615791/9007199254740992), by norm_num⟩
  | 1 => ⟨((-14401120515/68719476736), (-39308575717/274877906944)), (7/8589934592), by norm_num⟩
  | 2 => ⟨((79856768655/274877906944), (13623314215/68719476736)), (313/274877906944), by norm_num⟩
  | 3 => ⟨((-73803325389/274877906944), (-1573826973/8589934592)), (291/274877906944), by norm_num⟩
  | 4 => ⟨((51156566909/274877906944), (34908599329/274877906944)), (51/68719476736), by norm_num⟩
  | 5 => ⟨((-886475753/8589934592), (-38714875523/549755813888)), (57/137438953472), by norm_num⟩
  | 6 => ⟨((13108440935/274877906944), (35780142419/1099511627776)), (213/1099511627776), by norm_num⟩
  | 7 => ⟨((-20768180287/1099511627776), (-28343891243/2199023255552)), (85/1099511627776), by norm_num⟩
  | 8 => ⟨((57581622445/8796093022208), (19646488301/4398046511104)), (119/4398046511104), by norm_num⟩
  | 9 => ⟨((-70955625333/35184372088832), (-48419228351/35184372088832)), (295/35184372088832), by norm_num⟩
  | 10 => ⟨((78692306631/140737488355328), (26849321293/70368744177664)), (329/140737488355328), by norm_num⟩
  | 11 => ⟨((-79338691597/562949953421312), (-6767465947/70368744177664)), (167/281474976710656), by norm_num⟩
  | 12 => ⟨((9165565065/281474976710656), (50035732701/2251799813685248)), (311/2251799813685248), by norm_num⟩
  | 13 => ⟨((-488698891/70368744177664), (-42685694829/9007199254740992)), (67/2251799813685248), by norm_num⟩
  | 14 => ⟨((49552860663/36028797018963968), (16907125155/18014398509481984)), (107/18014398509481984), by norm_num⟩
  | 15 => ⟨((-73274508069/288230376151711744), (-1562550151/9007199254740992)), (319/288230376151711744), by norm_num⟩
  | 16 => ⟨((50790018675/1152921504606846976), (34658471413/1152921504606846976)), (223/1152921504606846976), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (780013500247/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444570120353813/158456325028528675187087900672), (461311442191/316912650057057350374175801344)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472298164456005/9903520314283042199192993792), (518867771659/19807040628566084398385987584)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944466788079253/1237940039285380274899124224), (1102325149587/2475880078570760549798248448)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885300008145981/77371252455336267181195264), (1102022808887/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999873679713/9671406556917033397649408), (129103157663/1208925819614629174706176)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314576132063953/151115727451828646838272), (903401110993/604462909807314587353088)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471751417937759/18889465931478580854784), (1467425218951/75557863725914323419136)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324237501167889/1180591620717411303424), (1100042800761/4722366482869645213696)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620638160238989/590295810358705651712), (1511704431365/590295810358705651712)), (4743/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822462980231179/73786976294838206464), (944174904879/36893488147419103232)), (2965/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910759946277591/4611686018427387904), (530658498615/2305843009213693952)), (417/576460752303423488), by norm_num⟩
  | 6 => ⟨((398192439141705/288230376151711744), (2120436757763/1152921504606846976)), (6675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193518197368131/144115188075855872), (926456640013/72057594037927936)), (2921/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490046600178197/36028797018963968), (1387219832453/18014398509481984)), (8767/36028797018963968), by norm_num⟩
  | 3 => ⟨((371818625320143/2251799813685248), (3459438507351/9007199254740992)), (10965/9007199254740992), by norm_num⟩
  | 2 => ⟨((277999706225707/562949953421312), (6893111150253/4503599627370496)), (10975/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210217769052827/2251799813685248), (2568871802991/562949953421312)), (32977/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169118962437935/2251799813685248), (10147831228367/1125899906842624)), (33083/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169118962437935/2251799813685248), (10147831228367/1125899906842624)), (126201633933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089291033199665/2251799813685248), (4887613235265/281474976710656)), (128667/2251799813685248), by norm_num⟩
  | 2 => ⟨((484457822810005/562949953421312), (72558112451213/2251799813685248)), (7601/70368744177664), by norm_num⟩
  | 3 => ⟨((1665301422815837/2251799813685248), (62441332434059/1125899906842624)), (54289/281474976710656), by norm_num⟩
  | 4 => ⟨((1224635126128199/2251799813685248), (184712049646683/2251799813685248)), (345279/1125899906842624), by norm_num⟩
  | 5 => ⟨((650862764067717/2251799813685248), (50227569707065/562949953421312)), (108051/281474976710656), by norm_num⟩
  | 6 => ⟨((42550118707465/562949953421312), (232285336579311/4503599627370496)), (2615791/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-46904149689/536870912)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-95859484477/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((401110438410863/18014398509481984), (-189017518298103/2251799813685248)), (7236377/18014398509481984), by norm_num⟩
  | 1 => ⟨((-17340567727/274877906944), (65371942761/274877906944)), (315/274877906944), by norm_num⟩
  | 2 => ⟨((24564763939/274877906944), (-46303165139/137438953472)), (7/4294967296), by norm_num⟩
  | 3 => ⟨((-2899884041/34359738368), (87457830229/274877906944)), (425/274877906944), by norm_num⟩
  | 4 => ⟨((8215990161/137438953472), (-61946672911/274877906944)), (303/274877906944), by norm_num⟩
  | 5 => ⟨((-18622122367/549755813888), (17550814031/137438953472)), (345/549755813888), by norm_num⟩
  | 6 => ⟨((17586815195/1099511627776), (-66300267349/1099511627776)), (41/137438953472), by norm_num⟩
  | 7 => ⟨((-28472685423/4398046511104), (107338744095/4398046511104)), (267/2199023255552), by norm_num⟩
  | 8 => ⟨((10083649035/4398046511104), (-38014195263/4398046511104)), (95/2199023255552), by norm_num⟩
  | 9 => ⟨((-3174347667/4398046511104), (95735400251/35184372088832)), (481/35184372088832), by norm_num⟩
  | 10 => ⟨((7194883335/35184372088832), (-108495525395/140737488355328)), (547/140737488355328), by norm_num⟩
  | 11 => ⟨((-1853149043/35184372088832), (55889267331/281474976710656)), (71/70368744177664), by norm_num⟩
  | 12 => ⟨((28001955185/2251799813685248), (-105564145327/2251799813685248)), (539/2251799813685248), by norm_num⟩
  | 13 => ⟨((-5959699/2199023255552), (2875824473/281474976710656)), (59/1125899906842624), by norm_num⟩
  | 14 => ⟨((2470048729/4503599627370496), (-72748431/35184372088832)), (3/281474976710656), by norm_num⟩
  | 15 => ⟨((-14929440041/144115188075855872), (56282269141/144115188075855872)), (73/36028797018963968), by norm_num⟩
  | 16 => ⟨((5287286093/288230376151711744), (-39864918991/576460752303423488)), (13/36028797018963968), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-427096264659/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778198188200651/633825300114114700748351602688), (-505138391829/158456325028528675187087900672)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944550000571483/19807040628566084398385987584), (-1136319770929/19807040628566084398385987584)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944417512563315/1237940039285380274899124224), (-301759698559/309485009821345068724781056)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885250674588259/77371252455336267181195264), (-2413400691359/154742504910672534362390528)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774453625011957/4835703278458516698824704), (-2261844188093/9671406556917033397649408)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258223359438707/604462909807314587353088), (-123649686129/37778931862957161709568)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943436770912231/37778931862957161709568), (-3213544883173/75557863725914323419136)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648425352850243/2361183241434822606848), (-2408980656505/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((810250648568983/295147905179352825856), (-3310435231569/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822291411642641/73786976294838206464), (-4135176186421/73786976294838206464)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821326205855693/9223372036854775808), (-2324066501587/4611686018427387904)), (6689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796287615896611/576460752303423488), (-2321606189239/576460752303423488)), (6693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298336762016403/36028797018963968), (-2028640746813/72057594037927936)), (5861/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489788002728763/36028797018963968), (-6074879461037/36028797018963968)), (8799/36028797018963968), by norm_num⟩
  | 3 => ⟨((743473995506799/4503599627370496), (-7574310179765/9007199254740992)), (5507/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111667449683067/2251799813685248), (-7545447775295/2251799813685248)), (22073/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104599764695819/1125899906842624), (-22492529436525/2251799813685248)), (16611/1125899906842624), by norm_num⟩
  | 0 => ⟨((270873410614831/281474976710656), (-22206391766753/1125899906842624)), (66901/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270873410614831/281474976710656), (-22206391766753/1125899906842624)), (255207070357512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084493199231607/2251799813685248), (-85480011695573/2251799813685248)), (65701/1125899906842624), by norm_num⟩
  | 2 => ⟨((481593105976879/562949953421312), (-39564463494215/562949953421312)), (253255/2251799813685248), by norm_num⟩
  | 3 => ⟨((818426474868063/1125899906842624), (-270773240067795/2251799813685248)), (468909/2251799813685248), by norm_num⟩
  | 4 => ⟨((578641452869243/1125899906842624), (-196827432892101/1125899906842624)), (794479/2251799813685248), by norm_num⟩
  | 5 => ⟨((16436013252615/70368744177664), (-809254968695035/4503599627370496)), (1094403/2251799813685248), by norm_num⟩
  | 6 => ⟨((401110438410863/18014398509481984), (-189017518298103/2251799813685248)), (7236377/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-95859484477/1073741824)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-48896696615/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1488554301650835/18014398509481984), (-43168546008415/18014398509481984)), (237845/562949953421312), by norm_num⟩
  | 1 => ⟨((65650563257/274877906944), (3807774237/549755813888)), (337/274877906944), by norm_num⟩
  | 2 => ⟨((-23719316741/68719476736), (-2751470779/274877906944)), (489/274877906944), by norm_num⟩
  | 3 => ⟨((91410190967/274877906944), (2650924477/274877906944)), (473/274877906944), by norm_num⟩
  | 4 => ⟨((-66052358589/274877906944), (-957769655/137438953472)), (343/274877906944), by norm_num⟩
  | 5 => ⟨((19091587181/137438953472), (2214648289/549755813888)), (199/274877906944), by norm_num⟩
  | 6 => ⟨((-73575712535/1099511627776), (-533429739/274877906944)), (385/1099511627776), by norm_num⟩
  | 7 => ⟨((7595041485/274877906944), (440517215/549755813888)), (319/2199023255552), by norm_num⟩
  | 8 => ⟨((-43904986817/4398046511104), (-1273258517/4398046511104)), (463/8796093022208), by norm_num⟩
  | 9 => ⟨((112801541269/35184372088832), (3271280407/35184372088832)), (597/35184372088832), by norm_num⟩
  | 10 => ⟨((-130415355653/140737488355328), (-472760825/17592186044416)), (173/35184372088832), by norm_num⟩
  | 11 => ⟨((68536156505/281474976710656), (1987570235/281474976710656)), (365/281474976710656), by norm_num⟩
  | 12 => ⟨((-132063314105/2251799813685248), (-957469479/562949953421312)), (705/2251799813685248), by norm_num⟩
  | 13 => ⟨((58724934361/4503599627370496), (1703041687/4503599627370496)), (629/9007199254740992), by norm_num⟩
  | 14 => ⟨((-48496254789/18014398509481984), (-2812813483/36028797018963968)), (261/18014398509481984), by norm_num⟩
  | 15 => ⟨((74758509443/144115188075855872), (271002555/18014398509481984)), (101/36028797018963968), by norm_num⟩
  | 16 => ⟨((-108039942179/1152921504606846976), (-3133192525/1152921504606846976)), (293/576460752303423488), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-506813703311/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27783001611245/9903520314283042199192993792), (-2397494317191/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889002614488249/39614081257132168796771975168), (-5393162997191/39614081257132168796771975168)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888730831387883/2475880078570760549798248448), (-179024217223/77371252455336267181195264)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442599086443409/38685626227668133590597632), (-5727131772853/154742504910672534362390528)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387201987434743/2417851639229258349412352), (-5367440485413/9671406556917033397649408)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314533903212993/151115727451828646838272), (-586845654765/75557863725914323419136)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886729344909333/75557863725914323419136), (-3812861031575/37778931862957161709568)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296741151998903/4722366482869645213696), (-1429107451569/1180591620717411303424)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((202543547379437/73786976294838206464), (-3927721055779/295147905179352825856)), (2389/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822096846637163/73786976294838206464), (-9812331883525/73786976294838206464)), (5977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821102629881397/9223372036854775808), (-11029292730801/9223372036854775808)), (6731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592345805702589/1152921504606846976), (-11017323166789/1152921504606846976)), (1685/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193139736450641/144115188075855872), (-4813350296927/72057594037927936)), (1477/36028797018963968), by norm_num⟩
  | 4 => ⟨((93091496978549/2251799813685248), (-14413158025843/36028797018963968)), (4441/18014398509481984), by norm_num⟩
  | 3 => ⟨((371630032357241/2251799813685248), (-17969433460245/9007199254740992)), (5569/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111205588310441/2251799813685248), (-17899009461135/2251799813685248)), (1399/281474976710656), by norm_num⟩
  | 1 => ⟨((1103822660021713/1125899906842624), (-26672795084833/1125899906842624)), (8461/562949953421312), by norm_num⟩
  | 0 => ⟨((1081606287414929/1125899906842624), (-52644767097219/1125899906842624)), (34385/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1081606287414929/1125899906842624), (-52644767097219/1125899906842624)), (131168369773482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036593646006865/1125899906842624), (-101147376859683/1125899906842624)), (69281/1125899906842624), by norm_num⟩
  | 2 => ⟨((945284379746357/1125899906842624), (-186248755374779/1125899906842624)), (35005/281474976710656), by norm_num⟩
  | 3 => ⟨((1525666632520385/2251799813685248), (-312741902069609/1125899906842624)), (562883/2251799813685248), by norm_num⟩
  | 4 => ⟨((214986771090511/562949953421312), (-211892674330443/562949953421312)), (134431/281474976710656), by norm_num⟩
  | 5 => ⟨((18769786564357/4503599627370496), (-1294726015204195/4503599627370496)), (407751/562949953421312), by norm_num⟩
  | 6 => ⟨((-1488554301650835/18014398509481984), (-43168546008415/18014398509481984)), (237845/562949953421312), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-48896696615/536870912)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2726851779/1073741824), (-24905678495/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((73704721880879/9007199254740992), (353416197964565/4503599627370496)), (1741331/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3311447999/137438953472), (-63513942209/274877906944)), (315/274877906944), by norm_num⟩
  | 2 => ⟨((4875178283/137438953472), (93506463581/274877906944)), (233/137438953472), by norm_num⟩
  | 3 => ⟨((-9569776645/274877906944), (-45887346029/137438953472)), (115/68719476736), by norm_num⟩
  | 4 => ⟨((1761101461/68719476736), (67556245149/274877906944)), (85/68719476736), by norm_num⟩
  | 5 => ⟨((-8296729261/549755813888), (-79566096601/549755813888)), (201/274877906944), by norm_num⟩
  | 6 => ⟨((2035767753/274877906944), (39046252709/549755813888)), (99/274877906944), by norm_num⟩
  | 7 => ⟨((-3425253671/1099511627776), (-65696747695/2199023255552)), (335/2199023255552), by norm_num⟩
  | 8 => ⟨((5042725211/4398046511104), (96720032359/8796093022208)), (495/8796093022208), by norm_num⟩
  | 9 => ⟨((-6444443/17179869184), (-7725321/2147483648)), (163/8796093022208), by norm_num⟩
  | 10 => ⟨((7772270251/70368744177664), (74536505439/70368744177664)), (193/35184372088832), by norm_num⟩
  | 11 => ⟨((-8321809267/281474976710656), (-19951653817/70368744177664)), (415/281474976710656), by norm_num⟩
  | 12 => ⟨((63810051/8796093022208), (78328569597/1125899906842624)), (409/1125899906842624), by norm_num⟩
  | 13 => ⟨((-7399770641/4503599627370496), (-35482106693/2251799813685248)), (93/1125899906842624), by norm_num⟩
  | 14 => ⟨((3112596159/9007199254740992), (7462492715/2251799813685248)), (157/9007199254740992), by norm_num⟩
  | 15 => ⟨((-9775839421/144115188075855872), (-11718855697/18014398509481984)), (495/144115188075855872), by norm_num⟩
  | 16 => ⟨((7196090661/576460752303423488), (69010911011/576460752303423488)), (183/288230376151711744), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (955398648253/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778049854405939/633825300114114700748351602688), (1129797008121/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118058320736725/2475880078570760549798248448), (635370561103/9903520314283042199192993792)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888657731102519/2475880078570760549798248448), (674906323907/618970019642690137449562112)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221290507554629/19342813113834066795298816), (1349419287859/77371252455336267181195264)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548741047468123/9671406556917033397649408), (2529325563631/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258077937865295/604462909807314587353088), (553081147995/151115727451828646838272)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943318621219793/37778931862957161709568), (898365502315/18889465931478580854784)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1296673490553667/4722366482869645213696), (673431856421/1180591620717411303424)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620257641673767/590295810358705651712), (3701651746109/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821986865532771/73786976294838206464), (2311865873759/36893488147419103232)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820983623696181/9223372036854775808), (5197119102199/9223372036854775808)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99514543145595/72057594037927936), (2595700356919/576460752303423488)), (6697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298261842663737/36028797018963968), (2268024999321/72057594037927936)), (5865/144115188075855872), by norm_num⟩
  | 4 => ⟨((744669290408357/18014398509481984), (3395621313945/18014398509481984)), (8807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486386381761829/9007199254740992), (8466639065119/9007199254740992)), (11025/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222212198342393/4503599627370496), (16866204901311/4503599627370496)), (22099/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103758408505379/1125899906842624), (3141527002707/281474976710656)), (33275/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163627487339623/2251799813685248), (6199950884589/281474976710656)), (67063/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163627487339623/2251799813685248), (6199950884589/281474976710656)), (255825051314543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2077815156797683/2251799813685248), (95314932153573/2251799813685248)), (131829/2251799813685248), by norm_num⟩
  | 2 => ⟨((956619425790781/1125899906842624), (175900903352255/2251799813685248)), (15903/140737488355328), by norm_num⟩
  | 3 => ⟨((1611840339155621/2251799813685248), (149453979113291/1125899906842624)), (59017/281474976710656), by norm_num⟩
  | 4 => ⟨((1114079189540595/2251799813685248), (427917172597823/2251799813685248)), (100157/281474976710656), by norm_num⟩
  | 5 => ⟨((939745467188503/4503599627370496), (846849020842707/4503599627370496)), (1097375/2251799813685248), by norm_num⟩
  | 6 => ⟨((73704721880879/9007199254740992), (353416197964565/4503599627370496)), (1741331/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-24905678495/268435456)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1387177309/536870912), (-50679090577/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((168084474430467/2251799813685248), (-202378814091583/18014398509481984)), (3041243/18014398509481984), by norm_num⟩
  | 1 => ⟨((-61466807219/274877906944), (1156373491/34359738368)), (141/274877906944), by norm_num⟩
  | 2 => ⟨((92069049069/274877906944), (-13856741549/274877906944)), (213/274877906944), by norm_num⟩
  | 3 => ⟨((-91938073897/274877906944), (1729628661/34359738368)), (215/274877906944), by norm_num⟩
  | 4 => ⟨((68855463785/274877906944), (-5181504401/137438953472)), (163/274877906944), by norm_num⟩
  | 5 => ⟨((-82509014029/549755813888), (388059999/17179869184)), (197/549755813888), by norm_num⟩
  | 6 => ⟨((82391638729/1099511627776), (-3100063635/274877906944)), (199/1099511627776), by norm_num⟩
  | 7 => ⟨((-35260470173/1099511627776), (5306834675/1099511627776)), (43/549755813888), by norm_num⟩
  | 8 => ⟨((52815464239/4398046511104), (-7948927953/4398046511104)), (65/2199023255552), by norm_num⟩
  | 9 => ⟨((-70320440339/17592186044416), (10583493337/17592186044416)), (175/17592186044416), by norm_num⟩
  | 10 => ⟨((42132242523/35184372088832), (-12682125023/70368744177664)), (53/17592186044416), by norm_num⟩
  | 11 => ⟨((-91794122679/281474976710656), (13815364083/281474976710656)), (233/281474976710656), by norm_num⟩
  | 12 => ⟨((91663538611/1125899906842624), (-13795710685/1125899906842624)), (235/1125899906842624), by norm_num⟩
  | 13 => ⟨((-21123032379/1125899906842624), (3179096595/1125899906842624)), (219/4503599627370496), by norm_num⟩
  | 14 => ⟨((36159399893/9007199254740992), (-10884254023/18014398509481984)), (95/9007199254740992), by norm_num⟩
  | 15 => ⟨((-115545473335/144115188075855872), (1086877035/9007199254740992)), (153/72057594037927936), by norm_num⟩
  | 16 => ⟨((86535825883/576460752303423488), (-13023970445/576460752303423488)), (231/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (-194587545103/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222248052271985/79228162514264337593543950336), (-115045359775/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944429841060359/19807040628566084398385987584), (-32349299711/4951760157141521099596496896)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888579910723309/2475880078570760549798248448), (-274896617065/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442561621794529/38685626227668133590597632), (-274815173503/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387167146227201/2417851639229258349412352), (-128776362747/4835703278458516698824704)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629007397638953/302231454903657293676544), (-225272173545/604462909807314587353088)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943267563402645/37778931862957161709568), (-182952624355/37778931862957161709568)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296597333049937/4722366482869645213696), (-274287238909/4722366482869645213696)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810076810860925/295147905179352825856), (-188457423801/295147905179352825856)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821857883995505/73786976294838206464), (-14712458367/2305843009213693952)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910419975838429/4611686018427387904), (-529174708683/9223372036854775808)), (3331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796045402437653/576460752303423488), (-528583117807/1152921504606846976)), (6663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192925225692703/144115188075855872), (-461845580713/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((744579680165199/18014398509481984), (-691441303987/36028797018963968)), (4373/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486169322406439/9007199254740992), (-430992132931/4503599627370496)), (5467/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221798865049827/4503599627370496), (-1717036407757/4503599627370496)), (10937/2251799813685248), by norm_num⟩
  | 1 => ⟨((551737096375265/562949953421312), (-2558293990465/2251799813685248)), (4103/281474976710656), by norm_num⟩
  | 0 => ⟨((135168408741705/140737488355328), (-2523981014013/1125899906842624)), (16427/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135168408741705/140737488355328), (-2523981014013/1125899906842624)), (62664034129905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((259637988378531/281474976710656), (-1212052671059/281474976710656)), (126511/2251799813685248), by norm_num⟩
  | 2 => ⟨((1915919254360369/2251799813685248), (-17888334998735/2251799813685248)), (234483/2251799813685248), by norm_num⟩
  | 3 => ⟨((1629996847141053/2251799813685248), (-30440188549829/2251799813685248)), (402741/2251799813685248), by norm_num⟩
  | 4 => ⟨((1179484561846611/2251799813685248), (-22034557006823/1125899906842624)), (593949/2251799813685248), by norm_num⟩
  | 5 => ⟨((308473634374927/1125899906842624), (-23083241821699/1125899906842624)), (645465/2251799813685248), by norm_num⟩
  | 6 => ⟨((168084474430467/2251799813685248), (-202378814091583/18014398509481984)), (3041243/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-50679090577/536870912)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2819539303/1073741824), (-25752239235/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-150888396828669/18014398509481984), (-2529342293831/35184372088832)), (6826525/18014398509481984), by norm_num⟩
  | 1 => ⟨((14019259941/549755813888), (60161245049/274877906944)), (159/137438953472), by norm_num⟩
  | 2 => ⟨((-10670487863/274877906944), (-91581130217/274877906944)), (243/137438953472), by norm_num⟩
  | 3 => ⟨((10828846573/274877906944), (46470134303/137438953472)), (495/274877906944), by norm_num⟩
  | 4 => ⟨((-128783853/4294967296), (-70739683285/274877906944)), (189/137438953472), by norm_num⟩
  | 5 => ⟨((5018692225/274877906944), (5384213825/34359738368)), (231/274877906944), by norm_num⟩
  | 6 => ⟨((-10186347391/1099511627776), (-21856479733/274877906944)), (471/1099511627776), by norm_num⟩
  | 7 => ⟨((2215183085/549755813888), (38024310261/1099511627776)), (411/2199023255552), by norm_num⟩
  | 8 => ⟨((-3372087303/2199023255552), (-115765865769/8796093022208)), (157/2199023255552), by norm_num⟩
  | 9 => ⟨((4562842425/8796093022208), (78322616857/17592186044416)), (427/17592186044416), by norm_num⟩
  | 10 => ⟨((-5556670457/35184372088832), (-95381985761/70368744177664)), (261/35184372088832), by norm_num⟩
  | 11 => ⟨((12303569371/281474976710656), (105597307565/281474976710656)), (145/70368744177664), by norm_num⟩
  | 12 => ⟨((-6243082169/562949953421312), (-107164457415/1125899906842624)), (591/1125899906842624), by norm_num⟩
  | 13 => ⟨((5848370383/2251799813685248), (100389106193/4503599627370496)), (139/1125899906842624), by norm_num⟩
  | 14 => ⟨((-10174568489/18014398509481984), (-21831206165/4503599627370496)), (243/9007199254740992), by norm_num⟩
  | 15 => ⟨((4130226941/36028797018963968), (70896636813/72057594037927936)), (99/18014398509481984), by norm_num⟩
  | 16 => ⟨((-12574568595/576460752303423488), (-421575003/2251799813685248)), (605/576460752303423488), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-2197228890793/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777916012201215/633825300114114700748351602688), (-2597940353385/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944391272478343/19807040628566084398385987584), (-2922015972267/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944248854928603/1237940039285380274899124224), (-3103810188815/2475880078570760549798248448)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770164013682311/154742504910672534362390528), (-3102874808157/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774295488290247/4835703278458516698824704), (-1453975817703/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314486649709589/151115727451828646838272), (-2543464571501/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886423766011695/75557863725914323419136), (-2065634336055/37778931862957161709568)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648256669576767/2361183241434822606848), (-3096823727931/4722366482869645213696)), (3459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101252335130475/36893488147419103232), (-531936129091/73786976294838206464)), (2379/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910855704657067/36893488147419103232), (-1328849650019/18446744073709551616)), (2975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455168397326443/2305843009213693952), (-5974379108249/9223372036854775808)), (3349/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591922474183117/1152921504606846976), (-1491895070517/288230376151711744)), (6703/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192775728319975/144115188075855872), (-5213993093243/144115188075855872)), (5871/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488930714064155/36028797018963968), (-7805732874427/36028797018963968)), (551/2251799813685248), by norm_num⟩
  | 3 => ⟨((1485875849729907/9007199254740992), (-9730517409065/9007199254740992)), (345/281474976710656), by norm_num⟩
  | 2 => ⟨((2221189066782219/4503599627370496), (-19381291072263/4503599627370496)), (22137/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205977049413611/2251799813685248), (-28873283893431/2251799813685248)), (4169/281474976710656), by norm_num⟩
  | 0 => ⟨((1080264129070171/1125899906842624), (-28478092732767/1125899906842624)), (67291/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080264129070171/1125899906842624), (-28478092732767/1125899906842624)), (256694802291106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64734861182083/70368744177664), (-13661899186853/281474976710656)), (33133/562949953421312), by norm_num⟩
  | 2 => ⟨((237545054015787/281474976710656), (-50272384859485/562949953421312)), (64177/562949953421312), by norm_num⟩
  | 3 => ⟨((1585812711866143/2251799813685248), (-339410814176199/2251799813685248)), (479137/2251799813685248), by norm_num⟩
  | 4 => ⟨((133204683746363/281474976710656), (-478054914468243/2251799813685248)), (819297/2251799813685248), by norm_num⟩
  | 5 => ⟨((805619318952067/4503599627370496), (-452467600774305/2251799813685248)), (2246635/4503599627370496), by norm_num⟩
  | 6 => ⟨((-150888396828669/18014398509481984), (-2529342293831/35184372088832)), (6826525/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-25752239235/268435456)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile063Terms2
