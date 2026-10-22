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
namespace Reinmann.XiBand97.Tile022Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28609/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28609/1280))
  have he : value ((69/80), (28609/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20060163/33554432), (-519838045/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-151227297768747/281474976710656), (-4139569754803/35184372088832)), (6477011/281474976710656), by norm_num⟩
  | 1 => ⟨((799734307/2147483648), (350260145/4294967296)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-138583395/1073741824), (-30347729/1073741824)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((512313011/17179869184), (28047257/4294967296)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-1420433277/274877906944), (-155527017/137438953472)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((787655457/1099511627776), (344969963/2199023255552)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-1455896425/17592186044416), (-318819943/17592186044416)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((288328715/35184372088832), (126279511/70368744177664)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-1598833887/2251799813685248), (-87530287/562949953421312)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((985090845/18014398509481984), (215720433/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1092500707/288230376151711744), (-14952601/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((275368649/1152921504606846976), (120603383/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-1017978681/73786976294838206464), (-111461193/36893488147419103232)), (63/73786976294838206464), by norm_num⟩
  | 13 => ⟨((868441911/1180591620717411303424), (380352057/2361183241434822606848)), (55/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-687952071/18889465931478580854784), (-301302807/37778931862957161709568)), (89/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((1017284349/604462909807314587353088), (222770337/604462909807314587353088)), (17/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-1410255557/19342813113834066795298816), (-154412631/9671406556917033397649408)), (3/604462909807314587353088), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1905727613247/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890518766466569/316912650057057350374175801344), (-4521652616077/633825300114114700748351602688)), (11581/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892293294965285/39614081257132168796771975168), (-5086553816239/39614081257132168796771975168)), (1629/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((473056681653969/618970019642690137449562112), (-1351032447143/618970019642690137449562112)), (27701/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773891730896177/154742504910672534362390528), (-2701877082213/77371252455336267181195264)), (27711/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776042165415399/4835703278458516698824704), (-5065620177449/9671406556917033397649408)), (25989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261001903314075/604462909807314587353088), (-4432018021389/604462909807314587353088)), (11375/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472846511916785/18889465931478580854784), (-7201279371849/75557863725914323419136)), (18493/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300232786100101/4722366482869645213696), (-5400302755979/4722366482869645213696)), (27757/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203143490342271/73786976294838206464), (-7424347910747/590295810358705651712)), (38191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228511761598813/9223372036854775808), (-9278830356701/73786976294838206464)), (23889/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456961630882903/2305843009213693952), (-10436474731423/9223372036854775808)), (13451/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599085930039847/1152921504606846976), (-2608427044333/288230376151711744)), (3367/72057594037927936), by norm_num⟩
  | 5 => ⟨((599516546230833/72057594037927936), (-2281593929143/36028797018963968)), (47215/144115188075855872), by norm_num⟩
  | 4 => ⟨((374573862357137/9007199254740992), (-13683309303307/36028797018963968)), (70975/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497544494442641/9007199254740992), (-4273288704547/2251799813685248)), (88987/9007199254740992), by norm_num⟩
  | 2 => ⟨((561103652800479/1125899906842624), (-17076608559429/2251799813685248)), (44695/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120268140227601/1125899906842624), (-25573290375937/1125899906842624)), (33773/281474976710656), by norm_num⟩
  | 0 => ⟨((557133014386419/562949953421312), (-25489277332383/562949953421312)), (137113/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557133014386419/562949953421312), (-25489277332383/562949953421312)), (523044588329124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((550222076719057/562949953421312), (-12612948831789/140737488355328)), (567619/1125899906842624), by norm_num⟩
  | 2 => ⟨((1066520916230113/1125899906842624), (-197244472126901/1125899906842624)), (1211313/1125899906842624), by norm_num⟩
  | 3 => ⟨((487859300944615/562949953421312), (-186841968682667/562949953421312)), (679819/281474976710656), by norm_num⟩
  | 4 => ⟨((180386173782091/281474976710656), (-323839061268819/562949953421312)), (6518161/1125899906842624), by norm_num⟩
  | 5 => ⟨((179660369521891/2251799813685248), (-207535639104131/281474976710656)), (31707313/2251799813685248), by norm_num⟩
  | 6 => ⟨((-151227297768747/281474976710656), (-4139569754803/35184372088832)), (6477011/281474976710656), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-519838045/33554432)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-25747619/1048576)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((365616595437865/1125899906842624), (476887399780337/2251799813685248)), (42720251/2251799813685248), by norm_num⟩
  | 1 => ⟨((-766126413/2147483648), (-499643667/2147483648)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((210418973/1073741824), (548914673/4294967296)), (53/4294967296), by norm_num⟩
  | 3 => ⟨((-616450319/8589934592), (-804059207/17179869184)), (5/1073741824), by norm_num⟩
  | 4 => ⟨((84654987/4294967296), (441674663/34359738368)), (45/34359738368), by norm_num⟩
  | 5 => ⟨((-297609629/68719476736), (-194091685/68719476736)), (41/137438953472), by norm_num⟩
  | 6 => ⟨((435943461/549755813888), (568617361/1099511627776)), (31/549755813888), by norm_num⟩
  | 7 => ⟨((-547351821/4398046511104), (-178482863/2199023255552)), (5/549755813888), by norm_num⟩
  | 8 => ⟨((601327437/35184372088832), (784333867/70368744177664)), (91/70368744177664), by norm_num⟩
  | 9 => ⟨((-587222855/281474976710656), (-765936733/562949953421312)), (91/562949953421312), by norm_num⟩
  | 10 => ⟨((129026049/562949953421312), (336587003/2251799813685248)), (41/2251799813685248), by norm_num⟩
  | 11 => ⟨((-824724963/36028797018963968), (-16808119/1125899906842624)), (17/9007199254740992), by norm_num⟩
  | 12 => ⟨((1208070639/576460752303423488), (196966465/144115188075855872)), (51/288230376151711744), by norm_num⟩
  | 13 => ⟨((-816739231/4611686018427387904), (-133162941/1152921504606846976)), (71/4611686018427387904), by norm_num⟩
  | 14 => ⟨((512731289/36893488147419103232), (334387299/36893488147419103232)), (23/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-1201691509/1180591620717411303424), (-783705591/1180591620717411303424)), (111/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((330048265/4722366482869645213696), (430494297/9444732965739290427392)), (63/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (188194258031/2535301200456458802993406410752)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780507731533277/633825300114114700748351602688), (892529568989/633825300114114700748351602688)), (46145/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891697946804979/39614081257132168796771975168), (1004010386791/39614081257132168796771975168)), (51915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891594994600347/2475880078570760549798248448), (1066657847867/2475880078570760549798248448)), (55163/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221657615922365/19342813113834066795298816), (1066541775897/154742504910672534362390528)), (55167/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551493938887629/9671406556917033397649408), (499879802057/4835703278458516698824704)), (51723/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630243148260571/302231454903657293676544), (437333180225/302231454903657293676544)), (22631/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945275017627475/37778931862957161709568), (1421101698549/75557863725914323419136)), (73557/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299607393920045/4722366482869645213696), (1065624066349/4722366482869645213696)), (27587/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812145317769637/295147905179352825856), (183113071773/73786976294838206464)), (37937/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827026422988147/73786976294838206464), (1830638065065/73786976294838206464)), (47429/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826650809159497/9223372036854775808), (1029395312727/4611686018427387904)), (106737/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399474244999881/288230376151711744), (1028972213849/576460752303423488)), (26691/288230376151711744), by norm_num⟩
  | 5 => ⟨((149750045802515/18014398509481984), (1799749813337/144115188075855872)), (93449/144115188075855872), by norm_num⟩
  | 4 => ⟨((93547597453885/2251799813685248), (1348861313375/18014398509481984)), (140233/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495653703672925/9007199254740992), (3368826933369/9007199254740992)), (43849/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120356320358085/2251799813685248), (1681921015895/1125899906842624)), (175555/2251799813685248), by norm_num⟩
  | 1 => ⟨((2235181984607609/2251799813685248), (10066633927567/2251799813685248)), (527459/2251799813685248), by norm_num⟩
  | 0 => ⟨((1109307945084891/1125899906842624), (10016946513975/1125899906842624)), (1058099/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109307945084891/1125899906842624), (10016946513975/1125899906842624)), (4036327370650481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2185742747348839/2251799813685248), (9869330555861/562949953421312)), (2103841/2251799813685248), by norm_num⟩
  | 2 => ⟨((1060465692730021/1125899906842624), (76638491761335/2251799813685248)), (4158017/2251799813685248), by norm_num⟩
  | 3 => ⟨((1995060331787535/2251799813685248), (36092236424187/562949953421312)), (507235/140737488355328), by norm_num⟩
  | 4 => ⟨((1758337180297875/2251799813685248), (127908686620857/1125899906842624)), (15421527/2251799813685248), by norm_num⟩
  | 5 => ⟨((1343950333761153/2251799813685248), (399514376014527/2251799813685248)), (6897003/562949953421312), by norm_num⟩
  | 6 => ⟨((365616595437865/1125899906842624), (476887399780337/2251799813685248)), (42720251/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-25747619/1048576)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-20060163/16777216), (-519838045/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1237651143476569/4503599627370496), (284679093940261/2251799813685248)), (60224773/4503599627370496), by norm_num⟩
  | 1 => ⟨((-818132783/2147483648), (-376366637/2147483648)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((17721451/67108864), (521754947/4294967296)), (15/1073741824), by norm_num⟩
  | 3 => ⟨((-1048198297/8589934592), (-482203961/8589934592)), (29/4294967296), by norm_num⟩
  | 4 => ⟨((1453111389/34359738368), (83559579/4294967296)), (83/34359738368), by norm_num⟩
  | 5 => ⟨((-402888025/34359738368), (-185341077/34359738368)), (3/4294967296), by norm_num⟩
  | 6 => ⟨((186173799/68719476736), (342583053/274877906944)), (23/137438953472), by norm_num⟩
  | 7 => ⟨((-1179847715/2199023255552), (-542766805/2199023255552)), (75/2199023255552), by norm_num⟩
  | 8 => ⟨((817808117/8796093022208), (376217281/8796093022208)), (27/4398046511104), by norm_num⟩
  | 9 => ⟨((-1007753583/70368744177664), (-463598129/70368744177664)), (17/17592186044416), by norm_num⟩
  | 10 => ⟨((139704311/70368744177664), (257073389/281474976710656)), (39/281474976710656), by norm_num⟩
  | 11 => ⟨((-281703707/1125899906842624), (-518370021/4503599627370496)), (81/4503599627370496), by norm_num⟩
  | 12 => ⟨((260349507/9007199254740992), (479075625/36028797018963968)), (77/36028797018963968), by norm_num⟩
  | 13 => ⟨((-888421055/288230376151711744), (-204350719/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 14 => ⟨((1407557827/4611686018427387904), (323760285/2305843009213693952)), (55/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-520343861/18446744073709551616), (-478748861/36893488147419103232)), (83/36893488147419103232), by norm_num⟩
  | 16 => ⟨((1442699521/590295810358705651712), (331843423/295147905179352825856)), (59/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (280819965449/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890062391326041/316912650057057350374175801344), (83204476801/79228162514264337593543950336)), (46133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472816795486987/9903520314283042199192993792), (748760513665/39614081257132168796771975168)), (25951/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945568685475431/1237940039285380274899124224), (795460971793/2475880078570760549798248448)), (13787/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886401687864653/77371252455336267181195264), (795351783659/154742504910672534362390528)), (55151/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551065060702867/9671406556917033397649408), (372763152551/4835703278458516698824704)), (51707/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315027776145369/151115727451828646838272), (81527443467/75557863725914323419136)), (45247/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889940491706659/75557863725914323419136), (529819685657/37778931862957161709568)), (73531/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649575180830977/2361183241434822606848), (198634839371/1180591620717411303424)), (55153/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405915604976437/147573952589676412928), (136522834955/73786976294838206464)), (75843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228280182365689/9223372036854775808), (682382551679/36893488147419103232)), (94815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114110509028507/576460752303423488), (1534724036301/9223372036854775808)), (106683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798507419939849/576460752303423488), (383482135679/288230376151711744)), (106703/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299307270906943/36028797018963968), (670646538659/72057594037927936)), (23347/36028797018963968), by norm_num⟩
  | 4 => ⟨((46737681682471/1125899906842624), (502538037963/9007199254740992)), (140127/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494211082800749/9007199254740992), (2509565120063/9007199254740992)), (175237/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237833573966613/4503599627370496), (5009766989453/4503599627370496)), (350711/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230878794958975/2251799813685248), (234102630055/70368744177664)), (526661/2251799813685248), by norm_num⟩
  | 0 => ⟨((552517747731123/562949953421312), (3722338363417/562949953421312)), (1055711/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552517747731123/562949953421312), (3722338363417/562949953421312)), (4027217873580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2169017006927597/2251799813685248), (3653358520325/281474976710656)), (2086257/2251799813685248), by norm_num⟩
  | 2 => ⟨((1044449097546653/1125899906842624), (28152402233377/1125899906842624)), (4073277/2251799813685248), by norm_num⟩
  | 3 => ⟨((1936373478653955/2251799813685248), (104463108763827/2251799813685248)), (7760909/2251799813685248), by norm_num⟩
  | 4 => ⟨((1660285112833033/2251799813685248), (44915092380475/562949953421312)), (14067635/2251799813685248), by norm_num⟩
  | 5 => ⟨((1209818382149953/2251799813685248), (264932464307403/2251799813685248)), (22989329/2251799813685248), by norm_num⟩
  | 6 => ⟨((1237651143476569/4503599627370496), (284679093940261/2251799813685248)), (60224773/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-519838045/16777216)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-2911141/2097152), (-603513281/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-43685088233001/1125899906842624), (555077759249349/2251799813685248)), (46625099/1125899906842624), by norm_num⟩
  | 1 => ⟨((268205403/4294967296), (-1703955059/4294967296)), (289/4294967296), by norm_num⟩
  | 2 => ⟨((-53957493/1073741824), (1371204937/4294967296)), (117/2147483648), by norm_num⟩
  | 3 => ⟨((115788313/4294967296), (-1471246141/8589934592)), (253/8589934592), by norm_num⟩
  | 4 => ⟨((-186354101/17179869184), (1183939659/17179869184)), (205/17179869184), by norm_num⟩
  | 5 => ⟨((59985071/17179869184), (-1524381899/68719476736)), (133/34359738368), by norm_num⟩
  | 6 => ⟨((-257445993/274877906944), (1635598681/274877906944)), (287/274877906944), by norm_num⟩
  | 7 => ⟨((29595953/137438953472), (-376056361/274877906944)), (133/549755813888), by norm_num⟩
  | 8 => ⟨((-190531395/4398046511104), (1210478729/4398046511104)), (27/549755813888), by norm_num⟩
  | 9 => ⟨((272576401/35184372088832), (-432931191/8796093022208)), (39/4398046511104), by norm_num⟩
  | 10 => ⟨((-87738959/70368744177664), (278710349/35184372088832)), (203/140737488355328), by norm_num⟩
  | 11 => ⟨((51349239/281474976710656), (-1304922189/1125899906842624)), (15/70368744177664), by norm_num⟩
  | 12 => ⟨((-6886951/281474976710656), (175015937/1125899906842624)), (259/9007199254740992), by norm_num⟩
  | 13 => ⟨((109135951/36028797018963968), (-693359469/36028797018963968)), (259/72057594037927936), by norm_num⟩
  | 14 => ⟨((-100370021/288230376151711744), (1275336019/576460752303423488)), (15/36028797018963968), by norm_num⟩
  | 15 => ⟨((172308605/4611686018427387904), (-34209569/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 16 => ⟨((-138660001/36893488147419103232), (880930837/36893488147419103232)), (337/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (70296948421/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444956037257405/158456325028528675187087900672), (1332592581869/316912650057057350374175801344)), (46231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236366099967057/4951760157141521099596496896), (2997958133163/39614081257132168796771975168)), (104037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236347203055001/309485009821345068724781056), (1592439314127/1237940039285380274899124224)), (110559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772443387011047/154742504910672534362390528), (3184370289329/154742504910672534362390528)), (110581/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550727314057803/9671406556917033397649408), (2984807092173/9671406556917033397649408)), (25923/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259815319184455/604462909807314587353088), (2611166214579/604462909807314587353088)), (90755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889459358702147/75557863725914323419136), (2121066374673/37778931862957161709568)), (147519/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298789090686411/4722366482869645213696), (397589236287/590295810358705651712)), (110677/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25361952943469/9223372036854775808), (4372042633905/590295810358705651712)), (38061/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825618644590743/73786976294838206464), (5462895284447/73786976294838206464)), (95199/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228133258827933/1152921504606846976), (191962207793/288230376151711744)), (107163/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798155504386163/576460752303423488), (6139083540921/1152921504606846976)), (107243/576460752303423488), by norm_num⟩
  | 5 => ⟨((299152814428589/36028797018963968), (5367529078529/144115188075855872)), (11741/9007199254740992), by norm_num⟩
  | 4 => ⟨((747337567835909/18014398509481984), (8042959274503/36028797018963968)), (8817/1125899906842624), by norm_num⟩
  | 3 => ⟨((746520429754239/4503599627370496), (10039122317687/9007199254740992)), (353313/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117736286640333/2251799813685248), (5008636913451/1125899906842624)), (354263/2251799813685248), by norm_num⟩
  | 1 => ⟨((69602692578141/70368744177664), (14971347964193/1125899906842624)), (533773/1125899906842624), by norm_num⟩
  | 0 => ⟨((550670679919211/562949953421312), (14862398152459/562949953421312)), (1077085/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550670679919211/562949953421312), (14862398152459/562949953421312)), (4108753208640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1076533730937413/1125899906842624), (29076428006095/562949953421312)), (2164055/1125899906842624), by norm_num⟩
  | 2 => ⟨((1026328461491889/1125899906842624), (111206175019641/1125899906842624)), (136309/35184372088832), by norm_num⟩
  | 3 => ⟨((924578900112935/1125899906842624), (12671426409961/70368744177664)), (4406963/562949953421312), by norm_num⟩
  | 4 => ⟨((361373815509359/562949953421312), (83245293275409/281474976710656)), (35300227/2251799813685248), by norm_num⟩
  | 5 => ⟨((365474474242535/1125899906842624), (855000884431835/2251799813685248)), (258595/8796093022208), by norm_num⟩
  | 6 => ⟨((-43685088233001/1125899906842624), (555077759249349/2251799813685248)), (46625099/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-603513281/16777216)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-1343761853/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-673520263506535/4503599627370496), (-171124126804757/1125899906842624)), (21653363/1125899906842624), by norm_num⟩
  | 1 => ⟨((575440555/2147483648), (292409205/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-128881383/536870912), (-261963481/1073741824)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((615798503/4294967296), (39114629/268435456)), (21/1073741824), by norm_num⟩
  | 4 => ⟨((-68960175/1073741824), (-560672055/8589934592)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((395392149/17179869184), (803671571/34359738368)), (7/2147483648), by norm_num⟩
  | 6 => ⟨((-236149209/34359738368), (-959990765/137438953472)), (17/17179869184), by norm_num⟩
  | 7 => ⟨((967137329/549755813888), (245724649/137438953472)), (141/549755813888), by norm_num⟩
  | 8 => ⟨((-433219367/1099511627776), (-880558933/2199023255552)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((172494423/2199023255552), (87652767/1099511627776)), (13/1099511627776), by norm_num⟩
  | 10 => ⟨((-989019251/70368744177664), (-502568561/35184372088832)), (151/70368744177664), by norm_num⟩
  | 11 => ⟨((644394403/281474976710656), (40930999/17592186044416)), (25/70368744177664), by norm_num⟩
  | 12 => ⟨((-384866591/1125899906842624), (-782277387/2251799813685248)), (121/2251799813685248), by norm_num⟩
  | 13 => ⟨((424362067/9007199254740992), (862555641/18014398509481984)), (135/18014398509481984), by norm_num⟩
  | 14 => ⟨((-217244215/36028797018963968), (-441569211/72057594037927936)), (141/144115188075855872), by norm_num⟩
  | 15 => ⟨((207599669/288230376151711744), (52745721/72057594037927936)), (137/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-371968673/4611686018427387904), (-756061161/9223372036854775808)), (125/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1529339097185/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779578269720677/633825300114114700748351602688), (-3622948210359/633825300114114700748351602688)), (23139/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472663008999161/9903520314283042199192993792), (-2037622271873/19807040628566084398385987584)), (52075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236310421172843/309485009821345068724781056), (-1082315696623/618970019642690137449562112)), (55343/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221518614289207/19342813113834066795298816), (-4328492663429/154742504910672534362390528)), (27679/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550451014800579/9671406556917033397649408), (-4057143662345/9671406556917033397649408)), (25957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314893331596871/151115727451828646838272), (-1774591273361/302231454903657293676544)), (45441/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472266421928537/18889465931478580854784), (-5765887702731/75557863725914323419136)), (36935/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649246729585759/2361183241434822606848), (-2161536846885/2361183241434822606848)), (55429/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622757880977025/590295810358705651712), (-5942045651159/590295810358705651712)), (2383/18446744073709551616), by norm_num⟩
  | 8 => ⟨((456277210079103/18446744073709551616), (-7424286411401/73786976294838206464)), (11923/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912245638780149/4611686018427387904), (-8347825658951/9223372036854775808)), (107393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595734639295071/1152921504606846976), (-4171102929813/576460752303423488)), (107503/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196105164602993/144115188075855872), (-1823277271407/36028797018963968)), (23547/36028797018963968), by norm_num⟩
  | 4 => ⟨((746956232739039/18014398509481984), (-10927024641447/36028797018963968)), (141527/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492081363825039/9007199254740992), (-13636669580191/9007199254740992)), (44335/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116767594958511/2251799813685248), (-850219803583/140737488355328)), (177987/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112167196715263/1125899906842624), (-10161221651767/562949953421312)), (33575/140737488355328), by norm_num⟩
  | 0 => ⟨((1098299058909311/1125899906842624), (-20156930571785/562949953421312)), (271849/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098299058909311/1125899906842624), (-20156930571785/562949953421312)), (1037021639110374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((267482839300287/281474976710656), (-9831396975409/140737488355328)), (1099675/1125899906842624), by norm_num⟩
  | 2 => ⟨((1011250729081195/1125899906842624), (-149482842588819/1125899906842624)), (2243659/1125899906842624), by norm_num⟩
  | 3 => ⟨((444214850165465/562949953421312), (-268522330687433/1125899906842624)), (2313075/562949953421312), by norm_num⟩
  | 4 => ⟨((1274008614786295/2251799813685248), (-105943349108983/281474976710656)), (19014955/2251799813685248), by norm_num⟩
  | 5 => ⟨((401795212409045/2251799813685248), (-239759748844215/562949953421312)), (2239391/140737488355328), by norm_num⟩
  | 6 => ⟨((-673520263506535/4503599627370496), (-171124126804757/1125899906842624)), (21653363/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1343761853/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-56315997/33554432), (-729684947/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((23185587942491/140737488355328), (197720649800687/2251799813685248)), (78215473/4503599627370496), by norm_num⟩
  | 1 => ⟨((-172107967/536870912), (-366922969/2147483648)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((1339626559/4294967296), (713999129/4294967296)), (145/4294967296), by norm_num⟩
  | 3 => ⟨((-217232743/1073741824), (-463126051/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((845430799/8589934592), (225300421/4294967296)), (95/8589934592), by norm_num⟩
  | 5 => ⟨((-658052949/17179869184), (-701463001/34359738368)), (75/17179869184), by norm_num⟩
  | 6 => ⟨((53354663/4294967296), (227497329/34359738368)), (99/68719476736), by norm_num⟩
  | 7 => ⟨((-474621167/137438953472), (-505930699/274877906944)), (7/17179869184), by norm_num⟩
  | 8 => ⟨((461785073/549755813888), (492247841/1099511627776)), (55/549755813888), by norm_num⟩
  | 9 => ⟨((-199687169/1099511627776), (-425720031/4398046511104)), (3/137438953472), by norm_num⟩
  | 10 => ⟨((310858631/8796093022208), (662730343/35184372088832)), (151/35184372088832), by norm_num⟩
  | 11 => ⟨((-439929429/70368744177664), (-468950437/140737488355328)), (109/140737488355328), by norm_num⟩
  | 12 => ⟨((1141417521/1125899906842624), (608356943/1125899906842624)), (143/1125899906842624), by norm_num⟩
  | 13 => ⟨((-683414135/4503599627370496), (-45531075/562949953421312)), (173/9007199254740992), by norm_num⟩
  | 14 => ⟨((759921429/36028797018963968), (405025741/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 15 => ⟨((-788660705/288230376151711744), (-420343307/288230376151711744)), (103/288230376151711744), by norm_num⟩
  | 16 => ⟨((767331435/2305843009213693952), (204487577/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2491677729/39614081257132168796771975168)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889689931077331/316912650057057350374175801344), (755379079075/633825300114114700748351602688)), (92275/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890429249315587/39614081257132168796771975168), (849675774317/39614081257132168796771975168)), (51907/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890247193029649/2475880078570760549798248448), (902625936545/2475880078570760549798248448)), (27577/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771913338968365/154742504910672534362390528), (902452089845/154742504910672534362390528)), (55157/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387557700298455/2417851639229258349412352), (845864168193/9671406556917033397649408)), (51713/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629690638716693/302231454903657293676544), (369973266489/302231454903657293676544)), (11313/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888754803627371/75557863725914323419136), (150258384327/9444732965739290427392)), (147081/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298261341441313/4722366482869645213696), (901247629769/4722366482869645213696)), (110323/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622440416463017/590295810358705651712), (1238723848463/590295810358705651712)), (75855/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824714553440119/73786976294838206464), (48364615869/2305843009213693952)), (189665/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912025599398827/4611686018427387904), (870056620587/4611686018427387904)), (213409/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797649461221987/576460752303423488), (1738847957277/1152921504606846976)), (213455/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195728811875799/144115188075855872), (1520069725601/144115188075855872)), (186825/144115188075855872), by norm_num⟩
  | 4 => ⟨((746678858177531/18014398509481984), (2277263130079/36028797018963968)), (70085/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491404999505311/9007199254740992), (1420806569221/4503599627370496)), (350605/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232233506300359/4503599627370496), (5668356028885/4503599627370496)), (87719/562949953421312), by norm_num⟩
  | 1 => ⟨((2222508882200397/2251799813685248), (8465453017001/2251799813685248)), (1053991/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193451569494431/2251799813685248), (16783148157057/2251799813685248)), (1056731/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193451569494431/2251799813685248), (16783148157057/2251799813685248)), (4031108860496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068245073211465/1125899906842624), (16348266148005/1125899906842624)), (2074451/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013305235839221/1125899906842624), (62044430990781/2251799813685248)), (7993379/2251799813685248), by norm_num⟩
  | 3 => ⟨((911115736745793/1125899906842624), (111679459951161/2251799813685248)), (1853563/281474976710656), by norm_num⟩
  | 4 => ⟨((1469071638208567/2251799813685248), (90374741852605/1125899906842624)), (25470299/2251799813685248), by norm_num⟩
  | 5 => ⟨((29497253283399/70368744177664), (117920757661667/1125899906842624)), (37322535/2251799813685248), by norm_num⟩
  | 6 => ⟨((23185587942491/140737488355328), (197720649800687/2251799813685248)), (78215473/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-729684947/16777216)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-60180489/33554432), (-1559514135/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-597962406824467/4503599627370496), (-903023406379699/9007199254740992)), (4232249/140737488355328), by norm_num⟩
  | 1 => ⟨((1185825223/4294967296), (447698685/2147483648)), (271/4294967296), by norm_num⟩
  | 2 => ⟨((-308231779/1073741824), (-232740811/1073741824)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((427299977/2147483648), (161323637/1073741824)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((-888545323/8589934592), (-670926145/8589934592)), (211/8589934592), by norm_num⟩
  | 5 => ⟨((739071223/17179869184), (558060679/17179869184)), (89/8589934592), by norm_num⟩
  | 6 => ⟨((-1024570269/68719476736), (-773636373/68719476736)), (249/68719476736), by norm_num⟩
  | 7 => ⟨((304361997/68719476736), (919275207/274877906944)), (299/274877906944), by norm_num⟩
  | 8 => ⟨((-158225745/137438953472), (-477894763/549755813888)), (79/274877906944), by norm_num⟩
  | 9 => ⟨((584926555/2199023255552), (883337087/4398046511104)), (295/4398046511104), by norm_num⟩
  | 10 => ⟨((-486528231/8796093022208), (-367369567/8796093022208)), (31/2199023255552), by norm_num⟩
  | 11 => ⟨((91973365/8796093022208), (138895189/17592186044416)), (95/35184372088832), by norm_num⟩
  | 12 => ⟨((-510008629/281474976710656), (-770198469/562949953421312)), (133/281474976710656), by norm_num⟩
  | 13 => ⟨((163158943/562949953421312), (246397337/1125899906842624)), (43/562949953421312), by norm_num⟩
  | 14 => ⟨((-775495963/18014398509481984), (-292782205/9007199254740992)), (207/18014398509481984), by norm_num⟩
  | 15 => ⟨((860052545/144115188075855872), (5073529/1125899906842624)), (29/18014398509481984), by norm_num⟩
  | 16 => ⟨((-894214495/1152921504606846976), (-337603423/576460752303423488)), (243/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-812453823899/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779194605916567/633825300114114700748351602688), (-961942918167/158456325028528675187087900672)), (92579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890220430852679/39614081257132168796771975168), (-4328042249997/39614081257132168796771975168)), (104175/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890024800917419/2475880078570760549798248448), (-1149425344391/618970019642690137449562112)), (55357/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110730647464831/9671406556917033397649408), (-4596752446777/154742504910672534362390528)), (55373/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550021134108849/9671406556917033397649408), (-67319488753/151115727451828646838272)), (51929/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78699824710123/37778931862957161709568), (-942220836031/151115727451828646838272)), (45455/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944227251146869/37778931862957161709568), (-3061272812455/37778931862957161709568)), (147791/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298035094324151/4722366482869645213696), (-2295127937671/2361183241434822606848)), (55449/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811063834481845/295147905179352825856), (-6308915595807/590295810358705651712)), (152575/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824321135297743/73786976294838206464), (-7882115934385/73786976294838206464)), (95427/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823605192755989/9223372036854775808), (-4430921219739/4611686018427387904)), (13431/576460752303423488), by norm_num⟩
  | 6 => ⟨((99678041245793/72057594037927936), (-8854921885293/1152921504606846976)), (26891/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195330053019179/144115188075855872), (-3870136842235/72057594037927936)), (188499/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492750043150131/36028797018963968), (-362339101845/1125899906842624)), (141635/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490628774469179/9007199254740992), (-14466350392781/9007199254740992)), (88751/2251799813685248), by norm_num⟩
  | 2 => ⟨((557657841406365/1125899906842624), (-14425560061725/2251799813685248)), (89095/562949953421312), by norm_num⟩
  | 1 => ⟨((554995544534779/562949953421312), (-21536470450311/1125899906842624)), (538017/1125899906842624), by norm_num⟩
  | 0 => ⟨((136744286121229/140737488355328), (-42666103574637/1125899906842624)), (272467/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((136744286121229/140737488355328), (-42666103574637/1125899906842624)), (1039379120946788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1061298240366825/1125899906842624), (-41455520793137/562949953421312)), (550123/281474976710656), by norm_num⟩
  | 2 => ⟨((994297723434555/1125899906842624), (-156307575847047/1125899906842624)), (2236277/562949953421312), by norm_num⟩
  | 3 => ⟨((856377994793397/1125899906842624), (-276074748520281/1125899906842624)), (4570695/562949953421312), by norm_num⟩
  | 4 => ⟨((1167361324398227/2251799813685248), (-209986996280955/562949953421312)), (4597297/281474976710656), by norm_num⟩
  | 5 => ⟨((291864241214065/2251799813685248), (-435439592090143/1125899906842624)), (65570285/2251799813685248), by norm_num⟩
  | 6 => ⟨((-597962406824467/4503599627370496), (-903023406379699/9007199254740992)), (4232249/140737488355328), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1559514135/33554432)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile022Terms0
