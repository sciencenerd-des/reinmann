/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile006Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (559/32)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (559/32))
  have he : value ((15/16), (559/32))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-812581963/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((131824565093039/281474976710656), (519816270776305/2251799813685248)), (26287871/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1394253931/4294967296), (-687235227/4294967296)), (37/4294967296), by norm_num⟩
  | 2 => ⟨((966423181/8589934592), (59544395/1073741824)), (27/8589934592), by norm_num⟩
  | 3 => ⟨((-893164671/34359738368), (-27515353/2147483648)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((1238189147/274877906944), (610310059/274877906944)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((-686597853/1099511627776), (-676855515/2199023255552)), (47/2199023255552), by norm_num⟩
  | 6 => ⟨((1269102309/17592186044416), (625547323/17592186044416)), (23/8796093022208), by norm_num⟩
  | 7 => ⟨((-251335625/35184372088832), (-495538701/140737488355328)), (19/70368744177664), by norm_num⟩
  | 8 => ⟨((1393700639/2251799813685248), (686962507/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | 9 => ⟨((-107337741/2251799813685248), (-211629389/9007199254740992)), (9/4503599627370496), by norm_num⟩
  | 10 => ⟨((952330913/288230376151711744), (234704503/144115188075855872)), (21/144115188075855872), by norm_num⟩
  | 11 => ⟨((-240038359/1152921504606846976), (-236632385/2305843009213693952)), (11/1152921504606846976), by norm_num⟩
  | 12 => ⟨((221842549/18446744073709551616), (437389521/73786976294838206464)), (43/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-757019261/1180591620717411303424), (-373138847/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 14 => ⟨((299843295/9444732965739290427392), (295588731/18889465931478580854784)), (63/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-886764947/604462909807314587353088), (-218545595/302231454903657293676544)), (49/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((614658623/9671406556917033397649408), (151484263/4835703278458516698824704)), (35/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (74567320145/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780967824957261/633825300114114700748351602688), (176908105091/158456325028528675187087900672)), (5767/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946107762009061/19807040628566084398385987584), (99504969279/4951760157141521099596496896)), (25953/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473036221806169/618970019642690137449562112), (422868060581/1237940039285380274899124224)), (3447/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886905391346365/77371252455336267181195264), (422836496863/77371252455336267181195264)), (13789/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552009388602331/9671406556917033397649408), (12386740067/151115727451828646838272)), (101/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((630468637689997/302231454903657293676544), (693590382691/604462909807314587353088)), (22625/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891282801573783/75557863725914323419136), (1126958645703/75557863725914323419136)), (36769/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325039225906063/1180591620717411303424), (845108987195/4722366482869645213696)), (27579/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203130763212845/73786976294838206464), (1161846137103/590295810358705651712)), (37925/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827970602176223/73786976294838206464), (1452039634631/73786976294838206464)), (11853/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456928198197941/2305843009213693952), (1633176109417/9223372036854775808)), (53347/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598958691197287/1152921504606846976), (1632715616447/1152921504606846976)), (26679/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198929057240945/144115188075855872), (1428108256155/144115188075855872)), (11675/36028797018963968), by norm_num⟩
  | 4 => ⟨((749076991284075/18014398509481984), (1070563466783/18014398509481984)), (70073/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497393160252395/9007199254740992), (334324681391/1125899906842624)), (87633/9007199254740992), by norm_num⟩
  | 2 => ⟨((70130885515101/140737488355328), (2671882272497/2251799813685248)), (175391/4503599627370496), by norm_num⟩
  | 1 => ⟨((2240387485724889/2251799813685248), (8002082435073/2251799813685248)), (263399/2251799813685248), by norm_num⟩
  | 0 => ⟨((1114497364019645/1125899906842624), (7974988182261/1125899906842624)), (264027/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114497364019645/1125899906842624), (7974988182261/1125899906842624)), (1007183079246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103153811827999/1125899906842624), (246694423423/17592186044416)), (526447/1125899906842624), by norm_num⟩
  | 2 => ⟨((1080645846243257/1125899906842624), (61877902579861/2251799813685248)), (261597/281474976710656), by norm_num⟩
  | 3 => ⟨((2072721063754351/2251799813685248), (118781603925505/2251799813685248)), (258271/140737488355328), by norm_num⟩
  | 4 => ⟨((1901618213428981/2251799813685248), (218670532741535/2251799813685248)), (1005421/281474976710656), by norm_num⟩
  | 5 => ⟨((396164770739045/562949953421312), (92332334622807/562949953421312)), (15147229/2251799813685248), by norm_num⟩
  | 6 => ⟨((131824565093039/281474976710656), (519816270776305/2251799813685248)), (26287871/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-812581963/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-321977985/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((378717808821035/1125899906842624), (-269491339719639/2251799813685248)), (66142619/4503599627370496), by norm_num⟩
  | 1 => ⟨((-99197397/268435456), (282351015/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((871835835/4294967296), (-310194295/4294967296)), (21/2147483648), by norm_num⟩
  | 3 => ⟨((-159634927/2147483648), (227188843/8589934592)), (1/268435456), by norm_num⟩
  | 4 => ⟨((350753785/17179869184), (-249592455/34359738368)), (73/68719476736), by norm_num⟩
  | 5 => ⟨((-308273935/68719476736), (438728541/274877906944)), (67/274877906944), by norm_num⟩
  | 6 => ⟨((451564711/549755813888), (-160664189/549755813888)), (51/1099511627776), by norm_num⟩
  | 7 => ⟨((-1133930379/8796093022208), (403446063/8796093022208)), (33/4398046511104), by norm_num⟩
  | 8 => ⟨((1245749849/70368744177664), (-443230803/70368744177664)), (75/70368744177664), by norm_num⟩
  | 9 => ⟨((-304132465/140737488355328), (432834495/562949953421312)), (19/140737488355328), by norm_num⟩
  | 10 => ⟨((1069195723/4503599627370496), (-95103459/1125899906842624)), (69/4503599627370496), by norm_num⟩
  | 11 => ⟨((-854277499/36028797018963968), (151973569/18014398509481984)), (57/36028797018963968), by norm_num⟩
  | 12 => ⟨((625679839/288230376151711744), (-111306687/144115188075855872)), (43/288230376151711744), by norm_num⟩
  | 13 => ⟨((-211501403/1152921504606846976), (301004047/4611686018427387904)), (15/1152921504606846976), by norm_num⟩
  | 14 => ⟨((1062208185/73786976294838206464), (-377927709/73786976294838206464)), (77/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-1244751963/1180591620717411303424), (27679735/73786976294838206464)), (93/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((1367499803/18889465931478580854784), (-30409297/1180591620717411303424)), (105/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (-445268483835/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780380760750417/633825300114114700748351602688), (-527860613929/633825300114114700748351602688)), (46127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945777566929815/19807040628566084398385987584), (-593788510509/39614081257132168796771975168)), (25947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945721645800381/1237940039285380274899124224), (-78854246875/309485009821345068724781056)), (13785/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443277316148507/38685626227668133590597632), (-315379689795/77371252455336267181195264)), (27571/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48479743679543/302231454903657293676544), (-147814418195/2417851639229258349412352)), (51697/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260361965729533/604462909807314587353088), (-517271231639/604462909807314587353088)), (22619/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890348077773055/75557863725914323419136), (-840417220101/75557863725914323419136)), (73515/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324863998958379/1180591620717411303424), (-315091489471/2361183241434822606848)), (13785/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406020644229517/147573952589676412928), (-866290503747/590295810358705651712)), (75823/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456691630064659/18446744073709551616), (-1082546585569/73786976294838206464)), (94789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826358652969643/9223372036854775808), (-608714906923/4611686018427387904)), (106649/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798802558301949/576460752303423488), (-1216886174969/1152921504606846976)), (53333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197745315092575/144115188075855872), (-1064164125155/144115188075855872)), (93351/144115188075855872), by norm_num⟩
  | 4 => ⟨((187047454991727/4503599627370496), (-199378052613/4503599627370496)), (140061/36028797018963968), by norm_num⟩
  | 3 => ⟨((747588727009591/4503599627370496), (-497911052097/2251799813685248)), (175139/9007199254740992), by norm_num⟩
  | 2 => ⟨((2239763584320309/4503599627370496), (-497110819315/562949953421312)), (350465/4503599627370496), by norm_num⟩
  | 1 => ⟨((1116883493844321/1125899906842624), (-5949349968195/2251799813685248)), (65771/281474976710656), by norm_num⟩
  | 0 => ⟨((2215820129607859/2251799813685248), (-5917464511923/1125899906842624)), (263557/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2215820129607859/2251799813685248), (-5917464511923/1125899906842624)), (1005390169383811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((272544141767827/281474976710656), (-23291656571017/2251799813685248)), (2085849/2251799813685248), by norm_num⟩
  | 2 => ⟨((2110932445864447/2251799813685248), (-22552642599645/1125899906842624)), (4082487/2251799813685248), by norm_num⟩
  | 3 => ⟨((1977973919875685/2251799813685248), (-84567206577147/2251799813685248)), (7817743/2251799813685248), by norm_num⟩
  | 4 => ⟨((1734270156497129/2251799813685248), (-74283570000205/1125899906842624)), (895085/140737488355328), by norm_num⟩
  | 5 => ⟨((1325881973381315/2251799813685248), (-57211026391633/562949953421312)), (11974773/1125899906842624), by norm_num⟩
  | 6 => ⟨((378717808821035/1125899906842624), (-269491339719639/2251799813685248)), (66142619/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-321977985/16777216)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-812581963/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((93476878038315/562949953421312), (973792478808029/4503599627370496)), (1160529/70368744177664), by norm_num⟩
  | 1 => ⟨((-494333149/2147483648), (-643712531/2147483648)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((685291257/4294967296), (223093763/1073741824)), (9/536870912), by norm_num⟩
  | 3 => ⟨((-158335901/2147483648), (-206182417/2147483648)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((878000667/34359738368), (142914761/4294967296)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-243433475/34359738368), (-633990167/68719476736)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((449960605/274877906944), (585931329/274877906944)), (53/274877906944), by norm_num⟩
  | 7 => ⟨((-712888971/2199023255552), (-232078085/549755813888)), (43/1099511627776), by norm_num⟩
  | 8 => ⟨((123534245/2199023255552), (643457081/8796093022208)), (61/8796093022208), by norm_num⟩
  | 9 => ⟨((-152226513/17592186044416), (-792907487/70368744177664)), (77/70368744177664), by norm_num⟩
  | 10 => ⟨((675298421/562949953421312), (879362543/562949953421312)), (11/70368744177664), by norm_num⟩
  | 11 => ⟨((-680845377/4503599627370496), (-443292849/2251799813685248)), (45/2251799813685248), by norm_num⟩
  | 12 => ⟨((314617369/18014398509481984), (819379169/36028797018963968)), (85/36028797018963968), by norm_num⟩
  | 13 => ⟨((-134200703/72057594037927936), (-699015829/288230376151711744)), (37/144115188075855872), by norm_num⟩
  | 14 => ⟨((425238121/2305843009213693952), (1107476231/4611686018427387904)), (15/576460752303423488), by norm_num⟩
  | 15 => ⟨((-628805557/36893488147419103232), (-102352537/4611686018427387904)), (91/36893488147419103232), by norm_num⟩
  | 16 => ⟨((435854799/295147905179352825856), (1135125959/590295810358705651712)), (1/4611686018427387904), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (74567320145/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779963452681987/633825300114114700748351602688), (353437649675/158456325028528675187087900672)), (23085/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891085657073921/39614081257132168796771975168), (1590284954369/39614081257132168796771975168)), (25973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945472231969445/1237940039285380274899124224), (1689453590191/2475880078570760549798248448)), (27599/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886305213653297/77371252455336267181195264), (422300359207/38685626227668133590597632)), (55203/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550884127581911/9671406556917033397649408), (395839619649/2417851639229258349412352)), (51759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259952744153257/604462909807314587353088), (692585425209/302231454903657293676544)), (2831/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944841536833703/37778931862957161709568), (2250400578913/75557863725914323419136)), (73617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324739306534991/1180591620717411303424), (421840311043/1180591620717411303424)), (55223/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623396741683667/590295810358705651712), (1159704113191/295147905179352825856)), (18987/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912954593009373/36893488147419103232), (724547601335/18446744073709551616)), (94959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912697048470851/4611686018427387904), (1629496845529/4611686018427387904)), (106863/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399160123052379/288230376151711744), (3257156397307/1152921504606846976)), (106905/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196901192375931/144115188075855872), (177996628775/9007199254740992)), (46795/72057594037927936), by norm_num⟩
  | 4 => ⟨((747556652232865/18014398509481984), (4267790435373/36028797018963968)), (2195/562949953421312), by norm_num⟩
  | 3 => ⟨((186699284097367/1125899906842624), (5327519462313/9007199254740992)), (21971/1125899906842624), by norm_num⟩
  | 2 => ⟨((2236596448232251/4503599627370496), (5316704709973/2251799813685248)), (176019/2251799813685248), by norm_num⟩
  | 1 => ⟨((2229014391809855/2251799813685248), (15896132131085/2251799813685248)), (529319/2251799813685248), by norm_num⟩
  | 0 => ⟨((2206307623655999/2251799813685248), (31576886198145/2251799813685248)), (1063693/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2206307623655999/2251799813685248), (31576886198145/2251799813685248)), (4057666787154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((540322923121629/562949953421312), (61877902579863/2251799813685248)), (2114241/2251799813685248), by norm_num⟩
  | 2 => ⟨((2072721063754355/2251799813685248), (118781603925509/2251799813685248)), (32615/17592186044416), by norm_num⟩
  | 3 => ⟨((475404553357247/562949953421312), (109335266370771/1125899906842624)), (4062933/1125899906842624), by norm_num⟩
  | 4 => ⟨((1584659082956191/2251799813685248), (369329338491241/2251799813685248)), (15302589/2251799813685248), by norm_num⟩
  | 5 => ⟨((263649130186081/562949953421312), (519816270776327/2251799813685248)), (26557497/2251799813685248), by norm_num⟩
  | 6 => ⟨((93476878038315/562949953421312), (973792478808029/4503599627370496)), (1160529/70368744177664), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-812581963/33554432)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1886756889/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-245849858245691/1125899906842624), (-158161044925467/4503599627370496)), (10421683/562949953421312), by norm_num⟩
  | 1 => ⟨((754699865/2147483648), (121379081/2147483648)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((-1214642575/4294967296), (-195352095/4294967296)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((1303261207/8589934592), (26200589/1073741824)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((-524379499/8589934592), (-168672885/17179869184)), (95/17179869184), by norm_num⟩
  | 5 => ⟨((675164997/34359738368), (217174829/68719476736)), (31/17179869184), by norm_num⟩
  | 6 => ⟨((-1448848191/274877906944), (-116509801/137438953472)), (135/274877906944), by norm_num⟩
  | 7 => ⟨((41639843/34359738368), (107151595/549755813888)), (63/549755813888), by norm_num⟩
  | 8 => ⟨((-33508371/137438953472), (-172453839/4398046511104)), (103/4398046511104), by norm_num⟩
  | 9 => ⟨((1533998725/35184372088832), (246714441/35184372088832)), (75/17592186044416), by norm_num⟩
  | 10 => ⟨((-493775141/70368744177664), (-79414315/70368744177664)), (49/70368744177664), by norm_num⟩
  | 11 => ⟨((1155927901/1125899906842624), (185908959/1125899906842624)), (117/1125899906842624), by norm_num⟩
  | 12 => ⟨((-155032849/1125899906842624), (-99736309/4503599627370496)), (127/9007199254740992), by norm_num⟩
  | 13 => ⟨((614192603/36028797018963968), (197562335/72057594037927936)), (1/562949953421312), by norm_num⟩
  | 14 => ⟨((-1129719841/576460752303423488), (-181693893/576460752303423488)), (119/576460752303423488), by norm_num⟩
  | 15 => ⟨((969714103/4611686018427387904), (155960021/4611686018427387904)), (13/576460752303423488), by norm_num⟩
  | 16 => ⟨((-780347321/36893488147419103232), (-251007971/73786976294838206464)), (169/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (-3884553774749/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55613448678367/19807040628566084398385987584), (-4601459948619/633825300114114700748351602688)), (46327/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890710375994297/39614081257132168796771975168), (-5175919320127/39614081257132168796771975168)), (13033/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890545028358557/2475880078570760549798248448), (-2749281917873/1237940039285380274899124224)), (55407/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886105102623553/77371252455336267181195264), (-5497606893123/154742504910672534362390528)), (27713/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550508084178371/9671406556917033397649408), (-2576494821761/4835703278458516698824704)), (25991/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629811435707363/302231454903657293676544), (-4507849043531/604462909807314587353088)), (45505/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944572733136905/37778931862957161709568), (-7323347857945/75557863725914323419136)), (36991/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298552652907639/4722366482869645213696), (-2745421125219/2361183241434822606848)), (1735/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405709558209717/147573952589676412928), (-7547196250727/590295810358705651712)), (76393/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825207722208699/73786976294838206464), (-2357481756899/18446744073709551616)), (23893/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824600379727221/9223372036854775808), (-10603073171903/9223372036854775808)), (107629/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199480133726005/144115188075855872), (-10596078500299/1152921504606846976)), (13471/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196195290226953/144115188075855872), (-4631848985361/72057594037927936)), (94453/144115188075855872), by norm_num⟩
  | 4 => ⟨((747020831552589/18014398509481984), (-6939900640619/18014398509481984)), (17749/4503599627370496), by norm_num⟩
  | 3 => ⟨((373058100616077/2251799813685248), (-4330546808271/2251799813685248)), (178037/9007199254740992), by norm_num⟩
  | 2 => ⟨((279225749264175/562949953421312), (-8640411032821/1125899906842624)), (178859/2251799813685248), by norm_num⟩
  | 1 => ⟨((34760355850841/35184372088832), (-25817756197207/1125899906842624)), (270349/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098472861988357/1125899906842624), (-25610615112383/562949953421312)), (548963/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1098472861988357/1125899906842624), (-25610615112383/562949953421312)), (2094127659324264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1069383705231489/1125899906842624), (-49973475455157/562949953421312)), (560565/562949953421312), by norm_num⟩
  | 2 => ⟨((251708013547427/281474976710656), (-189859933447887/1125899906842624)), (2328755/1125899906842624), by norm_num⟩
  | 3 => ⟨((108542507317181/140737488355328), (-339563163012815/1125899906842624)), (4950357/1125899906842624), by norm_num⟩
  | 4 => ⟨((1134579213842725/2251799813685248), (-261884999772829/562949953421312)), (10621819/1125899906842624), by norm_num⟩
  | 5 => ⟨((21086459554869/562949953421312), (-527807623668257/1125899906842624)), (20586267/1125899906842624), by norm_num⟩
  | 6 => ⟨((-245849858245691/1125899906842624), (-158161044925467/4503599627370496)), (10421683/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1886756889/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-56363879/33554432), (-1050246951/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1667776961211297/9007199254740992), (194551476260989/9007199254740992)), (114906665/9007199254740992), by norm_num⟩
  | 1 => ⟨((-356227775/1073741824), (-166220403/4294967296)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((638274489/2147483648), (148913491/4294967296)), (23/1073741824), by norm_num⟩
  | 3 => ⟨((-1524845813/8589934592), (-177878105/8589934592)), (111/8589934592), by norm_num⟩
  | 4 => ⟨((1366078463/17179869184), (79678695/8589934592)), (51/8589934592), by norm_num⟩
  | 5 => ⟨((-979073609/34359738368), (-114212045/34359738368)), (37/17179869184), by norm_num⟩
  | 6 => ⟨((1169509607/137438953472), (136427009/137438953472)), (45/68719476736), by norm_num⟩
  | 7 => ⟨((-1197417093/549755813888), (-69841253/274877906944)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((268185427/549755813888), (62569363/1099511627776)), (43/1099511627776), by norm_num⟩
  | 9 => ⟨((-854264495/8796093022208), (-199305331/17592186044416)), (139/17592186044416), by norm_num⟩
  | 10 => ⟨((1224509199/70368744177664), (71421443/35184372088832)), (101/70368744177664), by norm_num⟩
  | 11 => ⟨((-797827619/281474976710656), (-93069125/281474976710656)), (67/281474976710656), by norm_num⟩
  | 12 => ⟨((1906020255/4503599627370496), (222343315/4503599627370496)), (81/2251799813685248), by norm_num⟩
  | 13 => ⟨((-525404591/9007199254740992), (-30645057/4503599627370496)), (91/18014398509481984), by norm_num⟩
  | 14 => ⟨((1075884173/144115188075855872), (125505305/144115188075855872)), (95/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1028120349/1152921504606846976), (-119933503/1152921504606846976)), (93/1152921504606846976), by norm_num⟩
  | 16 => ⟨((1842144371/18446744073709551616), (107445995/9223372036854775808)), (169/18446744073709551616), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49430864790015/316912650057057350374175801344), (151270096735/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444844487195257/158456325028528675187087900672), (89568475747/316912650057057350374175801344)), (46109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890427113713265/39614081257132168796771975168), (12593704477/2475880078570760549798248448)), (51873/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945122472798225/1237940039285380274899124224), (214056291951/2475880078570760549798248448)), (13779/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885955557934733/77371252455336267181195264), (26751879287/19342813113834066795298816)), (55117/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550228742880643/9671406556917033397649408), (100297634819/4835703278458516698824704)), (103345/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314844875559149/151115727451828646838272), (87738524285/302231454903657293676544)), (90429/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888751967327221/75557863725914323419136), (285068082621/75557863725914323419136)), (146949/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649129628265043/2361183241434822606848), (13358077043/295147905179352825856)), (110215/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405609404602817/147573952589676412928), (293761022719/590295810358705651712)), (75775/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824711158824259/73786976294838206464), (367026358125/73786976294838206464)), (189443/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912023760621143/4611686018427387904), (412664280541/9223372036854775808)), (213133/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595295421372455/1152921504606846976), (412364029501/1152921504606846976)), (26643/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195725946638523/144115188075855872), (90120259489/36028797018963968)), (93257/72057594037927936), by norm_num⟩
  | 4 => ⟨((746676907020449/18014398509481984), (540047316923/36028797018963968)), (279795/36028797018963968), by norm_num⟩
  | 3 => ⟨((372850202970389/2251799813685248), (336940439775/4503599627370496)), (87447/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232227194159793/4503599627370496), (1344233563353/4503599627370496)), (349855/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111252272440815/1125899906842624), (1003776463371/1125899906842624)), (524953/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096731628883547/1125899906842624), (3980054262387/2251799813685248)), (2101201/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1096731628883547/1125899906842624), (3980054262387/2251799813685248)), (8015445717818450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2136630970969079/2251799813685248), (7753888898479/2251799813685248)), (4100961/2251799813685248), by norm_num⟩
  | 2 => ⟨((2027325766512087/2251799813685248), (14714628774065/2251799813685248)), (1952669/562949953421312), by norm_num⟩
  | 3 => ⟨((1825132597616569/2251799813685248), (3311944724951/281474976710656)), (7083097/1125899906842624), by norm_num⟩
  | 4 => ⟨((1478997806136691/2251799813685248), (2684403046077/140737488355328)), (11648693/1125899906842624), by norm_num⟩
  | 5 => ⟨((970596833798261/2251799813685248), (14105076985283/562949953421312)), (62985025/4503599627370496), by norm_num⟩
  | 6 => ⟨((1667776961211297/9007199254740992), (194551476260989/9007199254740992)), (114906665/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56363879/33554432), (-1050246951/33554432)), (1/16777216), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3825815/2097152), (-570301493/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-153423811030495/1125899906842624), (-777918185109127/9007199254740992)), (261518871/9007199254740992), by norm_num⟩
  | 1 => ⟨((1138873867/4294967296), (90227061/536870912)), (61/1073741824), by norm_num⟩
  | 2 => ⟨((-277018277/1073741824), (-702295015/4294967296)), (239/4294967296), by norm_num⟩
  | 3 => ⟨((359368451/2147483648), (113883583/1073741824)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((-174824679/2147483648), (-55401805/1073741824)), (77/4294967296), by norm_num⟩
  | 5 => ⟨((1088617975/34359738368), (344982191/17179869184)), (241/34359738368), by norm_num⟩
  | 6 => ⟨((-706117589/68719476736), (-447536231/68719476736)), (79/34359738368), by norm_num⟩
  | 7 => ⟨((785166505/274877906944), (497637311/274877906944)), (177/274877906944), by norm_num⟩
  | 8 => ⟨((-763931735/1099511627776), (-484178747/1099511627776)), (87/549755813888), by norm_num⟩
  | 9 => ⟨((660685563/4398046511104), (418741483/4398046511104)), (19/549755813888), by norm_num⟩
  | 10 => ⟨((-514253897/17592186044416), (-651866641/35184372088832)), (119/17592186044416), by norm_num⟩
  | 11 => ⟨((727775911/140737488355328), (461263241/140737488355328)), (85/70368744177664), by norm_num⟩
  | 12 => ⟨((-472062177/562949953421312), (-149596137/281474976710656)), (111/562949953421312), by norm_num⟩
  | 13 => ⟨((1130573023/9007199254740992), (716555425/9007199254740992)), (67/2251799813685248), by norm_num⟩
  | 14 => ⟨((-628569577/36028797018963968), (-398386421/36028797018963968)), (75/18014398509481984), by norm_num⟩
  | 15 => ⟨((1304682581/576460752303423488), (12920403/9007199254740992)), (313/576460752303423488), by norm_num⟩
  | 16 => ⟨((-634698769/2305843009213693952), (-804542187/4611686018427387904)), (307/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (-839107049381/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444786654790357/158456325028528675187087900672), (-3973799303071/633825300114114700748351602688)), (5787/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945083212381885/19807040628566084398385987584), (-1117446868381/9903520314283042199192993792)), (52095/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889967391157195/2475880078570760549798248448), (-593532876119/309485009821345068724781056)), (110731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442908229470475/38685626227668133590597632), (-4747266067037/154742504910672534362390528)), (27691/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193745906112181/1208925819614629174706176), (-4449502788463/9671406556917033397649408)), (25969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629575006040773/302231454903657293676544), (-973063976087/151115727451828646838272)), (90927/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944188883153413/37778931862957161709568), (-6322930395037/75557863725914323419136)), (36955/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297977487141851/4722366482869645213696), (-2370230385187/2361183241434822606848)), (110923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622048369531239/590295810358705651712), (-3257655673675/295147905179352825856)), (76305/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456055469225017/18446744073709551616), (-4069953332055/36893488147419103232)), (190903/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823493343031695/9223372036854775808), (-4575788290369/4611686018427387904)), (214957/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49835518147809/36028797018963968), (-9144305512371/1152921504606846976)), (215197/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597615863158011/72057594037927936), (-7993090062105/144115188075855872)), (188567/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492602040198435/36028797018963968), (-2993321829257/9007199254740992)), (141695/18014398509481984), by norm_num⟩
  | 3 => ⟨((745221438744585/4503599627370496), (-14938015770953/9007199254740992)), (22199/562949953421312), by norm_num⟩
  | 2 => ⟨((557564227220705/1125899906842624), (-14895156307595/2251799813685248)), (178303/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109706947874741/1125899906842624), (-22235693501935/1125899906842624)), (269235/562949953421312), by norm_num⟩
  | 0 => ⟨((546686495277331/562949953421312), (-1376371066869/35184372088832)), (1091233/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((546686495277331/562949953421312), (-1376371066869/35184372088832)), (4162723545554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1060062822966403/1125899906842624), (-85542919208335/1125899906842624)), (275599/140737488355328), by norm_num⟩
  | 2 => ⟨((991576241212769/1125899906842624), (-161081580821997/1125899906842624)), (4486763/1125899906842624), by norm_num⟩
  | 3 => ⟨((850232032740843/1125899906842624), (-283728007204485/1125899906842624)), (4593395/562949953421312), by norm_num⟩
  | 4 => ⟨((570559535108115/1125899906842624), (-428518803216665/1125899906842624)), (9252557/562949953421312), by norm_num⟩
  | 5 => ⟨((504164952959291/4503599627370496), (-868622468702491/2251799813685248)), (131365559/4503599627370496), by norm_num⟩
  | 6 => ⟨((-153423811030495/1125899906842624), (-777918185109127/9007199254740992)), (261518871/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-570301493/16777216)), (1/16777216), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-76179559/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((250865929678155/9007199254740992), (628690247174057/4503599627370496)), (192800663/9007199254740992), by norm_num⟩
  | 1 => ⟨((-124373683/2147483648), (-623380955/2147483648)), (97/2147483648), by norm_num⟩
  | 2 => ⟨((258627803/4294967296), (648142127/2147483648)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((-44816783/1073741824), (-14039309/67108864)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((186387761/8589934592), (934205515/8589934592)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((-155032981/17179869184), (-1554100605/34359738368)), (127/17179869184), by norm_num⟩
  | 6 => ⟨((214921347/68719476736), (1077220453/68719476736)), (89/34359738368), by norm_num⟩
  | 7 => ⟨((-255380787/274877906944), (-1280009691/274877906944)), (107/137438953472), by norm_num⟩
  | 8 => ⟨((265524709/1099511627776), (1330852663/1099511627776)), (225/1099511627776), by norm_num⟩
  | 9 => ⟨((-122698469/2199023255552), (-307492257/1099511627776)), (105/2199023255552), by norm_num⟩
  | 10 => ⟨((204115435/17592186044416), (1023059477/17592186044416)), (177/17592186044416), by norm_num⟩
  | 11 => ⟨((-77172021/35184372088832), (-1547194455/140737488355328)), (271/140737488355328), by norm_num⟩
  | 12 => ⟨((213966275/562949953421312), (536216737/281474976710656)), (95/281474976710656), by norm_num⟩
  | 13 => ⟨((-273803299/4503599627370496), (-1372346287/4503599627370496)), (245/4503599627370496), by norm_num⟩
  | 14 => ⟨((162673701/18014398509481984), (1630693645/36028797018963968)), (147/18014398509481984), by norm_num⟩
  | 15 => ⟨((-45102727/36028797018963968), (-452124281/72057594037927936)), (165/144115188075855872), by norm_num⟩
  | 16 => ⟨((23447121/144115188075855872), (235041503/288230376151711744)), (173/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (894807851445/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889479810583841/316912650057057350374175801344), (1059177278993/316912650057057350374175801344)), (92409/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889956434287601/39614081257132168796771975168), (1191369617285/19807040628566084398385987584)), (51987/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236218095679655/309485009821345068724781056), (2531156708363/2475880078570760549798248448)), (110487/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885705421075039/77371252455336267181195264), (1265295082059/77371252455336267181195264)), (110505/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549759636955687/9671406556917033397649408), (2371826475653/9671406556917033397649408)), (103617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629484467672883/302231454903657293676544), (1037373265883/302231454903657293676544)), (90683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944042305171851/37778931862957161709568), (3370335408133/75557863725914323419136)), (73697/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297758576455865/4722366482869645213696), (2526765171831/4722366482869645213696)), (110577/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405437229983969/147573952589676412928), (868174977189/147573952589676412928)), (38023/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823849891410675/73786976294838206464), (2169236378817/36893488147419103232)), (190189/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823078054415251/9223372036854775808), (2438740417627/4611686018427387904)), (214065/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398581320028339/288230376151711744), (4873357426557/1152921504606846976)), (214193/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298719079193539/36028797018963968), (4259552847407/144115188075855872)), (93781/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492077862892143/36028797018963968), (6380069297727/36028797018963968)), (281631/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489803250690111/9007199254740992), (7958903764201/9007199254740992)), (11017/281474976710656), by norm_num⟩
  | 2 => ⟨((1114512130155433/2251799813685248), (3967336811395/1125899906842624)), (176651/1125899906842624), by norm_num⟩
  | 1 => ⟨((2217680808352641/2251799813685248), (11841589385751/1125899906842624)), (1063707/2251799813685248), by norm_num⟩
  | 0 => ⟨((2183739594018967/2251799813685248), (46884837549509/2251799813685248)), (2142669/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2183739594018967/2251799813685248), (46884837549509/2251799813685248)), (8173633584029387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116760289935939/2251799813685248), (90935504562859/2251799813685248)), (265315/140737488355328), by norm_num⟩
  | 2 => ⟨((1986146739989349/2251799813685248), (85482139146697/1125899906842624)), (8323793/2251799813685248), by norm_num⟩
  | 3 => ⟨((108678346553091/140737488355328), (301589992079571/2251799813685248)), (498361/70368744177664), by norm_num⟩
  | 4 => ⟨((1302360498162331/2251799813685248), (465779261221649/2251799813685248)), (14450699/1125899906842624), by norm_num⟩
  | 5 => ⟨((328446724704323/1125899906842624), (269390070552293/1125899906842624)), (22693719/1125899906842624), by norm_num⟩
  | 6 => ⟨((250865929678155/9007199254740992), (628690247174057/4503599627370496)), (192800663/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-76179559/2097152)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile006Terms0
