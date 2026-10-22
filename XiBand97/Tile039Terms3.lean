/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile039Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (34337/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (34337/1280))
  have he : value ((69/80), (34337/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-5564642085/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((408917956165163/18014398509481984), (-1183875071420285/18014398509481984)), (45155651/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1205427897/17179869184), (3489883523/17179869184)), (67/4294967296), by norm_num⟩
  | 2 => ⟨((931507201/8589934592), (-674211133/2147483648)), (13/536870912), by norm_num⟩
  | 3 => ⟨((-1919552203/17179869184), (5557373959/17179869184)), (431/17179869184), by norm_num⟩
  | 4 => ⟨((741677169/8589934592), (-4294519709/17179869184)), (335/17179869184), by norm_num⟩
  | 5 => ⟨((-1834044493/34359738368), (5309817095/34359738368)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((944851565/34359738368), (-5470956687/68719476736)), (431/68719476736), by norm_num⟩
  | 7 => ⟨((-1668900743/137438953472), (603962835/17179869184)), (383/137438953472), by norm_num⟩
  | 8 => ⟨((644830381/137438953472), (-3733749527/274877906944)), (149/137438953472), by norm_num⟩
  | 9 => ⟨((-1771731629/1099511627776), (5129412577/1099511627776)), (411/1099511627776), by norm_num⟩
  | 10 => ⟨((2190599073/4398046511104), (-6342092815/4398046511104)), (511/4398046511104), by norm_num⟩
  | 11 => ⟨((-307783397/2199023255552), (3564305115/8796093022208)), (289/8796093022208), by norm_num⟩
  | 12 => ⟨((1268495395/35184372088832), (-3672472809/35184372088832)), (75/8796093022208), by norm_num⟩
  | 13 => ⟨((-1206453267/140737488355328), (3492852111/140737488355328)), (287/140737488355328), by norm_num⟩
  | 14 => ⟨((1065485219/562949953421312), (-6169459519/1125899906842624)), (509/1125899906842624), by norm_num⟩
  | 15 => ⟨((-219564003/562949953421312), (5085349677/4503599627370496)), (211/2251799813685248), by norm_num⟩
  | 16 => ⟨((1357363309/18014398509481984), (-245609871/1125899906842624)), (41/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-403229852229/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777855886241311/633825300114114700748351602688), (-953471600171/316912650057057350374175801344)), (23097/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59022344087223/1237940039285380274899124224), (-1072408314397/19807040628566084398385987584)), (51975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888426097080795/2475880078570760549798248448), (-2278248050465/2475880078570760549798248448)), (27615/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770092560801443/154742504910672534362390528), (-1138775651191/77371252455336267181195264)), (27619/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387131039817137/2417851639229258349412352), (-266808041411/1208925819614629174706176)), (25897/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628944151656695/302231454903657293676544), (-1866916590417/604462909807314587353088)), (2833/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943164676763779/37778931862957161709568), (-3032353192507/75557863725914323419136)), (36837/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648221403758719/2361183241434822606848), (-2273052580045/4722366482869645213696)), (27635/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202492603979293/73786976294838206464), (-780869635205/147573952589676412928)), (76017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821591421638103/73786976294838206464), (-243837327127/4611686018427387904)), (95055/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820539529899409/9223372036854775808), (-1096254476027/2305843009213693952)), (13373/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397947392701963/288230376151711744), (-1094988940165/288230376151711744)), (107041/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192660735133847/144115188075855872), (-3826773709437/144115188075855872)), (93727/144115188075855872), by norm_num⟩
  | 4 => ⟨((744380405332881/18014398509481984), (-716100463001/4503599627370496)), (8795/2251799813685248), by norm_num⟩
  | 3 => ⟨((1485667978345771/9007199254740992), (-1785292810031/2251799813685248)), (176129/9007199254740992), by norm_num⟩
  | 2 => ⟨((555196693652731/1125899906842624), (-14223006450349/4503599627370496)), (352945/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102703491567949/1125899906842624), (-10593371322325/1125899906842624)), (265573/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159520094143763/2251799813685248), (-41785843891541/2251799813685248)), (534621/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159520094143763/2251799813685248), (-41785843891541/2251799813685248)), (2039417271140670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517561658004535/562949953421312), (-80146884271081/2251799813685248)), (2090533/2251799813685248), by norm_num⟩
  | 2 => ⟨((1900478705218629/2251799813685248), (-1151327763883/17592186044416)), (3992779/2251799813685248), by norm_num⟩
  | 3 => ⟨((1594325296544789/2251799813685248), (-248755202163309/2251799813685248)), (7262287/2251799813685248), by norm_num⟩
  | 4 => ⟨((137667322019881/281474976710656), (-352248640439325/2251799813685248)), (11888251/2251799813685248), by norm_num⟩
  | 5 => ⟨((967108663947057/4503599627370496), (-689128782687843/4503599627370496)), (15348265/2251799813685248), by norm_num⟩
  | 6 => ⟨((408917956165163/18014398509481984), (-1183875071420285/18014398509481984)), (45155651/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-5564642085/67108864)), (1/33554432), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-1411166567/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-913402855234981/18014398509481984), (-786557777753453/18014398509481984)), (110725829/18014398509481984), by norm_num⟩
  | 1 => ⟨((2731294031/17179869184), (73499899/536870912)), (333/17179869184), by norm_num⟩
  | 2 => ⟨((-2140989159/8589934592), (-3687336131/17179869184)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((2237686375/8589934592), (481734213/2147483648)), (275/8589934592), by norm_num⟩
  | 4 => ⟨((-3508126343/17179869184), (-3020949677/17179869184)), (433/17179869184), by norm_num⟩
  | 5 => ⟨((4399883943/34359738368), (3788868095/34359738368)), (545/34359738368), by norm_num⟩
  | 6 => ⟨((-4598603551/68719476736), (-989997833/17179869184)), (143/17179869184), by norm_num⟩
  | 7 => ⟨((4119684239/137438953472), (443447497/17179869184)), (515/137438953472), by norm_num⟩
  | 8 => ⟨((-1614655763/137438953472), (-695213531/68719476736)), (203/137438953472), by norm_num⟩
  | 9 => ⟨((1125054179/274877906944), (3875267565/1099511627776)), (71/137438953472), by norm_num⟩
  | 10 => ⟨((-2822080697/2199023255552), (-2430175807/2199023255552)), (179/1099511627776), by norm_num⟩
  | 11 => ⟨((804419791/2199023255552), (2770837159/8796093022208)), (205/4398046511104), by norm_num⟩
  | 12 => ⟨((-1681502401/17592186044416), (-2895981295/35184372088832)), (215/17592186044416), by norm_num⟩
  | 13 => ⟨((3244517571/140737488355328), (698487123/35184372088832)), (417/140737488355328), by norm_num⟩
  | 14 => ⟨((-2906618879/562949953421312), (-156435881/35184372088832)), (375/562949953421312), by norm_num⟩
  | 15 => ⟨((2430316449/2251799813685248), (2092816213/2251799813685248)), (315/2251799813685248), by norm_num⟩
  | 16 => ⟨((-238132599/1125899906842624), (-3281006565/18014398509481984)), (31/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1583111452757/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444447819273771/158456325028528675187087900672), (-3743165836055/633825300114114700748351602688)), (46285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888642037320793/39614081257132168796771975168), (-4210064735149/39614081257132168796771975168)), (26041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888348174373901/2475880078570760549798248448), (-2235979281677/1237940039285380274899124224)), (55351/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885007100834655/77371252455336267181195264), (-4470569363261/154742504910672534362390528)), (55367/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12097267455289/75557863725914323419136), (-1047420800335/2417851639229258349412352)), (51923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257823156087015/604462909807314587353088), (-3664497728455/604462909807314587353088)), (45449/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943111311186247/37778931862957161709568), (-186001378695/2361183241434822606848)), (73885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296362001550193/4722366482869645213696), (-4461615055157/4722366482869645213696)), (55441/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619828494302323/590295810358705651712), (-6130793403475/590295810358705651712)), (76275/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227681144854333/9223372036854775808), (-239300134999/2305843009213693952)), (95409/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455094239514771/2305843009213693952), (-4303357671359/4611686018427387904)), (53713/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397905962194191/288230376151711744), (-8596612001153/1152921504606846976)), (107539/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596256097372947/72057594037927936), (-7510681000727/144115188075855872)), (94225/144115188075855872), by norm_num⟩
  | 4 => ⟨((744265479348287/18014398509481984), (-1405417735691/4503599627370496)), (17699/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485368398945227/9007199254740992), (-14014554111565/9007199254740992)), (88719/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110075526878115/2251799813685248), (-13955251321057/2251799813685248)), (178111/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102181401519419/1125899906842624), (-10392540943139/562949953421312)), (537709/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078537075917219/1125899906842624), (-81963503067729/2251799813685248)), (272247/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078537075917219/1125899906842624), (-81963503067729/2251799813685248)), (1038539888622093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2063349882365063/2251799813685248), (-39257786768321/562949953421312)), (2165633/2251799813685248), by norm_num⟩
  | 2 => ⟨((1879720359767475/2251799813685248), (-287778866373599/2251799813685248)), (2135417/1125899906842624), by norm_num⟩
  | 3 => ⟨((766172004727637/1125899906842624), (-120113651077171/562949953421312)), (8221895/2251799813685248), by norm_num⟩
  | 4 => ⟨((940244121011369/2251799813685248), (-653896256899259/2251799813685248)), (7349241/1125899906842624), by norm_num⟩
  | 5 => ⟨((405434523562303/4503599627370496), (-1092143462423799/4503599627370496)), (20811303/2251799813685248), by norm_num⟩
  | 6 => ⟨((-913402855234981/18014398509481984), (-786557777753453/18014398509481984)), (110725829/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1411166567/16777216)), (1/33554432), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-1430321029/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1055797251799367/18014398509481984), (242600886309471/9007199254740992)), (26152221/4503599627370496), by norm_num⟩
  | 1 => ⟨((3199940205/17179869184), (-1470563271/17179869184)), (319/17179869184), by norm_num⟩
  | 2 => ⟨((-5084791113/17179869184), (1168382309/8589934592)), (509/17179869184), by norm_num⟩
  | 3 => ⟨((2693289979/8589934592), (-1237727291/8589934592)), (271/8589934592), by norm_num⟩
  | 4 => ⟨((-4279710267/17179869184), (1966781979/17179869184)), (27/1073741824), by norm_num⟩
  | 5 => ⟨((5440459843/34359738368), (-2500215601/34359738368)), (69/4294967296), by norm_num⟩
  | 6 => ⟨((-5763358081/68719476736), (2648606589/68719476736)), (587/68719476736), by norm_num⟩
  | 7 => ⟨((2616608889/68719476736), (-2404975519/137438953472)), (535/137438953472), by norm_num⟩
  | 8 => ⟨((-4157861951/274877906944), (1910785415/274877906944)), (427/274877906944), by norm_num⟩
  | 9 => ⟨((5872848489/1099511627776), (-2698923959/1099511627776)), (303/549755813888), by norm_num⟩
  | 10 => ⟨((-3732845727/2199023255552), (1715465125/2199023255552)), (387/2199023255552), by norm_num⟩
  | 11 => ⟨((4313885331/8796093022208), (-1982487459/8796093022208)), (449/8796093022208), by norm_num⟩
  | 12 => ⟨((-4569919933/35184372088832), (2100150621/35184372088832)), (477/35184372088832), by norm_num⟩
  | 13 => ⟨((2234377161/70368744177664), (-128353687/8796093022208)), (117/35184372088832), by norm_num⟩
  | 14 => ⟨((-2028848827/281474976710656), (932376975/281474976710656)), (427/562949953421312), by norm_num⟩
  | 15 => ⟨((429852719/281474976710656), (-790171791/1125899906842624)), (91/562949953421312), by norm_num⟩
  | 16 => ⟨((-170761885/562949953421312), (2511208487/18014398509481984)), (145/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (3531142395829/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777732917807037/633825300114114700748351602688), (4174327076401/633825300114114700748351602688)), (46307/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944288149502977/19807040628566084398385987584), (4694987588123/39614081257132168796771975168)), (13027/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118017388253221/154742504910672534362390528), (2493513815819/1237940039285380274899124224)), (13845/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((55310753429187/4835703278458516698824704), (2492728385185/77371252455336267181195264)), (55397/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387096096376741/2417851639229258349412352), (4672197157177/9671406556917033397649408)), (51953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628882700491159/302231454903657293676544), (4086504481237/604462909807314587353088)), (22739/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943064256481181/37778931862957161709568), (6637443357539/75557863725914323419136)), (73935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296291194615965/4722366482869645213696), (2487674015455/2361183241434822606848)), (55481/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619730769938507/590295810358705651712), (3418331063613/295147905179352825856)), (76335/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821326457176735/73786976294838206464), (8539169257341/73786976294838206464)), (95493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910119084676931/4611686018427387904), (9597416158893/9223372036854775808)), (53765/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591484125927127/1152921504606846976), (37445268199/4503599627370496)), (13457/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192388889814295/144115188075855872), (8374896608967/144115188075855872)), (47171/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488343915092585/36028797018963968), (12536689150265/36028797018963968)), (141797/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485130963041625/9007199254740992), (15626033982085/9007199254740992)), (88873/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219665365385011/4503599627370496), (7779466519641/1125899906842624)), (178497/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203607499795111/2251799813685248), (46342275912239/2251799813685248)), (269629/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077729039520957/1125899906842624), (22838086639077/562949953421312)), (273413/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077729039520957/1125899906842624), (22838086639077/562949953421312)), (1042987825633811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1029766112222877/1125899906842624), (43721949044391/562949953421312)), (2182459/2251799813685248), by norm_num⟩
  | 2 => ⟨((467524601508299/562949953421312), (159955183272051/1125899906842624)), (2165615/1125899906842624), by norm_num⟩
  | 3 => ⟨((376912435221035/562949953421312), (16605157986061/70368744177664)), (8424757/2251799813685248), by norm_num⟩
  | 4 => ⟨((442015073193005/1125899906842624), (711530735060963/2251799813685248)), (15257311/2251799813685248), by norm_num⟩
  | 5 => ⟨((244456288796325/4503599627370496), (558677211048043/2251799813685248)), (5405447/562949953421312), by norm_num⟩
  | 6 => ⟨((-1055797251799367/18014398509481984), (242600886309471/9007199254740992)), (26152221/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1430321029/16777216)), (1/33554432), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-2897386909/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-50393664810105/18014398509481984), (35019330923587/562949953421312)), (92416911/18014398509481984), by norm_num⟩
  | 1 => ⟨((309392833/34359738368), (-3440029227/17179869184)), (285/17179869184), by norm_num⟩
  | 2 => ⟨((-124487139/8589934592), (2768256729/8589934592)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((267139095/17179869184), (-5940449775/17179869184)), (495/17179869184), by norm_num⟩
  | 4 => ⟨((-107485947/8589934592), (4780392543/17179869184)), (25/1073741824), by norm_num⟩
  | 5 => ⟨((276787133/34359738368), (-1538748999/8589934592)), (517/34359738368), by norm_num⟩
  | 6 => ⟨((-296981137/68719476736), (3302027969/34359738368)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((136563629/68719476736), (-6073610287/137438953472)), (513/137438953472), by norm_num⟩
  | 8 => ⟨((-109895341/137438953472), (4887549331/274877906944)), (207/137438953472), by norm_num⟩
  | 9 => ⟨((614131/2147483648), (-6992184171/1099511627776)), (297/549755813888), by norm_num⟩
  | 10 => ⟨((-101212745/1099511627776), (2250697259/1099511627776)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((236939097/8796093022208), (-2634441817/4398046511104)), (451/8796093022208), by norm_num⟩
  | 12 => ⟨((-63556461/8796093022208), (5653294051/35184372088832)), (243/17592186044416), by norm_num⟩
  | 13 => ⟨((251791207/140737488355328), (-1399788581/35184372088832)), (483/140737488355328), by norm_num⟩
  | 14 => ⟨((-231567037/562949953421312), (2574711785/281474976710656)), (223/281474976710656), by norm_num⟩
  | 15 => ⟨((198769477/2251799813685248), (-2210047339/1125899906842624)), (385/2251799813685248), by norm_num⟩
  | 16 => ⟨((-79976783/4503599627370496), (7113867951/18014398509481984)), (311/9007199254740992), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1052337980147/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27776323889267/9903520314283042199192993792), (2487890260225/633825300114114700748351602688)), (2889/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888522429578511/39614081257132168796771975168), (1399102218735/19807040628566084398385987584)), (52009/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236027679439265/309485009821345068724781056), (1486125116591/1237940039285380274899124224)), (55269/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769887849819179/154742504910672534362390528), (2971303429721/154742504910672534362390528)), (55279/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387083047574571/2417851639229258349412352), (348073920737/1208925819614629174706176)), (51835/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314430069532443/151115727451828646838272), (1217756136165/302231454903657293676544)), (45367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886056214667289/75557863725914323419136), (3955823649703/75557863725914323419136)), (73741/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296237867867815/4722366482869645213696), (2965220324339/4722366482869645213696)), (13831/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404914725306983/147573952589676412928), (1018625649345/147573952589676412928)), (76099/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56913712535027/2305843009213693952), (2544559096267/36893488147419103232)), (95167/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455035636961743/2305843009213693952), (2859874481385/4611686018427387904)), (26781/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795696117652921/576460752303423488), (5712869932999/1152921504606846976)), (107199/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596156335507799/72057594037927936), (2495516103763/72057594037927936)), (23471/36028797018963968), by norm_num⟩
  | 4 => ⟨((372059482139773/9007199254740992), (3735557562979/18014398509481984)), (35249/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485013011951803/9007199254740992), (4655970756547/4503599627370496)), (176543/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109736398411025/2251799813685248), (9271624080853/2251799813685248)), (353983/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101713032559409/1125899906842624), (1725878837045/140737488355328)), (266613/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155519413291409/2251799813685248), (54429522848033/2251799813685248)), (1075503/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155519413291409/2251799813685248), (54429522848033/2251799813685248)), (4102718361861418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062040035663537/2251799813685248), (3256392187987/70368744177664)), (2111029/2251799813685248), by norm_num⟩
  | 2 => ⟨((470862295868827/562949953421312), (190846408925471/2251799813685248)), (2030823/1125899906842624), by norm_num⟩
  | 3 => ⟨((779589387474923/1125899906842624), (159627650235749/1125899906842624)), (935369/281474976710656), by norm_num⟩
  | 4 => ⟨((258583655085571/562949953421312), (55264247432229/281474976710656)), (12484443/2251799813685248), by norm_num⟩
  | 5 => ⟨((776608409586445/4503599627370496), (812316960524365/4503599627370496)), (1023217/140737488355328), by norm_num⟩
  | 6 => ⟨((-50393664810105/18014398509481984), (35019330923587/562949953421312)), (92416911/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-2897386909/33554432)), (1/33554432), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-188583173/67108864), (-5865380817/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((916711686359009/18014398509481984), (579351636699675/18014398509481984)), (27057647/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2848372623/17179869184), (-1800139963/17179869184)), (169/17179869184), by norm_num⟩
  | 2 => ⟨((4640136491/17179869184), (2932514891/17179869184)), (277/17179869184), by norm_num⟩
  | 3 => ⟨((-2519668773/8589934592), (-1592402769/8589934592)), (303/17179869184), by norm_num⟩
  | 4 => ⟨((4104662053/17179869184), (1297050487/8589934592)), (249/17179869184), by norm_num⟩
  | 5 => ⟨((-2674677045/17179869184), (-1690366281/17179869184)), (41/4294967296), by norm_num⟩
  | 6 => ⟨((726196335/8589934592), (114737011/2147483648)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((-2704020303/68719476736), (-1708910895/68719476736)), (169/68719476736), by norm_num⟩
  | 8 => ⟨((2202489797/137438953472), (2783898335/274877906944)), (277/274877906944), by norm_num⟩
  | 9 => ⟨((-1594649863/274877906944), (-2015602117/549755813888)), (101/274877906944), by norm_num⟩
  | 10 => ⟨((2078209279/1099511627776), (164175657/137438953472)), (265/2199023255552), by norm_num⟩
  | 11 => ⟨((-4924368333/8796093022208), (-3112146267/8796093022208)), (79/2199023255552), by norm_num⟩
  | 12 => ⟨((668502809/4398046511104), (211243187/2199023255552)), (173/17592186044416), by norm_num⟩
  | 13 => ⟨((-1340336423/35184372088832), (-211769445/8796093022208)), (175/70368744177664), by norm_num⟩
  | 14 => ⟨((4990794811/562949953421312), (1577063533/281474976710656)), (41/70368744177664), by norm_num⟩
  | 15 => ⟨((-1084032753/562949953421312), (-2740386793/2251799813685248)), (287/2251799813685248), by norm_num⟩
  | 16 => ⟨((110371355/281474976710656), (2232111181/9007199254740992)), (59/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197539410918425/1267650600228229401496703205376), (734164018535/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777635559455507/633825300114114700748351602688), (867790318159/633825300114114700748351602688)), (721/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((944233643298155/19807040628566084398385987584), (61001789461/2475880078570760549798248448)), (25957/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944081538729819/1237940039285380274899124224), (1036733347099/2475880078570760549798248448)), (27581/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769829751740209/154742504910672534362390528), (518199660895/77371252455336267181195264)), (27583/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548277999347669/9671406556917033397649408), (971269612583/9671406556917033397649408)), (51721/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673136792361/604462909807314587353088), (424753164299/302231454903657293676544)), (11315/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942990063237647/37778931862957161709568), (1379783301261/75557863725914323419136)), (73555/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296181253106021/4722366482869645213696), (258564103165/1180591620717411303424)), (13793/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619581788417057/590295810358705651712), (1421159012377/590295810358705651712)), (75873/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821143507072583/73786976294838206464), (887517304693/36893488147419103232)), (11857/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820036847506317/9223372036854775808), (62342855653/288230376151711744)), (53367/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591288412505927/1152921504606846976), (996273024683/576460752303423488)), (106761/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192223932412613/144115188075855872), (1740753225117/144115188075855872)), (93445/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488109018664739/36028797018963968), (2605690511019/36028797018963968)), (35057/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484859188151573/9007199254740992), (811904086671/2251799813685248)), (175391/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109593479282963/2251799813685248), (3233415113331/2251799813685248)), (87775/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101525686659851/1125899906842624), (4814772959923/1125899906842624)), (527455/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154983561164233/2251799813685248), (4744531791469/562949953421312)), (1058165/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154983561164233/2251799813685248), (4744531791469/562949953421312)), (4036579140670012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257771247656877/281474976710656), (18162161580969/1125899906842624)), (255397/281474976710656), by norm_num⟩
  | 2 => ⟨((943961703278293/1125899906842624), (8316339707321/281474976710656)), (3808149/2251799813685248), by norm_num⟩
  | 3 => ⟨((1580881404731143/2251799813685248), (111559560809321/2251799813685248)), (3305291/1125899906842624), by norm_num⟩
  | 4 => ⟨((1104334614961619/2251799813685248), (156641308993447/2251799813685248)), (9936959/2251799813685248), by norm_num⟩
  | 5 => ⟨((530694795716989/2251799813685248), (153641028481355/2251799813685248)), (22258225/4503599627370496), by norm_num⟩
  | 6 => ⟨((916711686359009/18014398509481984), (579351636699675/18014398509481984)), (27057647/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-188583173/67108864), (-5865380817/67108864)), (1/33554432), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-1483330689/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((118218966107633/2251799813685248), (-455456496011615/18014398509481984)), (48261431/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2972644247/17179869184), (1431570349/17179869184)), (153/17179869184), by norm_num⟩
  | 2 => ⟨((4898675249/17179869184), (-1179555583/8589934592)), (127/8589934592), by norm_num⟩
  | 3 => ⟨((-5381744827/17179869184), (2591748517/17179869184)), (281/17179869184), by norm_num⟩
  | 4 => ⟨((4434338251/17179869184), (-2135495077/17179869184)), (233/17179869184), by norm_num⟩
  | 5 => ⟨((-2922971097/17179869184), (175956085/2147483648)), (155/17179869184), by norm_num⟩
  | 6 => ⟨((1605605983/17179869184), (-773230069/17179869184)), (43/8589934592), by norm_num⟩
  | 7 => ⟨((-3023894509/68719476736), (364062881/17179869184)), (163/68719476736), by norm_num⟩
  | 8 => ⟨((4983131501/274877906944), (-2399783729/274877906944)), (271/274877906944), by norm_num⟩
  | 9 => ⟨((-3649686335/549755813888), (1757621263/549755813888)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((4811508309/2199023255552), (-1158566591/1099511627776)), (265/2199023255552), by norm_num⟩
  | 11 => ⟨((-5766525987/8796093022208), (2777051987/8796093022208)), (5/137438953472), by norm_num⟩
  | 12 => ⟨((791897039/4398046511104), (-190681465/2199023255552)), (177/17592186044416), by norm_num⟩
  | 13 => ⟨((-1606131357/35184372088832), (1546966159/70368744177664)), (181/70368744177664), by norm_num⟩
  | 14 => ⟨((3024883965/281474976710656), (-364182007/70368744177664)), (43/70368744177664), by norm_num⟩
  | 15 => ⟨((-5317079513/2251799813685248), (640151725/562949953421312)), (19/140737488355328), by norm_num⟩
  | 16 => ⟨((4381056669/9007199254740992), (-2109835655/9007199254740992)), (63/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-584617972833/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777585589764503/633825300114114700748351602688), (-345494001727/316912650057057350374175801344)), (46135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944205546201055/19807040628566084398385987584), (-777172042471/39614081257132168796771975168)), (811/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888103399213695/2475880078570760549798248448), (-412753009827/1237940039285380274899124224)), (27575/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884885052532059/77371252455336267181195264), (-825236985359/154742504910672534362390528)), (55153/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774111057056005/4835703278458516698824704), (-193343486977/2417851639229258349412352)), (51709/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628812135356023/302231454903657293676544), (-84552077137/75557863725914323419136)), (45249/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471475195465403/18889465931478580854784), (-549320910393/37778931862957161709568)), (36767/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296121799519441/4722366482869645213696), (-823513375391/4722366482869645213696)), (13789/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619500128816647/590295810358705651712), (-1131570958029/590295810358705651712)), (9481/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821041566038897/73786976294838206464), (-1413324761177/73786976294838206464)), (47411/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909961173554465/4611686018427387904), (-198553235345/1152921504606846976)), (106691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591174140813893/1152921504606846976), (-793236317039/576460752303423488)), (106713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192124201458733/144115188075855872), (-692984683899/72057594037927936)), (46699/72057594037927936), by norm_num⟩
  | 4 => ⟨((743979967248809/18014398509481984), (-259321713659/4503599627370496)), (140145/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484673726509619/9007199254740992), (-2585569573489/9007199254740992)), (87633/4503599627370496), by norm_num⟩
  | 2 => ⟨((554704676110017/1125899906842624), (-5148268427591/4503599627370496)), (87697/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202505624784723/2251799813685248), (-3832738476793/1125899906842624)), (526829/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153918354524629/2251799813685248), (-3776187891637/562949953421312)), (1056287/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153918354524629/2251799813685248), (-3776187891637/562949953421312)), (4029415139205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060190295888641/2251799813685248), (-14448176717129/1125899906842624)), (508729/562949953421312), by norm_num⟩
  | 2 => ⟨((942257173626599/1125899906842624), (-26437513037359/1125899906842624)), (1887875/1125899906842624), by norm_num⟩
  | 3 => ⟨((1575894329084779/2251799813685248), (-44250712094215/1125899906842624)), (6497113/2251799813685248), by norm_num⟩
  | 4 => ⟨((1099391881690697/2251799813685248), (-30968315133267/562949953421312)), (9604555/2251799813685248), by norm_num⟩
  | 5 => ⟨((1059879228695165/4503599627370496), (-241913612677201/4503599627370496)), (20870271/4503599627370496), by norm_num⟩
  | 6 => ⟨((118218966107633/2251799813685248), (-455456496011615/18014398509481984)), (48261431/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1483330689/16777216)), (1/33554432), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile039Terms3
