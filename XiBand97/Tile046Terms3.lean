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
namespace Reinmann.XiBand97.Tile046Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨46,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36843/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36843/1280))
  have he : value ((69/80), (36843/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-5970763559/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((669639018550199/18014398509481984), (-1058469491501665/18014398509481984)), (40590887/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1973993907/17179869184), (3120206961/17179869184)), (241/17179869184), by norm_num⟩
  | 2 => ⟨((3050849485/17179869184), (-2411173045/8589934592)), (375/17179869184), by norm_num⟩
  | 3 => ⟨((-785858773/4294967296), (4968692163/17179869184)), (389/17179869184), by norm_num⟩
  | 4 => ⟨((1214561415/8589934592), (-3839609603/17179869184)), (303/17179869184), by norm_num⟩
  | 5 => ⟨((-3003408717/34359738368), (4747358515/34359738368)), (47/4294967296), by norm_num⟩
  | 6 => ⟨((386819327/8589934592), (-611428613/8589934592)), (195/34359738368), by norm_num⟩
  | 7 => ⟨((-2732971341/137438953472), (4319889829/137438953472)), (347/137438953472), by norm_num⟩
  | 8 => ⟨((1055966305/137438953472), (-1669120357/137438953472)), (135/137438953472), by norm_num⟩
  | 9 => ⟨((-181335371/68719476736), (573257987/137438953472)), (373/1099511627776), by norm_num⟩
  | 10 => ⟨((56051533/68719476736), (-2835143639/2199023255552)), (29/274877906944), by norm_num⟩
  | 11 => ⟨((-2016089229/8796093022208), (1593372609/4398046511104)), (263/8796093022208), by norm_num⟩
  | 12 => ⟨((1038636233/17592186044416), (-3283454919/35184372088832)), (273/35184372088832), by norm_num⟩
  | 13 => ⟨((-123479565/8796093022208), (780715273/35184372088832)), (261/140737488355328), by norm_num⟩
  | 14 => ⟨((1744825497/562949953421312), (-1378985173/281474976710656)), (29/70368744177664), by norm_num⟩
  | 15 => ⟨((-2876442499/4503599627370496), (4546668493/4503599627370496)), (385/4503599627370496), by norm_num⟩
  | 16 => ⟨((1111400735/9007199254740992), (-3513486333/18014398509481984)), (299/18014398509481984), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-2561249835/19807040628566084398385987584)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777856547356209/633825300114114700748351602688), (-775205772923/316912650057057350374175801344)), (46177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944357895350681/19807040628566084398385987584), (-217976452041/4951760157141521099596496896)), (25977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888426974182349/2475880078570760549798248448), (-463074036503/618970019642690137449562112)), (55207/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55315421635677/4835703278458516698824704), (-1851729760693/154742504910672534362390528)), (27607/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774262545190677/4835703278458516698824704), (-867697549925/4835703278458516698824704)), (25885/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257889175777749/604462909807314587353088), (-94866839029/37778931862957161709568)), (45305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886330879432917/75557863725914323419136), (-2465410958309/75557863725914323419136)), (73633/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296444046465531/4722366482869645213696), (-1848072777413/4722366482869645213696)), (13809/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619942688770073/590295810358705651712), (-2539499772527/590295810358705651712)), (1187/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1821593972511391/73786976294838206464), (-3171976099751/73786976294838206464)), (94987/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910271357437321/4611686018427387904), (-891294496141/2305843009213693952)), (53449/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591793148938367/1152921504606846976), (-1780531762271/576460752303423488)), (106945/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149083038383115/18014398509481984), (-3111307927633/144115188075855872)), (46815/72057594037927936), by norm_num⟩
  | 4 => ⟨((744383523810327/18014398509481984), (-2328865917955/18014398509481984)), (140551/36028797018963968), by norm_num⟩
  | 3 => ⟨((742838652994847/4503599627370496), (-2903023234551/4503599627370496)), (175875/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220809996733213/4503599627370496), (-5781937380563/2251799813685248)), (176155/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102726568751471/1125899906842624), (-17225744218345/2251799813685248)), (529875/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159657115427633/2251799813685248), (-8493517907831/562949953421312)), (1065425/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159657115427633/2251799813685248), (-8493517907831/562949953421312)), (4064273842818450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070772273065733/2251799813685248), (-32583866955099/1125899906842624)), (2075807/2251799813685248), by norm_num⟩
  | 2 => ⟨((1902411993872569/2251799813685248), (-119857489693021/2251799813685248)), (1969003/1125899906842624), by norm_num⟩
  | 3 => ⟨((400213815043259/562949953421312), (-50630239100671/562949953421312)), (1768299/562949953421312), by norm_num⟩
  | 4 => ⟨((1119869897366419/2251799813685248), (-287953428526065/2251799813685248)), (11329279/2251799813685248), by norm_num⟩
  | 5 => ⟨((520113467862319/2251799813685248), (-572822458710563/4503599627370496)), (28332223/4503599627370496), by norm_num⟩
  | 6 => ⟨((669639018550199/18014398509481984), (-1058469491501665/18014398509481984)), (40590887/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-5970763559/67108864)), (1/33554432), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-6056628107/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-790643175141457/18014398509481984), (-454934413761493/9007199254740992)), (110541125/18014398509481984), by norm_num⟩
  | 1 => ⟨((73881659/536870912), (1360363219/8589934592)), (333/17179869184), by norm_num⟩
  | 2 => ⟨((-3706488231/17179869184), (-4265411005/17179869184)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((3873890803/17179869184), (2229028589/8589934592)), (275/8589934592), by norm_num⟩
  | 4 => ⟨((-3036640551/17179869184), (-873638281/4294967296)), (433/17179869184), by norm_num⟩
  | 5 => ⟨((3808547553/34359738368), (4382860443/34359738368)), (545/34359738368), by norm_num⟩
  | 6 => ⟨((-497569951/8589934592), (-4580811189/68719476736)), (143/17179869184), by norm_num⟩
  | 7 => ⟨((3566006179/137438953472), (4103744853/137438953472)), (515/137438953472), by norm_num⟩
  | 8 => ⟨((-2795297937/274877906944), (-3216817063/274877906944)), (203/137438953472), by norm_num⟩
  | 9 => ⟨((486924473/137438953472), (1120701255/274877906944)), (71/137438953472), by norm_num⟩
  | 10 => ⟨((-1221399095/1099511627776), (-1405580921/1099511627776)), (179/1099511627776), by norm_num⟩
  | 11 => ⟨((174076809/549755813888), (3205229707/8796093022208)), (205/4398046511104), by norm_num⟩
  | 12 => ⟨((-2911023081/35184372088832), (-3349993069/35184372088832)), (215/17592186044416), by norm_num⟩
  | 13 => ⟨((1404230159/70368744177664), (1615982137/70368744177664)), (417/140737488355328), by norm_num⟩
  | 14 => ⟨((-2515974595/562949953421312), (-2895372939/562949953421312)), (375/562949953421312), by norm_num⟩
  | 15 => ⟨((262960793/281474976710656), (2420913361/2251799813685248)), (315/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1649024091/9007199254740992), (-237211245/1125899906842624)), (31/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1489013692903/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777792143983629/633825300114114700748351602688), (-1760338848849/316912650057057350374175801344)), (23137/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888643059882633/39614081257132168796771975168), (-3959826765023/39614081257132168796771975168)), (52069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888349324353775/2475880078570760549798248448), (-1051538590265/618970019642690137449562112)), (55337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770015423016515/154742504910672534362390528), (-2102424008249/77371252455336267181195264)), (55351/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548451455054731/9671406556917033397649408), (-985164365871/2417851639229258349412352)), (51907/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628912149980669/302231454903657293676544), (-1723344111123/302231454903657293676544)), (22717/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943112311471755/37778931862957161709568), (-5598268675685/75557863725914323419136)), (18465/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296363625881257/4722366482869645213696), (-2098213915293/2361183241434822606848)), (13855/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619830928817563/590295810358705651712), (-5766395508871/590295810358705651712)), (19061/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227681562884457/9223372036854775808), (-7202458687563/73786976294838206464)), (47683/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820381133538051/9223372036854775808), (-1011895003003/1152921504606846976)), (26843/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795814269783173/576460752303423488), (-4042830450087/576460752303423488)), (107479/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192516877264707/144115188075855872), (-1766069570997/36028797018963968)), (23541/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488539134521513/36028797018963968), (-2643774044583/9007199254740992)), (70743/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485380625582243/9007199254740992), (-13181622702011/9007199254740992)), (177279/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220181490792263/4503599627370496), (-26251761256795/4503599627370496)), (22239/281474976710656), by norm_num⟩
  | 1 => ⟨((1102211644809835/1125899906842624), (-39099834913699/2251799813685248)), (536913/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157253682358295/2251799813685248), (-38546926916965/1125899906842624)), (543295/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157253682358295/2251799813685248), (-38546926916965/1125899906842624)), (2072505955222701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2064037824100787/2251799813685248), (-147713841221309/2251799813685248)), (1078169/1125899906842624), by norm_num⟩
  | 2 => ⟨((1882242255582137/2251799813685248), (-270794014255671/2251799813685248)), (529497/281474976710656), by norm_num⟩
  | 3 => ⟨((1540770404836347/2251799813685248), (-226352241923571/1125899906842624)), (4050187/1125899906842624), by norm_num⟩
  | 4 => ⟨((963243747309163/2251799813685248), (-619516589893357/2251799813685248)), (7171105/1125899906842624), by norm_num⟩
  | 5 => ⟨((483202554925825/4503599627370496), (-66252057347901/281474976710656)), (40323801/4503599627370496), by norm_num⟩
  | 6 => ⟨((-790643175141457/18014398509481984), (-454934413761493/9007199254740992)), (110541125/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-6056628107/67108864)), (1/33554432), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-6138837717/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-270869059135223/4503599627370496), (419771178037335/18014398509481984)), (50621/8796093022208), by norm_num⟩
  | 1 => ⟨((3283830455/17179869184), (-318063593/4294967296)), (79/4294967296), by norm_num⟩
  | 2 => ⟨((-2609047489/8589934592), (252705805/2147483648)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((5527795577/17179869184), (-2141633737/17179869184)), (67/2147483648), by norm_num⟩
  | 4 => ⟨((-4391907977/17179869184), (1701556825/17179869184)), (107/4294967296), by norm_num⟩
  | 5 => ⟨((5583087987/34359738368), (-1081527837/17179869184)), (273/17179869184), by norm_num⟩
  | 6 => ⟨((-5914451387/68719476736), (1145717895/34359738368)), (145/17179869184), by norm_num⟩
  | 7 => ⟨((671301603/17179869184), (-520164735/34359738368)), (529/137438953472), by norm_num⟩
  | 8 => ⟨((-4266865261/274877906944), (206638941/34359738368)), (211/137438953472), by norm_num⟩
  | 9 => ⟨((753351527/137438953472), (-36483871/17179869184)), (299/549755813888), by norm_num⟩
  | 10 => ⟨((-3830706729/2199023255552), (371032659/549755813888)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((4426978979/8796093022208), (-1715144383/8796093022208)), (443/8796093022208), by norm_num⟩
  | 12 => ⟨((-2344862917/17592186044416), (227117549/4398046511104)), (471/35184372088832), by norm_num⟩
  | 13 => ⟨((2292954023/70368744177664), (-444179567/35184372088832)), (231/70368744177664), by norm_num⟩
  | 14 => ⟨((-4164075037/562949953421312), (1613287513/562949953421312)), (211/281474976710656), by norm_num⟩
  | 15 => ⟨((1764487283/1125899906842624), (-1367230549/2251799813685248)), (45/281474976710656), by norm_num⟩
  | 16 => ⟨((-350477223/1125899906842624), (1086283071/9007199254740992)), (287/9007199254740992), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (1805399716015/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444433122825163/158456325028528675187087900672), (4268493350589/633825300114114700748351602688)), (46311/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944287897977337/19807040628566084398385987584), (300056124537/2475880078570760549798248448)), (52113/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888277646320689/2475880078570760549798248448), (2549762898751/1237940039285380274899124224)), (27693/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769943508897635/154742504910672534362390528), (5097919330939/154742504910672534362390528)), (13851/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387095946238695/2417851639229258349412352), (4777592977433/9671406556917033397649408)), (6495/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157220604783307/75557863725914323419136), (4178687994017/604462909807314587353088)), (11371/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886127528812971/75557863725914323419136), (1696792658851/18889465931478580854784)), (73945/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648145197779985/2361183241434822606848), (5087581426001/4722366482869645213696)), (27745/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809864786171699/295147905179352825856), (3495441097093/295147905179352825856)), (76349/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821324812089379/73786976294838206464), (8731793067079/73786976294838206464)), (95511/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910118057700883/4611686018427387904), (4906954974177/4611686018427387904)), (107553/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591481818537889/1152921504606846976), (9802222461237/1152921504606846976)), (53841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192386586554311/144115188075855872), (8563808713077/144115188075855872)), (2949/4503599627370496), by norm_num⟩
  | 4 => ⟨((1488339893666513/36028797018963968), (1602434049431/4503599627370496)), (141843/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485124949430513/9007199254740992), (3994622382817/2251799813685248)), (88907/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109825198035559/2251799813685248), (15909853522793/2251799813685248)), (178581/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101788877386315/1125899906842624), (23693681796583/1125899906842624)), (134899/562949953421312), by norm_num⟩
  | 0 => ⟨((1077684904123485/1125899906842624), (93411837717819/2251799813685248)), (547335/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077684904123485/1125899906842624), (93411837717819/2251799813685248)), (2087917332175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1029597127305939/1125899906842624), (89411613557401/1125899906842624)), (1093203/1125899906842624), by norm_num⟩
  | 2 => ⟨((934431028481079/1125899906842624), (327055504337497/2251799813685248)), (4346049/2251799813685248), by norm_num⟩
  | 3 => ⟨((375885998442113/562949953421312), (33929615926685/140737488355328)), (8476389/2251799813685248), by norm_num⟩
  | 4 => ⟨((109131177369465/281474976710656), (362481033544083/1125899906842624)), (15406551/2251799813685248), by norm_num⟩
  | 5 => ⟨((210183239010829/4503599627370496), (562152734527875/2251799813685248)), (341669/35184372088832), by norm_num⟩
  | 6 => ⟨((-270869059135223/4503599627370496), (419771178037335/18014398509481984)), (50621/8796093022208), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-6138837717/67108864)), (1/33554432), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-6217690881/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-29351989381043/18014398509481984), (1121367025299081/18014398509481984)), (45962521/9007199254740992), by norm_num⟩
  | 1 => ⟨((180207079/34359738368), (-6884653489/34359738368)), (283/17179869184), by norm_num⟩
  | 2 => ⟨((-145016053/17179869184), (2770105585/8589934592)), (229/8589934592), by norm_num⟩
  | 3 => ⟨((77798111/8589934592), (-5944417267/17179869184)), (493/17179869184), by norm_num⟩
  | 4 => ⟨((-125211229/17179869184), (4783585259/17179869184)), (399/17179869184), by norm_num⟩
  | 5 => ⟨((161215759/34359738368), (-6159106779/34359738368)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((-43244459/17179869184), (3304233319/34359738368)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((79542025/68719476736), (-6077666715/137438953472)), (513/137438953472), by norm_num⟩
  | 8 => ⟨((-128017951/274877906944), (4890813615/274877906944)), (415/274877906944), by norm_num⟩
  | 9 => ⟨((91571975/549755813888), (-6996854093/1099511627776)), (595/1099511627776), by norm_num⟩
  | 10 => ⟨((-117903527/2199023255552), (2252200449/1099511627776)), (385/2199023255552), by norm_num⟩
  | 11 => ⟨((69003057/4398046511104), (-2636201301/4398046511104)), (453/8796093022208), by norm_num⟩
  | 12 => ⟨((-4627339/1099511627776), (2828534879/17592186044416)), (61/4398046511104), by norm_num⟩
  | 13 => ⟨((9166049/8796093022208), (-350180867/8796093022208)), (485/140737488355328), by norm_num⟩
  | 14 => ⟨((-8429821/35184372088832), (5152862753/562949953421312)), (7/8796093022208), by norm_num⟩
  | 15 => ⟨((115774067/2251799813685248), (-4423046759/2251799813685248)), (193/1125899906842624), by norm_num⟩
  | 16 => ⟨((-186331173/18014398509481984), (7118619143/18014398509481984)), (39/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (2080225913285/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777684805622749/633825300114114700748351602688), (1229494203945/316912650057057350374175801344)), (23111/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888522520047305/39614081257132168796771975168), (345712222635/4951760157141521099596496896)), (52007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472055384313881/618970019642690137449562112), (2937721705735/2475880078570760549798248448)), (55267/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769887957873479/154742504910672534362390528), (2936785918825/154742504910672534362390528)), (55277/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387083074575233/2417851639229258349412352), (2752242901183/9671406556917033397649408)), (51833/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257720379327403/604462909807314587353088), (2407219063715/604462909807314587353088)), (45365/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886056391653501/75557863725914323419136), (977467277879/18889465931478580854784)), (36869/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296238011566389/4722366482869645213696), (2930773597829/4722366482869645213696)), (55321/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25307173696815/9223372036854775808), (4027169496353/590295810358705651712)), (76095/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821239096960521/73786976294838206464), (5029998512033/73786976294838206464)), (47581/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820142917209491/9223372036854775808), (5653303486497/9223372036854775808)), (107117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591392650238431/1152921504606846976), (2823252299235/576460752303423488)), (107191/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298078271299733/36028797018963968), (4933052611801/144115188075855872)), (93877/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488238651696993/36028797018963968), (1846081414417/9007199254740992)), (70491/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485014093299999/9007199254740992), (2300942263749/2251799813685248)), (176523/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219475488469645/4503599627370496), (18327844409377/4503599627370496)), (88483/1125899906842624), by norm_num⟩
  | 1 => ⟨((68857231667957/70368744177664), (6823325446673/562949953421312)), (533123/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077767641882181/1125899906842624), (13449336601893/562949953421312)), (1075193/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077767641882181/1125899906842624), (13449336601893/562949953421312)), (4101535805709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062100803478289/2251799813685248), (102995015497967/2251799813685248)), (2109833/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883671774333519/2251799813685248), (47159188601457/562949953421312)), (4057191/2251799813685248), by norm_num⟩
  | 3 => ⟨((1559923536257567/2251799813685248), (39449524744233/281474976710656)), (7467585/2251799813685248), by norm_num⟩
  | 4 => ⟨((129549730876609/281474976710656), (218627754629723/1125899906842624)), (3109869/562949953421312), by norm_num⟩
  | 5 => ⟨((784197699590531/4503599627370496), (201248204052987/1125899906842624)), (32563243/4503599627370496), by norm_num⟩
  | 6 => ⟨((-29351989381043/18014398509481984), (1121367025299081/18014398509481984)), (45962521/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-6217690881/67108864)), (1/33554432), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-188583173/67108864), (-6293450955/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((967806362397661/18014398509481984), (244621891782187/9007199254740992)), (50548343/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3007132109/17179869184), (-1520160177/17179869184)), (159/17179869184), by norm_num⟩
  | 2 => ⟨((4898763357/17179869184), (2476414305/17179869184)), (261/17179869184), by norm_num⟩
  | 3 => ⟨((-5320214645/17179869184), (-2689465625/17179869184)), (143/8589934592), by norm_num⟩
  | 4 => ⟨((4333443229/17179869184), (547658665/4294967296)), (235/17179869184), by norm_num⟩
  | 5 => ⟨((-5647510553/34359738368), (-2854919681/34359738368)), (77/8589934592), by norm_num⟩
  | 6 => ⟨((3066689097/34359738368), (1550267321/34359738368)), (169/34359738368), by norm_num⟩
  | 7 => ⟨((-2854734037/68719476736), (-1443120169/68719476736)), (159/68719476736), by norm_num⟩
  | 8 => ⟨((4650499541/274877906944), (2350912413/274877906944)), (261/274877906944), by norm_num⟩
  | 9 => ⟨((-1683530717/274877906944), (-1702111021/549755813888)), (191/549755813888), by norm_num⟩
  | 10 => ⟨((4388084481/2199023255552), (1109128405/1099511627776)), (251/2199023255552), by norm_num⟩
  | 11 => ⟨((-2599418701/4398046511104), (-657026803/2199023255552)), (299/8796093022208), by norm_num⟩
  | 12 => ⟨((2823052357/17592186044416), (2854209003/35184372088832)), (327/35184372088832), by norm_num⟩
  | 13 => ⟨((-2830085265/70368744177664), (-1430659765/70368744177664)), (165/70368744177664), by norm_num⟩
  | 14 => ⟨((329310393/35184372088832), (665889661/140737488355328)), (309/562949953421312), by norm_num⟩
  | 15 => ⟨((-286113347/140737488355328), (-2314168319/2251799813685248)), (271/2251799813685248), by norm_num⟩
  | 16 => ⟨((3728739621/9007199254740992), (1884945947/9007199254740992)), (223/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197539410918425/1267650600228229401496703205376), (609690589647/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777635684860267/633825300114114700748351602688), (720661292859/633825300114114700748351602688)), (5767/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944233717241019/19807040628566084398385987584), (810548458975/39614081257132168796771975168)), (25953/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888163243772159/2475880078570760549798248448), (860961037659/2475880078570760549798248448)), (3447/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((110614370523207/9671406556917033397649408), (53792728305/9671406556917033397649408)), (55155/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548278175893395/9671406556917033397649408), (403298164287/4835703278458516698824704)), (51711/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628836651106659/302231454903657293676544), (705477332581/604462909807314587353088)), (45251/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885980415780763/75557863725914323419136), (1145848862093/75557863725914323419136)), (36769/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296181487996955/4722366482869645213696), (107363014759/590295810358705651712)), (55159/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619582140456627/590295810358705651712), (1180209614579/590295810358705651712)), (18963/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910571995322549/36893488147419103232), (1474087677583/73786976294838206464)), (94827/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820037451249923/9223372036854775808), (1656735511541/9223372036854775808)), (106699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795644545362993/576460752303423488), (413680372673/288230376151711744)), (3335/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192224609395253/144115188075855872), (90351175489/9007199254740992)), (46703/72057594037927936), by norm_num⟩
  | 4 => ⟨((372027550151381/9007199254740992), (1081955699087/18014398509481984)), (70079/18014398509481984), by norm_num⟩
  | 3 => ⟨((742430477759229/4503599627370496), (1348501596345/4503599627370496)), (175287/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109595678819077/2251799813685248), (5370421519629/4503599627370496)), (350839/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101530056834329/1125899906842624), (7996925874831/2251799813685248)), (131733/562949953421312), by norm_num⟩
  | 0 => ⟨((2155009494903361/2251799813685248), (15760554405423/2251799813685248)), (1056595/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2155009494903361/2251799813685248), (15760554405423/2251799813685248)), (4030590065962981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062269256718917/2251799813685248), (15083110044779/1125899906842624)), (2037149/2251799813685248), by norm_num⟩
  | 2 => ⟨((472071769050231/562949953421312), (55254350678979/2251799813685248)), (3785953/2251799813685248), by norm_num⟩
  | 3 => ⟨((395525283511775/562949953421312), (92669051357843/2251799813685248)), (6535357/2251799813685248), by norm_num⟩
  | 4 => ⟨((553880595893465/1125899906842624), (65108723410173/1125899906842624)), (4860655/1125899906842624), by norm_num⟩
  | 5 => ⟨((1074854227465485/4503599627370496), (8007474354763/140737488355328)), (10689027/2251799813685248), by norm_num⟩
  | 6 => ⟨((967806362397661/18014398509481984), (244621891782187/9007199254740992)), (50548343/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-188583173/67108864), (-6293450955/67108864)), (1/33554432), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-3183175733/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((855400918835859/18014398509481984), (-152105272027645/4503599627370496)), (849833/281474976710656), by norm_num⟩
  | 1 => ⟨((-2688657649/17179869184), (1912361767/17179869184)), (173/17179869184), by norm_num⟩
  | 2 => ⟨((1107672125/4294967296), (-1575708103/8589934592)), (287/17179869184), by norm_num⟩
  | 3 => ⟨((-4867608833/17179869184), (3462184571/17179869184)), (159/8589934592), by norm_num⟩
  | 4 => ⟨((501338895/2147483648), (-1426349443/8589934592)), (33/2147483648), by norm_num⟩
  | 5 => ⟨((-660932485/4294967296), (1880406031/17179869184)), (175/17179869184), by norm_num⟩
  | 6 => ⟨((363054275/4294967296), (-2065837173/34359738368)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-2735011803/68719476736), (972666045/34359738368)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((4507076365/274877906944), (-3205748609/274877906944)), (153/137438953472), by norm_num⟩
  | 9 => ⟨((-1650509827/274877906944), (9171549/2147483648)), (113/274877906944), by norm_num⟩
  | 10 => ⟨((1087962227/549755813888), (-1547669981/1099511627776)), (75/549755813888), by norm_num⟩
  | 11 => ⟨((-2607815285/4398046511104), (1854861011/4398046511104)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((2864977919/17592186044416), (-509443275/4398046511104)), (201/17592186044416), by norm_num⟩
  | 13 => ⟨((-363173071/8796093022208), (2066513141/70368744177664)), (205/70368744177664), by norm_num⟩
  | 14 => ⟨((1367953367/140737488355328), (-1945968627/281474976710656)), (97/140737488355328), by norm_num⟩
  | 15 => ⟨((-2404560607/1125899906842624), (3420584075/2251799813685248)), (343/2251799813685248), by norm_num⟩
  | 16 => ⟨((3962519747/9007199254740992), (-1409210887/4503599627370496)), (285/9007199254740992), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-402669698739/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777585359762797/633825300114114700748351602688), (-475934617327/316912650057057350374175801344)), (46147/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944205410595281/19807040628566084398385987584), (-535295878951/19807040628566084398385987584)), (51919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888103094209915/2475880078570760549798248448), (-568587056737/1237940039285380274899124224)), (431/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((442442445284625/38685626227668133590597632), (-568401742725/77371252455336267181195264)), (13793/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193527723793097/1208925819614629174706176), (-532679821813/4835703278458516698824704)), (51727/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257623967348451/604462909807314587353088), (-931796253633/604462909807314587353088)), (22633/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885900251311477/75557863725914323419136), (-1513431624731/75557863725914323419136)), (73565/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648060684381187/2361183241434822606848), (-283607248535/1180591620717411303424)), (55181/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619499483231691/590295810358705651712), (-1558792943149/590295810358705651712)), (75885/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821040679253519/73786976294838206464), (-973461055285/36893488147419103232)), (11859/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1819921239966607/9223372036854775808), (-1094066022009/4611686018427387904)), (53377/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795586448559005/576460752303423488), (-2185441085465/1152921504606846976)), (3337/36028797018963968), by norm_num⟩
  | 5 => ⟨((298030740014557/36028797018963968), (-238654752719/18014398509481984)), (23367/36028797018963968), by norm_num⟩
  | 4 => ⟨((1487957767201281/36028797018963968), (-22326735627/281474976710656)), (35067/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484670485849131/9007199254740992), (-3561741339839/9007199254740992)), (175451/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218810638670327/4503599627370496), (-7091972027727/4503599627370496)), (351251/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101244800220357/1125899906842624), (-5279762429531/1125899906842624)), (131939/562949953421312), by norm_num⟩
  | 0 => ⟨((1076935407169677/1125899906842624), (-10403684624923/1125899906842624)), (4137/8796093022208), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076935407169677/1125899906842624), (-10403684624923/1125899906842624)), (15781402621445057/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((1030004201540485/1125899906842624), (-39804946317213/2251799813685248)), (2045601/2251799813685248), by norm_num⟩
  | 2 => ⟨((941924357847433/1125899906842624), (-36414659686577/1125899906842624)), (3815065/2251799813685248), by norm_num⟩
  | 3 => ⟨((1573666474403641/2251799813685248), (-60928781915791/1125899906842624)), (6630123/2251799813685248), by norm_num⟩
  | 4 => ⟨((1093159743525537/2251799813685248), (-42579975735149/562949953421312)), (1248061/281474976710656), by norm_num⟩
  | 5 => ⟨((64725411448703/281474976710656), (-330734304682487/4503599627370496)), (22409093/4503599627370496), by norm_num⟩
  | 6 => ⟨((855400918835859/18014398509481984), (-152105272027645/4503599627370496)), (849833/281474976710656), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-3183175733/33554432)), (1/33554432), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile046Terms3
