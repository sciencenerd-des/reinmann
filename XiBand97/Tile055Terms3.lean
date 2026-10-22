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
namespace Reinmann.XiBand97.Tile055Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨55,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77803/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77803/2560))
  have he : value ((69/80), (77803/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-715655399/268435456), (-25217453365/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((597266260835703/9007199254740992), (376651225887161/18014398509481984)), (6417115/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7042600129/34359738368), (-1110310487/17179869184)), (153/68719476736), by norm_num⟩
  | 2 => ⟨((5442243995/17179869184), (6864033703/68719476736)), (239/68719476736), by norm_num⟩
  | 3 => ⟨((-2803701205/8589934592), (-7072339859/68719476736)), (31/8589934592), by norm_num⟩
  | 4 => ⟨((8666359451/34359738368), (5465225687/68719476736)), (193/68719476736), by norm_num⟩
  | 5 => ⟨((-21430467983/137438953472), (-3378648923/68719476736)), (15/8589934592), by norm_num⟩
  | 6 => ⟨((22080828777/274877906944), (6962364837/274877906944)), (125/137438953472), by norm_num⟩
  | 7 => ⟨((-4875198511/137438953472), (-6148847225/549755813888)), (223/549755813888), by norm_num⟩
  | 8 => ⟨((7534722783/549755813888), (4751586953/1099511627776)), (87/549755813888), by norm_num⟩
  | 9 => ⟨((-10351176887/2199023255552), (-6527714219/4398046511104)), (241/4398046511104), by norm_num⟩
  | 10 => ⟨((199974545/137438953472), (4035488355/8796093022208)), (301/17592186044416), by norm_num⟩
  | 11 => ⟨((-14385566445/35184372088832), (-4535951209/35184372088832)), (171/35184372088832), by norm_num⟩
  | 12 => ⟨((14822132199/140737488355328), (2336802959/70368744177664)), (89/70368744177664), by norm_num⟩
  | 13 => ⟨((-3524295375/140737488355328), (-4445019785/562949953421312)), (171/562949953421312), by norm_num⟩
  | 14 => ⟨((24899992279/4503599627370496), (3925641389/2251799813685248)), (19/281474976710656), by norm_num⟩
  | 15 => ⟨((-10262257763/9007199254740992), (-404477473/1125899906842624)), (63/4503599627370496), by norm_num⟩
  | 16 => ⟨((7930268603/36028797018963968), (2500514081/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (49734565239/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777857717906327/633825300114114700748351602688), (117601648887/158456325028528675187087900672)), (2883/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59022411612081/1237940039285380274899124224), (529085989619/39614081257132168796771975168)), (6487/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888428527152781/2475880078570760549798248448), (562001078699/2475880078570760549798248448)), (13785/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885047570849683/77371252455336267181195264), (561829284277/154742504910672534362390528)), (13785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548526738982097/9671406556917033397649408), (8227070257/151115727451828646838272)), (3231/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628945360268577/302231454903657293676544), (230266780069/302231454903657293676544)), (11309/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235791697644419/9444732965739290427392), (374012630217/37778931862957161709568)), (9189/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648223120054999/2361183241434822606848), (560720069211/4722366482869645213696)), (13785/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619945976605181/590295810358705651712), (770504752803/590295810358705651712)), (18955/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910799244506173/36893488147419103232), (962403506821/73786976294838206464)), (1481/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455137088524827/2305843009213693952), (1081704663781/9223372036854775808)), (6665/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591799484275189/1152921504606846976), (1080456971463/1152921504606846976)), (3333/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192670631429681/144115188075855872), (235999532927/36028797018963968)), (23335/144115188075855872), by norm_num⟩
  | 4 => ⟨((46524315331785/1125899906842624), (1413198592509/36028797018963968)), (35011/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485693821313013/9007199254740992), (880805766481/4503599627370496)), (21889/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220851113443985/4503599627370496), (877151562059/1125899906842624)), (87599/4503599627370496), by norm_num⟩
  | 1 => ⟨((551383714532277/562949953421312), (5226518450759/2251799813685248)), (65755/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159899727228019/2251799813685248), (5154188196341/1125899906842624)), (263473/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159899727228019/2251799813685248), (5154188196341/1125899906842624)), (1005069741255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035851531007341/1125899906842624), (19775345235755/2251799813685248)), (253927/1125899906842624), by norm_num⟩
  | 2 => ⟨((1905836605367835/2251799813685248), (9096866210825/562949953421312)), (471697/1125899906842624), by norm_num⟩
  | 3 => ⟨((1612438679804327/2251799813685248), (61593896627429/2251799813685248)), (1627395/2251799813685248), by norm_num⟩
  | 4 => ⟨((1152928724946709/2251799813685248), (88210666648379/2251799813685248)), (604919/562949953421312), by norm_num⟩
  | 5 => ⟨((293423845908845/1125899906842624), (90328288338539/2251799813685248)), (1333669/1125899906842624), by norm_num⟩
  | 6 => ⟨((597266260835703/9007199254740992), (376651225887161/18014398509481984)), (6417115/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-25217453365/268435456)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-725947119/268435456), (-1598756333/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((604444159576609/18014398509481984), (-521446349703175/9007199254740992)), (19924705/18014398509481984), by norm_num⟩
  | 1 => ⟨((-7229733147/68719476736), (6236999563/34359738368)), (15/4294967296), by norm_num⟩
  | 2 => ⟨((708399577/4294967296), (-9778038027/34359738368)), (379/68719476736), by norm_num⟩
  | 3 => ⟨((-2961577035/17179869184), (10219660559/34359738368)), (199/34359738368), by norm_num⟩
  | 4 => ⟨((9286007663/68719476736), (-16021843285/68719476736)), (157/34359738368), by norm_num⟩
  | 5 => ⟨((-5823244663/68719476736), (20094558779/137438953472)), (99/34359738368), by norm_num⟩
  | 6 => ⟨((3043124993/68719476736), (-10501062137/137438953472)), (13/8589934592), by norm_num⟩
  | 7 => ⟨((-5452400465/274877906944), (9407434169/274877906944)), (187/274877906944), by norm_num⟩
  | 8 => ⟨((2136996265/274877906944), (-921779857/68719476736)), (295/1099511627776), by norm_num⟩
  | 9 => ⟨((-11912070095/4398046511104), (20552785137/4398046511104)), (413/4398046511104), by norm_num⟩
  | 10 => ⟨((116719459/137438953472), (-12888627783/8796093022208)), (261/8796093022208), by norm_num⟩
  | 11 => ⟨((-8517194207/35184372088832), (14695351951/35184372088832)), (299/35184372088832), by norm_num⟩
  | 12 => ⟨((8901871057/140737488355328), (-15359063681/140737488355328)), (157/70368744177664), by norm_num⟩
  | 13 => ⟨((-8588235449/562949953421312), (7408962359/281474976710656)), (305/562949953421312), by norm_num⟩
  | 14 => ⟨((7693817879/2251799813685248), (-13274719213/2251799813685248)), (275/2251799813685248), by norm_num⟩
  | 15 => ⟨((-3216522861/4503599627370496), (11099414749/9007199254740992)), (231/9007199254740992), by norm_num⟩
  | 16 => ⟨((5042694413/36028797018963968), (-17401075373/72057594037927936)), (91/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (-340477839179/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777797402239269/633825300114114700748351602688), (-805038087077/316912650057057350374175801344)), (5773/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888649262400043/39614081257132168796771975168), (-905456587809/19807040628566084398385987584)), (6495/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944178149885007/1237940039285380274899124224), (-961782325617/1237940039285380274899124224)), (13803/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770022831326821/154742504910672534362390528), (-1922968020431/154742504910672534362390528)), (13805/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774229429956975/4835703278458516698824704), (-1802148847941/9671406556917033397649408)), (809/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257831238351863/604462909807314587353088), (-788123425489/302231454903657293676544)), (177/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1886236757800945/75557863725914323419136), (-640053529997/18889465931478580854784)), (18411/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324093369647261/1180591620717411303424), (-1919122548635/4722366482869645213696)), (13811/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619845695875883/590295810358705651712), (-659276950471/147573952589676412928)), (18995/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113842049268195/4611686018427387904), (-1646929073983/36893488147419103232)), (11875/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455101615212557/2305843009213693952), (-3702119500481/9223372036854775808)), (26729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591656992677151/1152921504606846976), (-3697785598487/1152921504606846976)), (26741/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596272640148865/72057594037927936), (-403836659133/18014398509481984)), (23413/144115188075855872), by norm_num⟩
  | 4 => ⟨((744294363668281/18014398509481984), (-2418158960659/18014398509481984)), (17573/18014398509481984), by norm_num⟩
  | 3 => ⟨((5802557774507/35184372088832), (-3014210226165/4503599627370496)), (43981/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110183059351113/2251799813685248), (-1500756983819/562949953421312)), (88105/4503599627370496), by norm_num⟩
  | 1 => ⟨((551197550529765/562949953421312), (-1117664386935/140737488355328)), (132523/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079171380015379/1125899906842624), (-17631244373701/1125899906842624)), (266519/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079171380015379/1125899906842624), (-17631244373701/1125899906842624)), (1016689309127043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2068212279955141/2251799813685248), (-8449745046837/281474976710656)), (16227/70368744177664), by norm_num⟩
  | 2 => ⟨((1897563240187605/2251799813685248), (-15521687462757/281474976710656)), (985035/2251799813685248), by norm_num⟩
  | 3 => ⟨((796102559981865/1125899906842624), (-209278877285673/2251799813685248)), (221099/281474976710656), by norm_num⟩
  | 4 => ⟨((276592026566909/562949953421312), (-295954283226605/2251799813685248)), (1415069/1125899906842624), by norm_num⟩
  | 5 => ⟨((1009380533650683/4503599627370496), (-581640300146117/4503599627370496)), (3524973/2251799813685248), by norm_num⟩
  | 6 => ⟨((604444159576609/18014398509481984), (-521446349703175/9007199254740992)), (19924705/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-1598756333/16777216)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-25927312701/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-807363845521723/18014398509481984), (-835638814359025/18014398509481984)), (13348021/9007199254740992), by norm_num⟩
  | 1 => ⟨((2446981203/17179869184), (2532677779/17179869184)), (325/68719476736), by norm_num⟩
  | 2 => ⟨((-7776637985/34359738368), (-16097972633/68719476736)), (519/68719476736), by norm_num⟩
  | 3 => ⟨((16476382757/68719476736), (17053407863/68719476736)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((-13090707833/68719476736), (-13549162045/68719476736)), (55/8589934592), by norm_num⟩
  | 5 => ⟨((16641189669/137438953472), (8611993267/68719476736)), (281/68719476736), by norm_num⟩
  | 6 => ⟨((-4407216381/68719476736), (-9123126063/137438953472)), (299/137438953472), by norm_num⟩
  | 7 => ⟨((8003640515/274877906944), (2070984695/68719476736)), (545/549755813888), by norm_num⟩
  | 8 => ⟨((-6359000099/549755813888), (-13163401685/1099511627776)), (435/1099511627776), by norm_num⟩
  | 9 => ⟨((8981886499/2199023255552), (9296444255/2199023255552)), (309/2199023255552), by norm_num⟩
  | 10 => ⟨((-11417967517/8796093022208), (-11817840109/8796093022208)), (395/8796093022208), by norm_num⟩
  | 11 => ⟨((13195241965/35184372088832), (3414339275/8796093022208)), (229/17592186044416), by norm_num⟩
  | 12 => ⟨((-13978396423/140737488355328), (-7233969341/70368744177664)), (487/140737488355328), by norm_num⟩
  | 13 => ⟨((6834476353/281474976710656), (7073828915/281474976710656)), (239/281474976710656), by norm_num⟩
  | 14 => ⟨((-12411619287/2251799813685248), (-6423145451/1125899906842624)), (109/562949953421312), by norm_num⟩
  | 15 => ⟨((10518611791/9007199254740992), (10886987735/9007199254740992)), (371/9007199254740992), by norm_num⟩
  | 16 => ⟨((-8357178623/36028797018963968), (-2162464567/9007199254740992)), (37/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-3046791537685/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222216913295573/79228162514264337593543950336), (-112554796245/19807040628566084398385987584)), (5785/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236072389529557/4951760157141521099596496896), (-1012750698995/9903520314283042199192993792)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888281380310107/2475880078570760549798248448), (-4302985989943/2475880078570760549798248448)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884973737296899/77371252455336267181195264), (-537703924481/19342813113834066795298816)), (865/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774193874387843/4835703278458516698824704), (-4031340636255/9671406556917033397649408)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628884276178471/302231454903657293676544), (-881496193811/151115727451828646838272)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886134024489983/75557863725914323419136), (-2863514789003/37778931862957161709568)), (4617/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648147834783511/2361183241434822606848), (-2146457278859/2361183241434822606848)), (6929/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619737476829501/590295810358705651712), (-5898928428965/590295810358705651712)), (19065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821335670162825/73786976294838206464), (-3683960248899/36893488147419103232)), (11923/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820249672113889/9223372036854775808), (-4140511922265/4611686018427387904)), (26849/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795748524012521/576460752303423488), (-8271174202607/1152921504606846976)), (6719/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192401788804707/144115188075855872), (-1806552152243/36028797018963968)), (23547/144115188075855872), by norm_num⟩
  | 4 => ⟨((744183218203077/18014398509481984), (-5408602665845/18014398509481984)), (17691/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485164641352549/9007199254740992), (-13482885972293/9007199254740992)), (44335/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109874599580575/2251799813685248), (-3356272491501/562949953421312)), (88993/4503599627370496), by norm_num⟩
  | 1 => ⟨((550943521140621/562949953421312), (-39987234014619/2251799813685248)), (67151/1125899906842624), by norm_num⟩
  | 0 => ⟨((269494055237175/281474976710656), (-78827980735767/2251799813685248)), (271869/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269494055237175/281474976710656), (-78827980735767/2251799813685248)), (1037097939498137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1030712644384587/1125899906842624), (-150945369587701/2251799813685248)), (539629/2251799813685248), by norm_num⟩
  | 2 => ⟨((117314206032257/140737488355328), (-276367908194693/2251799813685248)), (530181/1125899906842624), by norm_num⟩
  | 3 => ⟨((191338736587425/281474976710656), (-460742650754129/2251799813685248)), (126753/140737488355328), by norm_num⟩
  | 4 => ⟨((473130198438169/1125899906842624), (-313199836509299/1125899906842624)), (1793571/1125899906842624), by norm_num⟩
  | 5 => ⟨((223391167048507/2251799813685248), (-1052912784860259/4503599627370496)), (2505265/1125899906842624), by norm_num⟩
  | 6 => ⟨((-807363845521723/18014398509481984), (-835638814359025/18014398509481984)), (13348021/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-25927312701/268435456)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-102579485/1048576)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1015836923359503/18014398509481984), (237908017531721/9007199254740992)), (25285917/18014398509481984), by norm_num⟩
  | 1 => ⟨((3118374743/17179869184), (-365160163/4294967296)), (39/8589934592), by norm_num⟩
  | 2 => ⟨((-10037661073/34359738368), (9403241767/68719476736)), (63/8589934592), by norm_num⟩
  | 3 => ⟨((10769994855/34359738368), (-630580575/4294967296)), (543/68719476736), by norm_num⟩
  | 4 => ⟨((-4333409509/17179869184), (4059521137/34359738368)), (439/68719476736), by norm_num⟩
  | 5 => ⟨((5579482843/34359738368), (-10453675559/137438953472)), (567/137438953472), by norm_num⟩
  | 6 => ⟨((-2993277073/34359738368), (2804090295/68719476736)), (153/68719476736), by norm_num⟩
  | 7 => ⟨((11011413951/274877906944), (-5157724835/274877906944)), (565/549755813888), by norm_num⟩
  | 8 => ⟨((-8861093541/549755813888), (8301037891/1099511627776)), (57/137438953472), by norm_num⟩
  | 9 => ⟨((12676782125/2199023255552), (-2968890021/1099511627776)), (41/274877906944), by norm_num⟩
  | 10 => ⟨((-16321995007/8796093022208), (1911297663/2199023255552)), (53/1099511627776), by norm_num⟩
  | 11 => ⟨((19104900051/35184372088832), (-8948697951/35184372088832)), (249/17592186044416), by norm_num⟩
  | 12 => ⟨((-10249383485/70368744177664), (9601582499/140737488355328)), (67/17592186044416), by norm_num⟩
  | 13 => ⟨((10151228529/281474976710656), (-9509631319/562949953421312)), (533/562949953421312), by norm_num⟩
  | 14 => ⟨((-583491859/70368744177664), (8745806387/2251799813685248)), (123/562949953421312), by norm_num⟩
  | 15 => ⟨((4006800723/2251799813685248), (-7507110599/9007199254740992)), (53/1125899906842624), by norm_num⟩
  | 16 => ⟨((-6448696991/18014398509481984), (6041114205/36028797018963968)), (343/36028797018963968), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (3521668798283/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444419687994071/158456325028528675187087900672), (2081442860643/316912650057057350374175801344)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236064422572495/4951760157141521099596496896), (2341053024885/19807040628566084398385987584)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236026688527709/309485009821345068724781056), (1243331755707/618970019642690137449562112)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884939715326577/77371252455336267181195264), (2485870231879/77371252455336267181195264)), (6925/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774161887580137/4835703278458516698824704), (1164830364679/2417851639229258349412352)), (12989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314428098303949/151115727451828646838272), (2037610802105/302231454903657293676544)), (5685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886042424619449/75557863725914323419136), (6619077523493/75557863725914323419136)), (4621/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296226671466609/4722366482869645213696), (2480773217045/2361183241434822606848)), (13871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809821060319651/295147905179352825856), (6817640777055/590295810358705651712)), (19085/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910607875283011/36893488147419103232), (8515326477757/73786976294838206464)), (23873/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820113768755575/9223372036854775808), (1196312797835/1152921504606846976)), (13441/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591359905670253/1152921504606846976), (2389740477875/288230376151711744)), (13457/576460752303423488), by norm_num⟩
  | 5 => ⟨((596140199930181/72057594037927936), (4175560789701/72057594037927936)), (23585/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488181585418857/36028797018963968), (6250387260131/18014398509481984)), (35449/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484928759505725/9007199254740992), (15580702160713/9007199254740992)), (44435/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219263081388537/4503599627370496), (484779644801/70368744177664)), (89245/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203009372329759/2251799813685248), (46201096149843/2251799813685248)), (67403/1125899906842624), by norm_num⟩
  | 0 => ⟨((134642685164083/140737488355328), (2845540562161/70368744177664)), (136693/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((134642685164083/140737488355328), (2845540562161/70368744177664)), (521442417625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2057307058729607/2251799813685248), (174227908261251/2251799813685248)), (136301/562949953421312), by norm_num⟩
  | 2 => ⟨((933066284210321/1125899906842624), (159179472045053/1125899906842624)), (270149/562949953421312), by norm_num⟩
  | 3 => ⟨((750754646369879/1125899906842624), (131916698456925/562949953421312)), (2096593/2251799813685248), by norm_num⟩
  | 4 => ⟨((877563759827035/2251799813685248), (703700737150191/2251799813685248)), (3778629/2251799813685248), by norm_num⟩
  | 5 => ⟨((122090526620173/2251799813685248), (548487712747361/2251799813685248)), (5306877/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1015836923359503/18014398509481984), (237908017531721/9007199254740992)), (25285917/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-102579485/1048576)), (1/134217728), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-754332693/268435456), (-6645079997/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((64204176206987/18014398509481984), (135317130397065/2251799813685248)), (10830651/9007199254740992), by norm_num⟩
  | 1 => ⟨((-24936605/2147483648), (-26908952275/137438953472)), (541/137438953472), by norm_num⟩
  | 2 => ⟨((1299933863/68719476736), (10958995531/34359738368)), (221/34359738368), by norm_num⟩
  | 3 => ⟨((-705885003/34359738368), (-1487727725/4294967296)), (241/34359738368), by norm_num⟩
  | 4 => ⟨((574960371/34359738368), (19388642201/68719476736)), (197/34359738368), by norm_num⟩
  | 5 => ⟨((-1498621115/137438953472), (-25268027213/137438953472)), (129/34359738368), by norm_num⟩
  | 6 => ⟨((406887689/68719476736), (13720945331/137438953472)), (563/274877906944), by norm_num⟩
  | 7 => ⟨((-757531069/274877906944), (-12772618423/274877906944)), (263/274877906944), by norm_num⟩
  | 8 => ⟨((1234054677/1099511627776), (20807211933/1099511627776)), (215/549755813888), by norm_num⟩
  | 9 => ⟨((-223370515/549755813888), (-30129735629/4398046511104)), (625/4398046511104), by norm_num⟩
  | 10 => ⟨((1164420323/8796093022208), (19633117469/8796093022208)), (409/8796093022208), by norm_num⟩
  | 11 => ⟨((-689780695/17592186044416), (-11630289465/17592186044416)), (487/35184372088832), by norm_num⟩
  | 12 => ⟨((1498248063/140737488355328), (6315434307/35184372088832)), (265/70368744177664), by norm_num⟩
  | 13 => ⟨((-750990281/281474976710656), (-25324670341/562949953421312)), (533/562949953421312), by norm_num⟩
  | 14 => ⟨((1398170763/2251799813685248), (11787174395/1125899906842624)), (249/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1214766753/9007199254740992), (-10241000557/4503599627370496)), (435/9007199254740992), by norm_num⟩
  | 16 => ⟨((494728419/18014398509481984), (8341542115/18014398509481984)), (89/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (1968971411653/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777633057076393/633825300114114700748351602688), (581836716529/158456325028528675187087900672)), (11555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888464335622859/39614081257132168796771975168), (654407500139/9903520314283042199192993792)), (13001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944079879397819/1237940039285380274899124224), (2780434725499/2475880078570760549798248448)), (13815/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769826227176223/154742504910672534362390528), (1389769177175/77371252455336267181195264)), (13817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774137238244233/4835703278458516698824704), (2604865182841/9671406556917033397649408)), (12957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257669835922157/604462909807314587353088), (284788178365/75557863725914323419136)), (2835/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942987176785363/37778931862957161709568), (14454933351/295147905179352825856)), (18431/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648088283005387/2361183241434822606848), (86680863403/147573952589676412928)), (3457/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809787381850681/295147905179352825856), (3811425337315/590295810358705651712)), (4755/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455283464427793/18446744073709551616), (595060698669/9223372036854775808)), (23785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820024800222923/9223372036854775808), (5350331377839/9223372036854775808)), (6693/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591274879112097/1152921504606846976), (2671909894155/576460752303423488)), (13395/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192210423731051/144115188075855872), (2334263228837/72057594037927936)), (23461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488085433971343/36028797018963968), (3494091072345/18014398509481984)), (35231/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484823921853069/9007199254740992), (4354859393455/4503599627370496)), (11027/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219099179263007/4503599627370496), (8671563845709/2251799813685248)), (88425/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202876969453939/2251799813685248), (25824673753343/2251799813685248)), (133165/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077233045640755/1125899906842624), (12723450731585/562949953421312)), (8389/70368744177664), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077233045640755/1125899906842624), (12723450731585/562949953421312)), (32001495629763581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1030094667188291/1125899906842624), (48693925629967/1125899906842624)), (1027/4398046511104), by norm_num⟩
  | 2 => ⟨((940335742584341/1125899906842624), (178201819934615/2251799813685248)), (251911/562949953421312), by norm_num⟩
  | 3 => ⟨((1556607885477209/2251799813685248), (37207912457337/281474976710656)), (921313/1125899906842624), by norm_num⟩
  | 4 => ⟨((518346403392239/1125899906842624), (102883266232177/562949953421312)), (3034665/2251799813685248), by norm_num⟩
  | 5 => ⟨((25129135220155/140737488355328), (189463275364315/1125899906842624)), (7806877/4503599627370496), by norm_num⟩
  | 6 => ⟨((64204176206987/18014398509481984), (135317130397065/2251799813685248)), (10830651/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-6645079997/67108864)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-763070545/268435456), (-26888214485/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((245180462439023/4503599627370496), (46782675346391/2251799813685248)), (2827719/4503599627370496), by norm_num⟩
  | 1 => ⟨((-24660486051/137438953472), (-4705446353/68719476736)), (287/137438953472), by norm_num⟩
  | 2 => ⟨((20319234765/68719476736), (7754191781/68719476736)), (239/68719476736), by norm_num⟩
  | 3 => ⟨((-22322961009/68719476736), (-8518850379/68719476736)), (265/68719476736), by norm_num⟩
  | 4 => ⟨((18393209463/68719476736), (1754796321/17179869184)), (55/17179869184), by norm_num⟩
  | 5 => ⟨((-24248407133/137438953472), (-9253635851/137438953472)), (73/34359738368), by norm_num⟩
  | 6 => ⟨((13319799029/137438953472), (2541539515/68719476736)), (81/68719476736), by norm_num⟩
  | 7 => ⟨((-3135706049/68719476736), (-4786571217/274877906944)), (77/137438953472), by norm_num⟩
  | 8 => ⟨((20669551195/1099511627776), (7887878939/1099511627776)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-15138548629/2199023255552), (-1444286789/549755813888)), (189/2199023255552), by norm_num⟩
  | 10 => ⟨((4989418667/2199023255552), (7616213831/8796093022208)), (251/8796093022208), by norm_num⟩
  | 11 => ⟨((-11959498169/17592186044416), (-9127926663/35184372088832)), (303/35184372088832), by norm_num⟩
  | 12 => ⟨((13138851655/70368744177664), (5014026201/70368744177664)), (21/8796093022208), by norm_num⟩
  | 13 => ⟨((-6662078717/140737488355328), (-5084742277/281474976710656)), (43/70368744177664), by norm_num⟩
  | 14 => ⟨((6273464183/562949953421312), (4788137443/1125899906842624)), (41/281474976710656), by norm_num⟩
  | 15 => ⟨((-22054735501/9007199254740992), (-1052061327/1125899906842624)), (291/9007199254740992), by norm_num⟩
  | 16 => ⟨((2271525323/4503599627370496), (3467422507/18014398509481984)), (121/18014398509481984), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (237440280237/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777585676923371/633825300114114700748351602688), (35080255997/39614081257132168796771975168)), (11533/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944205597588855/19807040628566084398385987584), (631290740967/39614081257132168796771975168)), (12975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888103514795283/2475880078570760549798248448), (167638013559/618970019642690137449562112)), (6893/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110610639238537/9671406556917033397649408), (167583381087/38685626227668133590597632)), (6893/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774111118402447/4835703278458516698824704), (314102795659/4835703278458516698824704)), (6463/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257624385673293/604462909807314587353088), (549447917497/604462909807314587353088)), (11311/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885900982917113/75557863725914323419136), (55776134541/4722366482869645213696)), (4595/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296121962758271/4722366482869645213696), (668933479893/4722366482869645213696)), (13787/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619500373467087/590295810358705651712), (919166264897/590295810358705651712)), (9479/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28453779720245/1152921504606846976), (287008177719/18446744073709551616)), (5925/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819922766673829/9223372036854775808), (161283254161/1152921504606846976)), (13333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795587306064553/576460752303423488), (322169870979/288230376151711744)), (13335/576460752303423488), by norm_num⟩
  | 5 => ⟨((596062335952901/72057594037927936), (1125812301341/144115188075855872)), (23341/144115188075855872), by norm_num⟩
  | 4 => ⟨((743980377914829/18014398509481984), (842580249897/18014398509481984)), (17511/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484674954615113/9007199254740992), (1050119449543/4503599627370496)), (21897/4503599627370496), by norm_num⟩
  | 2 => ⟨((554705440279583/1125899906842624), (2090950620511/2251799813685248)), (10955/562949953421312), by norm_num⟩
  | 1 => ⟨((2202511697544895/2251799813685248), (3113307497885/1125899906842624)), (131593/2251799813685248), by norm_num⟩
  | 0 => ⟨((538484092742969/562949953421312), (6134752284305/1125899906842624)), (263727/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538484092742969/562949953421312), (6134752284305/1125899906842624)), (1006038674361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1030129614821437/1125899906842624), (5868135343009/562949953421312)), (253703/1125899906842624), by norm_num⟩
  | 2 => ⟨((942383312081449/1125899906842624), (42951882055419/2251799813685248)), (469535/1125899906842624), by norm_num⟩
  | 3 => ⟨((197092362618573/281474976710656), (17975459730265/562949953421312)), (1607837/2251799813685248), by norm_num⟩
  | 4 => ⟨((1101756769072679/2251799813685248), (100693166228693/2251799813685248)), (73573/70368744177664), by norm_num⟩
  | 5 => ⟨((534563000297221/2251799813685248), (98533960983203/2251799813685248)), (314301/281474976710656), by norm_num⟩
  | 6 => ⟨((245180462439023/4503599627370496), (46782675346391/2251799813685248)), (2827719/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-26888214485/268435456)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile055Terms3
