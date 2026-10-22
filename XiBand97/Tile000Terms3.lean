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
namespace Reinmann.XiBand97.Tile000Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (18227/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (18227/1280))
  have he : value ((69/80), (18227/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-1476930589/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((625898728130303/9007199254740992), (-10539236524073/4503599627370496)), (80488777/18014398509481984), by norm_num⟩
  | 1 => ⟨((-461263547/2147483648), (31068065/4294967296)), (121/8589934592), by norm_num⟩
  | 2 => ⟨((712892603/2147483648), (-24008177/2147483648)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-183631775/536870912), (24736765/2147483648)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((1135227225/4294967296), (-38231195/4294967296)), (79/4294967296), by norm_num⟩
  | 5 => ⟨((-1403614219/8589934592), (47269699/8589934592)), (25/2147483648), by norm_num⟩
  | 6 => ⟨((361552595/4294967296), (-48704215/17179869184)), (105/17179869184), by norm_num⟩
  | 7 => ⟨((-1277227909/34359738368), (21506685/17179869184)), (47/17179869184), by norm_num⟩
  | 8 => ⟨((1973982845/137438953472), (-16619519/34359738368)), (37/34359738368), by norm_num⟩
  | 9 => ⟨((-677962753/137438953472), (45663679/274877906944)), (103/274877906944), by norm_num⟩
  | 10 => ⟨((1676489321/1099511627776), (-14114837/274877906944)), (129/1099511627776), by norm_num⟩
  | 11 => ⟨((-942199939/2199023255552), (63461179/4398046511104)), (147/4398046511104), by norm_num⟩
  | 12 => ⟨((970793337/8796093022208), (-32693533/8796093022208)), (153/17592186044416), by norm_num⟩
  | 13 => ⟨((-923311821/35184372088832), (7773623/8796093022208)), (37/17592186044416), by norm_num⟩
  | 14 => ⟨((815427439/140737488355328), (-54922511/281474976710656)), (133/281474976710656), by norm_num⟩
  | 15 => ⟨((-1344277777/1125899906842624), (45271417/1125899906842624)), (111/1125899906842624), by norm_num⟩
  | 16 => ⟨((1038804919/4503599627370496), (-1093249/140737488355328)), (87/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-21925824625/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777857835140089/633825300114114700748351602688), (-25922747255/316912650057057350374175801344)), (46103/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472179327471583/9903520314283042199192993792), (-58312801825/39614081257132168796771975168)), (25933/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118026792667995/154742504910672534362390528), (-61940513271/2475880078570760549798248448)), (13777/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442523826722123/38685626227668133590597632), (-61921579649/154742504910672534362390528)), (13777/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774263452047949/4835703278458516698824704), (-29015686069/4835703278458516698824704)), (3229/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1257890875251299/604462909807314587353088), (-50757351059/604462909807314587353088)), (90413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235791731468127/9444732965739290427392), (-82443028377/75557863725914323419136)), (146921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81027903738377/295147905179352825856), (-61799332147/4722366482869645213696)), (6887/295147905179352825856), by norm_num⟩
  | 9 => ⟨((404986576474669/147573952589676412928), (-84920592277/590295810358705651712)), (151515/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821598941364425/73786976294838206464), (-106070570335/73786976294838206464)), (47349/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113784307431255/576460752303423488), (-7451203873/576460752303423488)), (106537/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795900059398859/576460752303423488), (-119081755887/1152921504606846976)), (106539/576460752303423488), by norm_num⟩
  | 5 => ⟨((596335632427765/72057594037927936), (-104042056283/144115188075855872)), (11653/9007199254740992), by norm_num⟩
  | 4 => ⟨((372194799162137/9007199254740992), (-155754658933/36028797018963968)), (139841/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485695475442449/9007199254740992), (-24269347501/1125899906842624)), (87405/2251799813685248), by norm_num⟩
  | 2 => ⟨((277606903950283/562949953421312), (-386698721767/4503599627370496)), (699297/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205543043142347/2251799813685248), (-576037711771/2251799813685248)), (131137/281474976710656), by norm_num⟩
  | 0 => ⟨((1079962013563463/1125899906842624), (-1136133891293/2251799813685248)), (2098863/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079962013563463/1125899906842624), (-1136133891293/2251799813685248)), (8006526955611418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035898147740961/1125899906842624), (-1089778440749/1125899906842624)), (4028573/2251799813685248), by norm_num⟩
  | 2 => ⟨((953089860257087/1125899906842624), (-250666036421/140737488355328)), (7420877/2251799813685248), by norm_num⟩
  | 3 => ⟨((1613600382880729/2251799813685248), (-6790152656995/2251799813685248)), (6295093/1125899906842624), by norm_num⟩
  | 4 => ⟨((1156257351846315/2251799813685248), (-4865704695665/1125899906842624)), (18119745/2251799813685248), by norm_num⟩
  | 5 => ⟨((593674604307775/2251799813685248), (-19987591408735/4503599627370496)), (9382459/1125899906842624), by norm_num⟩
  | 6 => ⟨((625898728130303/9007199254740992), (-10539236524073/4503599627370496)), (80488777/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-1476930589/33554432)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-46817815/1048576)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((236829209839789/4503599627370496), (-745364823131895/18014398509481984)), (128656489/18014398509481984), by norm_num⟩
  | 1 => ⟨((-88522031/536870912), (69650623/536870912)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1110241265/4294967296), (-436778251/2147483648)), (39/1073741824), by norm_num⟩
  | 3 => ⟨((-1160385021/4294967296), (913010453/4294967296)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((454797565/2147483648), (-178921187/1073741824)), (33/1073741824), by norm_num⟩
  | 5 => ⟨((-1140812107/8589934592), (897610155/8589934592)), (21/1073741824), by norm_num⟩
  | 6 => ⟨((1192336587/17179869184), (-938150483/17179869184)), (89/8589934592), by norm_num⟩
  | 7 => ⟨((-534080639/17179869184), (840447261/34359738368)), (81/17179869184), by norm_num⟩
  | 8 => ⟨((837303377/68719476736), (-658804381/68719476736)), (129/68719476736), by norm_num⟩
  | 9 => ⟨((-291706655/68719476736), (918078811/274877906944)), (91/137438953472), by norm_num⟩
  | 10 => ⟨((731715623/549755813888), (-35982885/34359738368)), (29/137438953472), by norm_num⟩
  | 11 => ⟨((-417143655/1099511627776), (656431289/2199023255552)), (67/1099511627776), by norm_num⟩
  | 12 => ⟨((435983839/4398046511104), (-171519709/2199023255552)), (71/4398046511104), by norm_num⟩
  | 13 => ⟨((-420623017/17592186044416), (330953265/17592186044416)), (139/35184372088832), by norm_num⟩
  | 14 => ⟨((376817439/70368744177664), (-592972599/140737488355328)), (63/70368744177664), by norm_num⟩
  | 15 => ⟨((-19691815/17592186044416), (495803241/562949953421312)), (107/562949953421312), by norm_num⟩
  | 16 => ⟨((15435893/70368744177664), (-777294097/4503599627370496)), (85/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-868386793489/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798227428901/633825300114114700748351602688), (-256655633137/158456325028528675187087900672)), (46151/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888650235775117/39614081257132168796771975168), (-577340738715/19807040628566084398385987584)), (51923/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944178697221039/1237940039285380274899124224), (-1226510809541/2475880078570760549798248448)), (13793/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442505998483777/38685626227668133590597632), (-1226130462389/154742504910672534362390528)), (6897/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774230010990847/4835703278458516698824704), (-143636669155/1208925819614629174706176)), (12933/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628916163608149/302231454903657293676544), (-1005052912975/604462909807314587353088)), (90541/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886238662166141/75557863725914323419136), (-1632454303843/75557863725914323419136)), (147145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162046878101321/590295810358705651712), (-1223679023965/4722366482869645213696)), (55187/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809924006663943/295147905179352825856), (-840742060725/295147905179352825856)), (37947/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821475971734687/73786976294838206464), (-2100244627707/73786976294838206464)), (189771/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820410435579769/9223372036854775808), (-2360562814727/9223372036854775808)), (106771/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591661457964765/1152921504606846976), (-73681263781/36028797018963968)), (213605/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298137434435665/36028797018963968), (-2059971994075/144115188075855872)), (5843/4503599627370496), by norm_num⟩
  | 4 => ⟨((1488596510250253/36028797018963968), (-3083761888443/36028797018963968)), (280605/36028797018963968), by norm_num⟩
  | 3 => ⟨((742733214746351/4503599627370496), (-1921941584877/4503599627370496)), (87751/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220395094072313/4503599627370496), (-7655404507039/4503599627370496)), (87845/562949953421312), by norm_num⟩
  | 1 => ⟨((1102423893122179/1125899906842624), (-11402536301243/2251799813685248)), (528013/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079256844623435/1125899906842624), (-5621196943605/562949953421312)), (529917/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079256844623435/1125899906842624), (-5621196943605/562949953421312)), (2021472933055686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2068867646525195/2251799813685248), (-43106604695439/2251799813685248)), (1026511/562949953421312), by norm_num⟩
  | 2 => ⟨((949985681113559/1125899906842624), (-39604701654181/1125899906842624)), (7702159/2251799813685248), by norm_num⟩
  | 3 => ⟨((800163723660031/1125899906842624), (-33416735579769/562949953421312)), (6769681/1125899906842624), by norm_num⟩
  | 4 => ⟨((70587454969379/140737488355328), (-189991024328653/2251799813685248)), (5212981/562949953421312), by norm_num⟩
  | 5 => ⟨((1100849316799569/4503599627370496), (-190581529215947/2251799813685248)), (24435411/2251799813685248), by norm_num⟩
  | 6 => ⟨((236829209839789/4503599627370496), (-745364823131895/18014398509481984)), (128656489/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-46817815/1048576)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-1518505483/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1333101563789/70368744177664), (-555351387357249/9007199254740992)), (85076899/9007199254740992), by norm_num⟩
  | 1 => ⟨((-129292863/2147483648), (420793677/2147483648)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((205449839/2147483648), (-1337304957/4294967296)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-217643549/2147483648), (1416675713/4294967296)), (225/4294967296), by norm_num⟩
  | 4 => ⟨((345841457/4294967296), (-1125567919/4294967296)), (181/4294967296), by norm_num⟩
  | 5 => ⟨((-439641107/8589934592), (715423087/4294967296)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((14554199/536870912), (-1515768721/17179869184)), (31/2147483648), by norm_num⟩
  | 7 => ⟨((-422893969/34359738368), (1376341311/34359738368)), (227/34359738368), by norm_num⟩
  | 8 => ⟨((335994949/68719476736), (-546760847/34359738368)), (91/34359738368), by norm_num⟩
  | 9 => ⟨((-237291119/137438953472), (1544564803/274877906944)), (65/68719476736), by norm_num⟩
  | 10 => ⟨((75412395/137438953472), (-490871009/274877906944)), (167/549755813888), by norm_num⟩
  | 11 => ⟨((-43575391/274877906944), (1134555993/2199023255552)), (195/2199023255552), by norm_num⟩
  | 12 => ⟨((369293169/8796093022208), (-300473335/2199023255552)), (209/8796093022208), by norm_num⟩
  | 13 => ⟨((-180559011/17592186044416), (1175286687/35184372088832)), (103/17592186044416), by norm_num⟩
  | 14 => ⟨((163950359/70368744177664), (-266794597/35184372088832)), (189/140737488355328), by norm_num⟩
  | 15 => ⟨((-277889635/562949953421312), (452206715/281474976710656)), (81/281474976710656), by norm_num⟩
  | 16 => ⟨((441574109/4503599627370496), (-718568641/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (-1657824470963/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777740205288641/633825300114114700748351602688), (-1959791138765/633825300114114700748351602688)), (46197/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472146223592091/9903520314283042199192993792), (-137765212089/2475880078570760549798248448)), (25989/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118017992401725/154742504910672534362390528), (-1170676958819/1237940039285380274899124224)), (110467/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769954375945931/154742504910672534362390528), (-2340617745967/154742504910672534362390528)), (110483/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774197323434851/4835703278458516698824704), (-2193547258763/9671406556917033397649408)), (103595/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257775015859915/604462909807314587353088), (-479643078947/151115727451828646838272)), (90663/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886145328703425/75557863725914323419136), (-779053840303/18889465931478580854784)), (147359/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296304847759799/4722366482869645213696), (-2335880677433/4722366482869645213696)), (27637/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101234452049075/36893488147419103232), (-401219490385/73786976294838206464)), (152049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455338641549861/18446744073709551616), (-4009077273571/73786976294838206464)), (190131/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820273264581253/9223372036854775808), (-4505929059301/9223372036854775808)), (26749/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591523551671689/1152921504606846976), (-281286329021/72057594037927936)), (214111/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192428245164281/144115188075855872), (-1966000149455/72057594037927936)), (187481/144115188075855872), by norm_num⟩
  | 4 => ⟨((744206314404859/18014398509481984), (-2943001856137/18014398509481984)), (140745/18014398509481984), by norm_num⟩
  | 3 => ⟨((742616858966085/4503599627370496), (-7336555007247/9007199254740992)), (352333/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109960575217451/2251799813685248), (-14610439376157/4503599627370496)), (353041/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204115774235155/2251799813685248), (-21759604767695/2251799813685248)), (1062677/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156966500001547/2251799813685248), (-42898713261341/2251799813685248)), (2139655/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156966500001547/2251799813685248), (-42898713261341/2251799813685248)), (8162136086470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065309782097489/2251799813685248), (-82184114978187/2251799813685248)), (4180615/2251799813685248), by norm_num⟩
  | 2 => ⟨((945632520570967/1125899906842624), (-37688886810877/562949953421312)), (7973929/2251799813685248), by norm_num⟩
  | 3 => ⟨((1578362427788043/2251799813685248), (-126618136535525/1125899906842624)), (7231073/1125899906842624), by norm_num⟩
  | 4 => ⟨((1077848629662115/2251799813685248), (-355003687574057/2251799813685248)), (2940853/281474976710656), by norm_num⟩
  | 5 => ⟨((919913079287689/4503599627370496), (-679705604114913/4503599627370496)), (59881815/4503599627370496), by norm_num⟩
  | 6 => ⟨((1333101563789/70368744177664), (-555351387357249/9007199254740992)), (85076899/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1518505483/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-384502659/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-313445442468413/18014398509481984), (-269267234743733/4503599627370496)), (97829607/9007199254740992), by norm_num⟩
  | 1 => ⟨((60137627/1073741824), (206646393/1073741824)), (303/8589934592), by norm_num⟩
  | 2 => ⟨((-387151107/4294967296), (-665169079/2147483648)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((415397113/4294967296), (1427397779/4294967296)), (133/2147483648), by norm_num⟩
  | 4 => ⟨((-334277931/4294967296), (-1148654051/4294967296)), (27/536870912), by norm_num⟩
  | 5 => ⟨((107599915/2147483648), (1478949903/8589934592)), (281/8589934592), by norm_num⟩
  | 6 => ⟨((-115450255/4294967296), (-793426015/8589934592)), (19/1073741824), by norm_num⟩
  | 7 => ⟨((424708611/34359738368), (729697091/17179869184)), (141/17179869184), by norm_num⟩
  | 8 => ⟨((-170885535/34359738368), (-1174402163/68719476736)), (229/68719476736), by norm_num⟩
  | 9 => ⟨((30558851/17179869184), (840056607/137438953472)), (165/137438953472), by norm_num⟩
  | 10 => ⟨((-157384235/274877906944), (-540807581/274877906944)), (215/549755813888), by norm_num⟩
  | 11 => ⟨((368436589/2199023255552), (158253859/274877906944)), (127/1099511627776), by norm_num⟩
  | 12 => ⟨((-197658605/4398046511104), (-1358398723/8796093022208)), (275/8796093022208), by norm_num⟩
  | 13 => ⟨((97882847/8796093022208), (336347447/8796093022208)), (137/17592186044416), by norm_num⟩
  | 14 => ⟨((-22505195/8796093022208), (-309331619/35184372088832)), (127/70368744177664), by norm_num⟩
  | 15 => ⟨((309083427/562949953421312), (1062080075/562949953421312)), (55/140737488355328), by norm_num⟩
  | 16 => ⟨((-248725293/2251799813685248), (-427337985/1125899906842624)), (179/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-301878891971/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777683677303909/633825300114114700748351602688), (-713688538541/158456325028528675187087900672)), (46241/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59016287167063/1237940039285380274899124224), (-802706326409/9903520314283042199192993792)), (104061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472055010186709/618970019642690137449562112), (-426316941223/309485009821345068724781056)), (110585/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884943184254425/77371252455336267181195264), (-3409448831959/154742504910672534362390528)), (6913/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548330709696171/9671406556917033397649408), (-3195204081577/9671406556917033397649408)), (103721/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628859445408699/302231454903657293676544), (-2794649843241/604462909807314587353088)), (90781/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886053788374017/75557863725914323419136), (-2269571876955/37778931862957161709568)), (147565/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296235897913065/4722366482869645213696), (-3402466852733/4722366482869645213696)), (27679/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619655948758969/590295810358705651712), (-1168830244851/147573952589676412928)), (38075/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821234745475361/73786976294838206464), (-5839548082571/73786976294838206464)), (190475/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820137484283269/9223372036854775808), (-3281583794173/4611686018427387904)), (214423/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591386547027869/1152921504606846976), (-819408818721/144115188075855872)), (53649/288230376151711744), by norm_num⟩
  | 5 => ⟨((596153496506247/72057594037927936), (-178968390875/4503599627370496)), (93983/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488228015133321/36028797018963968), (-4286381825523/18014398509481984)), (70585/9007199254740992), by norm_num⟩
  | 3 => ⟨((185624773484453/1125899906842624), (-5342503773037/4503599627370496)), (353609/9007199254740992), by norm_num⟩
  | 2 => ⟨((554858974353801/1125899906842624), (-10638709678379/2251799813685248)), (354637/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203352746919337/2251799813685248), (-15842748282249/1125899906842624)), (66817/140737488355328), by norm_num⟩
  | 0 => ⟨((2155301849641045/2251799813685248), (-31226795254621/1125899906842624)), (2158887/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155301849641045/2251799813685248), (-31226795254621/1125899906842624)), (8235500344283293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2061207032654717/2251799813685248), (-119554445580133/2251799813685248)), (265781/140737488355328), by norm_num⟩
  | 2 => ⟨((470099644323795/562949953421312), (-218870667381049/2251799813685248)), (8236683/2251799813685248), by norm_num⟩
  | 3 => ⟨((1548980695022589/2251799813685248), (-91385586110653/562949953421312)), (3839377/562949953421312), by norm_num⟩
  | 4 => ⟨((503090899600003/1125899906842624), (-502902639314321/2251799813685248)), (6528623/562949953421312), by norm_num⟩
  | 5 => ⟨((674563292701481/4503599627370496), (-898856957661059/4503599627370496)), (70004401/4503599627370496), by norm_num⟩
  | 6 => ⟨((-313445442468413/18014398509481984), (-269267234743733/4503599627370496)), (97829607/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-384502659/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-94291587/33554432), (-194593835/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-808743936795265/18014398509481984), (-90306928418353/2251799813685248)), (199611205/18014398509481984), by norm_num⟩
  | 1 => ⟨((628224807/4294967296), (561196691/4294967296)), (157/4294967296), by norm_num⟩
  | 2 => ⟨((-1023408535/4294967296), (-457108249/2147483648)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((555727301/2147483648), (124108567/536870912)), (141/2147483648), by norm_num⟩
  | 4 => ⟨((-452653299/2147483648), (-808715385/4294967296)), (231/4294967296), by norm_num⟩
  | 5 => ⟨((589915259/4294967296), (526974559/4294967296)), (19/536870912), by norm_num⟩
  | 6 => ⟨((-320333477/4294967296), (-572311329/8589934592)), (167/8589934592), by norm_num⟩
  | 7 => ⟨((596387081/17179869184), (266377937/8589934592)), (157/17179869184), by norm_num⟩
  | 8 => ⟨((-485771671/34359738368), (-433942517/34359738368)), (129/34359738368), by norm_num⟩
  | 9 => ⟨((351709111/68719476736), (628367383/137438953472)), (189/137438953472), by norm_num⟩
  | 10 => ⟨((-458360895/274877906944), (-409456319/274877906944)), (31/68719476736), by norm_num⟩
  | 11 => ⟨((67881093/137438953472), (242554221/549755813888)), (37/274877906944), by norm_num⟩
  | 12 => ⟨((-589768411/4398046511104), (-526843379/4398046511104)), (81/2199023255552), by norm_num⟩
  | 13 => ⟨((591237667/17592186044416), (264077937/8796093022208)), (41/4398046511104), by norm_num⟩
  | 14 => ⟨((-550374113/70368744177664), (-983304471/140737488355328)), (77/35184372088832), by norm_num⟩
  | 15 => ⟨((239089599/140737488355328), (427160119/281474976710656)), (269/562949953421312), by norm_num⟩
  | 16 => ⟨((-778976995/2251799813685248), (-695864453/2251799813685248)), (221/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (-3142535617047/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444407139968161/158456325028528675187087900672), (-1857256630689/316912650057057350374175801344)), (92567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472114758054663/9903520314283042199192993792), (-4177802988227/39614081257132168796771975168)), (104161/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888153794612685/2475880078570760549798248448), (-277352637011/154742504910672534362390528)), (55349/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884909946480205/77371252455336267181195264), (-1109052501533/38685626227668133590597632)), (110729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548268145340399/9671406556917033397649408), (-2078712839299/4835703278458516698824704)), (103841/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628831951864305/302231454903657293676544), (-3636226823665/604462909807314587353088)), (90893/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885963978743757/75557863725914323419136), (-1476504640589/18889465931478580854784)), (147763/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296168142564645/4722366482869645213696), (-4427021332137/4722366482869645213696)), (27719/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619562139200695/590295810358705651712), (-6083106091473/590295810358705651712)), (152541/590295810358705651712), by norm_num⟩
  | 8 => ⟨((7113736391971/288230376151711744), (-3798907067123/36893488147419103232)), (190807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820003149472233/9223372036854775808), (-8539203044093/9223372036854775808)), (107419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591250557668653/1152921504606846976), (-8528790173913/1152921504606846976)), (215063/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298046536697773/36028797018963968), (-7450989912131/144115188075855872)), (188433/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488043049294347/36028797018963968), (-11153114341755/36028797018963968)), (141579/18014398509481984), by norm_num⟩
  | 3 => ⟨((185595068045439/1125899906842624), (-13900567475289/9007199254740992)), (88709/2251799813685248), by norm_num⟩
  | 2 => ⟨((554735358011107/1125899906842624), (-27678950214989/4503599627370496)), (178087/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202563557223723/2251799813685248), (-41213982992361/2251799813685248)), (537615/1125899906842624), by norm_num⟩
  | 0 => ⟨((269192026834979/281474976710656), (-81216304388879/2251799813685248)), (2177423/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269192026834979/281474976710656), (-81216304388879/2251799813685248)), (8306209572798918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514157842950053/562949953421312), (-38836101606579/562949953421312)), (4321879/2251799813685248), by norm_num⟩
  | 2 => ⟨((933830949204601/1125899906842624), (-283760730193133/2251799813685248)), (8490891/2251799813685248), by norm_num⟩
  | 3 => ⟨((756648258441955/1125899906842624), (-470707121321901/2251799813685248)), (4056199/562949953421312), by norm_num⟩
  | 4 => ⟨((28706220094735/70368744177664), (-632666760908127/2251799813685248)), (1786907/140737488355328), by norm_num⟩
  | 5 => ⟨((393957729994237/4503599627370496), (-129045014924513/562949953421312)), (78784063/4503599627370496), by norm_num⟩
  | 6 => ⟨((-808743936795265/18014398509481984), (-90306928418353/2251799813685248)), (199611205/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-194593835/4194304)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-393695845/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1030481659732105/18014398509481984), (-199986252924163/18014398509481984)), (180957159/18014398509481984), by norm_num⟩
  | 1 => ⟨((1619481775/8589934592), (78573473/2147483648)), (287/8589934592), by norm_num⟩
  | 2 => ⟨((-667193467/2147483648), (-258965349/4294967296)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((1465973883/4294967296), (284502515/4294967296)), (33/536870912), by norm_num⟩
  | 4 => ⟨((-301975673/1073741824), (-234418469/4294967296)), (219/4294967296), by norm_num⟩
  | 5 => ⟨((1592420089/8589934592), (309042013/8589934592)), (291/8589934592), by norm_num⟩
  | 6 => ⟨((-874726139/8589934592), (-339517353/17179869184)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((1647402661/34359738368), (319712517/34359738368)), (305/34359738368), by norm_num⟩
  | 8 => ⟨((-678696303/34359738368), (-263430075/68719476736)), (253/68719476736), by norm_num⟩
  | 9 => ⟨((994165465/137438953472), (192938345/137438953472)), (187/137438953472), by norm_num⟩
  | 10 => ⟨((-327660719/137438953472), (-63589331/137438953472)), (31/68719476736), by norm_num⟩
  | 11 => ⟨((98174207/137438953472), (152421863/1099511627776)), (299/2199023255552), by norm_num⟩
  | 12 => ⟨((-431421561/2199023255552), (-334905063/8796093022208)), (331/8796093022208), by norm_num⟩
  | 13 => ⟨((1750024721/35184372088832), (339628447/35184372088832)), (169/17592186044416), by norm_num⟩
  | 14 => ⟨((-102996357/8796093022208), (-159908565/70368744177664)), (5/2199023255552), by norm_num⟩
  | 15 => ⟨((1448359213/562949953421312), (281084023/562949953421312)), (283/562949953421312), by norm_num⟩
  | 16 => ⟨((-596694461/1125899906842624), (-231601771/2251799813685248)), (235/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-3842580401337/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888787388208759/316912650057057350374175801344), (-4541729955313/633825300114114700748351602688)), (11581/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888398341607237/39614081257132168796771975168), (-1277042438979/9903520314283042199192993792)), (52129/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944044529894853/1237940039285380274899124224), (-5425854106511/2475880078570760549798248448)), (110807/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442438719014973/38685626227668133590597632), (-1356020308781/38685626227668133590597632)), (110845/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387051723141651/2417851639229258349412352), (-5083193011861/9671406556917033397649408)), (103957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257610008434461/604462909807314587353088), (-4445911334329/604462909807314587353088)), (45501/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885875838709843/75557863725914323419136), (-451317337473/4722366482869645213696)), (147953/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324025387011005/1180591620717411303424), (-2706360930191/2361183241434822606848)), (111031/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404867444386871/147573952589676412928), (-464842491981/36893488147419103232)), (76387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820999875169075/73786976294838206464), (-4644667480103/36893488147419103232)), (95563/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909935148325339/4611686018427387904), (-5220087807783/4611686018427387904)), (215237/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591115670755139/1152921504606846976), (-10427277965147/1152921504606846976)), (26939/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192065839640119/144115188075855872), (-284667883647/4503599627370496)), (188883/144115188075855872), by norm_num⟩
  | 4 => ⟨((743929022230779/18014398509481984), (-6817550659759/18014398509481984)), (283945/36028797018963968), by norm_num⟩
  | 3 => ⟨((92782586047823/562949953421312), (-8496640011969/4503599627370496)), (356019/9007199254740992), by norm_num⟩
  | 2 => ⟨((554609881060875/1125899906842624), (-16917541703371/2251799813685248)), (357655/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100876164619503/1125899906842624), (-25187515063105/1125899906842624)), (540585/1125899906842624), by norm_num⟩
  | 0 => ⟨((537920917218673/562949953421312), (-49623131138407/1125899906842624)), (2195313/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((537920917218673/562949953421312), (-49623131138407/1125899906842624)), (8374454506880950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2051644538847935/2251799813685248), (-189667447736741/2251799813685248)), (4388931/2251799813685248), by norm_num⟩
  | 2 => ⟨((1853304875367095/2251799813685248), (-172808515651073/1125899906842624)), (2184245/562949953421312), by norm_num⟩
  | 3 => ⟨((368070888071929/562949953421312), (-142227058824089/562949953421312)), (17063629/2251799813685248), by norm_num⟩
  | 4 => ⟨((204720937774119/562949953421312), (-92991640786339/281474976710656)), (30935379/2251799813685248), by norm_num⟩
  | 5 => ⟨((52017990544845/2251799813685248), (-33817101842241/140737488355328)), (21470085/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1030481659732105/18014398509481984), (-199986252924163/18014398509481984)), (180957159/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-393695845/8388608)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile000Terms3
