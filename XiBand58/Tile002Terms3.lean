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
namespace Reinmann.XiBand58.Tile002Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2403/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2403/160))
  have he : value ((15/16), (2403/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-1557717323/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-759559926043497/18014398509481984), (-320076436188037/9007199254740992)), (183018093/18014398509481984), by norm_num⟩
  | 1 => ⟨((139941691/1073741824), (471768309/4294967296)), (17/536870912), by norm_num⟩
  | 2 => ⟨((-108141427/536870912), (-712039/4194304)), (53/1073741824), by norm_num⟩
  | 3 => ⟨((445692989/2147483648), (751255135/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-688827975/4294967296), (-580540379/4294967296)), (171/4294967296), by norm_num⟩
  | 5 => ⟨((425839303/4294967296), (717789983/8589934592)), (213/8589934592), by norm_num⟩
  | 6 => ⟨((-877524909/17179869184), (-739573103/17179869184)), (111/8589934592), by norm_num⟩
  | 7 => ⟨((774990499/34359738368), (326578837/17179869184)), (99/17179869184), by norm_num⟩
  | 8 => ⟨((-598882133/68719476736), (-504734525/68719476736)), (155/68719476736), by norm_num⟩
  | 9 => ⟨((411371133/137438953472), (346701299/137438953472)), (215/274877906944), by norm_num⟩
  | 10 => ⟨((-1017252509/1099511627776), (-857334747/1099511627776)), (67/274877906944), by norm_num⟩
  | 11 => ⟨((285851881/1099511627776), (963657491/4398046511104)), (303/4398046511104), by norm_num⟩
  | 12 => ⟨((-589053533/8796093022208), (-124112759/2199023255552)), (157/8796093022208), by norm_num⟩
  | 13 => ⟨((1120485833/70368744177664), (944339217/70368744177664)), (301/70368744177664), by norm_num⟩
  | 14 => ⟨((-989562651/281474976710656), (-833997889/281474976710656)), (67/70368744177664), by norm_num⟩
  | 15 => ⟨((815674711/1125899906842624), (343723051/562949953421312)), (223/1125899906842624), by norm_num⟩
  | 16 => ⟨((-315160645/2251799813685248), (-531231271/4503599627370496)), (87/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (-397507690279/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777493292141733/633825300114114700748351602688), (-3758324329913/633825300114114700748351602688)), (92571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944153442736573/19807040628566084398385987584), (-1056762069637/9903520314283042199192993792)), (104167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887992172855263/2475880078570760549798248448), (-4489910160185/2475880078570760549798248448)), (6919/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769658309655339/154742504910672534362390528), (-1122103994689/38685626227668133590597632)), (110735/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548116701853965/9671406556917033397649408), (-1051575737937/2417851639229258349412352)), (103847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628765715773691/302231454903657293676544), (-3678928660867/604462909807314587353088)), (22725/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885748788094909/75557863725914323419136), (-1493821455295/18889465931478580854784)), (147773/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296006816658399/4722366482869645213696), (-1119716014443/1180591620717411303424)), (27721/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619340425114063/590295810358705651712), (-769276874137/73786976294838206464)), (152553/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820839537338121/73786976294838206464), (-960804791943/9223372036854775808)), (23853/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1819691773123441/9223372036854775808), (-1079818210039/1152921504606846976)), (214859/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99433716420761/72057594037927936), (-16850945621/2251799813685248)), (215087/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595957127737323/72057594037927936), (-3768509281039/72057594037927936)), (94229/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487635846231307/36028797018963968), (-11281153009455/36028797018963968)), (4425/562949953421312), by norm_num⟩
  | 3 => ⟨((371063162695061/2251799813685248), (-878679044199/562949953421312)), (354901/9007199254740992), by norm_num⟩
  | 2 => ⟨((138620561197021/281474976710656), (-3498789631755/562949953421312)), (712511/4503599627370496), by norm_num⟩
  | 1 => ⟨((550263306418117/562949953421312), (-41668053828347/2251799813685248)), (1075559/2251799813685248), by norm_num⟩
  | 0 => ⟨((2150549013088285/2251799813685248), (-82073064184033/2251799813685248)), (1089213/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2150549013088285/2251799813685248), (-82073064184033/2251799813685248)), (4155017857078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2050859513249765/2251799813685248), (-19595674769735/281474976710656)), (1079937/562949953421312), by norm_num⟩
  | 2 => ⟨((928468269607011/1125899906842624), (-285552744259543/2251799813685248)), (8470011/2251799813685248), by norm_num⟩
  | 3 => ⟨((747551563077041/1125899906842624), (-470959559962465/2251799813685248)), (16117693/2251799813685248), by norm_num⟩
  | 4 => ⟨((447093573433681/1125899906842624), (-625395833246529/2251799813685248)), (28144949/2251799813685248), by norm_num⟩
  | 5 => ⟨((45347137753801/562949953421312), (-993375898505367/4503599627370496)), (75972271/4503599627370496), by norm_num⟩
  | 6 => ⟨((-759559926043497/18014398509481984), (-320076436188037/9007199254740992)), (183018093/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-1557717323/33554432)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-790059297/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-952287073579819/18014398509481984), (-7784399261321/4503599627370496)), (314240655/36028797018963968), by norm_num⟩
  | 1 => ⟨((1423783593/8589934592), (46554449/8589934592)), (237/8589934592), by norm_num⟩
  | 2 => ⟨((-1116066305/4294967296), (-36492801/4294967296)), (187/4294967296), by norm_num⟩
  | 3 => ⟨((291618287/1073741824), (38140989/4294967296)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((-228591863/1073741824), (-59795425/8589934592)), (311/8589934592), by norm_num⟩
  | 5 => ⟨((1146797543/8589934592), (18748821/4294967296)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((-599296177/8589934592), (-39191213/17179869184)), (207/17179869184), by norm_num⟩
  | 7 => ⟨((1073765541/34359738368), (35109663/34359738368)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((-1683392821/137438953472), (-55043073/137438953472)), (295/137438953472), by norm_num⟩
  | 9 => ⟨((1172948545/274877906944), (38352719/274877906944)), (207/274877906944), by norm_num⟩
  | 10 => ⟨((-1471109351/1099511627776), (-48101891/1099511627776)), (131/549755813888), by norm_num⟩
  | 11 => ⟨((104833065/274877906944), (428475/34359738368)), (301/4398046511104), by norm_num⟩
  | 12 => ⟨((-1753085167/17592186044416), (-57321851/17592186044416)), (317/17592186044416), by norm_num⟩
  | 13 => ⟨((422829877/17592186044416), (3456391/4398046511104)), (77/17592186044416), by norm_num⟩
  | 14 => ⟨((-1515177867/281474976710656), (-24771415/140737488355328)), (139/140737488355328), by norm_num⟩
  | 15 => ⟨((1266888383/1125899906842624), (41424335/1125899906842624)), (117/562949953421312), by norm_num⟩
  | 16 => ⟨((-993080299/4503599627370496), (-64942881/9007199254740992)), (369/9007199254740992), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-2024848978161/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222178053166593/79228162514264337593543950336), (-4785765948763/633825300114114700748351602688)), (181/1237940039285380274899124224), by norm_num⟩
  | 16 => ⟨((944114587626449/19807040628566084398385987584), (-2691298165265/19807040628566084398385987584)), (52143/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((943954641868397/1237940039285380274899124224), (-5717290881219/2475880078570760549798248448)), (13855/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769575058748229/154742504910672534362390528), (-714419861603/19342813113834066795298816)), (110879/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193504783762119/1208925819614629174706176), (-1339024202255/2417851639229258349412352)), (103991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257462420143235/604462909807314587353088), (-2342266605695/302231454903657293676544)), (91035/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942817963081345/37778931862957161709568), (-3804260653891/37778931862957161709568)), (74005/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295921542489105/4722366482869645213696), (-5703027860577/4722366482869645213696)), (27769/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202402769341903/73786976294838206464), (-7836200854537/590295810358705651712)), (76421/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820690174653705/73786976294838206464), (-4893530983683/36893488147419103232)), (191221/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819521648306041/9223372036854775808), (-1374899017893/1152921504606846976)), (53839/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795383365089425/576460752303423488), (-10985137597805/1152921504606846976)), (107823/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191760190412651/144115188075855872), (-1199524924139/18014398509481984)), (189017/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487398924500791/36028797018963968), (-14362745486273/36028797018963968)), (284179/36028797018963968), by norm_num⟩
  | 3 => ⟨((11593330939803/70368744177664), (-8949149747091/4503599627370496)), (356371/9007199254740992), by norm_num⟩
  | 2 => ⟨((554321549568969/1125899906842624), (-17815773900775/2251799813685248)), (358097/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100007152278445/1125899906842624), (-13258976248057/562949953421312)), (270735/562949953421312), by norm_num⟩
  | 0 => ⟨((1074088324718203/1125899906842624), (-52216707636157/1125899906842624)), (275083/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1074088324718203/1125899906842624), (-52216707636157/1125899906842624)), (1049358368993663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((255559827686457/281474976710656), (-199255211538301/2251799813685248)), (137591/70368744177664), by norm_num⟩
  | 2 => ⟨((1838613792065069/2251799813685248), (-361819925319343/2251799813685248)), (8774283/2251799813685248), by norm_num⟩
  | 3 => ⟨((1443106531168769/2251799813685248), (-295429061186113/1125899906842624)), (17148265/2251799813685248), by norm_num⟩
  | 4 => ⟨((769803394153323/2251799813685248), (-757324172608409/2251799813685248)), (30978745/2251799813685248), by norm_num⟩
  | 5 => ⟨((8463169379953/2251799813685248), (-2071199100400315/9007199254740992)), (84036771/4503599627370496), by norm_num⟩
  | 6 => ⟨((-952287073579819/18014398509481984), (-7784399261321/4503599627370496)), (314240655/36028797018963968), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-790059297/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-1601566325/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-752238743644027/18014398509481984), (521851291568309/18014398509481984)), (84136899/9007199254740992), by norm_num⟩
  | 1 => ⟨((1139953241/8589934592), (-790820835/8589934592)), (257/8589934592), by norm_num⟩
  | 2 => ⟨((-905708191/4294967296), (157079449/1073741824)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((119932891/536870912), (-665609259/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-762306367/4294967296), (264417757/2147483648)), (11/268435456), by norm_num⟩
  | 5 => ⟨((242265067/2147483648), (-168066773/2147483648)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((-8020119/134217728), (356083501/8589934592)), (241/17179869184), by norm_num⟩
  | 7 => ⟨((932146099/34359738368), (-646658591/34359738368)), (221/34359738368), by norm_num⟩
  | 8 => ⟨((-185150655/17179869184), (513778953/68719476736)), (177/68719476736), by norm_num⟩
  | 9 => ⟨((1046077775/274877906944), (-90712065/34359738368)), (63/68719476736), by norm_num⟩
  | 10 => ⟨((-83112287/68719476736), (461260521/549755813888)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((12006151/34359738368), (-133264615/549755813888)), (189/2199023255552), by norm_num⟩
  | 12 => ⟨((-813998809/8796093022208), (17646755/274877906944)), (101/4398046511104), by norm_num⟩
  | 13 => ⟨((795979087/35184372088832), (-552195321/35184372088832)), (199/35184372088832), by norm_num⟩
  | 14 => ⟨((-722761253/140737488355328), (125350461/35184372088832)), (91/70368744177664), by norm_num⟩
  | 15 => ⟨((612526445/562949953421312), (-424928547/562949953421312)), (311/1125899906842624), by norm_num⟩
  | 16 => ⟨((-973321007/4503599627370496), (337611449/2251799813685248)), (249/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (1651116614515/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444341781685115/158456325028528675187087900672), (3902185635727/633825300114114700748351602688)), (92585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888164954774853/39614081257132168796771975168), (1097205362085/9903520314283042199192993792)), (104183/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((943920686599509/1237940039285380274899124224), (291356527567/154742504910672534362390528)), (110723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769507511989671/154742504910672534362390528), (582513672587/19342813113834066795298816)), (27689/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((386993832799253/2417851639229258349412352), (4367158381283/9671406556917033397649408)), (25967/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314351933605455/151115727451828646838272), (3819570082073/604462909807314587353088)), (90919/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235693473060537/9444732965739290427392), (6203627473485/75557863725914323419136)), (147807/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647928033868109/2361183241434822606848), (1162486209783/1180591620717411303424)), (1733/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1619133151675165/590295810358705651712), (6389166168013/590295810358705651712)), (76297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910290227671353/36893488147419103232), (7979700339177/73786976294838206464)), (5965/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1819400319860003/9223372036854775808), (4483939490787/4611686018427387904)), (214929/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590648027696667/1152921504606846976), (4478142664465/576460752303423488)), (107583/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191659271354915/144115188075855872), (3911861113095/72057594037927936)), (188537/144115188075855872), by norm_num⟩
  | 4 => ⟨((11619167310081/281474976710656), (2927391749521/9007199254740992)), (141669/18014398509481984), by norm_num⟩
  | 3 => ⟨((1483774698220961/9007199254740992), (1823939597527/1125899906842624)), (355109/9007199254740992), by norm_num⟩
  | 2 => ⟨((138560834610041/281474976710656), (3630881729917/562949953421312)), (713031/4503599627370496), by norm_num⟩
  | 1 => ⟨((2199620566427181/2251799813685248), (43231841565605/2251799813685248)), (1076605/2251799813685248), by norm_num⟩
  | 0 => ⟨((2147687282798943/2251799813685248), (85115974774085/2251799813685248)), (136349/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2147687282798943/2251799813685248), (85115974774085/2251799813685248)), (520130158007574037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2045171114921447/2251799813685248), (162361232534403/2251799813685248)), (4326361/2251799813685248), by norm_num⟩
  | 2 => ⟨((230724535004109/281474976710656), (294925420052299/2251799813685248)), (4241311/1125899906842624), by norm_num⟩
  | 3 => ⟨((368592146137177/562949953421312), (483499678711455/2251799813685248)), (16128373/2251799813685248), by norm_num⟩
  | 4 => ⟨((861528974289741/2251799813685248), (39571498130029/140737488355328)), (28046215/2251799813685248), by norm_num⟩
  | 5 => ⟨((151594686444537/2251799813685248), (484476348035973/2251799813685248)), (2327023/140737488355328), by norm_num⟩
  | 6 => ⟨((-752238743644027/18014398509481984), (521851291568309/18014398509481984)), (84136899/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-1601566325/33554432)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-202767299/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-303133981275995/18014398509481984), (827368885270549/18014398509481984)), (39058119/4503599627370496), by norm_num⟩
  | 1 => ⟨((116318541/2147483648), (-1269911625/8589934592)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((-93603735/1073741824), (510960979/2147483648)), (197/4294967296), by norm_num⟩
  | 3 => ⟨((401731733/4294967296), (-548239981/2147483648)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-323281141/4294967296), (882358211/4294967296)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((104060185/2147483648), (-568040303/4294967296)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-446609085/17179869184), (609483733/8589934592)), (121/8589934592), by norm_num⟩
  | 7 => ⟨((410736911/34359738368), (-1121058545/34359738368)), (225/34359738368), by norm_num⟩
  | 8 => ⟨((-165263889/34359738368), (451068531/34359738368)), (183/68719476736), by norm_num⟩
  | 9 => ⟨((472856833/274877906944), (-322651909/68719476736)), (33/34359738368), by norm_num⟩
  | 10 => ⟨((-152206743/274877906944), (103857643/68719476736)), (171/549755813888), by norm_num⟩
  | 11 => ⟨((356316077/2199023255552), (-486261609/1099511627776)), (101/1099511627776), by norm_num⟩
  | 12 => ⟨((-191156201/4398046511104), (1043477159/8796093022208)), (219/8796093022208), by norm_num⟩
  | 13 => ⟨((378651123/35184372088832), (-258371031/8796093022208)), (219/35184372088832), by norm_num⟩
  | 14 => ⟨((-348237413/140737488355328), (475236723/70368744177664)), (203/140737488355328), by norm_num⟩
  | 15 => ⟨((37364433/70368744177664), (-815854933/562949953421312)), (11/35184372088832), by norm_num⟩
  | 16 => ⟨((-60135735/562949953421312), (328266965/1125899906842624)), (143/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (2503608053353/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777311695844819/633825300114114700748351602688), (1479139226781/316912650057057350374175801344)), (23123/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472025699855935/9903520314283042199192993792), (3327197412077/39614081257132168796771975168)), (104073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((943887804527189/1237940039285380274899124224), (3534058969059/2475880078570760549798248448)), (110599/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769442057874157/154742504910672534362390528), (3532835236343/154742504910672534362390528)), (110623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((386978574271191/2417851639229258349412352), (3310733337643/9671406556917033397649408)), (103735/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628677329187007/302231454903657293676544), (2895592558517/604462909807314587353088)), (90795/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885462151726519/75557863725914323419136), (1175725828573/18889465931478580854784)), (147589/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647896190664997/2361183241434822606848), (1762524228771/2361183241434822606848)), (110735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619046456105619/590295810358705651712), (2421742141935/295147905179352825856)), (76165/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910236696755701/36893488147419103232), (6049173404133/73786976294838206464)), (47629/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819281669675959/9223372036854775808), (6798201501863/9223372036854775808)), (107237/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198816451883323/144115188075855872), (6789313178013/1152921504606846976)), (107327/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191559920116877/144115188075855872), (5930663263289/144115188075855872)), (23503/18014398509481984), by norm_num⟩
  | 4 => ⟨((1487109389909829/36028797018963968), (277376790997/1125899906842624)), (141221/18014398509481984), by norm_num⟩
  | 3 => ⟨((741801688121953/4503599627370496), (5530128575411/4503599627370496)), (176881/4503599627370496), by norm_num⟩
  | 2 => ⟨((1108328337261065/2251799813685248), (5504093851767/1125899906842624)), (177415/1125899906842624), by norm_num⟩
  | 1 => ⟨((2199209880547285/2251799813685248), (4095659924385/281474976710656)), (1069851/2251799813685248), by norm_num⟩
  | 0 => ⟨((2147119788402835/2251799813685248), (16124946303299/562949953421312)), (135079/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2147119788402835/2251799813685248), (16124946303299/562949953421312)), (515285492480230287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1022729270929387/1125899906842624), (123002732602893/2251799813685248)), (4245399/2251799813685248), by norm_num⟩
  | 2 => ⟨((1851306207994005/2251799813685248), (223463017045729/2251799813685248)), (8176557/2251799813685248), by norm_num⟩
  | 3 => ⟨((1499866433616309/2251799813685248), (367438053950967/2251799813685248)), (3766869/562949953421312), by norm_num⟩
  | 4 => ⟨((469532989199635/1125899906842624), (489482235680997/2251799813685248)), (24989403/2251799813685248), by norm_num⟩
  | 5 => ⟨((285217206625759/2251799813685248), (1594752505603/8796093022208)), (63413395/4503599627370496), by norm_num⟩
  | 6 => ⟨((-303133981275995/18014398509481984), (827368885270549/18014398509481984)), (39058119/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-202767299/4194304)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-820951749/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((400234962848319/36028797018963968), (412714693228923/9007199254740992)), (127992291/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2428897/67108864), (-320592955/2147483648)), (201/8589934592), by norm_num⟩
  | 2 => ⟨((253234589/4294967296), (1044522797/4294967296)), (165/4294967296), by norm_num⟩
  | 3 => ⟨((-275020913/4294967296), (-567192685/2147483648)), (181/4294967296), by norm_num⟩
  | 4 => ⟨((224011171/4294967296), (461992131/2147483648)), (149/4294967296), by norm_num⟩
  | 5 => ⟨((-36492501/1073741824), (-602085985/4294967296)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((317056243/17179869184), (1307769509/17179869184)), (215/17179869184), by norm_num⟩
  | 7 => ⟨((-147571407/17179869184), (-304345665/8589934592)), (101/17179869184), by norm_num⟩
  | 8 => ⟨((240400945/68719476736), (495793779/34359738368)), (83/34359738368), by norm_num⟩
  | 9 => ⟨((-348110883/274877906944), (-1435861329/274877906944)), (121/137438953472), by norm_num⟩
  | 10 => ⟨((226835773/549755813888), (935634965/549755813888)), (159/549755813888), by norm_num⟩
  | 11 => ⟨((-134373245/1099511627776), (-554252553/1099511627776)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((36483417/1099511627776), (150484027/1099511627776)), (13/549755813888), by norm_num⟩
  | 13 => ⟨((-18287153/2199023255552), (-603435677/17592186044416)), (105/17592186044416), by norm_num⟩
  | 14 => ⟨((136185851/70368744177664), (1123458109/140737488355328)), (197/140737488355328), by norm_num⟩
  | 15 => ⟨((-236643547/562949953421312), (-976089327/562949953421312)), (173/562949953421312), by norm_num⟩
  | 16 => ⟨((385503761/4503599627370496), (1590096629/4503599627370496)), (71/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (434077447879/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777257542007631/633825300114114700748351602688), (2051509482191/633825300114114700748351602688)), (92403/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944021011980661/19807040628566084398385987584), (2307344172421/39614081257132168796771975168)), (103967/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887711234516077/2475880078570760549798248448), (2450789672407/2475880078570760549798248448)), (6905/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769377907364137/154742504910672534362390528), (1224965601099/77371252455336267181195264)), (3453/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((24185224903207/151115727451828646838272), (1147949388147/4835703278458516698824704)), (12951/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257302480595593/604462909807314587353088), (2008000152373/604462909807314587353088)), (90675/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885377807826399/75557863725914323419136), (3261292556809/75557863725914323419136)), (147381/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295729512277841/4722366482869645213696), (2444476140941/4722366482869645213696)), (110565/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404740160538431/147573952589676412928), (3358729904449/590295810358705651712)), (38019/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820367070949185/73786976294838206464), (262173644891/4611686018427387904)), (190167/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909581676690063/4611686018427387904), (4714133840555/9223372036854775808)), (214037/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590414915580165/1152921504606846976), (4707901725441/1152921504606846976)), (107081/576460752303423488), by norm_num⟩
  | 5 => ⟨((297864905397903/36028797018963968), (4112413309289/144115188075855872)), (187533/144115188075855872), by norm_num⟩
  | 4 => ⟨((371740638934979/9007199254740992), (6154644596471/36028797018963968)), (281581/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483426127222763/9007199254740992), (3834453660243/4503599627370496)), (176235/4503599627370496), by norm_num⟩
  | 2 => ⟨((2216320937408717/4503599627370496), (1908106587693/562949953421312)), (176607/1125899906842624), by norm_num⟩
  | 1 => ⟨((1099376379279739/1125899906842624), (22715688472459/2251799813685248)), (531689/1125899906842624), by norm_num⟩
  | 0 => ⟨((2146388982204801/2251799813685248), (44709881032441/2251799813685248)), (2141803/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2146388982204801/2251799813685248), (44709881032441/2251799813685248)), (8170330056197356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((31953514067125/35184372088832), (85233860896955/2251799813685248)), (4168135/2251799813685248), by norm_num⟩
  | 2 => ⟨((1854011180929433/2251799813685248), (154814266191251/2251799813685248)), (492895/140737488355328), by norm_num⟩
  | 3 => ⟨((757924834448035/1125899906842624), (254931525210691/2251799813685248)), (14070737/2251799813685248), by norm_num⟩
  | 4 => ⟨((495783444553161/1125899906842624), (343225774985175/2251799813685248)), (22130029/2251799813685248), by norm_num⟩
  | 5 => ⟨((768630459686839/4503599627370496), (604549857220527/4503599627370496)), (52471807/4503599627370496), by norm_num⟩
  | 6 => ⟨((400234962848319/36028797018963968), (412714693228923/9007199254740992)), (127992291/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-820951749/16777216)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-1660922571/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((36922325834473/1125899906842624), (142105533003479/4503599627370496)), (5854389/1125899906842624), by norm_num⟩
  | 1 => ⟨((-7253287/67108864), (-893319425/8589934592)), (149/8589934592), by norm_num⟩
  | 2 => ⟨((382490411/2147483648), (736058773/4294967296)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((-210104333/1073741824), (-808643213/4294967296)), (139/4294967296), by norm_num⟩
  | 4 => ⟨((346234803/2147483648), (166572257/1073741824)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((-456453371/4294967296), (-878391977/8589934592)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((1002930565/17179869184), (241253055/4294967296)), (43/4294967296), by norm_num⟩
  | 7 => ⟨((-472213647/17179869184), (-454360407/17179869184)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((778169573/68719476736), (374374445/34359738368)), (137/68719476736), by norm_num⟩
  | 9 => ⟨((-284968885/68719476736), (-548389821/137438953472)), (51/68719476736), by norm_num⟩
  | 10 => ⟨((751368765/549755813888), (180740339/137438953472)), (137/549755813888), by norm_num⟩
  | 11 => ⟨((-450252523/1099511627776), (-108307395/274877906944)), (83/1099511627776), by norm_num⟩
  | 12 => ⟨((494652955/4398046511104), (951902681/8796093022208)), (185/8796093022208), by norm_num⟩
  | 13 => ⟨((-1003258735/35184372088832), (-60332999/2199023255552)), (95/17592186044416), by norm_num⟩
  | 14 => ⟨((944736321/140737488355328), (909018159/140737488355328)), (181/140737488355328), by norm_num⟩
  | 15 => ⟨((-830319145/562949953421312), (-24966463/17592186044416)), (161/562949953421312), by norm_num⟩
  | 16 => ⟨((85518639/281474976710656), (658283113/2251799813685248)), (67/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (31186661457/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888602301023823/316912650057057350374175801344), (589535254741/316912650057057350374175801344)), (92317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1887982563673345/39614081257132168796771975168), (1326104609683/39614081257132168796771975168)), (12983/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((943824094528843/1237940039285380274899124224), (704271195337/1237940039285380274899124224)), (110365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769315009198891/154742504910672534362390528), (704021734689/77371252455336267181195264)), (55187/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547795583140023/9671406556917033397649408), (1319510893667/9671406556917033397649408)), (51743/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628625588738463/302231454903657293676544), (72127653057/37778931862957161709568)), (90561/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942647366418745/37778931862957161709568), (234290824631/9444732965739290427392)), (147181/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295667461721823/4722366482869645213696), (1404877198537/4722366482869645213696)), (110403/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618875737527393/590295810358705651712), (482574288051/147573952589676412928)), (18979/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910130780724061/36893488147419103232), (18834061439/576460752303423488)), (189831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909522753874753/4611686018427387904), (1354602271545/4611686018427387904)), (106809/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590298133094785/1152921504606846976), (2705583826847/1152921504606846976)), (106845/576460752303423488), by norm_num⟩
  | 5 => ⟨((297839657363221/36028797018963968), (2363318946627/144115188075855872)), (46765/36028797018963968), by norm_num⟩
  | 4 => ⟨((743406721934451/18014398509481984), (3536860599109/36028797018963968)), (140377/18014398509481984), by norm_num⟩
  | 3 => ⟨((185405484547307/1125899906842624), (4406905450165/9007199254740992)), (351229/9007199254740992), by norm_num⟩
  | 2 => ⟨((1107984387305685/2251799813685248), (548215199183/281474976710656)), (703323/4503599627370496), by norm_num⟩
  | 1 => ⟨((1099127544784071/1125899906842624), (6525872491971/1125899906842624)), (264291/562949953421312), by norm_num⟩
  | 0 => ⟨((1072757161625125/1125899906842624), (25684794524911/2251799813685248)), (2123135/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1072757161625125/1125899906842624), (25684794524911/2251799813685248)), (8099117287642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2043952563913627/2251799813685248), (24472466072705/1125899906842624)), (4094281/2251799813685248), by norm_num⟩
  | 2 => ⟨((927113158943087/1125899906842624), (44427181733115/1125899906842624)), (3805361/1125899906842624), by norm_num⟩
  | 3 => ⟨((380835378792047/562949953421312), (36583202955433/562949953421312)), (13134603/2251799813685248), by norm_num⟩
  | 4 => ⟨((1021030406897719/2251799813685248), (98994078392129/1125899906842624)), (9739103/1125899906842624), by norm_num⟩
  | 5 => ⟨((445556383602727/2251799813685248), (22443372525145/281474976710656)), (21089171/2251799813685248), by norm_num⟩
  | 6 => ⟨((36922325834473/1125899906842624), (142105533003479/4503599627370496)), (5854389/1125899906842624), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-1660922571/33554432)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile002Terms3
