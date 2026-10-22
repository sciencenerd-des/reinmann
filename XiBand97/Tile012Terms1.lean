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
namespace Reinmann.XiBand97.Tile012Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25387/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25387/1280))
  have he : value ((69/80), (25387/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1462263883/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((622557963358093/4503599627370496), (265739546155467/4503599627370496)), (118493691/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1304530771/4294967296), (-8700631/67108864)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((44786673/134217728), (611751689/4294967296)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((-1049668039/4294967296), (-448051949/4294967296)), (53/2147483648), by norm_num⟩
  | 4 => ⟨((1153178207/8589934592), (492235377/8589934592)), (119/8589934592), by norm_num⟩
  | 5 => ⟨((-126689575/2147483648), (-432620667/17179869184)), (107/17179869184), by norm_num⟩
  | 6 => ⟨((742307861/34359738368), (316854921/34359738368)), (5/2147483648), by norm_num⟩
  | 7 => ⟨((-466004879/68719476736), (-397829383/137438953472)), (51/68719476736), by norm_num⟩
  | 8 => ⟨((511958687/274877906944), (437060249/549755813888)), (57/274877906944), by norm_num⟩
  | 9 => ⟨((-999900631/2199023255552), (-106702169/549755813888)), (113/2199023255552), by norm_num⟩
  | 10 => ⟨((878802497/8796093022208), (375117805/8796093022208)), (101/8796093022208), by norm_num⟩
  | 11 => ⟨((-702155071/35184372088832), (-599431317/70368744177664)), (41/17592186044416), by norm_num⟩
  | 12 => ⟨((1028528253/281474976710656), (439028407/281474976710656)), (61/140737488355328), by norm_num⟩
  | 13 => ⟨((-695356171/1125899906842624), (-593627081/2251799813685248)), (21/281474976710656), by norm_num⟩
  | 14 => ⟨((109132405/1125899906842624), (372666289/9007199254740992)), (27/2251799813685248), by norm_num⟩
  | 15 => ⟨((-31971787/2251799813685248), (-436710149/72057594037927936)), (1/562949953421312), by norm_num⟩
  | 16 => ⟨((1123987139/576460752303423488), (14992973/18014398509481984)), (143/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (525522378933/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045651986399/633825300114114700748351602688), (311056333667/316912650057057350374175801344)), (46131/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118128332978189/2475880078570760549798248448), (349880248325/19807040628566084398385987584)), (103799/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889847856303323/2475880078570760549798248448), (371675906291/1237940039285380274899124224)), (110291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771514092260443/154742504910672534362390528), (743190186587/154742504910672534362390528)), (110295/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549856603022659/9671406556917033397649408), (696569121325/9671406556917033397649408)), (6463/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314763487405179/151115727451828646838272), (38082897357/37778931862957161709568)), (90487/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888223075092965/75557863725914323419136), (989833654477/75557863725914323419136)), (147051/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297862701741949/4722366482869645213696), (742093890763/4722366482869645213696)), (55149/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810946270697585/295147905179352825856), (1019922125367/590295810358705651712)), (75837/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824030091171731/73786976294838206464), (1274217578933/73786976294838206464)), (94807/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823281703055661/9223372036854775808), (1432553417751/9223372036854775808)), (106673/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199316260196743/144115188075855872), (1431377653973/1152921504606846976)), (213383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597528406068649/72057594037927936), (1251133996667/144115188075855872)), (186753/144115188075855872), by norm_num⟩
  | 4 => ⟨((746175593512077/18014398509481984), (937030649883/18014398509481984)), (280215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490149406851367/9007199254740992), (2337964362099/9007199254740992)), (350419/9007199254740992), by norm_num⟩
  | 2 => ⟨((69679062879575/140737488355328), (2331060353343/2251799813685248)), (701287/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109386406699591/1125899906842624), (6958761506181/2251799813685248)), (131633/281474976710656), by norm_num⟩
  | 0 => ⟨((1093027894870887/1125899906842624), (6890223045203/1125899906842624)), (263837/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093027894870887/1125899906842624), (6890223045203/1125899906842624)), (1006458283544444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2122146909386427/2251799813685248), (6689054634891/562949953421312)), (2061989/1125899906842624), by norm_num⟩
  | 2 => ⟨((249955146013771/281474976710656), (25215663548563/1125899906842624)), (983883/281474976710656), by norm_num⟩
  | 3 => ⟨((887295011342153/1125899906842624), (89567960005115/2251799813685248)), (14331871/2251799813685248), by norm_num⟩
  | 4 => ⟨((697474817712697/1125899906842624), (141172769631893/2251799813685248)), (11864675/1125899906842624), by norm_num⟩
  | 5 => ⟨((1710591432491437/4503599627370496), (43727000582639/562949953421312)), (16187579/1125899906842624), by norm_num⟩
  | 6 => ⟨((622557963358093/4503599627370496), (265739546155467/4503599627370496)), (118493691/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1462263883/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-766190915/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-142395232613061/9007199254740992), (-1227974462930951/9007199254740992)), (102503143/4503599627370496), by norm_num⟩
  | 1 => ⟨((39086001/1073741824), (337066137/1073741824)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((-179997687/4294967296), (-1552246925/4294967296)), (33/536870912), by norm_num⟩
  | 3 => ⟨((69076665/2147483648), (148924193/536870912)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-159054899/8589934592), (-1371642507/8589934592)), (119/4294967296), by norm_num⟩
  | 5 => ⟨((286123/33554432), (315832359/4294967296)), (221/17179869184), by norm_num⟩
  | 6 => ⟨((-112439049/34359738368), (-121205147/4294967296)), (43/8589934592), by norm_num⟩
  | 7 => ⟨((73971565/68719476736), (159477237/17179869184)), (57/34359738368), by norm_num⟩
  | 8 => ⟨((-170325823/549755813888), (-1468839635/549755813888)), (265/549755813888), by norm_num⟩
  | 9 => ⟨((87153267/1099511627776), (751584055/1099511627776)), (273/2199023255552), by norm_num⟩
  | 10 => ⟨((-160542251/8796093022208), (-1384468993/8796093022208)), (127/4398046511104), by norm_num⟩
  | 11 => ⟨((16802827/4398046511104), (1159220969/35184372088832)), (107/17592186044416), by norm_num⟩
  | 12 => ⟨((-206346341/281474976710656), (-1779469949/281474976710656)), (331/281474976710656), by norm_num⟩
  | 13 => ⟨((146193849/1125899906842624), (1260732609/1125899906842624)), (59/281474976710656), by norm_num⟩
  | 14 => ⟨((-48089111/2251799813685248), (-1658825207/9007199254740992)), (313/9007199254740992), by norm_num⟩
  | 15 => ⟨((118111221/36028797018963968), (509278159/18014398509481984)), (97/18014398509481984), by norm_num⟩
  | 16 => ⟨((-16997571/36028797018963968), (-1172656297/288230376151711744)), (113/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-1098258044549/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889451061459063/316912650057057350374175801344), (-81245089473/19807040628566084398385987584)), (11557/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944945845492377/19807040628566084398385987584), (-1462154775583/19807040628566084398385987584)), (52015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889675899820779/2475880078570760549798248448), (-3106448890731/2475880078570760549798248448)), (110551/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771341891268657/154742504910672534362390528), (-3105740296249/154742504910672534362390528)), (27643/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193711863121613/1208925819614629174706176), (-2910878820409/9671406556917033397649408)), (25921/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258912204399777/604462909807314587353088), (-2546266456559/604462909807314587353088)), (45373/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471998063272877/18889465931478580854784), (-4136272449713/75557863725914323419136)), (147505/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297689160384305/4722366482869645213696), (-775242632321/1180591620717411303424)), (55333/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202706654050287/73786976294838206464), (-2130915160201/295147905179352825856)), (152227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911864960915265/36893488147419103232), (-5324283030273/73786976294838206464)), (95187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113933912138009/576460752303423488), (-2992844465687/4611686018427387904)), (214297/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99636825191287/72057594037927936), (-747566301451/144115188075855872)), (214453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298689139259367/36028797018963968), (-1306791337225/36028797018963968)), (187823/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491896842739733/36028797018963968), (-7829161929701/36028797018963968)), (35261/4503599627370496), by norm_num⟩
  | 3 => ⟨((186196821089197/1125899906842624), (-9766202449881/9007199254740992)), (176615/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228559712605635/4503599627370496), (-19471757752945/4503599627370496)), (22135/140737488355328), by norm_num⟩
  | 1 => ⟨((554241538792027/562949953421312), (-3632047256451/281474976710656)), (1067143/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091119862367311/1125899906842624), (-3594367194851/140737488355328)), (2153003/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091119862367311/1125899906842624), (-3594367194851/140737488355328)), (8213054665572356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((528339908542485/562949953421312), (-55733344182491/1125899906842624)), (1070741/562949953421312), by norm_num⟩
  | 2 => ⟨((1977912998151797/2251799813685248), (-209227479559673/2251799813685248)), (8463321/2251799813685248), by norm_num⟩
  | 3 => ⟨((858949287264585/1125899906842624), (-367558207329581/2251799813685248)), (16440603/2251799813685248), by norm_num⟩
  | 4 => ⟨((625294588683993/1125899906842624), (-140205118721145/562949953421312)), (30452235/2251799813685248), by norm_num⟩
  | 5 => ⟨((554868899938019/2251799813685248), (-622929278237399/2251799813685248)), (48993231/2251799813685248), by norm_num⟩
  | 6 => ⟨((-142395232613061/9007199254740992), (-1227974462930951/9007199254740992)), (102503143/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-766190915/16777216)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-398952807/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-516303986832493/4503599627370496), (239913846090981/4503599627370496)), (25370423/1125899906842624), by norm_num⟩
  | 1 => ⟨((590344853/2147483648), (-548637655/4294967296)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((-353896283/1073741824), (164446955/1073741824)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((1131474965/4294967296), (-8215137/67108864)), (57/1073741824), by norm_num⟩
  | 4 => ⟨((-1356579235/8589934592), (315184611/4294967296)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((650586987/8589934592), (-604623751/17179869184)), (267/17179869184), by norm_num⟩
  | 6 => ⟨((-1040026307/34359738368), (483274811/34359738368)), (27/4294967296), by norm_num⟩
  | 7 => ⟨((178133869/17179869184), (-10346807/2147483648)), (299/137438953472), by norm_num⟩
  | 8 => ⟨((-854292725/274877906944), (198484477/137438953472)), (181/274877906944), by norm_num⟩
  | 9 => ⟨((910446439/1099511627776), (-423062213/1099511627776)), (195/1099511627776), by norm_num⟩
  | 10 => ⟨((-873262085/4398046511104), (396273/4294967296)), (189/4398046511104), by norm_num⟩
  | 11 => ⟨((380725641/8796093022208), (-88456951/4398046511104)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((-304313405/35184372088832), (141407003/35184372088832)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((898106677/562949953421312), (-417328227/562949953421312)), (25/70368744177664), by norm_num⟩
  | 14 => ⟨((-1230609003/4503599627370496), (571833933/4503599627370496)), (69/1125899906842624), by norm_num⟩
  | 15 => ⟨((393449535/9007199254740992), (-365652769/18014398509481984)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-235862695/36028797018963968), (438398523/144115188075855872)), (27/18014398509481984), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (881412749991/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222346210759549/79228162514264337593543950336), (4172468966045/633825300114114700748351602688)), (92611/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236217800478779/4951760157141521099596496896), (1173289000389/9903520314283042199192993792)), (52107/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236189611835405/309485009821345068724781056), (4985423655289/2475880078570760549798248448)), (55379/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885591225251215/77371252455336267181195264), (4984237300857/154742504910672534362390528)), (13849/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549544966713999/9671406556917033397649408), (4671462142115/9671406556917033397649408)), (3247/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258780546236751/604462909807314587353088), (4086269242427/604462909807314587353088)), (90953/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887777442729053/75557863725914323419136), (6637825187339/75557863725914323419136)), (73933/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324381823936911/1180591620717411303424), (1244075566605/1180591620717411303424)), (6935/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810714720015203/295147905179352825856), (6839058132993/590295810358705651712)), (152667/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823448341084963/73786976294838206464), (1067973476123/9223372036854775808)), (47745/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911311644742349/4611686018427387904), (2401210145369/2305843009213693952)), (107527/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796933373176705/576460752303423488), (9596193043967/1152921504606846976)), (107653/576460752303423488), by norm_num⟩
  | 5 => ⟨((597235434837599/72057594037927936), (8386945036177/144115188075855872)), (188677/144115188075855872), by norm_num⟩
  | 4 => ⟨((186432657097681/4503599627370496), (12560981326957/36028797018963968)), (141791/18014398509481984), by norm_num⟩
  | 3 => ⟨((93063611649209/562949953421312), (15667239255595/9007199254740992)), (22217/562949953421312), by norm_num⟩
  | 2 => ⟨((1113704716442967/2251799813685248), (3904077571383/562949953421312)), (44621/281474976710656), by norm_num⟩
  | 1 => ⟨((276893699056865/281474976710656), (11648663062273/562949953421312)), (269599/562949953421312), by norm_num⟩
  | 0 => ⟨((272280735293585/281474976710656), (11521799733575/281474976710656)), (1093435/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272280735293585/281474976710656), (11521799733575/281474976710656)), (4171123508933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525830379721375/562949953421312), (22290891645321/281474976710656)), (2204955/1125899906842624), by norm_num⟩
  | 2 => ⟨((975255619680665/1125899906842624), (166568668450213/1125899906842624)), (4468367/1125899906842624), by norm_num⟩
  | 3 => ⟨((1640249540474487/2251799813685248), (577127785450655/2251799813685248)), (9063133/1125899906842624), by norm_num⟩
  | 4 => ⟨((1046870179116683/2251799813685248), (840779521454223/2251799813685248)), (35698353/2251799813685248), by norm_num⟩
  | 5 => ⟨((345525357860591/4503599627370496), (1563526212007143/4503599627370496)), (59850779/2251799813685248), by norm_num⟩
  | 6 => ⟨((-516303986832493/4503599627370496), (239913846090981/4503599627370496)), (25370423/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-398952807/8388608)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-413429433/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((146911428883053/2251799813685248), (877773732388799/9007199254740992)), (4188295/281474976710656), by norm_num⟩
  | 1 => ⟨((-696298955/4294967296), (-1040070431/4294967296)), (161/4294967296), by norm_num⟩
  | 2 => ⟨((108139869/536870912), (323059741/1073741824)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((-716579945/4294967296), (-535182199/2147483648)), (171/4294967296), by norm_num⟩
  | 4 => ⟨((55644821/536870912), (332469451/2147483648)), (27/1073741824), by norm_num⟩
  | 5 => ⟨((-221235497/4294967296), (-82615555/1073741824)), (109/8589934592), by norm_num⟩
  | 6 => ⟨((366499705/17179869184), (1094890357/34359738368)), (183/34359738368), by norm_num⟩
  | 7 => ⟨((-520410031/68719476736), (-777342951/68719476736)), (33/17179869184), by norm_num⟩
  | 8 => ⟨((646585173/274877906944), (482906167/137438953472)), (83/137438953472), by norm_num⟩
  | 9 => ⟨((-44630661/68719476736), (-266661499/274877906944)), (185/1099511627776), by norm_num⟩
  | 10 => ⟨((88722421/549755813888), (1060206291/4398046511104)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((-641358353/17592186044416), (-119750621/2199023255552)), (85/8796093022208), by norm_num⟩
  | 12 => ⟨((531238545/70368744177664), (396758819/35184372088832)), (143/70368744177664), by norm_num⟩
  | 13 => ⟨((-812355811/562949953421312), (-1213426003/562949953421312)), (221/562949953421312), by norm_num⟩
  | 14 => ⟨((576750959/2251799813685248), (430750049/1125899906842624)), (159/2251799813685248), by norm_num⟩
  | 15 => ⟨((-191089639/4503599627370496), (-1141731905/18014398509481984)), (213/18014398509481984), by norm_num⟩
  | 16 => ⟨((474839915/72057594037927936), (709274301/72057594037927936)), (135/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (19963611839/158456325028528675187087900672)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778662096130701/633825300114114700748351602688), (188985771041/79228162514264337593543950336)), (92349/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889621846189459/39614081257132168796771975168), (1700553287471/39614081257132168796771975168)), (103903/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944694713358157/1237940039285380274899124224), (451610709193/618970019642690137449562112)), (13801/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771055684610021/154742504910672534362390528), (902999291767/77371252455336267181195264)), (27605/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549426869183171/9671406556917033397649408), (1692651796971/9671406556917033397649408)), (25883/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258677955872287/604462909807314587353088), (1480598609245/604462909807314587353088)), (22651/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887612129114039/75557863725914323419136), (1202544311021/37778931862957161709568)), (18407/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648702265348671/2361183241434822606848), (112690200453/295147905179352825856)), (863/36893488147419103232), by norm_num⟩
  | 9 => ⟨((810631309392857/295147905179352825856), (2477928508227/590295810358705651712)), (151923/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911621390985957/36893488147419103232), (1547763955055/36893488147419103232)), (47489/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227799513732527/1152921504606846976), (3479881982695/9223372036854775808)), (106887/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593644650924173/1152921504606846976), (3476651081871/1152921504606846976)), (213865/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298570560959513/36028797018963968), (3038438703505/144115188075855872)), (187235/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491189703248039/36028797018963968), (4550405484975/36028797018963968)), (281059/36028797018963968), by norm_num⟩
  | 3 => ⟨((744349100486649/4503599627370496), (5675336017387/9007199254740992)), (351685/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226829561515239/4503599627370496), (2828186005269/1125899906842624)), (88057/562949953421312), by norm_num⟩
  | 1 => ⟨((1107213545545011/1125899906842624), (16874591155705/2251799813685248)), (1059411/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177384462467963/2251799813685248), (16686424477223/1125899906842624)), (2129777/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177384462467963/2251799813685248), (16686424477223/1125899906842624)), (8124454506880950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((263116714546683/281474976710656), (64539949190935/2251799813685248)), (2090959/1125899906842624), by norm_num⟩
  | 2 => ⟨((1965796656692935/2251799813685248), (30165273635647/562949953421312)), (4029027/1125899906842624), by norm_num⟩
  | 3 => ⟨((1709653483552079/2251799813685248), (210671636797537/2251799813685248)), (7466379/1125899906842624), by norm_num⟩
  | 4 => ⟨((1278325221352541/2251799813685248), (319900104394335/2251799813685248)), (25469183/2251799813685248), by norm_num⟩
  | 5 => ⟨((1360493313344439/4503599627370496), (363208460428223/2251799813685248)), (72307483/4503599627370496), by norm_num⟩
  | 6 => ⟨((146911428883053/2251799813685248), (877773732388799/9007199254740992)), (4188295/281474976710656), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-413429433/8388608)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1706986553/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((809925120041053/9007199254740992), (-140520012938883/2251799813685248)), (100367503/9007199254740992), by norm_num⟩
  | 1 => ⟨((-990589579/4294967296), (343729703/2147483648)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((317601513/1073741824), (-6887885/33554432)), (41/1073741824), by norm_num⟩
  | 3 => ⟨((-1086175729/4294967296), (188448813/1073741824)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((696496435/4294967296), (-241680831/2147483648)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((-714591233/8589934592), (247959637/4294967296)), (97/8589934592), by norm_num⟩
  | 6 => ⟨((1221926883/34359738368), (-26500163/1073741824)), (21/4294967296), by norm_num⟩
  | 7 => ⟨((-223870041/17179869184), (310727205/34359738368)), (125/68719476736), by norm_num⟩
  | 8 => ⟨((287107659/68719476736), (-796999545/274877906944)), (81/137438953472), by norm_num⟩
  | 9 => ⟨((-327296269/274877906944), (454280771/549755813888)), (47/274877906944), by norm_num⟩
  | 10 => ⟨((167899671/549755813888), (-466082869/2199023255552)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((-626406041/8796093022208), (108679905/2199023255552)), (93/8796093022208), by norm_num⟩
  | 12 => ⟨((535566591/35184372088832), (-743355873/70368744177664)), (81/35184372088832), by norm_num⟩
  | 13 => ⟨((-845354575/281474976710656), (18333367/8796093022208)), (65/140737488355328), by norm_num⟩
  | 14 => ⟨((619511907/1125899906842624), (-214967579/562949953421312)), (193/2251799813685248), by norm_num⟩
  | 15 => ⟨((-211868889/2251799813685248), (147034921/2251799813685248)), (67/4503599627370496), by norm_num⟩
  | 16 => ⟨((543432971/36028797018963968), (-188568563/18014398509481984)), (175/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-790269877553/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778556444533927/633825300114114700748351602688), (-935030851827/633825300114114700748351602688)), (92293/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472375763351553/9903520314283042199192993792), (-1051707082215/39614081257132168796771975168)), (103835/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263293142741/2475880078570760549798248448), (-1117186664489/2475880078570760549798248448)), (110331/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770929645198767/154742504910672534362390528), (-17451611755/2417851639229258349412352)), (110339/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549308807228681/9671406556917033397649408), (-261698893239/2417851639229258349412352)), (103451/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258574751594999/604462909807314587353088), (-915645105771/604462909807314587353088)), (2829/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1887444609408765/75557863725914323419136), (-1487359120747/75557863725914323419136)), (36781/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297279054629273/4722366482869645213696), (-1115025923759/4722366482869645213696)), (27589/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810545177490525/295147905179352825856), (-1532359287589/590295810358705651712)), (75881/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911513925238813/36893488147419103232), (-957123925447/36893488147419103232)), (94867/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455538714713479/2305843009213693952), (-2151878364669/9223372036854775808)), (213497/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593404082547731/1152921504606846976), (-1074908586531/576460752303423488)), (106777/576460752303423488), by norm_num⟩
  | 5 => ⟨((597036256529119/72057594037927936), (-939386892997/72057594037927936)), (46731/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490876636660569/36028797018963968), (-703383672671/9007199254740992)), (280513/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488309536610387/9007199254740992), (-1754418735415/4503599627370496)), (350867/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226060207891025/4503599627370496), (-6993490505985/4503599627370496)), (351205/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213292888460851/2251799813685248), (-5214989019809/1125899906842624)), (1055317/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087597355764713/1125899906842624), (-5155035403667/562949953421312)), (2117487/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087597355764713/1125899906842624), (-5155035403667/562949953421312)), (8077571877486418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050503427096977/1125899906842624), (-19918654721713/1125899906842624)), (1032421/562949953421312), by norm_num⟩
  | 2 => ⟨((1959607050026639/2251799813685248), (-18584791526451/562949953421312)), (7852395/2251799813685248), by norm_num⟩
  | 3 => ⟨((425718735696723/562949953421312), (-64692941667681/1125899906842624)), (14185409/2251799813685248), by norm_num⟩
  | 4 => ⟨((1280328005377469/2251799813685248), (-97845277960811/1125899906842624)), (23084975/2251799813685248), by norm_num⟩
  | 5 => ⟨((1421924806945305/4503599627370496), (-222531414748007/2251799813685248)), (60527321/4503599627370496), by norm_num⟩
  | 6 => ⟨((809925120041053/9007199254740992), (-140520012938883/2251799813685248)), (100367503/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1706986553/33554432)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-109769111/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-448008130704359/9007199254740992), (-809054654960601/9007199254740992)), (165727063/9007199254740992), by norm_num⟩
  | 1 => ⟨((563773699/4294967296), (1018114861/4294967296)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-185978889/1073741824), (-1343431743/4294967296)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((654411933/4294967296), (295449449/1073741824)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-107939413/1073741824), (-389854017/2147483648)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((227886639/4294967296), (823077681/8589934592)), (11/536870912), by norm_num⟩
  | 6 => ⟨((-200468635/8589934592), (-724049729/17179869184)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((302313269/34359738368), (1091890711/68719476736)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((-24931939/8589934592), (-360195273/68719476736)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((58486059/68719476736), (422478211/274877906944)), (47/137438953472), by norm_num⟩
  | 10 => ⟨((-61739225/274877906944), (-891955375/2199023255552)), (201/2199023255552), by norm_num⟩
  | 11 => ⟨((118496985/2199023255552), (855971407/8796093022208)), (195/8796093022208), by norm_num⟩
  | 12 => ⟨((-416960449/35184372088832), (-47061617/2199023255552)), (173/35184372088832), by norm_num⟩
  | 13 => ⟨((677158479/281474976710656), (1222875621/281474976710656)), (283/281474976710656), by norm_num⟩
  | 14 => ⟨((-510588585/1125899906842624), (-922068249/1125899906842624)), (27/140737488355328), by norm_num⟩
  | 15 => ⟨((718652025/9007199254740992), (1297808517/9007199254740992)), (307/9007199254740992), by norm_num⟩
  | 16 => ⟨((-474140973/36028797018963968), (-428123885/18014398509481984)), (205/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-338110518997/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778452920798267/633825300114114700748351602688), (-800006221881/158456325028528675187087900672)), (92515/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472346582700435/9903520314283042199192993792), (-1799652702513/19807040628566084398385987584)), (26025/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944569467017675/1237940039285380274899124224), (-3823373110717/2475880078570760549798248448)), (55315/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770804902452571/154742504910672534362390528), (-1911186681593/77371252455336267181195264)), (1729/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1549191453584811/9671406556917033397649408), (-3582413064691/9671406556917033397649408)), (12971/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258471660171439/604462909807314587353088), (-3133549770123/604462909807314587353088)), (90825/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471819080864473/18889465931478580854784), (-5090028402459/75557863725914323419136)), (147643/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648576086893057/2361183241434822606848), (-3815780715809/4722366482869645213696)), (110779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620914812282809/590295810358705651712), (-5243871234019/590295810358705651712)), (152395/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822806802119511/73786976294838206464), (-6550600270513/73786976294838206464)), (95303/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910951977871169/4611686018427387904), (-920450051257/1152921504606846976)), (214587/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593150405450271/1152921504606846976), (-3678162208475/576460752303423488)), (53695/288230376151711744), by norm_num⟩
  | 5 => ⟨((298461858155437/36028797018963968), (-6428605417255/144115188075855872)), (188151/144115188075855872), by norm_num⟩
  | 4 => ⟨((186316601176963/4503599627370496), (-9626568836849/36028797018963968)), (282661/36028797018963968), by norm_num⟩
  | 3 => ⟨((371967233624389/2251799813685248), (-6002328444355/4503599627370496)), (177045/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112573361476875/2251799813685248), (-11961904811141/2251799813685248)), (710475/4503599627370496), by norm_num⟩
  | 1 => ⟨((552960641095203/562949953421312), (-35672507806693/2251799813685248)), (535733/1125899906842624), by norm_num⟩
  | 0 => ⟨((135748580708389/140737488355328), (-35247754434521/1125899906842624)), (1083017/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((135748580708389/140737488355328), (-35247754434521/1125899906842624)), (4131381992820357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2092777390183919/2251799813685248), (-135993122900233/2251799813685248)), (2157063/1125899906842624), by norm_num⟩
  | 2 => ⟨((968386054764649/1125899906842624), (-63194634597721/562949953421312)), (8540011/2251799813685248), by norm_num⟩
  | 3 => ⟨((1637440944959117/2251799813685248), (-108707359345993/562949953421312)), (4151965/562949953421312), by norm_num⟩
  | 4 => ⟨((1106730799721653/2251799813685248), (-158097429558091/562949953421312)), (30567529/2251799813685248), by norm_num⟩
  | 5 => ⟨((366345312897263/2251799813685248), (-19425715996753/70368744177664)), (94432227/4503599627370496), by norm_num⟩
  | 6 => ⟨((-448008130704359/9007199254740992), (-809054654960601/9007199254740992)), (165727063/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-109769111/2097152)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1802220875/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-831615413562451/9007199254740992), (520503776436795/18014398509481984)), (305404749/18014398509481984), by norm_num⟩
  | 1 => ⟨((134233015/536870912), (-336062993/4294967296)), (199/4294967296), by norm_num⟩
  | 2 => ⟨((-1454038973/4294967296), (14219929/134217728)), (17/268435456), by norm_num⟩
  | 3 => ⟨((328134211/1073741824), (-102688751/1073741824)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-222150979/1073741824), (278086293/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((962553605/8589934592), (-301228657/8589934592)), (185/8589934592), by norm_num⟩
  | 6 => ⟨((-868881161/17179869184), (67978527/4294967296)), (169/17179869184), by norm_num⟩
  | 7 => ⟨((1344556459/68719476736), (-105193865/17179869184)), (33/8589934592), by norm_num⟩
  | 8 => ⟨((-910281597/137438953472), (284870267/137438953472)), (45/34359738368), by norm_num⟩
  | 9 => ⟨((1095594783/549755813888), (-85715887/137438953472)), (219/549755813888), by norm_num⟩
  | 10 => ⟨((-1186770269/2199023255552), (46424585/274877906944)), (239/2199023255552), by norm_num⟩
  | 11 => ⟨((1168666715/8796093022208), (-91432805/2199023255552)), (119/4398046511104), by norm_num⟩
  | 12 => ⟨((-263734011/8796093022208), (330139501/35184372088832)), (217/35184372088832), by norm_num⟩
  | 13 => ⟨((439510733/70368744177664), (-137543745/70368744177664)), (183/140737488355328), by norm_num⟩
  | 14 => ⟨((-1360248147/1125899906842624), (425686133/1125899906842624)), (285/1125899906842624), by norm_num⟩
  | 15 => ⟨((491149369/2251799813685248), (-307407845/4503599627370496)), (207/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1330057147/36028797018963968), (208118969/18014398509481984)), (141/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1848601476347/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444589114916279/158456325028528675187087900672), (2186781116283/316912650057057350374175801344)), (92631/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236159696067729/4951760157141521099596496896), (1229808167885/9903520314283042199192993792)), (104237/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889023050507319/2475880078570760549798248448), (5225436666165/2475880078570760549798248448)), (110785/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770688655188605/154742504910672534362390528), (2612016381317/77371252455336267181195264)), (27705/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549082085603449/9671406556917033397649408), (4896039341893/9671406556917033397649408)), (103933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258375577351455/604462909807314587353088), (1070635839799/151115727451828646838272)), (22745/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471779866536033/18889465931478580854784), (6956337866927/75557863725914323419136)), (147913/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297033899122295/4722366482869645213696), (2607404175125/2361183241434822606848)), (55499/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202593894934439/73786976294838206464), (895798688111/73786976294838206464)), (152725/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822600700724725/73786976294838206464), (8952031068939/73786976294838206464)), (191059/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910834992151497/4611686018427387904), (10062849211771/9223372036854775808)), (215153/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592913805470443/1152921504606846976), (10052622291593/1152921504606846976)), (215417/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596818729161035/72057594037927936), (8784546453765/144115188075855872)), (47197/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490211968782301/36028797018963968), (6576920841819/18014398509481984)), (283777/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487457638826683/9007199254740992), (4100532851431/2251799813685248)), (177883/4503599627370496), by norm_num⟩
  | 2 => ⟨((139018348211721/281474976710656), (16341957093625/2251799813685248)), (44667/281474976710656), by norm_num⟩
  | 1 => ⟨((552621761326197/562949953421312), (6090696645359/281474976710656)), (269969/562949953421312), by norm_num⟩
  | 0 => ⟨((542241681598425/562949953421312), (24063351184567/562949953421312)), (1095679/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542241681598425/562949953421312), (24063351184567/562949953421312)), (4179683689597701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042533158086399/1125899906842624), (46356348133305/562949953421312)), (2204419/1125899906842624), by norm_num⟩
  | 2 => ⟨((478852398471375/562949953421312), (171695653310049/1125899906842624)), (1111359/281474976710656), by norm_num⟩
  | 3 => ⟨((788452930252949/1125899906842624), (584186035685453/2251799813685248)), (17837031/2251799813685248), by norm_num⟩
  | 4 => ⟨((952730680396013/2251799813685248), (818195629735373/2251799813685248)), (17118513/1125899906842624), by norm_num⟩
  | 5 => ⟨((211609983624493/4503599627370496), (692352911903905/2251799813685248)), (53851369/2251799813685248), by norm_num⟩
  | 6 => ⟨((-831615413562451/9007199254740992), (520503776436795/18014398509481984)), (305404749/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1802220875/33554432)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile012Terms1
