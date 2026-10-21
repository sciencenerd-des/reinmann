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
namespace Reinmann.XiBand58.Tile000Terms1
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
  | 0 => ⟨((15/16), (4561/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4561/320))
  have he : value ((15/16), (4561/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-1050834769/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1142542751782409/9007199254740992), (56516361354317/4503599627370496)), (77763747/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1197062977/4294967296), (-118426455/4294967296)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((1315108097/4294967296), (130104759/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-1926391889/8589934592), (-190579583/8589934592)), (35/2147483648), by norm_num⟩
  | 4 => ⟨((1058178901/8589934592), (13085817/1073741824)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-1860045351/34359738368), (-23001983/4294967296)), (141/34359738368), by norm_num⟩
  | 6 => ⟨((681156227/34359738368), (67387363/34359738368)), (53/34359738368), by norm_num⟩
  | 7 => ⟨((-427615201/68719476736), (-169217337/274877906944)), (17/34359738368), by norm_num⟩
  | 8 => ⟨((1879133259/1099511627776), (92952123/549755813888)), (19/137438953472), by norm_num⟩
  | 9 => ⟨((-229382099/549755813888), (-45385931/1099511627776)), (151/4398046511104), by norm_num⟩
  | 10 => ⟨((806406377/8796093022208), (159556933/17592186044416)), (135/17592186044416), by norm_num⟩
  | 11 => ⟨((-1288622481/70368744177664), (-63742257/35184372088832)), (55/35184372088832), by norm_num⟩
  | 12 => ⟨((1887595325/562949953421312), (186741405/562949953421312)), (41/140737488355328), by norm_num⟩
  | 13 => ⟨((-638072437/1125899906842624), (-63125047/1125899906842624)), (113/2251799813685248), by norm_num⟩
  | 14 => ⟨((200284063/2251799813685248), (158514177/18014398509481984)), (9/1125899906842624), by norm_num⟩
  | 15 => ⟨((-938814007/72057594037927936), (-185755331/144115188075855872)), (171/144115188075855872), by norm_num⟩
  | 16 => ⟨((1031392605/576460752303423488), (102036545/576460752303423488)), (3/18014398509481984), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (8028156309/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222348970906105/79228162514264337593543950336), (152018182887/633825300114114700748351602688)), (11527/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889767767828307/39614081257132168796771975168), (85494857369/19807040628566084398385987584)), (1621/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889544524549185/2475880078570760549798248448), (22704800903/309485009821345068724781056)), (27557/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((27675169460497/2417851639229258349412352), (181595488049/154742504910672534362390528)), (55115/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549572399402153/9671406556917033397649408), (170200182773/9671406556917033397649408)), (51671/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258805361660595/604462909807314587353088), (2326243575/9444732965739290427392)), (45213/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58994352772529/2361183241434822606848), (241843920235/75557863725914323419136)), (287/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1297560009816721/4722366482869645213696), (45327059835/1180591620717411303424)), (55105/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405369145029279/147573952589676412928), (62294376119/147573952589676412928)), (151543/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455877624875569/18446744073709551616), (311290006031/73786976294838206464)), (189433/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822697656921783/9223372036854775808), (349951361713/9223372036854775808)), (1665/72057594037927936), by norm_num⟩
  | 6 => ⟨((1593946652948089/1152921504606846976), (43704908291/144115188075855872)), (106565/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194547005948613/144115188075855872), (152791813183/72057594037927936)), (46625/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491587863367685/36028797018963968), (228837457101/18014398509481984)), (69943/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489197672429085/9007199254740992), (570869830875/9007199254740992)), (174877/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227833784990451/4503599627370496), (569038320507/2251799813685248)), (349813/2251799813685248), by norm_num⟩
  | 1 => ⟨((2215946511403197/2251799813685248), (1697986794331/2251799813685248)), (1049745/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180474949104591/2251799813685248), (1679818344557/1125899906842624)), (525187/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2180474949104591/2251799813685248), (1679818344557/1125899906842624)), (2003429414989280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2111404258770649/2251799813685248), (6506443063175/2251799813685248)), (4074685/2251799813685248), by norm_num⟩
  | 2 => ⟨((1979743307136017/2251799813685248), (1525194592071/281474976710656)), (1916205/562949953421312), by norm_num⟩
  | 3 => ⟨((435122458526733/562949953421312), (21454793751251/2251799813685248)), (13560619/2251799813685248), by norm_num⟩
  | 4 => ⟨((672538592473219/1125899906842624), (33166225691973/2251799813685248)), (21221301/2251799813685248), by norm_num⟩
  | 5 => ⟨((200743048288297/562949953421312), (19811323021671/1125899906842624)), (51955097/4503599627370496), by norm_num⟩
  | 6 => ⟨((1142542751782409/9007199254740992), (56516361354317/4503599627370496)), (77763747/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1050834769/33554432)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-68826501/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((173603672473203/9007199254740992), (-512772581321713/4503599627370496)), (158594599/9007199254740992), by norm_num⟩
  | 1 => ⟨((-47652391/1073741824), (1126005651/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((109723685/2147483648), (-1296361913/4294967296)), (205/4294967296), by norm_num⟩
  | 3 => ⟨((-168432081/4294967296), (994994539/4294967296)), (159/4294967296), by norm_num⟩
  | 4 => ⟨((193914599/8589934592), (-1145529797/8589934592)), (185/8589934592), by norm_num⟩
  | 5 => ⟨((-89300973/8589934592), (527535967/8589934592)), (43/4294967296), by norm_num⟩
  | 6 => ⟨((274164119/68719476736), (-202449409/8589934592)), (133/34359738368), by norm_num⟩
  | 7 => ⟨((-90183745/68719476736), (532750847/68719476736)), (177/137438953472), by norm_num⟩
  | 8 => ⟨((207655747/549755813888), (-1226704159/549755813888)), (103/274877906944), by norm_num⟩
  | 9 => ⟨((-212508901/2199023255552), (1255373649/2199023255552)), (213/2199023255552), by norm_num⟩
  | 10 => ⟨((195727931/8796093022208), (-289060465/2199023255552)), (99/4398046511104), by norm_num⟩
  | 11 => ⟨((-163883715/35184372088832), (968125553/35184372088832)), (167/35184372088832), by norm_num⟩
  | 12 => ⟨((251570799/281474976710656), (-1486127645/281474976710656)), (259/281474976710656), by norm_num⟩
  | 13 => ⟨((-89117411/562949953421312), (263225797/281474976710656)), (185/1125899906842624), by norm_num⟩
  | 14 => ⟨((14657173/562949953421312), (-1385370963/9007199254740992)), (245/9007199254740992), by norm_num⟩
  | 15 => ⟨((-143997389/36028797018963968), (1701298415/72057594037927936)), (303/72057594037927936), by norm_num⟩
  | 16 => ⟨((165783121/288230376151711744), (-244836523/72057594037927936)), (177/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (-1827703017201/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889318507174565/316912650057057350374175801344), (-2162691445983/633825300114114700748351602688)), (92413/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889593562321405/39614081257132168796771975168), (-76017724819/1237940039285380274899124224)), (51989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944679643647537/1237940039285380274899124224), (-2584033299921/2475880078570760549798248448)), (110493/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442756361622753/38685626227668133590597632), (-2583392988681/154742504910672534362390528)), (110511/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549398416152619/9671406556917033397649408), (-2421250789465/9671406556917033397649408)), (103623/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258652954758055/604462909807314587353088), (-2117914520763/604462909807314587353088)), (90689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887571306140521/75557863725914323419136), (-1720168354025/37778931862957161709568)), (147405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648686870998801/2361183241434822606848), (-2579137903063/4722366482869645213696)), (110585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405305001502365/147573952589676412928), (-3544504211597/590295810358705651712)), (152105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823189099096917/73786976294838206464), (-4427916170521/73786976294838206464)), (190207/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911167572150757/4611686018427387904), (-4977676271147/9223372036854775808)), (107043/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796791485668917/576460752303423488), (-77703409077/18014398509481984)), (107109/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194227472810705/144115188075855872), (-4346155621079/144115188075855872)), (46897/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491105948649959/36028797018963968), (-813596938417/4503599627370496)), (70419/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488590721727493/9007199254740992), (-8117696450797/9007199254740992)), (352611/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226606287326745/4503599627370496), (-2022585961757/562949953421312)), (176693/1125899906842624), by norm_num⟩
  | 1 => ⟨((2214071538118143/2251799813685248), (-24134665449151/2251799813685248)), (1064047/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176591671183747/2251799813685248), (-1491445091223/70368744177664)), (1071855/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2176591671183747/2251799813685248), (-1491445091223/70368744177664)), (4088802341941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051441935474191/1125899906842624), (-92264456372501/2251799813685248)), (529387/281474976710656), by norm_num⟩
  | 2 => ⟨((980017810189335/1125899906842624), (-5385176670357/70368744177664)), (8257097/2251799813685248), by norm_num⟩
  | 3 => ⟨((1692887386857461/2251799813685248), (-299995067960365/2251799813685248)), (15638259/2251799813685248), by norm_num⟩
  | 4 => ⟨((308183552431067/562949953421312), (-451068397450837/2251799813685248)), (13840135/1125899906842624), by norm_num⟩
  | 5 => ⟨((1168994619012453/4503599627370496), (-987738681003147/4503599627370496)), (41396319/2251799813685248), by norm_num⟩
  | 6 => ⟨((173603672473203/9007199254740992), (-512772581321713/4503599627370496)), (158594599/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-68826501/2097152)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-1146806635/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-883364392493933/9007199254740992), (-88211388388247/2251799813685248)), (84349527/4503599627370496), by norm_num⟩
  | 1 => ⟨((1010043765/4294967296), (201722785/2147483648)), (195/4294967296), by norm_num⟩
  | 2 => ⟨((-1210989585/4294967296), (-483710113/4294967296)), (59/1073741824), by norm_num⟩
  | 3 => ⟨((967942067/4294967296), (386628731/4294967296)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((-1160511853/8589934592), (-463547603/8589934592)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((1113114355/17179869184), (222307721/8589934592)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((-444855275/17179869184), (-177690211/17179869184)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((1219104413/137438953472), (60868931/17179869184)), (249/137438953472), by norm_num⟩
  | 8 => ⟨((-1461642355/549755813888), (-72978661/68719476736)), (301/549755813888), by norm_num⟩
  | 9 => ⟨((389429477/549755813888), (311102553/1099511627776)), (81/549755813888), by norm_num⟩
  | 10 => ⟨((-1494097763/8796093022208), (-596793073/8796093022208)), (313/8796093022208), by norm_num⟩
  | 11 => ⟨((651398175/17592186044416), (16261901/1099511627776)), (275/35184372088832), by norm_num⟩
  | 12 => ⟨((-520661535/70368744177664), (-415939579/140737488355328)), (111/70368744177664), by norm_num⟩
  | 13 => ⟨((768302667/562949953421312), (306886015/562949953421312)), (83/281474976710656), by norm_num⟩
  | 14 => ⟨((-526374095/2251799813685248), (-420503157/4503599627370496)), (115/2251799813685248), by norm_num⟩
  | 15 => ⟨((1346335951/36028797018963968), (537772017/36028797018963968)), (37/4503599627370496), by norm_num⟩
  | 16 => ⟨((-807093153/144115188075855872), (-80595061/36028797018963968)), (179/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (-3597259139425/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222311512757923/79228162514264337593543950336), (-4255950823737/633825300114114700748351602688)), (92619/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889430163936077/39614081257132168796771975168), (-2393491687333/19807040628566084398385987584)), (3257/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1889185185201515/2475880078570760549798248448), (-9931642389/4835703278458516698824704)), (110769/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770850792171819/154742504910672534362390528), (-2541842991415/77371252455336267181195264)), (27701/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549234091416057/9671406556917033397649408), (-4764558748195/9671406556917033397649408)), (25979/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258508584781929/604462909807314587353088), (-2083796157933/302231454903657293676544)), (22741/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471833901878991/18889465931478580854784), (-6769719487333/75557863725914323419136)), (73943/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297196008812901/4722366482869645213696), (-5074999421149/4722366482869645213696)), (867/36893488147419103232), by norm_num⟩
  | 9 => ⟨((810487033033049/295147905179352825856), (-3487201861649/295147905179352825856)), (152691/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822879342289843/73786976294838206464), (-8712425833013/73786976294838206464)), (191013/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821983466990581/9223372036854775808), (-1224226409131/1152921504606846976)), (26887/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593227301034025/1152921504606846976), (-2446057793913/288230376151711744)), (26919/144115188075855872), by norm_num⟩
  | 5 => ⟨((298477945087997/36028797018963968), (-2137607763575/36028797018963968)), (188723/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490623475973337/36028797018963968), (-12804120115297/36028797018963968)), (17729/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487972059065935/9007199254740992), (-15967514843251/9007199254740992)), (88899/2251799813685248), by norm_num⟩
  | 2 => ⟨((556330624172569/1125899906842624), (-15911134055949/2251799813685248)), (357123/2251799813685248), by norm_num⟩
  | 1 => ⟨((8640744382803/8796093022208), (-2965750286239/140737488355328)), (269755/562949953421312), by norm_num⟩
  | 0 => ⟨((1086026889090257/1125899906842624), (-46890733213699/1125899906842624)), (68399/70368744177664), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1086026889090257/1125899906842624), (-46890733213699/1125899906842624)), (260921478539919831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1045613074315937/1125899906842624), (-90460256386455/1125899906842624)), (2202411/1125899906842624), by norm_num⟩
  | 2 => ⟨((240945850648027/281474976710656), (-84009623065783/562949953421312)), (277789/70368744177664), by norm_num⟩
  | 3 => ⟨((399968049809641/562949953421312), (-287652853958849/1125899906842624)), (2233963/281474976710656), by norm_num⟩
  | 4 => ⟨((247425901582083/562949953421312), (-817493280323577/2251799813685248)), (34527169/2251799813685248), by norm_num⟩
  | 5 => ⟨((138208540170261/2251799813685248), (-1437207770900923/4503599627370496)), (110840037/4503599627370496), by norm_num⟩
  | 6 => ⟨((-883364392493933/9007199254740992), (-88211388388247/2251799813685248)), (84349527/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-1146806635/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-594210153/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-71486256907259/1125899906842624), (664505174429823/9007199254740992)), (159816321/9007199254740992), by norm_num⟩
  | 1 => ⟨((677630139/4294967296), (-787369407/4294967296)), (191/4294967296), by norm_num⟩
  | 2 => ⟨((-841923819/4294967296), (978269737/4294967296)), (15/268435456), by norm_num⟩
  | 3 => ⟨((697367365/4294967296), (-810302991/4294967296)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((-866446401/8589934592), (1006763645/8589934592)), (63/2147483648), by norm_num⟩
  | 5 => ⟨((861215369/17179869184), (-500342735/8589934592)), (253/17179869184), by norm_num⟩
  | 6 => ⟨((-713346599/34359738368), (828869993/34359738368)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((506457059/68719476736), (-147118897/17179869184)), (19/8589934592), by norm_num⟩
  | 8 => ⟨((-629249257/274877906944), (731153451/274877906944)), (191/274877906944), by norm_num⟩
  | 9 => ⟨((694944739/1099511627776), (-25234001/34359738368)), (213/1099511627776), by norm_num⟩
  | 10 => ⟨((-690749121/4398046511104), (100326619/549755813888)), (213/4398046511104), by norm_num⟩
  | 11 => ⟨((39010161/1099511627776), (-181310751/4398046511104)), (97/8796093022208), by norm_num⟩
  | 12 => ⟨((-516995245/70368744177664), (150180097/17592186044416)), (81/35184372088832), by norm_num⟩
  | 13 => ⟨((790575337/562949953421312), (-114825699/70368744177664)), (125/281474976710656), by norm_num⟩
  | 14 => ⟨((-561287403/2251799813685248), (326092735/1125899906842624)), (45/562949953421312), by norm_num⟩
  | 15 => ⟨((5811445/140737488355328), (-54020667/1125899906842624)), (241/18014398509481984), by norm_num⟩
  | 16 => ⟨((-924217493/144115188075855872), (1073890517/144115188075855872)), (151/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (742953266639/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778369475724677/633825300114114700748351602688), (1757753133609/316912650057057350374175801344)), (92547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889292411209001/39614081257132168796771975168), (1977065416405/19807040628566084398385987584)), (104137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889039084297165/2475880078570760549798248448), (1050066090185/618970019642690137449562112)), (110671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770704985108875/154742504910672534362390528), (1049785001451/38685626227668133590597632)), (27675/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774548854656805/4835703278458516698824704), (491937427457/1208925819614629174706176)), (25953/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258389562250691/604462909807314587353088), (1721183991937/302231454903657293676544)), (90867/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887142780095947/75557863725914323419136), (5591609904015/75557863725914323419136)), (36929/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324262974742409/1180591620717411303424), (2095874906379/2361183241434822606848)), (55419/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620776744116033/590295810358705651712), (1440119043083/147573952589676412928)), (38121/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822633932012383/73786976294838206464), (7195827767993/73786976294838206464)), (23841/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455427271504211/2305843009213693952), (8088754708271/9223372036854775808)), (214739/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398238762118869/288230376151711744), (8080570858711/1152921504606846976)), (214951/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298418987231235/36028797018963968), (7061300320267/144115188075855872)), (94161/72057594037927936), by norm_num⟩
  | 4 => ⟨((745137247851991/18014398509481984), (10573571240379/36028797018963968)), (141481/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487544148217833/9007199254740992), (13184843399945/9007199254740992)), (354541/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224491508472451/4503599627370496), (13136748449329/2251799813685248)), (177901/1125899906842624), by norm_num⟩
  | 1 => ⟨((2210845779117809/2251799813685248), (9792593160815/562949953421312)), (536865/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169928710385509/2251799813685248), (38692432850865/1125899906842624)), (2172851/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2169928710385509/2251799813685248), (38692432850865/1125899906842624)), (8288768776900481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((522093722778521/562949953421312), (149142602122075/2251799813685248)), (4337045/2251799813685248), by norm_num⟩
  | 2 => ⟨((481733116738161/562949953421312), (138318541272735/1125899906842624)), (8619075/2251799813685248), by norm_num⟩
  | 3 => ⟨((807474233423407/1125899906842624), (473453255196365/2251799813685248)), (16868935/2251799813685248), by norm_num⟩
  | 4 => ⟨((1058664518589421/2251799813685248), (679103536607609/2251799813685248)), (31289739/2251799813685248), by norm_num⟩
  | 5 => ⟨((292916335403607/2251799813685248), (1277098993055623/4503599627370496)), (48294089/2251799813685248), by norm_num⟩
  | 6 => ⟨((-71486256907259/1125899906842624), (664505174429823/9007199254740992)), (159816321/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-594210153/16777216)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-1226701173/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((339223160831457/9007199254740992), (739213533628925/9007199254740992)), (223893575/18014398509481984), by norm_num⟩
  | 1 => ⟨((-51861419/536870912), (-452052421/2147483648)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((532087653/4294967296), (1159491567/4294967296)), (45/1073741824), by norm_num⟩
  | 3 => ⟨((-454925961/4294967296), (-991345717/4294967296)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((291715513/4294967296), (317843945/2147483648)), (101/4294967296), by norm_num⟩
  | 5 => ⟨((-299294207/8589934592), (-326101449/4294967296)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((511782989/34359738368), (139405617/4294967296)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((-187528207/34359738368), (-817299081/68719476736)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((240500177/137438953472), (1048165377/274877906944)), (175/274877906944), by norm_num⟩
  | 9 => ⟨((-548329577/1099511627776), (-597442469/549755813888)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((562575039/4398046511104), (612963871/2199023255552)), (105/2199023255552), by norm_num⟩
  | 11 => ⟨((-262359361/8796093022208), (-17866151/274877906944)), (99/8796093022208), by norm_num⟩
  | 12 => ⟨((224312825/35184372088832), (977616481/70368744177664)), (171/70368744177664), by norm_num⟩
  | 13 => ⟨((-11064443/8796093022208), (-385774887/140737488355328)), (137/281474976710656), by norm_num⟩
  | 14 => ⟨((518943743/2251799813685248), (1130849199/2251799813685248)), (203/2251799813685248), by norm_num⟩
  | 15 => ⟨((-22184407/562949953421312), (-193371395/2251799813685248)), (141/9007199254740992), by norm_num⟩
  | 16 => ⟨((113803761/18014398509481984), (991975671/72057594037927936)), (183/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (371429295167/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111141176129659/39614081257132168796771975168), (219663923549/79228162514264337593543950336)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889168224888531/39614081257132168796771975168), (988280968557/19807040628566084398385987584)), (103931/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888907534196867/2475880078570760549798248448), (1049790979785/1237940039285380274899124224)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770573882215427/154742504910672534362390528), (2099002707291/154742504910672534362390528)), (55227/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548975275185779/9671406556917033397649408), (1967199791963/9671406556917033397649408)), (51783/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314570726715191/151115727451828646838272), (1720684807481/604462909807314587353088)), (22659/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886970353951549/75557863725914323419136), (2794960168013/75557863725914323419136)), (147313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162115419543425/590295810358705651712), (2095212062673/4722366482869645213696)), (55255/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50643789349057/18446744073709551616), (2879279420799/590295810358705651712)), (18999/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911208232522755/36893488147419103232), (3596645167661/73786976294838206464)), (190051/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455366757313671/2305843009213693952), (4042854077363/9223372036854775808)), (213893/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199089528443141/144115188075855872), (4038643397883/1152921504606846976)), (13375/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193470612493379/144115188075855872), (441135180113/18014398509481984)), (93685/72057594037927936), by norm_num⟩
  | 4 => ⟨((186246716722973/4503599627370496), (5284172786603/36028797018963968)), (140647/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487180823345337/9007199254740992), (3294355168117/4503599627370496)), (176019/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111901276391585/2251799813685248), (3282006637835/1125899906842624)), (352671/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104952961452827/1125899906842624), (2446122928341/281474976710656)), (1061189/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084209688273603/1125899906842624), (38648306944467/2251799813685248)), (2135145/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1084209688273603/1125899906842624), (38648306944467/2251799813685248)), (8144931801802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087463047286997/2251799813685248), (18608611906751/562949953421312)), (4185461/2251799813685248), by norm_num⟩
  | 2 => ⟨((966329568984387/1125899906842624), (138004415776463/2251799813685248)), (8036717/2251799813685248), by norm_num⟩
  | 3 => ⟨((825145757232893/1125899906842624), (118445473531647/1125899906842624)), (7390239/1125899906842624), by norm_num⟩
  | 4 => ⟨((1184539027717527/2251799813685248), (347223689616099/2251799813685248)), (12387185/1125899906842624), by norm_num⟩
  | 5 => ⟨((71196849391351/281474976710656), (22831737150805/140737488355328)), (33705001/2251799813685248), by norm_num⟩
  | 6 => ⟨((339223160831457/9007199254740992), (739213533628925/9007199254740992)), (223893575/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1226701173/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-631071859/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1512097619303247/18014398509481984), (31942346231805/4503599627370496)), (102072253/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1902824547/8589934592), (-80392535/4294967296)), (131/8589934592), by norm_num⟩
  | 2 => ⟨((1255415767/4294967296), (53040127/2147483648)), (89/4294967296), by norm_num⟩
  | 3 => ⟨((-552185697/2147483648), (-93317291/4294967296)), (5/268435456), by norm_num⟩
  | 4 => ⟨((1457249711/8589934592), (15391855/1073741824)), (27/2147483648), by norm_num⟩
  | 5 => ⟨((-384576553/4294967296), (-129983961/17179869184)), (29/4294967296), by norm_num⟩
  | 6 => ⟨((676613047/17179869184), (57172521/17179869184)), (13/4294967296), by norm_num⟩
  | 7 => ⟨((-63772165/4294967296), (-86218035/68719476736)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((1346387195/274877906944), (113767169/274877906944)), (27/68719476736), by norm_num⟩
  | 9 => ⟨((-789598443/549755813888), (-133439147/1099511627776)), (129/1099511627776), by norm_num⟩
  | 10 => ⟨((833518223/2199023255552), (8803839/274877906944)), (139/4398046511104), by norm_num⟩
  | 11 => ⟨((-799891773/8796093022208), (-135178681/17592186044416)), (17/2199023255552), by norm_num⟩
  | 12 => ⟨((1407306831/70368744177664), (118914763/70368744177664)), (61/35184372088832), by norm_num⟩
  | 13 => ⟨((-1142757971/281474976710656), (-96560885/281474976710656)), (101/281474976710656), by norm_num⟩
  | 14 => ⟨((215414557/281474976710656), (72808489/1125899906842624)), (155/2251799813685248), by norm_num⟩
  | 15 => ⟨((-303195395/2251799813685248), (-102477747/9007199254740992)), (111/9007199254740992), by norm_num⟩
  | 16 => ⟨((1600300059/72057594037927936), (135222325/72057594037927936)), (149/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (54903687041/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778153425682769/633825300114114700748351602688), (129865639131/633825300114114700748351602688)), (92213/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889049775126037/39614081257132168796771975168), (146067602739/39614081257132168796771975168)), (103741/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944390916945607/1237940039285380274899124224), (77578840119/1237940039285380274899124224)), (55113/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442612088347785/38685626227668133590597632), (19389207493/19342813113834066795298816)), (110227/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548857773991625/9671406556917033397649408), (145372302309/9671406556917033397649408)), (103339/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258180275259005/604462909807314587353088), (31788507631/151115727451828646838272)), (90423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943401959227167/37778931862957161709568), (206537715607/75557863725914323419136)), (146939/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296798827685679/4722366482869645213696), (154826692935/4722366482869645213696)), (110207/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620430515908307/590295810358705651712), (212762317029/590295810358705651712)), (151537/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822203760499551/73786976294838206464), (265766456013/73786976294838206464)), (94713/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821228731342201/9223372036854775808), (298731132283/9223372036854775808)), (213111/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592479170720395/1152921504606846976), (149205652751/576460752303423488)), (1665/9007199254740992), by norm_num⟩
  | 5 => ⟨((1193264580852523/144115188075855872), (260750549517/144115188075855872)), (93245/72057594037927936), by norm_num⟩
  | 4 => ⟨((186208433080211/4503599627370496), (390408292885/36028797018963968)), (139877/18014398509481984), by norm_num⟩
  | 3 => ⟨((743401415685997/4503599627370496), (486757278689/9007199254740992)), (10929/281474976710656), by norm_num⟩
  | 2 => ⟨((2223061031986947/4503599627370496), (30305176343/140737488355328)), (174891/1125899906842624), by norm_num⟩
  | 1 => ⟨((2208829554763667/2251799813685248), (1445312296225/2251799813685248)), (1049629/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166408830862319/2251799813685248), (2853495830495/2251799813685248)), (2100439/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2166408830862319/2251799813685248), (2853495830495/2251799813685248)), (8012538918502043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084252361811327/2251799813685248), (5490575608403/2251799813685248)), (1011725/562949953421312), by norm_num⟩
  | 2 => ⟨((241144757567623/281474976710656), (10164087508995/2251799813685248)), (7511309/2251799813685248), by norm_num⟩
  | 3 => ⟨((826349547428187/1125899906842624), (8707759556091/1125899906842624)), (12937961/2251799813685248), by norm_num⟩
  | 4 => ⟨((1212856925040531/2251799813685248), (25564095438885/2251799813685248)), (4797913/562949953421312), by norm_num⟩
  | 5 => ⟨((1305949479795711/4503599627370496), (55076992185563/4503599627370496)), (5277411/562949953421312), by norm_num⟩
  | 6 => ⟨((1512097619303247/18014398509481984), (31942346231805/4503599627370496)), (102072253/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-631071859/16777216)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-323784985/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((885243515504855/18014398509481984), (-139176253515957/2251799813685248)), (43473585/4503599627370496), by norm_num⟩
  | 1 => ⟨((-71444627/536870912), (718872607/4294967296)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((386951273/2147483648), (-486685777/2147483648)), (39/1073741824), by norm_num⟩
  | 3 => ⟨((-349294491/2147483648), (109830793/536870912)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((118238377/1073741824), (-297427301/2147483648)), (49/2147483648), by norm_num⟩
  | 5 => ⟨((-512312737/8589934592), (322179225/4294967296)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((924912407/34359738368), (-1163303353/34359738368)), (197/34359738368), by norm_num⟩
  | 7 => ⟨((-89453901/8589934592), (225020277/17179869184)), (155/68719476736), by norm_num⟩
  | 8 => ⟨((484491309/137438953472), (-304683103/68719476736)), (107/137438953472), by norm_num⟩
  | 9 => ⟨((-72890377/68719476736), (366709839/274877906944)), (131/549755813888), by norm_num⟩
  | 10 => ⟨((2467385/8589934592), (-397227461/1099511627776)), (9/137438953472), by norm_num⟩
  | 11 => ⟨((-77751883/1099511627776), (782335931/8796093022208)), (9/549755813888), by norm_num⟩
  | 12 => ⟨((561482673/35184372088832), (-353100829/17592186044416)), (33/8796093022208), by norm_num⟩
  | 13 => ⟨((-935706625/281474976710656), (588439859/140737488355328)), (111/140737488355328), by norm_num⟩
  | 14 => ⟨((180995751/281474976710656), (-455292765/562949953421312)), (87/562949953421312), by norm_num⟩
  | 15 => ⟨((-8169093/70368744177664), (328788177/2251799813685248)), (127/4503599627370496), by norm_num⟩
  | 16 => ⟨((353957023/18014398509481984), (-890374889/36028797018963968)), (87/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-146391761063/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444513191831881/158456325028528675187087900672), (-1384914558673/633825300114114700748351602688)), (92337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472234125655623/9903520314283042199192993792), (-194710828003/4951760157141521099596496896)), (6493/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888661437550557/2475880078570760549798248448), (-827306780649/1237940039285380274899124224)), (110391/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770327907284053/154742504910672534362390528), (-1654131745353/154742504910672534362390528)), (110403/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774372401472421/4835703278458516698824704), (-1550236772211/9671406556917033397649408)), (103515/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081372834131/604462909807314587353088), (-677972825439/302231454903657293676544)), (22647/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117915193951469/4722366482869645213696), (-550613257183/18889465931478580854784)), (147227/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81042383122089/295147905179352825856), (-412750351043/1180591620717411303424)), (110441/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202533052065281/73786976294838206464), (-2268765436033/590295810358705651712)), (9493/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455498981673593/18446744073709551616), (-1416958021727/36893488147419103232)), (47477/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455248657713211/2305843009213693952), (-796337983885/2305843009213693952)), (106857/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592244711961869/1152921504606846976), (-1590925522809/576460752303423488)), (213799/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193059027832467/144115188075855872), (-2780186145087/144115188075855872)), (187169/144115188075855872), by norm_num⟩
  | 4 => ⟨((744679167753397/18014398509481984), (-2081212307461/18014398509481984)), (280943/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486415028739913/9007199254740992), (-5189313152069/9007199254740992)), (351511/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111140642674319/2251799813685248), (-5168792491215/2251799813685248)), (88003/562949953421312), by norm_num⟩
  | 1 => ⟨((2207649693793033/2251799813685248), (-120345027413/17592186044416)), (529277/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082004407669603/1125899906842624), (-30401799145307/2251799813685248)), (2127243/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1082004407669603/1125899906842624), (-30401799145307/2251799813685248)), (8114788064009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129951879353899/140737488355328), (-58433046270615/2251799813685248)), (4146057/2251799813685248), by norm_num⟩
  | 2 => ⟨((479592283852057/562949953421312), (-107909900453361/2251799813685248)), (7871813/2251799813685248), by norm_num⟩
  | 3 => ⟨((1629139309265363/2251799813685248), (-183862722766561/2251799813685248)), (14166881/2251799813685248), by norm_num⟩
  | 4 => ⟨((1163642243971137/2251799813685248), (-33255397232375/281474976710656)), (11406247/1125899906842624), by norm_num⟩
  | 5 => ⟨((1139785421128241/4503599627370496), (-68740364617583/562949953421312)), (57935329/4503599627370496), by norm_num⟩
  | 6 => ⟨((885243515504855/18014398509481984), (-139176253515957/2251799813685248)), (43473585/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-323784985/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile000Terms1
