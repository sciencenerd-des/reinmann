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
namespace Reinmann.XiBand97.Tile061Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨61,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79951/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79951/2560))
  have he : value ((69/80), (79951/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-73681465113/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((596029222757841/4503599627370496), (320850569647735/4503599627370496)), (3961289/9007199254740992), by norm_num⟩
  | 1 => ⟨((-79932254459/274877906944), (-21514305337/137438953472)), (67/68719476736), by norm_num⟩
  | 2 => ⟨((43907278505/137438953472), (47271760451/274877906944)), (297/274877906944), by norm_num⟩
  | 3 => ⟨((-32158050485/137438953472), (-17311112313/137438953472)), (55/68719476736), by norm_num⟩
  | 4 => ⟨((70658458885/549755813888), (38036401435/549755813888)), (61/137438953472), by norm_num⟩
  | 5 => ⟨((-7762625123/137438953472), (-33429806427/1099511627776)), (217/1099511627776), by norm_num⟩
  | 6 => ⟨((5685410235/274877906944), (24484264099/2199023255552)), (161/2199023255552), by norm_num⟩
  | 7 => ⟨((-14276712115/2199023255552), (-7685346691/2199023255552)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((62738285485/35184372088832), (16886432635/17592186044416)), (227/35184372088832), by norm_num⟩
  | 9 => ⟨((-61266712359/140737488355328), (-4122587201/17592186044416)), (7/4398046511104), by norm_num⟩
  | 10 => ⟨((53846690467/562949953421312), (28986399745/562949953421312)), (199/562949953421312), by norm_num⟩
  | 11 => ⟨((-86046015783/4503599627370496), (-46319730857/4503599627370496)), (321/4503599627370496), by norm_num⟩
  | 12 => ⟨((63020806887/18014398509481984), (2120309397/1125899906842624)), (119/9007199254740992), by norm_num⟩
  | 13 => ⟨((-85212840477/144115188075855872), (-45871221353/144115188075855872)), (325/144115188075855872), by norm_num⟩
  | 14 => ⟨((13373696243/144115188075855872), (28796964271/576460752303423488)), (103/288230376151711744), by norm_num⟩
  | 15 => ⟨((-62688030027/4611686018427387904), (-33745812079/4611686018427387904)), (61/1152921504606846976), by norm_num⟩
  | 16 => ⟨((17217460035/9223372036854775808), (37073563841/36893488147419103232)), (135/18446744073709551616), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (643264267541/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045548814027/633825300114114700748351602688), (761495352665/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29532081339169/618970019642690137449562112), (856539921471/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472461929787503/618970019642690137449562112), (909897746617/2475880078570760549798248448)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771513946577525/154742504910672534362390528), (909699901431/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549856457387475/9671406556917033397649408), (426316753315/4835703278458516698824704)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053813138403/604462909807314587353088), (372922117171/302231454903657293676544)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236027854543771/9444732965739290427392), (1211603115709/75557863725914323419136)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648931253929129/2361183241434822606848), (454178967295/2361183241434822606848)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621892250735427/590295810358705651712), (1248432773125/590295810358705651712)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824029691783719/73786976294838206464), (1559702352347/73786976294838206464)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911640602111951/4611686018427387904), (1753512809401/9223372036854775808)), (3335/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594529520942019/1152921504606846976), (219009190419/144115188075855872)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((597528126098345/72057594037927936), (1531446695681/144115188075855872)), (5839/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492350208681135/36028797018963968), (286742332987/4503599627370496)), (4381/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490147942437197/9007199254740992), (1430888584011/4503599627370496)), (5479/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229726361937575/4503599627370496), (5706650805613/4503599627370496)), (5483/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218765545366151/2251799813685248), (4258919739381/1125899906842624)), (8235/562949953421312), by norm_num⟩
  | 0 => ⟨((2186034146917531/2251799813685248), (16867862649187/2251799813685248)), (66053/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2186034146917531/2251799813685248), (16867862649187/2251799813685248)), (251972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1061031433091465/1125899906842624), (16375222838433/1125899906842624)), (64619/1125899906842624), by norm_num⟩
  | 2 => ⟨((999662178888911/1125899906842624), (61727072006529/2251799813685248)), (15459/140737488355328), by norm_num⟩
  | 3 => ⟨((1773464777781265/2251799813685248), (54806132342193/1125899906842624)), (452785/2251799813685248), by norm_num⟩
  | 4 => ⟨((695701822697517/1125899906842624), (86328051654137/1125899906842624)), (94661/281474976710656), by norm_num⟩
  | 5 => ⟨((52907510994765/140737488355328), (426741897894861/4503599627370496)), (525999/1125899906842624), by norm_num⟩
  | 6 => ⟨((596029222757841/4503599627370496), (320850569647735/4503599627370496)), (3961289/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-73681465113/1073741824)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-9651826499/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1163393764758371/9007199254740992), (-417986415316173/9007199254740992)), (848007/1125899906842624), by norm_num⟩
  | 1 => ⟨((40875444641/137438953472), (3671452671/34359738368)), (479/274877906944), by norm_num⟩
  | 2 => ⟨((-94119189499/274877906944), (-33815328759/274877906944)), (277/137438953472), by norm_num⟩
  | 3 => ⟨((4514946723/17179869184), (6488555993/68719476736)), (427/274877906944), by norm_num⟩
  | 4 => ⟨((-2599012255/17179869184), (-29880904609/549755813888)), (247/274877906944), by norm_num⟩
  | 5 => ⟨((38300459999/549755813888), (27521330207/1099511627776)), (457/1099511627776), by norm_num⟩
  | 6 => ⟨((-3674586177/137438953472), (-10561700779/1099511627776)), (11/68719476736), by norm_num⟩
  | 7 => ⟨((77358147237/8796093022208), (27793388309/8796093022208)), (465/8796093022208), by norm_num⟩
  | 8 => ⟨((-22265464581/8796093022208), (-15999160401/17592186044416)), (269/17592186044416), by norm_num⟩
  | 9 => ⟨((91143336591/140737488355328), (32746158435/140737488355328)), (553/140737488355328), by norm_num⟩
  | 10 => ⟨((-1311658051/8796093022208), (-15080163253/281474976710656)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((8786048801/281474976710656), (25253352077/2251799813685248)), (431/2251799813685248), by norm_num⟩
  | 12 => ⟨((-53948333321/9007199254740992), (-19382664013/9007199254740992)), (333/9007199254740992), by norm_num⟩
  | 13 => ⟨((19110865861/18014398509481984), (3433094863/9007199254740992)), (237/36028797018963968), by norm_num⟩
  | 14 => ⟨((-100581473933/576460752303423488), (-18068555553/288230376151711744)), (627/576460752303423488), by norm_num⟩
  | 15 => ⟨((7719913417/288230376151711744), (22189006223/2305843009213693952)), (387/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-17775757553/4611686018427387904), (-25546037479/18446744073709551616)), (7/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-3642978649449/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889447895267669/316912650057057350374175801344), (-4311906518415/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((118117763007723/2475880078570760549798248448), (-4850025603939/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944833741912883/1237940039285380274899124224), (-5152105293023/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771332951998045/154742504910672534362390528), (-2575463764151/77371252455336267181195264)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549685968766487/9671406556917033397649408), (-4827743314953/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258903829961289/604462909807314587353088), (-2111512153037/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887977604332663/75557863725914323419136), (-6860069010705/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20276207255747/73786976294838206464), (-2571499886569/2361183241434822606848)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621635399049303/590295810358705651712), (-7068290805859/590295810358705651712)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455926354576351/18446744073709551616), (-4415181861945/36893488147419103232)), (5971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455727997698347/2305843009213693952), (-9927286180135/9223372036854775808)), (1681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199269351242397/144115188075855872), (-9918697463619/1152921504606846976)), (1683/288230376151711744), by norm_num⟩
  | 5 => ⟨((298680552134655/36028797018963968), (-8669201483033/144115188075855872)), (5899/144115188075855872), by norm_num⟩
  | 4 => ⟨((186479604148887/4503599627370496), (-12984493427413/36028797018963968)), (8867/36028797018963968), by norm_num⟩
  | 3 => ⟨((372371188711861/2251799813685248), (-16196846259161/9007199254740992)), (2779/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114167939336345/2251799813685248), (-2018278799487/281474976710656)), (2791/562949953421312), by norm_num⟩
  | 1 => ⟨((138532536626401/140737488355328), (-24092946498641/1125899906842624)), (8433/562949953421312), by norm_num⟩
  | 0 => ⟨((272614185810935/281474976710656), (-47681146582491/1125899906842624)), (34217/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272614185810935/281474976710656), (-47681146582491/1125899906842624)), (130527500632857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131763757365713/140737488355328), (-46180151095561/562949953421312)), (69179/1125899906842624), by norm_num⟩
  | 2 => ⟨((979321149425797/1125899906842624), (-172942413430163/1125899906842624)), (140887/1125899906842624), by norm_num⟩
  | 3 => ⟨((825260602388069/1125899906842624), (-300854742194365/1125899906842624)), (288373/1125899906842624), by norm_num⟩
  | 4 => ⟨((524506203761171/1125899906842624), (-110260052543611/281474976710656)), (576857/1125899906842624), by norm_num⟩
  | 5 => ⟨((71578557119911/1125899906842624), (-821843309298581/2251799813685248)), (1978799/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1163393764758371/9007199254740992), (-417986415316173/9007199254740992)), (848007/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-9651826499/134217728)), (1/536870912), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-20102683029/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((15528216147451/140737488355328), (555755170288955/9007199254740992)), (3379687/9007199254740992), by norm_num⟩
  | 1 => ⟨((-72724679873/274877906944), (-20334513789/137438953472)), (125/137438953472), by norm_num⟩
  | 2 => ⟨((87193083041/274877906944), (48760034489/274877906944)), (151/137438953472), by norm_num⟩
  | 3 => ⟨((-69693293881/274877906944), (-19486909367/137438953472)), (61/68719476736), by norm_num⟩
  | 4 => ⟨((83558609971/549755813888), (11681891963/137438953472)), (295/549755813888), by norm_num⟩
  | 5 => ⟨((-20036479585/274877906944), (-44819125625/1099511627776)), (143/549755813888), by norm_num⟩
  | 6 => ⟨((500472705/17179869184), (35823856489/2199023255552)), (231/2199023255552), by norm_num⟩
  | 7 => ⟨((-43888681453/4398046511104), (-24543387465/4398046511104)), (319/8796093022208), by norm_num⟩
  | 8 => ⟨((52620230893/17592186044416), (14713118195/8796093022208)), (193/17592186044416), by norm_num⟩
  | 9 => ⟨((-14019755879/17592186044416), (-31360459171/70368744177664)), (13/4398046511104), by norm_num⟩
  | 10 => ⟨((53788650157/281474976710656), (30079638719/281474976710656)), (101/140737488355328), by norm_num⟩
  | 11 => ⟨((-11725413631/281474976710656), (-26228299451/1125899906842624)), (89/562949953421312), by norm_num⟩
  | 12 => ⟨((74976837113/9007199254740992), (41928476845/9007199254740992)), (287/9007199254740992), by norm_num⟩
  | 13 => ⟨((-6914869357/4503599627370496), (-7733853571/9007199254740992)), (107/18014398509481984), by norm_num⟩
  | 14 => ⟨((37899731527/144115188075855872), (10597126239/72057594037927936)), (37/36028797018963968), by norm_num⟩
  | 15 => ⟨((-48469113103/1152921504606846976), (-27104852175/1152921504606846976)), (191/1152921504606846976), by norm_num⟩
  | 16 => ⟨((58111928593/9223372036854775808), (16248649225/4611686018427387904)), (231/9223372036854775808), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (332096688349/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889389337113753/316912650057057350374175801344), (786046676701/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889753022799179/39614081257132168796771975168), (884142789923/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889528837774395/2475880078570760549798248448), (58700222711/154742504910672534362390528)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885597568006989/77371252455336267181195264), (234745181283/38685626227668133590597632)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774778823850597/4835703278458516698824704), (880057737535/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629396214928285/302231454903657293676544), (192453477653/151115727451828646838272)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798229455641/75557863725914323419136), (1250504136837/75557863725914323419136)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648772087979431/2361183241434822606848), (937490243467/4722366482869645213696)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621454744596893/590295810358705651712), (161052392759/73786976294838206464)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455870777320625/18446744073709551616), (201197448497/9223372036854775808)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455666677845533/2305843009213693952), (1809479502321/9223372036854775808)), (6671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796957771647073/576460752303423488), (1807858982743/1152921504606846976)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194519600803545/144115188075855872), (790027722989/72057594037927936)), (365/9007199254740992), by norm_num⟩
  | 4 => ⟨((1491546388329205/36028797018963968), (591611409307/9007199254740992)), (4381/18014398509481984), by norm_num⟩
  | 3 => ⟨((744572594116295/4503599627370496), (1475851071197/4503599627370496)), (10959/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113863452514249/2251799813685248), (5884382603885/4503599627370496)), (21935/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107890723055655/1125899906842624), (8779169981055/2251799813685248)), (16473/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180126037621949/2251799813685248), (2171202908865/281474976710656)), (66071/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180126037621949/2251799813685248), (2171202908865/281474976710656)), (252040871627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((263824952778913/281474976710656), (33633511936963/2251799813685248)), (32239/562949953421312), by norm_num⟩
  | 2 => ⟨((494437774305213/562949953421312), (31524506377985/1125899906842624)), (30699/281474976710656), by norm_num⟩
  | 3 => ⟨((1735289345349847/2251799813685248), (55375816890551/1125899906842624)), (445159/2251799813685248), by norm_num⟩
  | 4 => ⟨((166475899049363/281474976710656), (170695573303123/2251799813685248)), (364945/1125899906842624), by norm_num⟩
  | 5 => ⟨((387373115577797/1125899906842624), (100956395348049/1125899906842624)), (60877/140737488355328), by norm_num⟩
  | 6 => ⟨((15528216147451/140737488355328), (555755170288955/9007199254740992)), (3379687/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-20102683029/268435456)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-83328561183/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-314036641767939/4503599627370496), (-849316295027173/9007199254740992)), (5975607/9007199254740992), by norm_num⟩
  | 1 => ⟨((47628890345/274877906944), (64406485269/274877906944)), (455/274877906944), by norm_num⟩
  | 2 => ⟨((-29588336585/137438953472), (-10002756471/34359738368)), (71/34359738368), by norm_num⟩
  | 3 => ⟨((24508084779/137438953472), (8285305357/34359738368)), (473/274877906944), by norm_num⟩
  | 4 => ⟨((-30450151421/274877906944), (-20588210377/137438953472)), (37/34359738368), by norm_num⟩
  | 5 => ⟨((30266313501/549755813888), (40927824699/549755813888)), (37/68719476736), by norm_num⟩
  | 6 => ⟨((-25069654561/1099511627776), (-33900607919/1099511627776)), (493/2199023255552), by norm_num⟩
  | 7 => ⟨((35597572187/4398046511104), (24068527443/2199023255552)), (11/137438953472), by norm_num⟩
  | 8 => ⟨((-22114160961/8796093022208), (-29904021947/8796093022208)), (439/17592186044416), by norm_num⟩
  | 9 => ⟨((24422944723/35184372088832), (66052180437/70368744177664)), (487/70368744177664), by norm_num⟩
  | 10 => ⟨((-6068873775/35184372088832), (-65653400961/281474976710656)), (243/140737488355328), by norm_num⟩
  | 11 => ⟨((21935396073/562949953421312), (59324571865/1125899906842624)), (221/562949953421312), by norm_num⟩
  | 12 => ⟨((-36338274379/4503599627370496), (-49138674375/4503599627370496)), (23/281474976710656), by norm_num⟩
  | 13 => ⟨((55567519783/36028797018963968), (18785387495/9007199254740992)), (283/18014398509481984), by norm_num⟩
  | 14 => ⟨((-19725728489/72057594037927936), (-53348496349/144115188075855872)), (101/36028797018963968), by norm_num⟩
  | 15 => ⟨((52284366821/1152921504606846976), (70701884445/1152921504606846976)), (269/576460752303423488), by norm_num⟩
  | 16 => ⟨((-32480442699/4611686018427387904), (-43921895703/4611686018427387904)), (21/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-2875575729917/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778657120784601/633825300114114700748351602688), (-1701354509677/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59050499037685/1237940039285380274899124224), (-3827319750691/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889382816958959/2475880078570760549798248448), (-15881394187/9671406556917033397649408)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110690541503025/9671406556917033397649408), (-508079435349/19342813113834066795298816)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774709925607197/4835703278458516698824704), (-952382993421/2417851639229258349412352)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258671379280543/604462909807314587353088), (-1666138470323/302231454903657293676544)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887600625584389/75557863725914323419136), (-2706478220027/37778931862957161709568)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648697594619537/2361183241434822606848), (-4057973482249/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621248615623123/590295810358705651712), (-697110100249/73786976294838206464)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823223542280301/73786976294838206464), (-6966853677411/73786976294838206464)), (745/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911186041108213/4611686018427387904), (-3915936603133/4611686018427387904)), (3355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398404412502675/288230376151711744), (-7824581067269/1152921504606846976)), (1679/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194255280620795/144115188075855872), (-854788842671/18014398509481984)), (1471/36028797018963968), by norm_num⟩
  | 4 => ⟨((372785650583773/9007199254740992), (-10241085638129/36028797018963968)), (1105/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488627718790003/9007199254740992), (-6386362385923/4503599627370496)), (11075/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113326973545043/2251799813685248), (-12729843474119/2251799813685248)), (11113/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107038815432773/1125899906842624), (-2373474613935/140737488355328)), (16765/1125899906842624), by norm_num⟩
  | 0 => ⟨((2176344893629445/2251799813685248), (-75098261173723/2251799813685248)), (4239/140737488355328), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176344893629445/2251799813685248), (-75098261173723/2251799813685248)), (16170502245855287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((65653556857665/70368744177664), (-1134090857515/17592186044416)), (33907/562949953421312), by norm_num⟩
  | 2 => ⟨((1950780158446407/2251799813685248), (-16929584170525/140737488355328)), (33821/281474976710656), by norm_num⟩
  | 3 => ⟨((207177100842745/281474976710656), (-3666611113685/17592186044416)), (533893/2251799813685248), by norm_num⟩
  | 4 => ⟨((561054173807937/1125899906842624), (-345443304673175/1125899906842624)), (504243/1125899906842624), by norm_num⟩
  | 5 => ⟨((347190204059769/2251799813685248), (-86069999083845/281474976710656)), (202991/281474976710656), by norm_num⟩
  | 6 => ⟨((-314036641767939/4503599627370496), (-849316295027173/9007199254740992)), (5975607/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-83328561183/1073741824)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-43006351865/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9937348470683/18014398509481984), (123230475965281/1125899906842624)), (9947663/18014398509481984), by norm_num⟩
  | 1 => ⟨((388928155/274877906944), (-4822996981/17179869184)), (391/274877906944), by norm_num⟩
  | 2 => ⟨((-498790511/274877906944), (24741486015/68719476736)), (63/34359738368), by norm_num⟩
  | 3 => ⟨((426457467/274877906944), (-84614211543/274877906944)), (433/274877906944), by norm_num⟩
  | 4 => ⟨((-546920903/549755813888), (108515583765/549755813888)), (557/549755813888), by norm_num⟩
  | 5 => ⟨((561129767/1099511627776), (-55667395371/549755813888)), (287/549755813888), by norm_num⟩
  | 6 => ⟨((-239878239/1099511627776), (95189366659/2199023255552)), (493/2199023255552), by norm_num⟩
  | 7 => ⟨((87896505/1099511627776), (-69758829957/4398046511104)), (363/4398046511104), by norm_num⟩
  | 8 => ⟨((-56362521/2199023255552), (44731966519/8796093022208)), (467/17592186044416), by norm_num⟩
  | 9 => ⟨((514016043/70368744177664), (-25496717507/17592186044416)), (267/35184372088832), by norm_num⟩
  | 10 => ⟨((-8240157/4398046511104), (26159115675/70368744177664)), (275/140737488355328), by norm_num⟩
  | 11 => ⟨((491882715/1125899906842624), (-97595355553/1125899906842624)), (515/1125899906842624), by norm_num⟩
  | 12 => ⟨((-210275709/2251799813685248), (41721190753/2251799813685248)), (221/2251799813685248), by norm_num⟩
  | 13 => ⟨((165952783/9007199254740992), (-65853994717/18014398509481984)), (175/9007199254740992), by norm_num⟩
  | 14 => ⟨((-486469125/144115188075855872), (96521235107/144115188075855872)), (515/144115188075855872), by norm_num⟩
  | 15 => ⟨((41592289/72057594037927936), (-132038442651/1152921504606846976)), (707/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-106682115/1152921504606846976), (21166994915/1152921504606846976)), (455/4611686018427387904), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (2052702731437/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778553753842075/633825300114114700748351602688), (2428715098559/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944749937823987/19807040628566084398385987584), (2731774029847/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889259719185723/2475880078570760549798248448), (725463643915/618970019642690137449562112)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885462924577233/77371252455336267181195264), (1450558776521/77371252455336267181195264)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((774652506314725/4835703278458516698824704), (2719014840037/9671406556917033397649408)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314642798923275/151115727451828646838272), (2378355367205/604462909807314587353088)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471859597412255/18889465931478580854784), (965840147595/18889465931478580854784)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648637001974987/2361183241434822606848), (2896237448563/4722366482869645213696)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202635347998943/73786976294838206464), (3980242613835/590295810358705651712)), (4757/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455754362133695/18446744073709551616), (2486089589067/36893488147419103232)), (1487/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455535467166951/2305843009213693952), (2794704379563/4611686018427387904)), (6695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49793421418957/36028797018963968), (5584046946039/1152921504606846976)), (6699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194057936917039/144115188075855872), (2440007409713/72057594037927936)), (1467/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490851175599573/36028797018963968), (3653992077497/18014398509481984)), (8811/36028797018963968), by norm_num⟩
  | 3 => ⟨((93016964951917/562949953421312), (9113946029971/9007199254740992)), (1379/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112982646728621/2251799813685248), (18164919283555/4503599627370496)), (11059/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213104043727723/2251799813685248), (27090400316219/2251799813685248)), (1041/70368744177664), by norm_num⟩
  | 0 => ⟨((1087316538796947/1125899906842624), (53555600825199/2251799813685248)), (67171/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087316538796947/1125899906842624), (53555600825199/2251799813685248)), (256237038619231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098837024082975/2251799813685248), (51720308500377/1125899906842624)), (66467/1125899906842624), by norm_num⟩
  | 2 => ⟨((1951513125504781/2251799813685248), (192827972927007/2251799813685248)), (130011/1125899906842624), by norm_num⟩
  | 3 => ⟨((837379244139469/1125899906842624), (83556788184399/562949953421312)), (123807/562949953421312), by norm_num⟩
  | 4 => ⟨((1195980294548381/2251799813685248), (248578829103159/1125899906842624)), (883655/2251799813685248), by norm_num⟩
  | 5 => ⟨((1050895484264595/4503599627370496), (1056205367608555/4503599627370496)), (2657697/4503599627370496), by norm_num⟩
  | 6 => ⟨((-9937348470683/18014398509481984), (123230475965281/1125899906842624)), (9947663/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-43006351865/536870912)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5531114473/67108864)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((170951570649461/2251799813685248), (-622647317024653/9007199254740992)), (1602931/4503599627370496), by norm_num⟩
  | 1 => ⟨((-55072143009/274877906944), (50146544365/274877906944)), (261/274877906944), by norm_num⟩
  | 2 => ⟨((18167317833/68719476736), (-33084901365/137438953472)), (87/68719476736), by norm_num⟩
  | 3 => ⟨((-31963062191/137438953472), (29104317149/137438953472)), (77/68719476736), by norm_num⟩
  | 4 => ⟨((5272022097/34359738368), (-9600995187/68719476736)), (205/274877906944), by norm_num⟩
  | 5 => ⟨((-22261069691/274877906944), (316719709/4294967296)), (109/274877906944), by norm_num⟩
  | 6 => ⟨((9791373189/274877906944), (-8915642341/274877906944)), (97/549755813888), by norm_num⟩
  | 7 => ⟨((-59062846129/4398046511104), (53780322899/4398046511104)), (147/2199023255552), by norm_num⟩
  | 8 => ⟨((19483779623/4398046511104), (-17741169417/4398046511104)), (49/2199023255552), by norm_num⟩
  | 9 => ⟨((-22852805077/17592186044416), (20808872527/17592186044416)), (29/4398046511104), by norm_num⟩
  | 10 => ⟨((48247890193/140737488355328), (-43932646051/140737488355328)), (247/140737488355328), by norm_num⟩
  | 11 => ⟨((-2893839733/35184372088832), (42160280571/562949953421312)), (239/562949953421312), by norm_num⟩
  | 12 => ⟨((40730714443/2251799813685248), (-37087799153/2251799813685248)), (53/562949953421312), by norm_num⟩
  | 13 => ⟨((-33074058613/9007199254740992), (60231894273/18014398509481984)), (347/18014398509481984), by norm_num⟩
  | 14 => ⟨((49876763887/72057594037927936), (-22707917437/36028797018963968)), (33/9007199254740992), by norm_num⟩
  | 15 => ⟨((-35100703817/288230376151711744), (63922662349/576460752303423488)), (187/288230376151711744), by norm_num⟩
  | 16 => ⟨((23158192421/1152921504606846976), (-21086946325/1152921504606846976)), (249/2305843009213693952), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-120266771407/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778457711870641/633825300114114700748351602688), (-284564247501/158456325028528675187087900672)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944695994125581/19807040628566084398385987584), (-1280285541273/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889145296789361/2475880078570760549798248448), (-169998451403/309485009821345068724781056)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442702915130649/38685626227668133590597632), (-679816252927/77371252455336267181195264)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774599104502677/4835703278458516698824704), (-79642393843/604462909807314587353088)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258477990564175/604462909807314587353088), (-1114616483629/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29488865562805/1180591620717411303424), (-1810545157169/75557863725914323419136)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297161164970933/4722366482869645213696), (-1357290870439/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620928289840041/590295810358705651712), (-466317817067/147573952589676412928)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822825318787887/73786976294838206464), (-72815142485/2305843009213693952)), (1483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910963539567795/4611686018427387904), (-1309639008701/4611686018427387904)), (1669/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99573524277335/72057594037927936), (-1308348270847/576460752303423488)), (3339/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193873377112643/144115188075855872), (-2286708630249/144115188075855872)), (2923/72057594037927936), by norm_num⟩
  | 4 => ⟨((745289062886617/18014398509481984), (-3424269539069/36028797018963968)), (8773/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487936736318357/9007199254740992), (-4270217068143/9007199254740992)), (10975/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225315624296195/4503599627370496), (-8510148854357/4503599627370496)), (10987/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212178562614103/2251799813685248), (-12689769462917/2251799813685248)), (33025/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172976299975157/2251799813685248), (-25079275084611/2251799813685248)), (66309/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172976299975157/2251799813685248), (-25079275084611/2251799813685248)), (252948769576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096632658694621/2251799813685248), (-48402766576509/2251799813685248)), (64727/1125899906842624), by norm_num⟩
  | 2 => ⟨((975558673331237/1125899906842624), (-90134851738349/2251799813685248)), (123317/1125899906842624), by norm_num⟩
  | 3 => ⟨((1686977050918389/2251799813685248), (-19524789869945/281474976710656)), (111787/562949953421312), by norm_num⟩
  | 4 => ⟨((1252994888058861/2251799813685248), (-117018829948993/1125899906842624)), (732013/2251799813685248), by norm_num⟩
  | 5 => ⟨((672893990861173/2251799813685248), (-520913075280011/4503599627370496)), (966807/2251799813685248), by norm_num⟩
  | 6 => ⟨((170951570649461/2251799813685248), (-622647317024653/9007199254740992)), (1602931/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5531114473/67108864)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-90811430235/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1689340145083457/18014398509481984), (-214120786853119/9007199254740992)), (9437203/18014398509481984), by norm_num⟩
  | 1 => ⟨((69806181635/274877906944), (8847806395/137438953472)), (49/34359738368), by norm_num⟩
  | 2 => ⟨((-94519322107/274877906944), (-23960303887/274877906944)), (533/274877906944), by norm_num⟩
  | 3 => ⟨((10665127885/34359738368), (10814284293/137438953472)), (121/68719476736), by norm_num⟩
  | 4 => ⟨((-57763403427/274877906944), (-14642812377/274877906944)), (329/274877906944), by norm_num⟩
  | 5 => ⟨((62570478507/549755813888), (15861388401/549755813888)), (179/274877906944), by norm_num⟩
  | 6 => ⟨((-56481332301/1099511627776), (-894863251/68719476736)), (325/1099511627776), by norm_num⟩
  | 7 => ⟨((43701223799/2199023255552), (2769525265/549755813888)), (505/4398046511104), by norm_num⟩
  | 8 => ⟨((-14793138487/2199023255552), (-7500013451/4398046511104)), (43/1099511627776), by norm_num⟩
  | 9 => ⟨((71218776275/35184372088832), (9026850193/17592186044416)), (13/1099511627776), by norm_num⟩
  | 10 => ⟨((-77145608565/140737488355328), (-611129087/4398046511104)), (453/140737488355328), by norm_num⟩
  | 11 => ⟨((37984396507/281474976710656), (2407226541/70368744177664)), (7/8796093022208), by norm_num⟩
  | 12 => ⟨((-68575768399/2251799813685248), (-4345926879/562949953421312)), (203/1125899906842624), by norm_num⟩
  | 13 => ⟨((57140499509/9007199254740992), (14484908503/9007199254740992)), (85/2251799813685248), by norm_num⟩
  | 14 => ⟨((-44211240339/36028797018963968), (-22414776791/72057594037927936)), (33/4503599627370496), by norm_num⟩
  | 15 => ⟨((31927002211/144115188075855872), (8093378773/144115188075855872)), (383/288230376151711744), by norm_num⟩
  | 16 => ⟨((-43229962379/1152921504606846976), (-10958638007/1152921504606846976)), (521/2305843009213693952), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (-235555011219/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444589014617059/158456325028528675187087900672), (-2229175977499/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889277094865787/39614081257132168796771975168), (-2507300053617/19807040628566084398385987584)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889022517787013/2475880078570760549798248448), (-5326740239491/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770688089376123/154742504910672534362390528), (-5325308952283/154742504910672534362390528)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774540760009577/4835703278458516698824704), (-1247739167403/2417851639229258349412352)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258375047358583/604462909807314587353088), (-4365566915301/604462909807314587353088)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471779634785327/18889465931478580854784), (-7091196560705/75557863725914323419136)), (289/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297033146386789/4722366482869645213696), (-5315904597051/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202593753895877/73786976294838206464), (-7305319190307/590295810358705651712)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911299575295781/36893488147419103232), (-9125576656615/73786976294838206464)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821668048572221/9223372036854775808), (-1282240965305/1152921504606846976)), (3363/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592911630433483/1152921504606846976), (-5123750183003/576460752303423488)), (3367/576460752303423488), by norm_num⟩
  | 5 => ⟨((596817643304083/72057594037927936), (-2238709788183/36028797018963968)), (2951/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490208175753865/36028797018963968), (-13408829189511/36028797018963968)), (8871/36028797018963968), by norm_num⟩
  | 3 => ⟨((743725982105349/4503599627370496), (-4180018724731/2251799813685248)), (5561/4503599627370496), by norm_num⟩
  | 2 => ⟨((556069859255543/1125899906842624), (-16658712895087/2251799813685248)), (2793/562949953421312), by norm_num⟩
  | 1 => ⟨((552614733205145/562949953421312), (-12417473198211/562949953421312)), (4221/281474976710656), by norm_num⟩
  | 0 => ⟨((135555198013669/140737488355328), (-49059099261743/1125899906842624)), (34269/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((135555198013669/140737488355328), (-49059099261743/1125899906842624)), (130725864890670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521186096114169/562949953421312), (-23626313047479/281474976710656)), (34501/562949953421312), by norm_num⟩
  | 2 => ⟨((957108654055567/1125899906842624), (-174988285021795/1125899906842624)), (139351/1125899906842624), by norm_num⟩
  | 3 => ⟨((1572850429051425/2251799813685248), (-37188652591325/140737488355328)), (560473/2251799813685248), by norm_num⟩
  | 4 => ⟨((235346356457315/562949953421312), (-831223988258641/2251799813685248)), (539583/1125899906842624), by norm_num⟩
  | 5 => ⟨((43359360836689/1125899906842624), (-1390003042705169/4503599627370496)), (3398065/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1689340145083457/18014398509481984), (-214120786853119/9007199254740992)), (9437203/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-90811430235/1073741824)), (1/536870912), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile061Terms1
