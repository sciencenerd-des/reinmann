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
namespace Reinmann.XiBand58.Tile005Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2697/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2697/160))
  have he : value ((15/16), (2697/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-77672149/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((452747053642911/4503599627370496), (88234484978599/1125899906842624)), (120947897/9007199254740992), by norm_num⟩
  | 1 => ⟨((-59293923/268435456), (-369779547/2147483648)), (129/4294967296), by norm_num⟩
  | 2 => ⟨((1042256519/4294967296), (812488709/4294967296)), (9/268435456), by norm_num⟩
  | 3 => ⟨((-763357213/4294967296), (-595073387/4294967296)), (27/1073741824), by norm_num⟩
  | 4 => ⟨((838633615/8589934592), (81719367/1073741824)), (121/8589934592), by norm_num⟩
  | 5 => ⟨((-184266639/4294967296), (-574578565/17179869184)), (109/17179869184), by norm_num⟩
  | 6 => ⟨((33739599/2147483648), (841652097/68719476736)), (81/34359738368), by norm_num⟩
  | 7 => ⟨((-338895891/68719476736), (-264185525/68719476736)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((744630381/549755813888), (580474929/549755813888)), (29/137438953472), by norm_num⟩
  | 9 => ⟨((-363582261/1099511627776), (-283429729/1099511627776)), (115/2199023255552), by norm_num⟩
  | 10 => ⟨((19971797/274877906944), (498207013/8796093022208)), (103/8796093022208), by norm_num⟩
  | 11 => ⟨((-1021265995/70368744177664), (-199031399/17592186044416)), (167/70368744177664), by norm_num⟩
  | 12 => ⟨((373991791/140737488355328), (583088909/281474976710656)), (31/70368744177664), by norm_num⟩
  | 13 => ⟨((-126422147/281474976710656), (-788416789/2251799813685248)), (85/1125899906842624), by norm_num⟩
  | 14 => ⟨((634920797/9007199254740992), (247475535/4503599627370496)), (109/9007199254740992), by norm_num⟩
  | 15 => ⟨((-744033909/72057594037927936), (-290004975/36028797018963968)), (65/36028797018963968), by norm_num⟩
  | 16 => ⟨((204351199/144115188075855872), (637206059/576460752303423488)), (145/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (215629461647/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778791221891989/633825300114114700748351602688), (1020769827923/633825300114114700748351602688)), (92301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944883561754099/19807040628566084398385987584), (17939988819/618970019642690137449562112)), (103845/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944771899940875/1237940039285380274899124224), (304915732673/618970019642690137449562112)), (110343/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442802518938835/38685626227668133590597632), (609687342859/77371252455336267181195264)), (110351/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48424113436205/302231454903657293676544), (1142857600735/9671406556917033397649408)), (12933/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258804640597037/604462909807314587353088), (249923584585/151115727451828646838272)), (90539/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887818027439053/75557863725914323419136), (1623929655643/75557863725914323419136)), (147143/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297558985568053/4722366482869645213696), (1217445525655/4722366482869645213696)), (27593/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621475044693541/590295810358705651712), (418293181561/147573952589676412928)), (151785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823508389836607/73786976294838206464), (2090244330011/73786976294838206464)), (189767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822695022150445/9223372036854775808), (1174923193229/4611686018427387904)), (106769/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593943692004573/1152921504606846976), (1173875028043/576460752303423488)), (6675/36028797018963968), by norm_num⟩
  | 5 => ⟨((298636012242085/36028797018963968), (2051925366693/144115188075855872)), (186969/144115188075855872), by norm_num⟩
  | 4 => ⟨((1456623728083/35184372088832), (3073182276873/36028797018963968)), (280593/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489189941491373/9007199254740992), (3833256430951/9007199254740992)), (175493/4503599627370496), by norm_num⟩
  | 2 => ⟨((556953629932497/1125899906842624), (1910475819317/1125899906842624)), (175677/1125899906842624), by norm_num⟩
  | 1 => ⟨((2215908166573595/2251799813685248), (11401521858985/2251799813685248)), (527955/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090180419581191/1125899906842624), (22558853660227/2251799813685248)), (2119255/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1090180419581191/1125899906842624), (22558853660227/2251799813685248)), (8084316262252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055481144057607/1125899906842624), (43686335524343/2251799813685248)), (4146505/2251799813685248), by norm_num⟩
  | 2 => ⟨((123630363888879/140737488355328), (81907997538121/2251799813685248)), (7935219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734663346304559/2251799813685248), (143903598954115/2251799813685248)), (3629653/562949953421312), by norm_num⟩
  | 4 => ⟨((1327093403711547/2251799813685248), (27713864370839/281474976710656)), (24224343/2251799813685248), by norm_num⟩
  | 5 => ⟨((1520580259359259/4503599627370496), (522659414029603/4503599627370496)), (1041355/70368744177664), by norm_num⟩
  | 6 => ⟨((452747053642911/4503599627370496), (88234484978599/1125899906842624)), (120947897/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-77672149/2097152)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-1302346491/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((229464438070665/4503599627370496), (-116676998212557/1125899906842624)), (140871605/9007199254740992), by norm_num⟩
  | 1 => ⟨((-125971173/1073741824), (128106459/536870912)), (157/4294967296), by norm_num⟩
  | 2 => ⟨((290059345/2147483648), (-1179904091/4294967296)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-445257549/4294967296), (905609857/4294967296)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((256310849/4294967296), (-1042621879/8589934592)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((-29508877/1073741824), (960290239/17179869184)), (39/4294967296), by norm_num⟩
  | 6 => ⟨((181191201/17179869184), (-737049997/34359738368)), (61/17179869184), by norm_num⟩
  | 7 => ⟨((-119202331/34359738368), (969783049/137438953472)), (81/68719476736), by norm_num⟩
  | 8 => ⟨((548947021/549755813888), (-279125999/137438953472)), (189/549755813888), by norm_num⟩
  | 9 => ⟨((-280888273/1099511627776), (1142597981/2199023255552)), (49/549755813888), by norm_num⟩
  | 10 => ⟨((64676915/1099511627776), (-1052371631/8796093022208)), (183/8796093022208), by norm_num⟩
  | 11 => ⟨((-433233747/35184372088832), (881154629/35184372088832)), (155/35184372088832), by norm_num⟩
  | 12 => ⟨((665038379/281474976710656), (-676311171/140737488355328)), (241/281474976710656), by norm_num⟩
  | 13 => ⟨((-235585763/562949953421312), (29947385/35184372088832)), (173/1125899906842624), by norm_num⟩
  | 14 => ⟨((309975009/4503599627370496), (-630458535/4503599627370496)), (115/4503599627370496), by norm_num⟩
  | 15 => ⟨((-380663379/36028797018963968), (774231693/36028797018963968)), (143/36028797018963968), by norm_num⟩
  | 16 => ⟨((438254911/288230376151711744), (-445683589/144115188075855872)), (167/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (-1450898540875/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778637940517147/633825300114114700748351602688), (-1716824798017/633825300114114700748351602688)), (46185/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889594656288617/39614081257132168796771975168), (-965531599147/19807040628566084398385987584)), (103927/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944680258831983/1237940039285380274899124224), (-1025651399633/1237940039285380274899124224)), (55217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885513376662957/77371252455336267181195264), (-2050794644409/154742504910672534362390528)), (110449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549399722501693/9671406556917033397649408), (-1922080227135/9671406556917033397649408)), (12945/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258654178944321/604462909807314587353088), (-1681280629609/604462909807314587353088)), (90631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887573447434959/75557863725914323419136), (-2731069719433/75557863725914323419136)), (147303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324343870208189/1180591620717411303424), (-2047417787145/4722366482869645213696)), (55251/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405305653142911/147573952589676412928), (-2813762868593/590295810358705651712)), (37995/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227899085046823/9223372036854775808), (-1757524987745/36893488147419103232)), (190035/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455584904195937/2305843009213693952), (-3951472075467/9223372036854775808)), (13367/576460752303423488), by norm_num⟩
  | 6 => ⟨((1593587997227549/1152921504606846976), (-1973888120157/576460752303423488)), (26747/144115188075855872), by norm_num⟩
  | 5 => ⟨((597116245821049/72057594037927936), (-3450150652721/144115188075855872)), (93673/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491114715744757/36028797018963968), (-1291732373985/9007199254740992)), (281253/36028797018963968), by norm_num⟩
  | 3 => ⟨((372150960175517/2251799813685248), (-6444166917449/9007199254740992)), (351977/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113319487081567/2251799813685248), (-6422472202607/2251799813685248)), (352593/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214136580935619/2251799813685248), (-19159276381953/2251799813685248)), (1060871/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176785151958793/2251799813685248), (-4735998346053/281474976710656)), (2134165/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2176785151958793/2251799813685248), (-4735998346053/281474976710656)), (8141193398482512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051815989471661/1125899906842624), (-73251633234787/2251799813685248)), (4197957/2251799813685248), by norm_num⟩
  | 2 => ⟨((245353831754915/281474976710656), (-136863390116671/2251799813685248)), (8116587/2251799813685248), by norm_num⟩
  | 3 => ⟨((851312928791747/1125899906842624), (-29824993312471/281474976710656)), (1892081/281474976710656), by norm_num⟩
  | 4 => ⟨((631051849984629/1125899906842624), (-180409659890543/1125899906842624)), (26097927/2251799813685248), by norm_num⟩
  | 5 => ⟨((1299152046340173/4503599627370496), (-404468812679059/2251799813685248)), (75237465/4503599627370496), by norm_num⟩
  | 6 => ⟨((229464438070665/4503599627370496), (-116676998212557/1125899906842624)), (140871605/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-1302346491/33554432)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-1356254109/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-868095582292141/9007199254740992), (-194449668676193/4503599627370496)), (169722757/9007199254740992), by norm_num⟩
  | 1 => ⟨((496292661/2147483648), (111167417/1073741824)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((-595028913/2147483648), (-533135647/4294967296)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((951211345/4294967296), (426134483/4294967296)), (3/67108864), by norm_num⟩
  | 4 => ⟨((-570226297/4294967296), (-510912931/8589934592)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((546937177/8589934592), (490046281/17179869184)), (225/17179869184), by norm_num⟩
  | 6 => ⟨((-54645753/2147483648), (-97923305/8589934592)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((1198032391/137438953472), (536708183/137438953472)), (63/34359738368), by norm_num⟩
  | 8 => ⟨((-179547263/68719476736), (-643485007/549755813888)), (305/549755813888), by norm_num⟩
  | 9 => ⟨((765396503/1099511627776), (342891035/1099511627776)), (165/1099511627776), by norm_num⟩
  | 10 => ⟨((-1468272525/8796093022208), (-328886717/4398046511104)), (319/8796093022208), by norm_num⟩
  | 11 => ⟨((640138863/17592186044416), (573553385/35184372088832)), (281/35184372088832), by norm_num⟩
  | 12 => ⟨((-1023323969/140737488355328), (-458440317/140737488355328)), (113/70368744177664), by norm_num⟩
  | 13 => ⟨((755022679/562949953421312), (84560913/140737488355328)), (21/70368744177664), by norm_num⟩
  | 14 => ⟨((-1034551607/4503599627370496), (-231735101/2251799813685248)), (233/4503599627370496), by norm_num⟩
  | 15 => ⟨((1323064751/36028797018963968), (592721603/36028797018963968)), (301/36028797018963968), by norm_num⟩
  | 16 => ⟨((-396571339/72057594037927936), (-177660541/72057594037927936)), (91/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (-1771819110073/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778492389123021/633825300114114700748351602688), (-4192511414251/633825300114114700748351602688)), (92613/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118089406433051/2475880078570760549798248448), (-4715629130827/39614081257132168796771975168)), (13027/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889185566454373/2475880078570760549798248448), (-5009204531883/2475880078570760549798248448)), (13845/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885425598556601/77371252455336267181195264), (-2503954661891/77371252455336267181195264)), (110795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96827156012513/604462909807314587353088), (-4693539077877/9671406556917033397649408)), (103907/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314627241025013/151115727451828646838272), (-4105471055599/604462909807314587353088)), (22739/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235917033873591/9444732965739290427392), (-6668811730895/75557863725914323419136)), (4621/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((81074784223221/295147905179352825856), (-2499676495865/2361183241434822606848)), (27741/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810487436828257/295147905179352825856), (-3435222888927/295147905179352825856)), (152673/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822880451837271/73786976294838206464), (-8582562269239/73786976294838206464)), (190989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821984852591391/9223372036854775808), (-2411957530893/2305843009213693952)), (215065/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593228858002411/1152921504606846976), (-9638394287311/1152921504606846976)), (107659/576460752303423488), by norm_num⟩
  | 5 => ⟨((149239166878903/18014398509481984), (-1052873269319/18014398509481984)), (188689/144115188075855872), by norm_num⟩
  | 4 => ⟨((372656547878889/9007199254740992), (-12613277728175/36028797018963968)), (70901/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487976122096759/9007199254740992), (-7864765502385/4503599627370496)), (355505/9007199254740992), by norm_num⟩
  | 2 => ⟨((556333154581341/1125899906842624), (-1959250605469/281474976710656)), (178505/1125899906842624), by norm_num⟩
  | 1 => ⟨((553012674407353/562949953421312), (-23372448153281/1125899906842624)), (539283/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086056824100517/1125899906842624), (-46192201864355/1125899906842624)), (273425/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1086056824100517/1125899906842624), (-46192201864355/1125899906842624)), (1043033600927257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1045728575432591/1125899906842624), (-89115126042947/1125899906842624)), (274967/140737488355328), by norm_num⟩
  | 2 => ⟨((482106242832459/562949953421312), (-41384777296821/281474976710656)), (4434421/1125899906842624), by norm_num⟩
  | 3 => ⟨((1602811254105063/2251799813685248), (-283532976553551/1125899906842624)), (8899183/1125899906842624), by norm_num⟩
  | 4 => ⟨((499031953785107/1125899906842624), (-807265091626765/2251799813685248)), (17150845/1125899906842624), by norm_num⟩
  | 5 => ⟨((305937173759179/4503599627370496), (-715607263929417/2251799813685248)), (6875149/281474976710656), by norm_num⟩
  | 6 => ⟨((-868095582292141/9007199254740992), (-194449668676193/4503599627370496)), (169722757/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-1356254109/33554432)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-351366977/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-27477638844097/562949953421312), (379255876426697/4503599627370496)), (9849357/562949953421312), by norm_num⟩
  | 1 => ⟨((520930233/4294967296), (-898757409/4294967296)), (189/4294967296), by norm_num⟩
  | 2 => ⟨((-161807875/1073741824), (1116664131/4294967296)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((268051643/2147483648), (-924935375/4294967296)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-333041655/4294967296), (143648629/1073741824)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((331030969/8589934592), (-1142250987/17179869184)), (249/17179869184), by norm_num⟩
  | 6 => ⟨((-548387371/34359738368), (7391633/268435456)), (13/2147483648), by norm_num⟩
  | 7 => ⟨((389340407/68719476736), (-167931593/17179869184)), (149/68719476736), by norm_num⟩
  | 8 => ⟨((-483737283/274877906944), (104323583/34359738368)), (187/274877906944), by norm_num⟩
  | 9 => ⟨((534240885/1099511627776), (-921722187/1099511627776)), (13/68719476736), by norm_num⟩
  | 10 => ⟨((-531015491/4398046511104), (229039359/1099511627776)), (209/4398046511104), by norm_num⟩
  | 11 => ⟨((239913441/8796093022208), (-413921037/8796093022208)), (191/17592186044416), by norm_num⟩
  | 12 => ⟨((-198720835/35184372088832), (685703425/70368744177664)), (5/2199023255552), by norm_num⟩
  | 13 => ⟨((607757199/562949953421312), (-1048559385/562949953421312)), (247/562949953421312), by norm_num⟩
  | 14 => ⟨((-431491401/2251799813685248), (744449197/2251799813685248)), (89/1125899906842624), by norm_num⟩
  | 15 => ⟨((285924227/9007199254740992), (-15415723/281474976710656)), (119/9007199254740992), by norm_num⟩
  | 16 => ⟨((-710495013/144115188075855872), (1225812243/144115188075855872)), (149/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (2730390538855/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889185253893113/316912650057057350374175801344), (50467429501/9903520314283042199192993792)), (46259/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889293629738271/39614081257132168796771975168), (227056838951/2475880078570760549798248448)), (13013/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889040454724957/2475880078570760549798248448), (3859048066845/2475880078570760549798248448)), (55317/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110669152541777/9671406556917033397649408), (1929007680857/77371252455336267181195264)), (27665/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549099164288387/9671406556917033397649408), (3615792439149/9671406556917033397649408)), (25943/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629195462834213/302231454903657293676544), (3162721744173/604462909807314587353088)), (90829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887145164835217/75557863725914323419136), (2568683659545/37778931862957161709568)), (73825/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648526917703319/2361183241434822606848), (3851227598391/4722366482869645213696)), (110785/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405194911684035/147573952589676412928), (82695588421/9223372036854775808)), (38101/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455659479952347/18446744073709551616), (6611268886845/73786976294838206464)), (95309/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910857032903959/4611686018427387904), (7431661140461/9223372036854775808)), (214601/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199120080491549/144115188075855872), (3712073083511/576460752303423488)), (214797/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596840767939901/72057594037927936), (6487681074301/144115188075855872)), (188167/144115188075855872), by norm_num⟩
  | 4 => ⟨((372571063441839/9007199254740992), (4857323384597/18014398509481984)), (141345/18014398509481984), by norm_num⟩
  | 3 => ⟨((371889686788145/2251799813685248), (12113819772089/9007199254740992)), (177067/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112263936247713/2251799813685248), (24139342520477/4503599627370496)), (710585/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210918108210437/2251799813685248), (35988862453673/2251799813685248)), (1071687/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085071854905577/1125899906842624), (71100663583913/2251799813685248)), (2166705/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1085071854905577/1125899906842624), (71100663583913/2251799813685248)), (8265323647505950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089203662012749/2251799813685248), (68522369041103/1125899906842624)), (2156549/1125899906842624), by norm_num⟩
  | 2 => ⟨((965003783799703/1125899906842624), (254298243494697/2251799813685248)), (8528315/2251799813685248), by norm_num⟩
  | 3 => ⟨((812741344079823/1125899906842624), (217957889235621/1125899906842624)), (16545387/2251799813685248), by norm_num⟩
  | 4 => ⟨((1088982861035657/2251799813685248), (629339737124325/2251799813685248)), (30292779/2251799813685248), by norm_num⟩
  | 5 => ⟨((701496786797487/4503599627370496), (152176091172035/562949953421312)), (46232145/2251799813685248), by norm_num⟩
  | 6 => ⟨((-27477638844097/562949953421312), (379255876426697/4503599627370496)), (9849357/562949953421312), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-351366977/8388608)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-181342527/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((596838605877445/9007199254740992), (276266483525843/4503599627370496)), (45429353/4503599627370496), by norm_num⟩
  | 1 => ⟨((-729971313/4294967296), (-337891359/2147483648)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((936169725/4294967296), (54167139/268435456)), (147/4294967296), by norm_num⟩
  | 3 => ⟨((-25012791/134217728), (-740991831/4294967296)), (1/33554432), by norm_num⟩
  | 4 => ⟨((1026504675/8589934592), (950303261/8589934592)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((-1053173003/17179869184), (-121873987/2147483648)), (87/8589934592), by norm_num⟩
  | 6 => ⟨((900445139/34359738368), (833601613/34359738368)), (151/34359738368), by norm_num⟩
  | 7 => ⟨((-659884623/68719476736), (-610898835/68719476736)), (7/4294967296), by norm_num⟩
  | 8 => ⟨((105785665/34359738368), (783462287/274877906944)), (73/137438953472), by norm_num⟩
  | 9 => ⟨((-964746217/1099511627776), (-893129373/1099511627776)), (169/1099511627776), by norm_num⟩
  | 10 => ⟨((247452519/1099511627776), (916332645/4398046511104)), (11/274877906944), by norm_num⟩
  | 11 => ⟨((-923204625/17592186044416), (-427335787/8796093022208)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((394662185/35184372088832), (91341221/8796093022208)), (9/4398046511104), by norm_num⟩
  | 13 => ⟨((-155736695/70368744177664), (-576703031/281474976710656)), (29/70368744177664), by norm_num⟩
  | 14 => ⟨((1783289/4398046511104), (422632591/1125899906842624)), (43/562949953421312), by norm_num⟩
  | 15 => ⟨((-39031859/562949953421312), (-289074985/4503599627370496)), (15/1125899906842624), by norm_num⟩
  | 16 => ⟨((800917933/72057594037927936), (741462697/72057594037927936)), (39/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (972880954147/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889129881667325/316912650057057350374175801344), (1150726936807/633825300114114700748351602688)), (46157/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((29518270948839/618970019642690137449562112), (1294297806233/39614081257132168796771975168)), (103861/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888908789127077/2475880078570760549798248448), (687427100347/1237940039285380274899124224)), (13795/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885287607544067/77371252455336267181195264), (1374474994463/154742504910672534362390528)), (55185/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548976607506843/9671406556917033397649408), (644083772019/4835703278458516698824704)), (103481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258284155325913/604462909807314587353088), (1126743999079/604462909807314587353088)), (90557/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943486268797237/37778931862957161709568), (114387778905/4722366482869645213696)), (147173/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296925129460033/4722366482869645213696), (42874795947/147573952589676412928)), (110397/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620603916919899/590295810358705651712), (942709682005/295147905179352825856)), (75911/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455605029084031/18446744073709551616), (2355167840831/73786976294838206464)), (94909/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821471588698601/9223372036854775808), (2647356892527/9223372036854775808)), (213601/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796360675253045/576460752303423488), (1322300481537/576460752303423488)), (213671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193475727447891/144115188075855872), (2310929173273/144115188075855872)), (187041/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489982666968113/36028797018963968), (3460209787173/36028797018963968)), (280719/36028797018963968), by norm_num⟩
  | 3 => ⟨((743597093610349/4503599627370496), (4314461322585/9007199254740992)), (43897/1125899906842624), by norm_num⟩
  | 2 => ⟨((555958959284133/1125899906842624), (4298301955425/2251799813685248)), (703185/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104986058439995/1125899906842624), (12814402294127/2251799813685248)), (132109/281474976710656), by norm_num⟩
  | 0 => ⟨((2168616093690899/2251799813685248), (1581784000587/140737488355328)), (2122175/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2168616093690899/2251799813685248), (1581784000587/140737488355328)), (8095455178267668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088220813785257/2251799813685248), (24373621275343/1125899906842624)), (129227/70368744177664), by norm_num⟩
  | 2 => ⟨((1935469506206673/2251799813685248), (90412128014511/2251799813685248)), (7848769/2251799813685248), by norm_num⟩
  | 3 => ⟨((1659946782945361/2251799813685248), (9713891733395/140737488355328)), (14122639/2251799813685248), by norm_num⟩
  | 4 => ⟨((1212926310901963/2251799813685248), (229143542650385/2251799813685248)), (22770943/2251799813685248), by norm_num⟩
  | 5 => ⟨((630022022347577/2251799813685248), (246855186828599/2251799813685248)), (58330747/4503599627370496), by norm_num⟩
  | 6 => ⟨((596838605877445/9007199254740992), (276266483525843/4503599627370496)), (45429353/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-181342527/4194304)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-1492655825/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1330033096916437/18014398509481984), (-730599881695995/18014398509481984)), (144270553/18014398509481984), by norm_num⟩
  | 1 => ⟨((-418428611/2147483648), (14365427/134217728)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((276064273/1073741824), (-606578967/4294967296)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((-971399257/4294967296), (533598889/4294967296)), (7/268435456), by norm_num⟩
  | 4 => ⟨((320447291/2147483648), (-704099029/8589934592)), (75/4294967296), by norm_num⟩
  | 5 => ⟨((-1353086035/17179869184), (743263081/17179869184)), (5/536870912), by norm_num⟩
  | 6 => ⟨((1190290539/34359738368), (-81729745/4294967296)), (143/34359738368), by norm_num⟩
  | 7 => ⟨((-897498563/68719476736), (123251133/17179869184)), (55/34359738368), by norm_num⟩
  | 8 => ⟨((148034385/34359738368), (-162633403/68719476736)), (147/274877906944), by norm_num⟩
  | 9 => ⟨((-694526629/549755813888), (190755055/274877906944)), (11/68719476736), by norm_num⟩
  | 10 => ⟨((183289559/549755813888), (-402730821/2199023255552)), (95/2199023255552), by norm_num⟩
  | 11 => ⟨((-175895147/2199023255552), (24155221/549755813888)), (93/8796093022208), by norm_num⟩
  | 12 => ⟨((154732459/8796093022208), (-679968139/70368744177664)), (83/35184372088832), by norm_num⟩
  | 13 => ⟨((-1005163889/281474976710656), (552146123/281474976710656)), (137/281474976710656), by norm_num⟩
  | 14 => ⟨((757910037/1125899906842624), (-416327221/1125899906842624)), (105/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1066756287/9007199254740992), (585979415/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | 16 => ⟨((703807749/36028797018963968), (-386608317/36028797018963968)), (101/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (-327159357139/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444538278438211/158456325028528675187087900672), (-96730204523/79228162514264337593543950336)), (92277/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((14758198491955/309485009821345068724781056), (-870385527555/39614081257132168796771975168)), (103817/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888781419846405/2475880078570760549798248448), (-924551332749/2475880078570760549798248448)), (110311/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770447913635025/154742504910672534362390528), (-924289002765/154742504910672534362390528)), (110317/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387214333605673/2417851639229258349412352), (-866242318421/9671406556917033397649408)), (103429/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258179863361911/604462909807314587353088), (-378841761961/302231454903657293676544)), (90507/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471700799507939/18889465931478580854784), (-1230713778519/75557863725914323419136)), (147087/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162099780339325/590295810358705651712), (-461289438915/2361183241434822606848)), (55163/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810214819551339/295147905179352825856), (-1238090509/576460752303423488)), (151717/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911101277974389/36893488147419103232), (-1583644751507/73786976294838206464)), (189673/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455306806809407/2305843009213693952), (-890036952039/4611686018427387904)), (53355/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398119370194519/288230376151711744), (-444541958047/288230376151711744)), (213467/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193262893625571/144115188075855872), (-1553755241445/144115188075855872)), (93419/72057594037927936), by norm_num⟩
  | 4 => ⟨((11638004047607/281474976710656), (-2326356427347/36028797018963968)), (280363/36028797018963968), by norm_num⟩
  | 3 => ⟨((185849802965299/1125899906842624), (-1450238511087/4503599627370496)), (175321/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223050055349721/4503599627370496), (-5778609376903/4503599627370496)), (350925/2251799813685248), by norm_num⟩
  | 1 => ⟨((138050483030279/140737488355328), (-4306132432959/1125899906842624)), (1054201/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166343983756467/2251799813685248), (-4250800798501/562949953421312)), (1057081/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2166343983756467/2251799813685248), (-4250800798501/562949953421312)), (4032444004539107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((260500351680847/281474976710656), (-32715862857841/2251799813685248)), (1024947/562949953421312), by norm_num⟩
  | 2 => ⟨((1928234193991483/2251799813685248), (-60555960459467/2251799813685248)), (1926925/562949953421312), by norm_num⟩
  | 3 => ⟨((824766939751157/1125899906842624), (-103709106731689/2251799813685248)), (6807443/1125899906842624), by norm_num⟩
  | 4 => ⟨((1203573436828473/2251799813685248), (-37985544746731/562949953421312)), (21201001/2251799813685248), by norm_num⟩
  | 5 => ⟨((1266100639515429/4503599627370496), (-10151522431695/140737488355328)), (3190591/281474976710656), by norm_num⟩
  | 6 => ⟨((1330033096916437/18014398509481984), (-730599881695995/18014398509481984)), (144270553/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-1492655825/33554432)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-382919581/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-67094571751767/9007199254740992), (-1416097188135233/18014398509481984)), (236669505/18014398509481984), by norm_num⟩
  | 1 => ⟨((86639151/4294967296), (1828604829/8589934592)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-117311585/4294967296), (-1237988419/4294967296)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((26473805/1073741824), (279377899/1073741824)), (193/4294967296), by norm_num⟩
  | 4 => ⟨((-71692393/4294967296), (-1513138751/8589934592)), (263/8589934592), by norm_num⟩
  | 5 => ⟨((155317279/17179869184), (1639062279/17179869184)), (287/17179869184), by norm_num⟩
  | 6 => ⟨((-70101165/17179869184), (-1479554311/34359738368)), (261/34359738368), by norm_num⟩
  | 7 => ⟨((108478557/68719476736), (143096691/8589934592)), (51/17179869184), by norm_num⟩
  | 8 => ⟨((-146882689/274877906944), (-1550052091/274877906944)), (139/137438953472), by norm_num⟩
  | 9 => ⟨((88392377/549755813888), (1865608389/1099511627776)), (337/1099511627776), by norm_num⟩
  | 10 => ⟨((-47874199/1099511627776), (-505216117/1099511627776)), (185/2199023255552), by norm_num⟩
  | 11 => ⟨((94287807/8796093022208), (995018623/8796093022208)), (23/1099511627776), by norm_num⟩
  | 12 => ⟨((-42556019/17592186044416), (-449093397/17592186044416)), (335/70368744177664), by norm_num⟩
  | 13 => ⟨((141838567/281474976710656), (748410747/140737488355328)), (281/281474976710656), by norm_num⟩
  | 14 => ⟨((-6859035/70368744177664), (-579066821/562949953421312)), (219/1125899906842624), by norm_num⟩
  | 15 => ⟨((39625837/2251799813685248), (836342411/4503599627370496)), (159/4503599627370496), by norm_num⟩
  | 16 => ⟨((-26827189/9007199254740992), (-1132428617/36028797018963968)), (217/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-542301346635/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222256283489867/79228162514264337593543950336), (-641293800185/158456325028528675187087900672)), (92453/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472233388291275/9903520314283042199192993792), (-2885184103421/39614081257132168796771975168)), (52013/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888658120489241/2475880078570760549798248448), (-3064714006241/2475880078570760549798248448)), (55273/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770324384275973/154742504910672534362390528), (-3063820978041/154742504910672534362390528)), (110567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774370640738307/4835703278458516698824704), (-2871383640513/9671406556917033397649408)), (405/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1258078073092993/604462909807314587353088), (-2511512514577/604462909807314587353088)), (45371/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886637331945431/75557863725914323419136), (-127482211595/2361183241434822606848)), (73749/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648336721926381/2361183241434822606848), (-764504725305/1180591620717411303424)), (110661/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810128696363717/295147905179352825856), (-4202251866351/590295810358705651712)), (76109/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821986277673411/73786976294838206464), (-1312257780879/18446744073709551616)), (190363/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910491291304983/4611686018427387904), (-1474990358185/2305843009213693952)), (107141/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796115587794953/576460752303423488), (-5893469230985/1152921504606846976)), (214437/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193045513807811/144115188075855872), (-1287372531885/36028797018963968)), (5869/4503599627370496), by norm_num⟩
  | 4 => ⟨((1489334736164643/36028797018963968), (-3854832482865/18014398509481984)), (141031/18014398509481984), by norm_num⟩
  | 3 => ⟨((371594932481967/2251799813685248), (-9611629773097/9007199254740992)), (353191/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222193388120575/4503599627370496), (-19147090812879/4503599627370496)), (354113/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207474945142645/2251799813685248), (-28530862645323/2251799813685248)), (133371/281474976710656), by norm_num⟩
  | 0 => ⟨((2163489773285121/2251799813685248), (-14076627676231/562949953421312)), (538133/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2163489773285121/2251799813685248), (-14076627676231/562949953421312)), (2052814485790061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2077235084368541/2251799813685248), (-54098308090765/1125899906842624)), (530485/281474976710656), by norm_num⟩
  | 2 => ⟨((955502141403929/1125899906842624), (-199617928535495/2251799813685248)), (4118799/1125899906842624), by norm_num⟩
  | 3 => ⟨((802045108442767/1125899906842624), (-42351757251931/281474976710656)), (15442277/2251799813685248), by norm_num⟩
  | 4 => ⟨((545854574429457/1125899906842624), (-241357296728969/1125899906842624)), (26647899/2251799813685248), by norm_num⟩
  | 5 => ⟨((851599223996573/4503599627370496), (-936111522459523/4503599627370496)), (18631801/1125899906842624), by norm_num⟩
  | 6 => ⟨((-67094571751767/9007199254740992), (-1416097188135233/18014398509481984)), (236669505/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-382919581/8388608)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile005Terms1
