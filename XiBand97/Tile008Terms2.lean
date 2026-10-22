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
namespace Reinmann.XiBand97.Tile008Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11709/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11709/640))
  have he : value ((69/80), (11709/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-1702061217/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((738571255087621/9007199254740992), (-91456830245553/2251799813685248)), (75870259/9007199254740992), by norm_num⟩
  | 1 => ⟨((-976445357/4294967296), (483650543/4294967296)), (103/4294967296), by norm_num⟩
  | 2 => ⟨((338410173/1073741824), (-670482021/4294967296)), (73/2147483648), by norm_num⟩
  | 3 => ⟨((-1251029639/4294967296), (619656963/4294967296)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((867147667/4294967296), (-429513477/4294967296)), (97/4294967296), by norm_num⟩
  | 5 => ⟨((-961697537/8589934592), (476345689/8589934592)), (109/8589934592), by norm_num⟩
  | 6 => ⟨((13887457/268435456), (-440236895/17179869184)), (103/17179869184), by norm_num⟩
  | 7 => ⟨((-352038461/17179869184), (697483343/68719476736)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((976057867/137438953472), (-483458613/137438953472)), (117/137438953472), by norm_num⟩
  | 9 => ⟨((-601379341/274877906944), (297873755/274877906944)), (73/274877906944), by norm_num⟩
  | 10 => ⟨((1333902063/2199023255552), (-660705131/2199023255552)), (41/549755813888), by norm_num⟩
  | 11 => ⟨((-672429421/4398046511104), (83266527/1099511627776)), (21/1099511627776), by norm_num⟩
  | 12 => ⟨((621456743/17592186044416), (-307818445/17592186044416)), (157/35184372088832), by norm_num⟩
  | 13 => ⟨((-1060334743/140737488355328), (262601215/70368744177664)), (17/17592186044416), by norm_num⟩
  | 14 => ⟨((52497717/35184372088832), (-416048667/562949953421312)), (55/281474976710656), by norm_num⟩
  | 15 => ⟨((-1242065733/4503599627370496), (307608491/2251799813685248)), (165/4503599627370496), by norm_num⟩
  | 16 => ⟨((860934361/18014398509481984), (-426435917/18014398509481984)), (29/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-299532067945/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444570167121679/158456325028528675187087900672), (-354295330019/316912650057057350374175801344)), (46135/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889192878661333/39614081257132168796771975168), (-99624912241/4951760157141521099596496896)), (103809/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888933824525295/2475880078570760549798248448), (-846605270555/2475880078570760549798248448)), (55151/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770600280085881/154742504910672534362390528), (-423186539945/77371252455336267181195264)), (27577/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774500068682919/4835703278458516698824704), (-198307037217/2417851639229258349412352)), (25855/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157288096918373/75557863725914323419136), (-86728514619/75557863725914323419136)), (90499/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471751525982849/18889465931478580854784), (-35219021577/2361183241434822606848)), (1149/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1296950355603209/4722366482869645213696), (-844852480967/4722366482869645213696)), (55157/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620638686260423/590295810358705651712), (-1161016000071/590295810358705651712)), (151699/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822463702899697/73786976294838206464), (-725143227697/36893488147419103232)), (11853/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910760397487373/4611686018427387904), (-1630221020399/9223372036854775808)), (213389/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398192692632493/288230376151711744), (-407133416117/288230376151711744)), (26679/144115188075855872), by norm_num⟩
  | 5 => ⟨((596759604879543/72057594037927936), (-1423071011059/144115188075855872)), (93401/72057594037927936), by norm_num⟩
  | 4 => ⟨((745024184164623/18014398509481984), (-266352555421/4503599627370496)), (280301/36028797018963968), by norm_num⟩
  | 3 => ⟨((371819286613193/2251799813685248), (-2656912994241/9007199254740992)), (87637/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224004238102967/4503599627370496), (-2647020237821/2251799813685248)), (701615/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105115435993585/1125899906842624), (-1972944760445/562949953421312)), (32929/70368744177664), by norm_num⟩
  | 0 => ⟨((271144738083263/281474976710656), (-7793760137171/1125899906842624)), (2112733/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((271144738083263/281474976710656), (-7793760137171/1125899906842624)), (8059436806685637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044720542206421/1125899906842624), (-30030904711637/2251799813685248)), (512455/281474976710656), by norm_num⟩
  | 2 => ⟨((1938388201059077/2251799813685248), (-55731247267393/2251799813685248)), (964681/281474976710656), by norm_num⟩
  | 3 => ⟨((1667218739102279/2251799813685248), (-95948841879175/2251799813685248)), (6834317/1125899906842624), by norm_num⟩
  | 4 => ⟨((307577534969887/562949953421312), (-35519966340685/562949953421312)), (21405183/2251799813685248), by norm_num⟩
  | 5 => ⟨((82904591644447/281474976710656), (-77627814855541/1125899906842624)), (815355/70368744177664), by norm_num⟩
  | 6 => ⟨((738571255087621/9007199254740992), (-91456830245553/2251799813685248)), (75870259/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1702061217/33554432)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-81995171/33554432), (-869638997/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2746028492907/18014398509481984), (-782216372037413/9007199254740992)), (31622587/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3709833/8589934592), (1056759769/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((2627687/4294967296), (-374253235/1073741824)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((-2481599/4294967296), (1413785679/4294967296)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((1757725/4294967296), (-1001389113/4294967296)), (167/4294967296), by norm_num⟩
  | 5 => ⟨((-498001/2147483648), (1134859599/8589934592)), (191/8589934592), by norm_num⟩
  | 6 => ⟨((3762515/34359738368), (-1071766453/17179869184)), (363/34359738368), by norm_num⟩
  | 7 => ⟨((-761429/17179869184), (867583719/34359738368)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((2157291/137438953472), (-1229024885/137438953472)), (211/137438953472), by norm_num⟩
  | 9 => ⟨((-1358237/274877906944), (48362357/17179869184)), (67/137438953472), by norm_num⟩
  | 10 => ⟨((769635/549755813888), (-1753867203/2199023255552)), (153/1099511627776), by norm_num⟩
  | 11 => ⟨((-3171695/8796093022208), (1806938169/8796093022208)), (159/4398046511104), by norm_num⟩
  | 12 => ⟨((2995363/35184372088832), (-426620111/8796093022208)), (151/17592186044416), by norm_num⟩
  | 13 => ⟨((-81601/4398046511104), (1487637897/140737488355328)), (265/140737488355328), by norm_num⟩
  | 14 => ⟨((2113765/562949953421312), (-1204227297/562949953421312)), (27/70368744177664), by norm_num⟩
  | 15 => ⟨((-3193999/4503599627370496), (1819644185/4503599627370496)), (329/4503599627370496), by norm_num⟩
  | 16 => ⟨((141395/1125899906842624), (-1288860047/18014398509481984)), (235/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-1021925570497/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778197244505345/633825300114114700748351602688), (-302164805663/79228162514264337593543950336)), (46219/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118068680453861/2475880078570760549798248448), (-1359451848065/19807040628566084398385987584)), (104009/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944416886202635/1237940039285380274899124224), (-722028722205/618970019642690137449562112)), (110527/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885250009329651/77371252455336267181195264), (-1443652430527/77371252455336267181195264)), (110547/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548905920067869/9671406556917033397649408), (-2705987930575/9671406556917033397649408)), (103659/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39319441037523/18889465931478580854784), (-591719843783/151115727451828646838272)), (90723/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886871362098761/75557863725914323419136), (-1922283514141/37778931862957161709568)), (18433/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296848935788789/4722366482869645213696), (-1441007736555/2361183241434822606848)), (110633/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620498644220751/590295810358705651712), (-495060199681/73786976294838206464)), (152177/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455571941761941/18446744073709551616), (-2473584827661/36893488147419103232)), (190305/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821321654856545/9223372036854775808), (-347553120379/576460752303423488)), (107105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592570118435025/1152921504606846976), (-5554960302359/1152921504606846976)), (214357/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193341942840985/144115188075855872), (-2426985857419/72057594037927936)), (11733/9007199254740992), by norm_num⟩
  | 4 => ⟨((1489779086856269/36028797018963968), (-3633869323945/18014398509481984)), (281921/36028797018963968), by norm_num⟩
  | 3 => ⟨((743467326836599/4503599627370496), (-566348814917/562949953421312)), (352979/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111650841666739/2251799813685248), (-4513512103085/1125899906842624)), (353847/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104566739010007/1125899906842624), (-13454429204579/1125899906842624)), (1065899/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166791025562809/2251799813685248), (-26566135586817/1125899906842624)), (537327/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166791025562809/2251799813685248), (-26566135586817/1125899906842624)), (2049739839793968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2083737764655185/2251799813685248), (-51126449006311/1125899906842624)), (2118883/1125899906842624), by norm_num⟩
  | 2 => ⟨((1923575706141193/2251799813685248), (-189242599488125/2251799813685248)), (4113917/1125899906842624), by norm_num⟩
  | 3 => ⟨((101705608818047/140737488355328), (-323316899424211/2251799813685248)), (7720011/1125899906842624), by norm_num⟩
  | 4 => ⟨((1129557817946841/2251799813685248), (-467297554921269/2251799813685248)), (13374817/1125899906842624), by norm_num⟩
  | 5 => ⟨((58704921992971/281474976710656), (-937631495057123/4503599627370496)), (18969403/1125899906842624), by norm_num⟩
  | 6 => ⟨((2746028492907/18014398509481984), (-782216372037413/9007199254740992)), (31622587/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-869638997/16777216)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83649375/33554432), (-887183453/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1287262229382819/18014398509481984), (-46796325023153/1125899906842624)), (269987241/18014398509481984), by norm_num⟩
  | 1 => ⟨((887075995/4294967296), (128992821/1073741824)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((-640994851/2147483648), (-372837207/2147483648)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((308785569/1073741824), (359212711/2147483648)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-871587/4194304), (-259564569/2147483648)), (195/4294967296), by norm_num⟩
  | 5 => ⟨((128983575/1073741824), (37511905/536870912)), (227/8589934592), by norm_num⟩
  | 6 => ⟨((-994161287/17179869184), (-578257871/17179869184)), (221/17179869184), by norm_num⟩
  | 7 => ⟨((410499387/17179869184), (238768603/17179869184)), (185/34359738368), by norm_num⟩
  | 8 => ⟨((-1186495835/137438953472), (-690130027/137438953472)), (269/137438953472), by norm_num⟩
  | 9 => ⟨((190523003/68719476736), (443273853/274877906944)), (175/274877906944), by norm_num⟩
  | 10 => ⟨((-220272923/274877906944), (-256245245/549755813888)), (205/1099511627776), by norm_num⟩
  | 11 => ⟨((926066379/4398046511104), (134662549/1099511627776)), (217/4398046511104), by norm_num⟩
  | 12 => ⟨((-892225369/17592186044416), (-259483219/8796093022208)), (211/17592186044416), by norm_num⟩
  | 13 => ⟨((396748155/35184372088832), (7211567/1099511627776)), (189/70368744177664), by norm_num⟩
  | 14 => ⟨((-1310571043/562949953421312), (-762298865/562949953421312)), (157/281474976710656), by norm_num⟩
  | 15 => ⟨((1010143341/2251799813685248), (73444237/281474976710656)), (61/562949953421312), by norm_num⟩
  | 16 => ⟨((-364961223/4503599627370496), (-424562297/9007199254740992)), (89/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-1703016306549/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778115730140637/633825300114114700748351602688), (-251754977369/39614081257132168796771975168)), (92597/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472251723771375/9903520314283042199192993792), (-4530591440023/39614081257132168796771975168)), (104197/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944367822737989/1237940039285380274899124224), (-2406263684197/1237940039285380274899124224)), (110739/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885200729392661/77371252455336267181195264), (-4811148357791/154742504910672534362390528)), (27693/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774406530274763/4835703278458516698824704), (-4508986743407/9671406556917033397649408)), (25971/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314535100474709/151115727451828646838272), (-3943898959269/604462909807314587353088)), (90935/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235842215133349/9444732965739290427392), (-400380677083/4722366482869645213696)), (73917/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296747953246049/4722366482869645213696), (-4802167123303/4722366482869645213696)), (55467/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810179286621521/295147905179352825856), (-6599079764167/590295810358705651712)), (38157/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455527712806475/18446744073709551616), (-8243002455347/73786976294838206464)), (95463/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821120116957895/9223372036854775808), (-9265342337253/9223372036854775808)), (214987/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398091363256019/288230376151711744), (-9255304872245/1152921504606846976)), (107615/576460752303423488), by norm_num⟩
  | 5 => ⟨((596579675874189/72057594037927936), (-2021777247233/36028797018963968)), (188601/144115188075855872), by norm_num⟩
  | 4 => ⟨((186187275805645/4503599627370496), (-1513515171737/4503599627370496)), (283451/36028797018963968), by norm_num⟩
  | 3 => ⟨((92910710488957/562949953421312), (-943484735977/562949953421312)), (355277/9007199254740992), by norm_num⟩
  | 2 => ⟨((555634692536477/1125899906842624), (-7518383696105/1125899906842624)), (356723/2251799813685248), by norm_num⟩
  | 1 => ⟨((551974750726801/562949953421312), (-11204024805483/562949953421312)), (538713/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081983062452215/1125899906842624), (-44229911199923/1125899906842624)), (1091997/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1081983062452215/1125899906842624), (-44229911199923/1125899906842624)), (4165637974265670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2076083416093725/2251799813685248), (-170018718293655/2251799813685248)), (1092301/562949953421312), by norm_num⟩
  | 2 => ⟨((1901241824424271/2251799813685248), (-9796969942937/70368744177664)), (4358149/1125899906842624), by norm_num⟩
  | 3 => ⟨((780805713417501/1125899906842624), (-529394384561195/2251799813685248)), (17145731/2251799813685248), by norm_num⟩
  | 4 => ⟨((479254821165559/1125899906842624), (-734264489417531/2251799813685248)), (31842817/2251799813685248), by norm_num⟩
  | 5 => ⟨((337149325366451/4503599627370496), (-1250199220820105/4503599627370496)), (47875213/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1287262229382819/18014398509481984), (-46796325023153/1125899906842624)), (269987241/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-887183453/16777216)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-225944771/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1272095642155977/18014398509481984), (633995564926225/18014398509481984)), (256126197/18014398509481984), by norm_num⟩
  | 1 => ⟨((111627817/536870912), (-222535283/2147483648)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-657362591/2147483648), (655241561/4294967296)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((161297003/536870912), (-80388283/536870912)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-474929183/2147483648), (118349197/1073741824)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((1118719999/8589934592), (-278777591/4294967296)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((-274500231/4294967296), (273614535/8589934592)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((230928337/8589934592), (-230183229/17179869184)), (99/17179869184), by norm_num⟩
  | 8 => ⟨((-679954397/68719476736), (84720059/17179869184)), (147/68719476736), by norm_num⟩
  | 9 => ⟨((444907607/137438953472), (-221736039/137438953472)), (97/137438953472), by norm_num⟩
  | 10 => ⟨((-65500165/68719476736), (522310589/1099511627776)), (115/549755813888), by norm_num⟩
  | 11 => ⟨((561050877/2199023255552), (-559240603/4398046511104)), (31/549755813888), by norm_num⟩
  | 12 => ⟨((-68832503/1099511627776), (548883277/17592186044416)), (123/8796093022208), by norm_num⟩
  | 13 => ⟨((997775285/70368744177664), (-497277943/70368744177664)), (225/70368744177664), by norm_num⟩
  | 14 => ⟨((-419698349/140737488355328), (13073255/8796093022208)), (191/281474976710656), by norm_num⟩
  | 15 => ⟨((1318161257/2251799813685248), (-328477027/1125899906842624)), (151/1125899906842624), by norm_num⟩
  | 16 => ⟨((-485155673/4503599627370496), (483590281/9007199254740992)), (7/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1745002344579/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444510865066209/158456325028528675187087900672), (4127069745561/633825300114114700748351602688)), (92607/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888925586318309/39614081257132168796771975168), (2320956021657/19807040628566084398385987584)), (104209/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888649245243533/2475880078570760549798248448), (616343980713/309485009821345068724781056)), (3461/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770315047720271/154742504910672534362390528), (4929312476093/154742504910672534362390528)), (55393/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548732038696715/9671406556917033397649408), (4619701493005/9671406556917033397649408)), (103899/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314517374083105/151115727451828646838272), (2020355138223/302231454903657293676544)), (90947/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886622478134051/75557863725914323419136), (6563289105403/75557863725914323419136)), (147857/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324165375601241/1180591620717411303424), (4919960771847/4722366482869645213696)), (110953/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810119836589807/295147905179352825856), (1690218851451/147573952589676412928)), (9541/36893488147419103232), by norm_num⟩
  | 8 => ⟨((910981090574059/36893488147419103232), (8444991227459/73786976294838206464)), (190965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820952801631869/9223372036854775808), (9492228264917/9223372036854775808)), (215035/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49756189419157/36028797018963968), (2370437970899/288230376151711744)), (53821/288230376151711744), by norm_num⟩
  | 5 => ⟨((596506399528969/72057594037927936), (517797304537/9007199254740992)), (11791/9007199254740992), by norm_num⟩
  | 4 => ⟨((372319552329467/9007199254740992), (3100902005465/9007199254740992)), (141773/18014398509481984), by norm_num⟩
  | 3 => ⟨((371574020418229/2251799813685248), (15463393009107/9007199254740992)), (355419/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110993673115831/2251799813685248), (15401828986525/2251799813685248)), (178451/1125899906842624), by norm_num⟩
  | 1 => ⟨((551767449835589/562949953421312), (5737305962727/281474976710656)), (8423/17592186044416), by norm_num⟩
  | 0 => ⟨((67571869146165/70368744177664), (11321678250759/281474976710656)), (1093079/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((67571869146165/70368744177664), (11321678250759/281474976710656)), (4169765476707076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2072713971304251/2251799813685248), (173946991998325/2251799813685248)), (4374401/2251799813685248), by norm_num⟩
  | 2 => ⟨((473608446995241/562949953421312), (320225944056031/2251799813685248)), (8728837/2251799813685248), by norm_num⟩
  | 3 => ⟨((1548243631875813/2251799813685248), (538810638957307/2251799813685248)), (17169737/2251799813685248), by norm_num⟩
  | 4 => ⟨((467790570499821/1125899906842624), (740927444333817/2251799813685248)), (7956785/562949953421312), by norm_num⟩
  | 5 => ⟨((72461724093731/1125899906842624), (1231366553198721/4503599627370496)), (94783691/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1272095642155977/18014398509481984), (633995564926225/18014398509481984)), (256126197/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-225944771/4194304)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-459761637/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-230075387742025/18014398509481984), (1340214712102237/18014398509481984)), (57682617/4503599627370496), by norm_num⟩
  | 1 => ⟨((82164319/2147483648), (-957232587/4294967296)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((-123071151/2147483648), (1433806277/4294967296)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((122896073/2147483648), (-357941645/1073741824)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-92040933/2147483648), (536148669/2147483648)), (3/67108864), by norm_num⟩
  | 5 => ⟨((220583995/8589934592), (-1284926297/8589934592)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-110135099/8589934592), (1283098393/17179869184)), (117/8589934592), by norm_num⟩
  | 7 => ⟨((23566805/4294967296), (-274558519/8589934592)), (101/17179869184), by norm_num⟩
  | 8 => ⟨((-282399353/137438953472), (1645007633/137438953472)), (305/137438953472), by norm_num⟩
  | 9 => ⟨((46999603/68719476736), (-1095111657/274877906944)), (205/274877906944), by norm_num⟩
  | 10 => ⟨((-56319291/274877906944), (656132267/549755813888)), (247/1099511627776), by norm_num⟩
  | 11 => ⟨((122703649/2199023255552), (-714762403/2199023255552)), (271/4398046511104), by norm_num⟩
  | 12 => ⟨((-61264547/4398046511104), (1427491199/17592186044416)), (273/17592186044416), by norm_num⟩
  | 13 => ⟨((225885761/70368744177664), (-1315809679/70368744177664)), (127/35184372088832), by norm_num⟩
  | 14 => ⟨((-193340933/281474976710656), (1126232435/281474976710656)), (219/281474976710656), by norm_num⟩
  | 15 => ⟨((154452713/1125899906842624), (-1799408455/2251799813685248)), (11/70368744177664), by norm_num⟩
  | 16 => ⟨((-231349489/9007199254740992), (84227281/562949953421312)), (133/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1133799469115/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888990295807207/316912650057057350374175801344), (167583140749/39614081257132168796771975168)), (92465/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944427583522845/19807040628566084398385987584), (3015818074455/39614081257132168796771975168)), (13005/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944287416469929/1237940039285380274899124224), (3203461898087/2475880078570760549798248448)), (55281/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770241094167273/154742504910672534362390528), (1601255926577/77371252455336267181195264)), (13823/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548663194297211/9671406556917033397649408), (3001345778701/9671406556917033397649408)), (6481/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258009744127421/604462909807314587353088), (2625168854173/604462909807314587353088)), (45379/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943263146192381/37778931862957161709568), (266500555107/4722366482869645213696)), (36881/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296590159854681/4722366482869645213696), (3196353278231/4722366482869645213696)), (110683/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405035717568203/147573952589676412928), (4392300528153/590295810358705651712)), (152251/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910921557150201/36893488147419103232), (2743175235665/36893488147419103232)), (23801/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820821509859099/9223372036854775808), (24088335773/36028797018963968)), (214339/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49752190178509/36028797018963968), (6159707519101/1152921504606846976)), (214501/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192904541334271/144115188075855872), (2690991608385/72057594037927936)), (187871/144115188075855872), by norm_num⟩
  | 4 => ⟨((186140405110309/4503599627370496), (503592205135/2251799813685248)), (282173/36028797018963968), by norm_num⟩
  | 3 => ⟨((743057649633583/4503599627370496), (10044769753761/9007199254740992)), (353357/9007199254740992), by norm_num⟩
  | 2 => ⟨((555416087963655/1125899906842624), (10004257788129/2251799813685248)), (177161/1125899906842624), by norm_num⟩
  | 1 => ⟨((551670246812079/562949953421312), (14905454568979/1125899906842624)), (1067803/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161900445220231/2251799813685248), (14704631141641/562949953421312)), (1077525/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161900445220231/2251799813685248), (14704631141641/562949953421312)), (4110431675437545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037026890185199/1125899906842624), (28235146320477/562949953421312)), (2125305/1125899906842624), by norm_num⟩
  | 2 => ⟨((952336766794053/1125899906842624), (208051218796245/2251799813685248)), (8256561/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591835978546463/2251799813685248), (10998692236751/70368744177664)), (3873311/562949953421312), by norm_num⟩
  | 4 => ⟨((535142428622439/1125899906842624), (7775164520849/35184372088832)), (26748095/2251799813685248), by norm_num⟩
  | 5 => ⟨((398744786852885/2251799813685248), (946061032806519/4503599627370496)), (74497237/4503599627370496), by norm_num⟩
  | 6 => ⟨((-230075387742025/18014398509481984), (1340214712102237/18014398509481984)), (57682617/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-459761637/8388608)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-88110603/33554432), (-1868998285/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((862258333177183/18014398509481984), (488969100984843/9007199254740992)), (155143953/18014398509481984), by norm_num⟩
  | 1 => ⟨((-78236009/536870912), (-709856701/4294967296)), (115/4294967296), by norm_num⟩
  | 2 => ⟨((238191285/1073741824), (1080587327/4294967296)), (177/4294967296), by norm_num⟩
  | 3 => ⟨((-966904949/4294967296), (-1096624121/4294967296)), (91/2147483648), by norm_num⟩
  | 4 => ⟨((735940953/4294967296), (417337093/2147483648)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((-448117749/4294967296), (-1016473715/8589934592)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((909536361/17179869184), (1031559011/17179869184)), (179/17179869184), by norm_num⟩
  | 7 => ⟨((-791172531/34359738368), (-897315587/34359738368)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((602185631/68719476736), (85371795/8589934592)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((-407415037/137438953472), (-462073503/137438953472)), (167/274877906944), by norm_num⟩
  | 10 => ⟨((992307377/1099511627776), (562717259/549755813888)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((-274645643/1099511627776), (-622983753/2199023255552)), (29/549755813888), by norm_num⟩
  | 12 => ⟨((557443215/8796093022208), (316114669/4398046511104)), (119/8796093022208), by norm_num⟩
  | 13 => ⟨((-130549875/8796093022208), (-148064339/8796093022208)), (113/35184372088832), by norm_num⟩
  | 14 => ⟨((454242313/140737488355328), (1030366177/281474976710656)), (199/281474976710656), by norm_num⟩
  | 15 => ⟨((-737573821/1125899906842624), (-836526119/1125899906842624)), (163/1125899906842624), by norm_num⟩
  | 16 => ⟨((140347503/1125899906842624), (636705635/4503599627370496)), (125/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (1104846978331/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888959358229989/316912650057057350374175801344), (1306339344699/633825300114114700748351602688)), (92329/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888785735459367/39614081257132168796771975168), (1469298648307/39614081257132168796771975168)), (51939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944250648984635/1237940039285380274899124224), (1560711820599/2475880078570760549798248448)), (110381/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770167824518431/154742504910672534362390528), (1560241805345/154742504910672534362390528)), (13799/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548594785693221/9671406556917033397649408), (1462227494763/9671406556917033397649408)), (6469/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628975084025711/302231454903657293676544), (159868759737/75557863725914323419136)), (45289/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886430008476525/75557863725914323419136), (2077358751481/75557863725914323419136)), (147209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162064800966137/590295810358705651712), (24331270177/73786976294838206464)), (55213/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620044958958025/590295810358705651712), (2139823761655/590295810358705651712)), (75933/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455430461320219/18446744073709551616), (1336394597829/36893488147419103232)), (94939/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820686619683601/9223372036854775808), (751038339439/2305843009213693952)), (213677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397984278333317/288230376151711744), (750184733349/288230376151711744)), (53439/288230376151711744), by norm_num⟩
  | 5 => ⟨((298197585618459/36028797018963968), (655452600033/36028797018963968)), (187127/144115188075855872), by norm_num⟩
  | 4 => ⟨((744478116343455/18014398509481984), (3925055901565/36028797018963968)), (280869/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485914015607477/9007199254740992), (2446471892017/4503599627370496)), (351401/9007199254740992), by norm_num⟩
  | 2 => ⟨((277660511292047/562949953421312), (1218234071029/562949953421312)), (703749/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206165927314211/2251799813685248), (14519166752065/2251799813685248)), (529003/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161089075139929/2251799813685248), (14321064452423/1125899906842624)), (1062803/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161089075139929/2251799813685248), (14321064452423/1125899906842624)), (4054271702293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((259208522376317/281474976710656), (27488319116481/1125899906842624)), (4134033/2251799813685248), by norm_num⟩
  | 2 => ⟨((477071414138827/562949953421312), (12656909441929/281474976710656)), (122123/35184372088832), by norm_num⟩
  | 3 => ⟨((1612621821052581/2251799813685248), (171617378046225/2251799813685248)), (13950011/2251799813685248), by norm_num⟩
  | 4 => ⟨((570898131721505/1125899906842624), (122903433523357/1125899906842624)), (22106901/2251799813685248), by norm_num⟩
  | 5 => ⟨((552126207564773/2251799813685248), (249277365258545/2251799813685248)), (27245411/2251799813685248), by norm_num⟩
  | 6 => ⟨((862258333177183/18014398509481984), (488969100984843/9007199254740992)), (155143953/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1868998285/33554432)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile008Terms2
