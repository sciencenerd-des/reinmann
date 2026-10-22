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
namespace Reinmann.XiBand97.Tile014Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26103/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26103/1280))
  have he : value ((69/80), (26103/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1503504713/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((918001071646131/9007199254740992), (-62188527911813/562949953421312)), (157203495/9007199254740992), by norm_num⟩
  | 1 => ⟨((-60112909/268435456), (1042496963/4294967296)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((132081561/536870912), (-572649987/2147483648)), (47/1073741824), by norm_num⟩
  | 3 => ⟨((-773900939/4294967296), (209706771/1073741824)), (35/1073741824), by norm_num⟩
  | 4 => ⟨((425108541/4294967296), (-921545743/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((-186811787/4294967296), (404968591/8589934592)), (35/4294967296), by norm_num⟩
  | 6 => ⟨((547289933/34359738368), (-148301157/8589934592)), (105/34359738368), by norm_num⟩
  | 7 => ⟨((-687153653/137438953472), (744802165/137438953472)), (67/68719476736), by norm_num⟩
  | 8 => ⟨((94364431/68719476736), (-818248811/549755813888)), (75/274877906944), by norm_num⟩
  | 9 => ⟨((-737208345/2199023255552), (799056177/2199023255552)), (37/549755813888), by norm_num⟩
  | 10 => ⟨((323962459/4398046511104), (-175570587/2199023255552)), (33/2199023255552), by norm_num⟩
  | 11 => ⟨((-129421505/8796093022208), (35069819/2199023255552)), (107/35184372088832), by norm_num⟩
  | 12 => ⟨((758314965/281474976710656), (-102741691/35184372088832)), (159/281474976710656), by norm_num⟩
  | 13 => ⟨((-1025346633/2251799813685248), (1111367723/2251799813685248)), (109/1125899906842624), by norm_num⟩
  | 14 => ⟨((643690521/9007199254740992), (-697692707/9007199254740992)), (139/9007199254740992), by norm_num⟩
  | 15 => ⟨((-377155369/36028797018963968), (817593367/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | 16 => ⟨((414347523/288230376151711744), (-112277265/72057594037927936)), (23/72057594037927936), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-537740896779/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222380623986093/79228162514264337593543950336), (-1273153863813/633825300114114700748351602688)), (46163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945026273724983/19807040628566084398385987584), (-358014912623/9903520314283042199192993792)), (51937/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472461744698289/618970019642690137449562112), (-1521269203023/2475880078570760549798248448)), (13797/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771513160176303/154742504910672534362390528), (-380234589267/38685626227668133590597632)), (55193/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549855671242597/9671406556917033397649408), (-712764140705/4835703278458516698824704)), (51749/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629526538199935/302231454903657293676544), (-1246985925319/604462909807314587353088)), (90573/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472055386900535/18889465931478580854784), (-506423407533/18889465931478580854784)), (575/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1297861461260669/4722366482869645213696), (-1518694264521/4722366482869645213696)), (110419/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405472670432863/147573952589676412928), (-2087269109381/590295810358705651712)), (9491/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824027535852623/73786976294838206464), (-1303841939027/36893488147419103232)), (23733/9223372036854775808), by norm_num⟩
  | 7 => ⟨((56977453483833/288230376151711744), (-366464640991/1152921504606846976)), (106829/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199315811824137/144115188075855872), (-1464654952471/576460752303423488)), (213735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195053229575357/144115188075855872), (-2560440542371/144115188075855872)), (187105/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492344927470737/36028797018963968), (-479406976543/4503599627370496)), (280831/36028797018963968), by norm_num⟩
  | 3 => ⟨((745070018674921/4503599627370496), (-2392312527309/4503599627370496)), (175671/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114853328825891/2251799813685248), (-9540972062139/4503599627370496)), (703597/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109363155812475/1125899906842624), (-1780119864379/281474976710656)), (1057687/2251799813685248), by norm_num⟩
  | 0 => ⟨((273239664570707/281474976710656), (-7050273471589/562949953421312)), (1062289/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((273239664570707/281474976710656), (-7050273471589/562949953421312)), (4052310947898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((530402301320311/562949953421312), (-54751989140093/2251799813685248)), (1044513/562949953421312), by norm_num⟩
  | 2 => ⟨((124850902938881/140737488355328), (-103172869507411/2251799813685248)), (8076163/2251799813685248), by norm_num⟩
  | 3 => ⟨((883697301545583/1125899906842624), (-183053230057277/2251799813685248)), (15069103/2251799813685248), by norm_num⟩
  | 4 => ⟨((1372313461978693/2251799813685248), (-287349957945115/2251799813685248)), (407889/35184372088832), by norm_num⟩
  | 5 => ⟨((99957500032493/281474976710656), (-43779892554229/281474976710656)), (38480635/2251799813685248), by norm_num⟩
  | 6 => ⟨((918001071646131/9007199254740992), (-62188527911813/562949953421312)), (157203495/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1503504713/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1575600225/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-609466987802929/4503599627370496), (-205906889139601/9007199254740992)), (26118279/1125899906842624), by norm_num⟩
  | 1 => ⟨((1338338471/4294967296), (226077143/4294967296)), (29/536870912), by norm_num⟩
  | 2 => ⟨((-1540819107/4294967296), (-130140465/2147483648)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((1182622369/4294967296), (49943249/1073741824)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-1361544319/8589934592), (-229997161/8589934592)), (243/8589934592), by norm_num⟩
  | 5 => ⟨((1254028661/17179869184), (105917607/8589934592)), (113/8589934592), by norm_num⟩
  | 6 => ⟨((-962502567/34359738368), (-162589535/34359738368)), (175/34359738368), by norm_num⟩
  | 7 => ⟨((1266425179/137438953472), (3342645/2147483648)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((-1458025869/549755813888), (-123147593/274877906944)), (135/274877906944), by norm_num⟩
  | 9 => ⟨((746050807/1099511627776), (63012847/549755813888)), (279/2199023255552), by norm_num⟩
  | 10 => ⟨((-687138187/4398046511104), (-58036977/2199023255552)), (65/2199023255552), by norm_num⟩
  | 11 => ⟨((287671663/8796093022208), (194378295/35184372088832)), (55/8796093022208), by norm_num⟩
  | 12 => ⟨((-220796161/35184372088832), (-149190855/140737488355328)), (85/70368744177664), by norm_num⟩
  | 13 => ⟨((1251450951/1125899906842624), (105699889/562949953421312)), (243/1125899906842624), by norm_num⟩
  | 14 => ⟨((-823306373/4503599627370496), (-278151987/9007199254740992)), (161/4503599627370496), by norm_num⟩
  | 15 => ⟨((505528795/18014398509481984), (10674477/2251799813685248)), (25/4503599627370496), by norm_num⟩
  | 16 => ⟨((-291005767/72057594037927936), (-196631133/288230376151711744)), (29/36028797018963968), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-3874291020481/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222361810866303/79228162514264337593543950336), (-2292846364591/316912650057057350374175801344)), (92651/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889882667677823/39614081257132168796771975168), (-2578988056319/19807040628566084398385987584)), (52131/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944832875645027/1237940039285380274899124224), (-2739617895277/1237940039285380274899124224)), (27703/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885665555870509/77371252455336267181195264), (-5477982686581/154742504910672534362390528)), (55425/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387421032285469/2417851639229258349412352), (-2567138725953/4835703278458516698824704)), (103961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314725526496255/151115727451828646838272), (-280697598293/37778931862957161709568)), (91007/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235996823589689/9444732965739290427392), (-911955226663/9444732965739290427392)), (147961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297674815439571/4722366482869645213696), (-5469547839423/4722366482869645213696)), (111037/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202703965982473/73786976294838206464), (-7517080535647/590295810358705651712)), (152783/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455925093499615/18446744073709551616), (-9391029891859/73786976294838206464)), (191139/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822905690776057/9223372036854775808), (-2639398481115/2305843009213693952)), (215253/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398536932448973/288230376151711744), (-10548452600293/1152921504606846976)), (215529/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194715137611953/144115188075855872), (-9219614874301/144115188075855872)), (47225/36028797018963968), by norm_num⟩
  | 4 => ⟨((745912239898527/18014398509481984), (-863054196425/2251799813685248)), (141987/18014398509481984), by norm_num⟩
  | 3 => ⟨((372366566546935/2251799813685248), (-17225128533123/9007199254740992)), (356061/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114144900963633/2251799813685248), (-8585613994351/1125899906842624)), (44713/281474976710656), by norm_num⟩
  | 1 => ⟨((1108214433411481/1125899906842624), (-6405551414833/281474976710656)), (33/68719476736), by norm_num⟩
  | 0 => ⟨((1090320248705699/1125899906842624), (-50706565145085/1125899906842624)), (1097873/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090320248705699/1125899906842624), (-50706565145085/1125899906842624)), (4188053135398482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131697662662949/140737488355328), (-98208365386655/1125899906842624)), (69539/35184372088832), by norm_num⟩
  | 2 => ⟨((977341474794581/1125899906842624), (-183800525737913/1125899906842624)), (4552835/1125899906842624), by norm_num⟩
  | 3 => ⟨((818379786242319/1125899906842624), (-319097418520029/1125899906842624)), (4695345/562949953421312), by norm_num⟩
  | 4 => ⟨((1008832683211617/2251799813685248), (-927765871803733/2251799813685248)), (2371813/140737488355328), by norm_num⟩
  | 5 => ⟨((139438567210179/4503599627370496), (-831299947851183/2251799813685248)), (130548009/4503599627370496), by norm_num⟩
  | 6 => ⟨((-609466987802929/4503599627370496), (-205906889139601/9007199254740992)), (26118279/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1575600225/33554432)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1640818549/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((232367451448343/9007199254740992), (557341728423539/4503599627370496)), (42749609/2251799813685248), by norm_num⟩
  | 1 => ⟨((-132845119/2147483648), (-1274535271/4294967296)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((318548683/4294967296), (1528101051/4294967296)), (15/268435456), by norm_num⟩
  | 3 => ⟨((-63653865/1073741824), (-610704381/2147483648)), (97/2147483648), by norm_num⟩
  | 4 => ⟨((76317651/2147483648), (366101287/2147483648)), (235/8589934592), by norm_num⟩
  | 5 => ⟨((-292802775/17179869184), (-1404596073/17179869184)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((234036797/34359738368), (280672857/8589934592)), (23/4294967296), by norm_num⟩
  | 7 => ⟨((-160341637/68719476736), (-1538340839/137438953472)), (127/68719476736), by norm_num⟩
  | 8 => ⟨((192241227/274877906944), (57637191/17179869184)), (77/137438953472), by norm_num⟩
  | 9 => ⟨((-25609685/137438953472), (-491406037/549755813888)), (83/549755813888), by norm_num⟩
  | 10 => ⟨((24563737/549755813888), (942672171/4398046511104)), (161/4398046511104), by norm_num⟩
  | 11 => ⟨((-342698291/35184372088832), (-1643948467/35184372088832)), (71/8796093022208), by norm_num⟩
  | 12 => ⟨((68479551/35184372088832), (1314005419/140737488355328)), (229/140737488355328), by norm_num⟩
  | 13 => ⟨((-202100667/562949953421312), (-484745751/281474976710656)), (171/562949953421312), by norm_num⟩
  | 14 => ⟨((138461781/2251799813685248), (1328422337/4503599627370496)), (59/1125899906842624), by norm_num⟩
  | 15 => ⟨((-354151307/36028797018963968), (-1698889409/36028797018963968)), (19/2251799813685248), by norm_num⟩
  | 16 => ⟨((53076109/36028797018963968), (1018439721/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1778428436459/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778776633812817/633825300114114700748351602688), (2104699943225/633825300114114700748351602688)), (11551/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889750612169965/39614081257132168796771975168), (2367357049545/39614081257132168796771975168)), (25993/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889526126543519/2475880078570760549798248448), (1257392991433/1237940039285380274899124224)), (110485/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885596128121629/77371252455336267181195264), (2514188916665/154742504910672534362390528)), (110503/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774777384478039/4835703278458516698824704), (2356417898321/9671406556917033397649408)), (103615/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258789732122295/604462909807314587353088), (1030615821607/302231454903657293676544)), (90681/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943896755299113/37778931862957161709568), (1674156523663/37778931862957161709568)), (147391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297540343927651/4722366482869645213696), (1255097684795/2361183241434822606848)), (55287/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202681125014849/73786976294838206464), (862457587883/147573952589676412928)), (19011/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823475216420447/73786976294838206464), (4309756862467/73786976294838206464)), (23773/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227832106748861/1152921504606846976), (4844998424937/9223372036854775808)), (214059/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796952232830937/576460752303423488), (1210163536165/288230376151711744)), (214185/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597254269035597/72057594037927936), (4230689563391/144115188075855872)), (46889/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491527062028047/36028797018963968), (3168139982631/18014398509481984)), (70405/9007199254740992), by norm_num⟩
  | 3 => ⟨((744558132815575/4503599627370496), (3951652536263/4503599627370496)), (352527/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113827416002211/2251799813685248), (7877788247533/2251799813685248)), (353281/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107818999260491/1125899906842624), (23506133583725/2251799813685248)), (1063623/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179699173315827/2251799813685248), (23252727999725/1125899906842624)), (2142427/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179699173315827/2251799813685248), (23252727999725/1125899906842624)), (8172710427291106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1054473337251057/1125899906842624), (45016392390041/1125899906842624)), (4236151/2251799813685248), by norm_num⟩
  | 2 => ⟨((123222270541575/140737488355328), (168642293070781/2251799813685248)), (258549/70368744177664), by norm_num⟩
  | 3 => ⟨((1713560020139063/2251799813685248), (295308471173703/2251799813685248)), (7863523/1125899906842624), by norm_num⟩
  | 4 => ⟨((632623031620491/1125899906842624), (449443850857675/2251799813685248)), (28060725/2251799813685248), by norm_num⟩
  | 5 => ⟨((621213225514795/2251799813685248), (505068931518285/2251799813685248)), (42735099/2251799813685248), by norm_num⟩
  | 6 => ⟨((232367451448343/9007199254740992), (557341728423539/4503599627370496)), (42749609/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1640818549/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1700358213/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((242283827368427/2251799813685248), (-420227276823389/9007199254740992)), (93225835/9007199254740992), by norm_num⟩
  | 1 => ⟨((-574162191/2147483648), (248962773/2147483648)), (7/268435456), by norm_num⟩
  | 2 => ⟨((713369723/2147483648), (-309324625/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-1181771445/4294967296), (512428545/4294967296)), (119/4294967296), by norm_num⟩
  | 4 => ⟨((1468295861/8589934592), (-636668549/8589934592)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((-1459431259/17179869184), (158206191/4294967296)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((1208850147/34359738368), (-524170155/34359738368)), (129/34359738368), by norm_num⟩
  | 7 => ⟨((-429125681/34359738368), (186073415/34359738368)), (47/34359738368), by norm_num⟩
  | 8 => ⟨((533168629/137438953472), (-231187533/137438953472)), (119/274877906944), by norm_num⟩
  | 9 => ⟨((-1177666019/1099511627776), (510648389/1099511627776)), (67/549755813888), by norm_num⟩
  | 10 => ⟨((73159753/274877906944), (-507565431/4398046511104)), (17/549755813888), by norm_num⟩
  | 11 => ⟨((-1057717275/17592186044416), (458637351/17592186044416)), (125/17592186044416), by norm_num⟩
  | 12 => ⟨((876109563/70368744177664), (-189945167/35184372088832)), (53/35184372088832), by norm_num⟩
  | 13 => ⟨((-1339723371/562949953421312), (145229541/140737488355328)), (165/562949953421312), by norm_num⟩
  | 14 => ⟨((951167861/2251799813685248), (-206218201/1125899906842624)), (119/2251799813685248), by norm_num⟩
  | 15 => ⟨((-315141779/4503599627370496), (546595177/18014398509481984)), (5/562949953421312), by norm_num⟩
  | 16 => ⟨((391548951/36028797018963968), (-339559497/72057594037927936)), (101/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-133238017261/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222332888378099/79228162514264337593543950336), (-630649644641/633825300114114700748351602688)), (92263/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472405760069697/9903520314283042199192993792), (-709348335583/39614081257132168796771975168)), (12975/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889390769695579/2475880078570760549798248448), (-753517875211/2475880078570760549798248448)), (27573/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771057111057497/154742504910672534362390528), (-188333156051/38685626227668133590597632)), (110297/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549428295104431/9671406556917033397649408), (-353026284853/4835703278458516698824704)), (103409/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629339646057299/302231454903657293676544), (-308799652349/302231454903657293676544)), (90489/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887614466420871/75557863725914323419136), (-501615110775/37778931862957161709568)), (147053/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297406428712315/4722366482869645213696), (-94012531357/590295810358705651712)), (110299/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621265463977345/590295810358705651712), (-1033614205285/590295810358705651712)), (37919/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823246691137409/73786976294838206464), (-645616397993/36893488147419103232)), (94809/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822400991861257/9223372036854775808), (-1451558384671/9223372036854775808)), (106675/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199206267131817/144115188075855872), (-1450211460197/1152921504606846976)), (213389/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597143861163165/72057594037927936), (-633710702649/72057594037927936)), (186759/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491199273432353/36028797018963968), (-237263628425/4503599627370496)), (280225/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488712521970627/9007199254740992), (-147959703073/562949953421312)), (175217/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226865244306527/4503599627370496), (-294931546799/281474976710656)), (701327/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214498098663993/2251799813685248), (-7038973189665/2251799813685248)), (263287/562949953421312), by norm_num⟩
  | 0 => ⟨((1088797851404173/1125899906842624), (-13921190856361/2251799813685248)), (2110969/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088797851404173/1125899906842624), (-13921190856361/2251799813685248)), (8052707680709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105750793883539/2251799813685248), (-26924884887679/2251799813685248)), (2054457/1125899906842624), by norm_num⟩
  | 2 => ⟨((1968852395124427/2251799813685248), (-50357138661153/2251799813685248)), (1945773/562949953421312), by norm_num⟩
  | 3 => ⟨((1720332282128225/2251799813685248), (-88059136040485/2251799813685248)), (13958341/2251799813685248), by norm_num⟩
  | 4 => ⟨((163857191675793/281474976710656), (-134551014300725/2251799813685248)), (22419529/2251799813685248), by norm_num⟩
  | 5 => ⟨((1510119582660617/4503599627370496), (-313308864583153/4503599627370496)), (28781759/2251799813685248), by norm_num⟩
  | 6 => ⟨((242283827368427/2251799813685248), (-420227276823389/9007199254740992)), (93225835/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1700358213/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-438782349/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-447054941571917/9007199254740992), (-439333177631491/4503599627370496)), (43931471/2251799813685248), by norm_num⟩
  | 1 => ⟨((546776431/4294967296), (1074664451/4294967296)), (217/4294967296), by norm_num⟩
  | 2 => ⟨((-43826683/268435456), (-1378229947/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((299768593/2147483648), (1178363339/4294967296)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-192222815/2147483648), (-188902643/1073741824)), (157/4294967296), by norm_num⟩
  | 5 => ⟨((394433429/8589934592), (775241141/8589934592)), (163/8589934592), by norm_num⟩
  | 6 => ⟨((-674467847/34359738368), (-662818089/17179869184)), (281/34359738368), by norm_num⟩
  | 7 => ⟨((123569705/17179869184), (971482761/68719476736)), (13/4294967296), by norm_num⟩
  | 8 => ⟨((-633900071/274877906944), (-622951021/137438953472)), (269/274877906944), by norm_num⟩
  | 9 => ⟨((722631813/1099511627776), (710150143/549755813888)), (309/1099511627776), by norm_num⟩
  | 10 => ⟨((-370702801/2199023255552), (-728599661/2199023255552)), (5/68719476736), by norm_num⟩
  | 11 => ⟨((172878893/4398046511104), (1359142715/17592186044416)), (301/17592186044416), by norm_num⟩
  | 12 => ⟨((-591234141/70368744177664), (-581022039/35184372088832)), (259/70368744177664), by norm_num⟩
  | 13 => ⟨((466610963/281474976710656), (458551417/140737488355328)), (103/140737488355328), by norm_num⟩
  | 14 => ⟨((-683904851/2251799813685248), (-672092093/1125899906842624)), (19/140737488355328), by norm_num⟩
  | 15 => ⟨((233890841/4503599627370496), (919403831/9007199254740992)), (105/4503599627370496), by norm_num⟩
  | 16 => ⟨((-299959081/36028797018963968), (-1179112133/72057594037927936)), (17/4503599627370496), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-2659216077681/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889275805658621/316912650057057350374175801344), (-393291131443/79228162514264337593543950336)), (46255/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889497345286715/39614081257132168796771975168), (-1769464360731/19807040628566084398385987584)), (52047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889256873351693/2475880078570760549798248448), (-117476947107/77371252455336267181195264)), (110623/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442730706620415/38685626227668133590597632), (-1879153444499/77371252455336267181195264)), (13831/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549301991110177/9671406556917033397649408), (-3522397823507/9671406556917033397649408)), (103761/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258568364243861/604462909807314587353088), (-1540541744251/302231454903657293676544)), (45409/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943716718530909/37778931862957161709568), (-5004858870967/75557863725914323419136)), (73815/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297269982267555/4722366482869645213696), (-937995167611/1180591620717411303424)), (110769/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621076755481239/590295810358705651712), (-2578135684543/295147905179352825856)), (38095/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823009165850433/73786976294838206464), (-3220644034361/36893488147419103232)), (95293/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227766440635121/1152921504606846976), (-1810220475631/2305843009213693952)), (6705/288230376151711744), by norm_num⟩
  | 6 => ⟨((1593377862291509/1152921504606846976), (-1808481913159/288230376151711744)), (214751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194046330559715/144115188075855872), (-3160934825761/72057594037927936)), (188121/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490830902132431/36028797018963968), (-4733593300111/18014398509481984)), (282609/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488241104230651/9007199254740992), (-368959013441/281474976710656)), (88503/2251799813685248), by norm_num⟩
  | 2 => ⟨((2225889718644481/4503599627370496), (-11765819098261/2251799813685248)), (710279/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106476840060169/1125899906842624), (-35093620643597/2251799813685248)), (1071073/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174185902648617/2251799813685248), (-34687476233541/1125899906842624)), (1082423/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174185902648617/2251799813685248), (-34687476233541/1125899906842624)), (4129116062644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1048554899628889/1125899906842624), (-66983771263395/1125899906842624)), (1078463/562949953421312), by norm_num⟩
  | 2 => ⟨((1945076192418829/2251799813685248), (-124764485949409/1125899906842624)), (8548307/2251799813685248), by norm_num⟩
  | 3 => ⟨((1652481123714033/2251799813685248), (-431079938464707/2251799813685248)), (16662369/2251799813685248), by norm_num⟩
  | 4 => ⟨((1130146621124187/2251799813685248), (-632695195012843/2251799813685248)), (7708737/562949953421312), by norm_num⟩
  | 5 => ⟨((778868681058211/4503599627370496), (-1270163240088481/4503599627370496)), (96557671/4503599627370496), by norm_num⟩
  | 6 => ⟨((-447054941571917/9007199254740992), (-439333177631491/4503599627370496)), (43931471/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-438782349/8388608)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-902919795/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-211936453313733/2251799813685248), (46200608085711/1125899906842624)), (82425817/4503599627370496), by norm_num⟩
  | 1 => ⟨((533401919/2147483648), (-232555491/2147483648)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-351919561/1073741824), (613727273/4294967296)), (35/536870912), by norm_num⟩
  | 3 => ⟨((1238314529/4294967296), (-539887153/4294967296)), (249/4294967296), by norm_num⟩
  | 4 => ⟨((-408497879/2147483648), (356198287/4294967296)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((862439457/8589934592), (-47001385/1073741824)), (177/8589934592), by norm_num⟩
  | 6 => ⟨((-758675723/17179869184), (330771599/17179869184)), (157/17179869184), by norm_num⟩
  | 7 => ⟨((286026961/17179869184), (-498814407/68719476736)), (239/68719476736), by norm_num⟩
  | 8 => ⟨((-188710387/34359738368), (164549977/68719476736)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((442682249/274877906944), (-386006065/549755813888)), (189/549755813888), by norm_num⟩
  | 10 => ⟨((-934611067/2199023255552), (203738427/1099511627776)), (201/2199023255552), by norm_num⟩
  | 11 => ⟨((896906249/8796093022208), (-391038101/8796093022208)), (195/8796093022208), by norm_num⟩
  | 12 => ⟨((-394497835/17592186044416), (343990655/35184372088832)), (173/35184372088832), by norm_num⟩
  | 13 => ⟨((1281356803/281474976710656), (-558652959/281474976710656)), (71/70368744177664), by norm_num⟩
  | 14 => ⟨((-483082009/562949953421312), (210616741/562949953421312)), (27/140737488355328), by norm_num⟩
  | 15 => ⟨((1359873191/9007199254740992), (-148221241/2251799813685248)), (153/4503599627370496), by norm_num⟩
  | 16 => ⟨((-224298957/9007199254740992), (6111943/562949953421312)), (51/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (3556721351959/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778448922019387/633825300114114700748351602688), (4207794568925/633825300114114700748351602688)), (46307/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889381608917743/39614081257132168796771975168), (4732808070867/39614081257132168796771975168)), (52109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889133623508801/2475880078570760549798248448), (5027438523441/2475880078570760549798248448)), (110763/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770799261987955/154742504910672534362390528), (1256530591121/38685626227668133590597632)), (110797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774592907667875/4835703278458516698824704), (4710591554445/9671406556917033397649408)), (103909/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314616594166571/151115727451828646838272), (2060184868039/302231454903657293676544)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471816770507253/18889465931478580854784), (1673245104979/18889465931478580854784)), (147875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648572334767291/2361183241434822606848), (627180384599/590295810358705651712)), (110967/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620903563618741/590295810358705651712), (6895260493367/590295810358705651712)), (76339/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911395673867137/36893488147419103232), (8613492024063/73786976294838206464)), (190995/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910942328270913/4611686018427387904), (4841252180333/4611686018427387904)), (6721/288230376151711744), by norm_num⟩
  | 6 => ⟨((1593128719656143/1152921504606846976), (1209114570809/144115188075855872)), (215327/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149228222382433/18014398509481984), (8453022489495/144115188075855872)), (188697/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490494988131241/36028797018963968), (1582248955627/4503599627370496)), (283619/36028797018963968), by norm_num⟩
  | 3 => ⟨((371953086822397/2251799813685248), (15784829024631/9007199254740992)), (44441/1125899906842624), by norm_num⟩
  | 2 => ⟨((278125720079693/562949953421312), (7864207297153/1125899906842624)), (357037/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105781076805369/1125899906842624), (23451853628523/1125899906842624)), (134835/281474976710656), by norm_num⟩
  | 0 => ⟨((1085571802790559/1125899906842624), (46342245269513/1125899906842624)), (1093873/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085571802790559/1125899906842624), (46342245269513/1125899906842624)), (4172794346335982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1044780737762107/1125899906842624), (89364666320413/1125899906842624)), (2199433/1125899906842624), by norm_num⟩
  | 2 => ⟨((962413034965847/1125899906842624), (165852188885839/1125899906842624)), (2215541/562949953421312), by norm_num⟩
  | 3 => ⟨((99779284980389/140737488355328), (567078147857633/2251799813685248)), (17761565/2251799813685248), by norm_num⟩
  | 4 => ⟨((247261570805897/562949953421312), (804087848695729/2251799813685248)), (8532725/562949953421312), by norm_num⟩
  | 5 => ⟨((294569064197131/4503599627370496), (1412701241565915/4503599627370496)), (108715317/4503599627370496), by norm_num⟩
  | 6 => ⟨((-211936453313733/2251799813685248), (46200608085711/1125899906842624)), (82425817/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-902919795/16777216)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-463262413/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((26664259517429/1125899906842624), (1689748320095825/18014398509481984)), (129356689/9007199254740992), by norm_num⟩
  | 1 => ⟨((-275452245/4294967296), (-545492563/2147483648)), (169/4294967296), by norm_num⟩
  | 2 => ⟨((186484627/2147483648), (1477221245/4294967296)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((-168336577/2147483648), (-166682887/536870912)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((227931951/4294967296), (902771251/4294967296)), (145/4294967296), by norm_num⟩
  | 5 => ⟨((-123450233/4294967296), (-977899947/8589934592)), (159/8589934592), by norm_num⟩
  | 6 => ⟨((27859119/2147483648), (882734049/17179869184)), (145/17179869184), by norm_num⟩
  | 7 => ⟨((-344886367/68719476736), (-1365993211/68719476736)), (227/68719476736), by norm_num⟩
  | 8 => ⟨((233492399/137438953472), (924794547/137438953472)), (155/137438953472), by norm_num⟩
  | 9 => ⟨((-70256571/137438953472), (-139132781/68719476736)), (189/549755813888), by norm_num⟩
  | 10 => ⟨((152206657/1099511627776), (602845689/1099511627776)), (207/2199023255552), by norm_num⟩
  | 11 => ⟨((-299769649/8796093022208), (-148412399/1099511627776)), (103/4398046511104), by norm_num⟩
  | 12 => ⟨((135298543/17592186044416), (133969409/4398046511104)), (47/8796093022208), by norm_num⟩
  | 13 => ⟨((-112736999/70368744177664), (-111629503/17592186044416)), (159/140737488355328), by norm_num⟩
  | 14 => ⟨((348911375/1125899906842624), (1381935077/1125899906842624)), (249/1125899906842624), by norm_num⟩
  | 15 => ⟨((-251965205/4503599627370496), (-997959883/4503599627370496)), (91/2251799813685248), by norm_num⟩
  | 16 => ⟨((85291803/9007199254740992), (1351262731/36028797018963968)), (31/4503599627370496), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1723986505313/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889182239648161/316912650057057350374175801344), (1019684659669/316912650057057350374175801344)), (92401/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236160879622093/4951760157141521099596496896), (2293822971745/39614081257132168796771975168)), (25991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472258424810527/618970019642690137449562112), (2436606150561/2475880078570760549798248448)), (110477/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885349982709113/77371252455336267181195264), (2435953038927/154742504910672534362390528)), (55247/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193636673909631/1208925819614629174706176), (2283012264429/9671406556917033397649408)), (51803/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258386171581309/604462909807314587353088), (998471135527/302231454903657293676544)), (90673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887137996371737/75557863725914323419136), (3243731481809/75557863725914323419136)), (147377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297048945866133/4722366482869645213696), (2431661895519/4722366482869645213696)), (55281/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810386856866687/295147905179352825856), (1670844467477/295147905179352825856)), (152071/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911315843537381/36893488147419103232), (2087171823221/36893488147419103232)), (11885/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821708678634223/9223372036854775808), (4692334076521/9223372036854775808)), (53507/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398239320887693/288230376151711744), (4687585142407/1152921504606846976)), (26769/144115188075855872), by norm_num⟩
  | 5 => ⟨((298420217540395/36028797018963968), (1024075062631/36028797018963968)), (93761/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490287790630229/36028797018963968), (3066895683727/18014398509481984)), (281561/36028797018963968), by norm_num⟩
  | 3 => ⟨((371892768570651/2251799813685248), (7648618506577/9007199254740992)), (352439/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112288060669933/2251799813685248), (15241504951093/4503599627370496)), (353171/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105524518408779/1125899906842624), (5680845382165/562949953421312)), (531595/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170637212637219/2251799813685248), (44893977783607/2251799813685248)), (2141151/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170637212637219/2251799813685248), (44893977783607/2251799813685248)), (8167842873580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2091504942411611/2251799813685248), (86551689193831/2251799813685248)), (2106665/1125899906842624), by norm_num⟩
  | 2 => ⟨((969646969213287/1125899906842624), (160780975842353/2251799813685248)), (2037675/562949953421312), by norm_num⟩
  | 3 => ⟨((1658677842819693/2251799813685248), (69233856839853/562949953421312)), (15203023/2251799813685248), by norm_num⟩
  | 4 => ⟨((593862504801701/1125899906842624), (101995447033345/562949953421312)), (26136581/2251799813685248), by norm_num⟩
  | 5 => ⟨((552554250793987/2251799813685248), (430384770692111/2251799813685248)), (18521327/1125899906842624), by norm_num⟩
  | 6 => ⟨((26664259517429/1125899906842624), (1689748320095825/18014398509481984)), (129356689/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-463262413/8388608)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile014Terms1
