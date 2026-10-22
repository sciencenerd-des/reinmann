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
namespace Reinmann.XiBand97.Tile025Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (29683/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (29683/1280))
  have he : value ((69/80), (29683/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-427427215/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((522999169631201/4503599627370496), (-429729906681583/4503599627370496)), (36151291/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1095911627/4294967296), (900471795/4294967296)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((601990991/2147483648), (-247317345/1073741824)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-881806267/4294967296), (724548999/4294967296)), (65/2147483648), by norm_num⟩
  | 4 => ⟨((968763201/8589934592), (-397999217/4294967296)), (145/8589934592), by norm_num⟩
  | 5 => ⟨((-425718063/8589934592), (699594929/17179869184)), (65/8589934592), by norm_num⟩
  | 6 => ⟨((311799397/17179869184), (-256194529/17179869184)), (97/34359738368), by norm_num⟩
  | 7 => ⟨((-391481885/68719476736), (321666809/68719476736)), (31/34359738368), by norm_num⟩
  | 8 => ⟨((215043405/137438953472), (-706774219/549755813888)), (139/549755813888), by norm_num⟩
  | 9 => ⟨((-104999701/274877906944), (43137269/137438953472)), (69/1099511627776), by norm_num⟩
  | 10 => ⟨((184566339/2199023255552), (-606606513/8796093022208)), (123/8796093022208), by norm_num⟩
  | 11 => ⟨((-589867195/35184372088832), (121168249/8796093022208)), (25/8796093022208), by norm_num⟩
  | 12 => ⟨((216011783/70368744177664), (-354978473/140737488355328)), (149/281474976710656), by norm_num⟩
  | 13 => ⟨((-1168311135/2251799813685248), (239989977/562949953421312)), (51/562949953421312), by norm_num⟩
  | 14 => ⟨((366720277/4503599627370496), (-18832567/281474976710656)), (65/4503599627370496), by norm_num⟩
  | 15 => ⟨((-859484593/72057594037927936), (353104035/36028797018963968)), (155/72057594037927936), by norm_num⟩
  | 16 => ⟨((59015021/36028797018963968), (-24245277/18014398509481984)), (173/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-895952155669/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111190328576825/39614081257132168796771975168), (-1060626926103/633825300114114700748351602688)), (92305/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890052861068569/39614081257132168796771975168), (-298251706879/9903520314283042199192993792)), (51925/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944923665763585/1237940039285380274899124224), (-79207794135/154742504910672534362390528)), (27587/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771513534847487/154742504910672534362390528), (-633524557185/77371252455336267181195264)), (110357/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774928022895769/4835703278458516698824704), (-1187565809607/9671406556917033397649408)), (103469/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314763356852417/151115727451828646838272), (-519413719805/302231454903657293676544)), (5659/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472055540402431/18889465931478580854784), (-843773038115/37778931862957161709568)), (9197/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324465489974651/1180591620717411303424), (-1265179802083/4722366482869645213696)), (110379/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202736428657867/73786976294838206464), (-434710747313/147573952589676412928)), (37949/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824028563017535/73786976294838206464), (-135774094643/4611686018427387904)), (94891/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823279794403219/9223372036854775808), (-2442328430249/9223372036854775808)), (53389/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594527936456021/1152921504606846976), (-19065026453/9007199254740992)), (53405/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195054669661707/144115188075855872), (-2133029413869/144115188075855872)), (93495/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492347443629531/36028797018963968), (-1597521166351/18014398509481984)), (140315/18014398509481984), by norm_num⟩
  | 3 => ⟨((745071901807909/4503599627370496), (-3985936719107/9007199254740992)), (5485/140737488355328), by norm_num⟩
  | 2 => ⟨((2229716045469793/4503599627370496), (-7948322506273/4503599627370496)), (702843/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218745003943063/2251799813685248), (-11863772913643/2251799813685248)), (1056177/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185972978486943/2251799813685248), (-11746849395757/1125899906842624)), (1060021/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185972978486943/2251799813685248), (-11746849395757/1125899906842624)), (4043659214500045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2121825341557657/2251799813685248), (-22806907794753/1125899906842624)), (4160373/2251799813685248), by norm_num⟩
  | 2 => ⟨((1998429048867771/2251799813685248), (-85961948530901/2251799813685248)), (8009021/2251799813685248), by norm_num⟩
  | 3 => ⟨((1770285787633747/2251799813685248), (-76289576896395/1125899906842624)), (7413595/1125899906842624), by norm_num⟩
  | 4 => ⟨((1381397828004577/2251799813685248), (-239904724928905/2251799813685248)), (25322575/2251799813685248), by norm_num⟩
  | 5 => ⟨((1643756848122057/4503599627370496), (-588691523874773/4503599627370496)), (36464659/2251799813685248), by norm_num⟩
  | 6 => ⟨((522999169631201/4503599627370496), (-429729906681583/4503599627370496)), (36151291/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-427427215/8388608)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1791692199/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-154516869869207/1125899906842624), (-6481649752685/4503599627370496)), (12455997/562949953421312), by norm_num⟩
  | 1 => ⟨((1357224431/4294967296), (1779145/536870912)), (221/4294967296), by norm_num⟩
  | 2 => ⟨((-390640593/1073741824), (-16386531/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((599655471/2147483648), (12577127/4294967296)), (199/4294967296), by norm_num⟩
  | 4 => ⟨((-1380757749/8589934592), (-14479953/8589934592)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((317931221/4294967296), (6668265/8589934592)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((-122010615/4294967296), (-10236165/34359738368)), (167/34359738368), by norm_num⟩
  | 7 => ⟨((1284296335/137438953472), (6734183/68719476736)), (111/68719476736), by norm_num⟩
  | 8 => ⟨((-739300399/274877906944), (-15506029/549755813888)), (129/274877906944), by norm_num⟩
  | 9 => ⟨((1513157403/2199023255552), (15868423/2199023255552)), (133/1099511627776), by norm_num⟩
  | 10 => ⟨((-43552171/274877906944), (-7307679/4398046511104)), (247/8796093022208), by norm_num⟩
  | 11 => ⟨((291731141/8796093022208), (12237493/35184372088832)), (13/2199023255552), by norm_num⟩
  | 12 => ⟨((-447823851/70368744177664), (-9392623/140737488355328)), (321/281474976710656), by norm_num⟩
  | 13 => ⟨((634555399/562949953421312), (3327279/281474976710656)), (115/562949953421312), by norm_num⟩
  | 14 => ⟨((-1669848917/9007199254740992), (-17511641/9007199254740992)), (305/9007199254740992), by norm_num⟩
  | 15 => ⟨((2050650253/72057594037927936), (10752545/36028797018963968)), (377/72057594037927936), by norm_num⟩
  | 16 => ⟨((-147556147/36028797018963968), (-12379325/288230376151711744)), (219/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-2039307627343/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889446634348053/316912650057057350374175801344), (-2413767605437/316912650057057350374175801344)), (92675/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889881228112623/39614081257132168796771975168), (-2714998113627/19807040628566084398385987584)), (52145/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944832066108191/1237940039285380274899124224), (-5768197983945/2475880078570760549798248448)), (27711/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885664696000229/77371252455336267181195264), (-1441719561395/38685626227668133590597632)), (27721/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774841204996127/4835703278458516698824704), (-2702523105603/4835703278458516698824704)), (25999/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258900494910063/604462909807314587353088), (-4728013378015/604462909807314587353088)), (45519/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887971770591837/75557863725914323419136), (-7680393068773/75557863725914323419136)), (148017/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297672526889355/4722366482869645213696), (-359874681347/295147905179352825856)), (55541/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810814148546875/295147905179352825856), (-3956753001763/295147905179352825856)), (76425/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823695660040993/73786976294838206464), (-2471569410787/18446744073709551616)), (747/288230376151711744), by norm_num⟩
  | 7 => ⟨((911449901673531/4611686018427387904), (-11114356673811/9223372036854775808)), (215369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797070556668159/576460752303423488), (-1388090763013/144115188075855872)), (215661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597354264886349/72057594037927936), (-9705803060607/144115188075855872)), (189031/144115188075855872), by norm_num⟩
  | 4 => ⟨((372953233866971/9007199254740992), (-14537045351961/36028797018963968)), (71051/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489448988457431/9007199254740992), (-18133415122363/9007199254740992)), (178203/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114123371601319/2251799813685248), (-18076602286369/2251799813685248)), (44767/281474976710656), by norm_num⟩
  | 1 => ⟨((1108171577945025/1125899906842624), (-13486479276463/562949953421312)), (135385/281474976710656), by norm_num⟩
  | 0 => ⟨((545096348788515/562949953421312), (-53378672109645/1125899906842624)), (1100485/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545096348788515/562949953421312), (-53378672109645/1125899906842624)), (4198017124656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263271812176245/281474976710656), (-103371602016533/1125899906842624)), (558879/281474976710656), by norm_num⟩
  | 2 => ⟨((487746316793629/562949953421312), (-96686495220603/562949953421312)), (4592385/1125899906842624), by norm_num⟩
  | 3 => ⟨((50747892818605/70368744177664), (-20942572976927/70368744177664)), (9535273/1125899906842624), by norm_num⟩
  | 4 => ⟨((485842352335273/1125899906842624), (-241650797938497/562949953421312)), (38857489/2251799813685248), by norm_num⟩
  | 5 => ⟨((546753474811/281474976710656), (-1668413917089639/4503599627370496)), (133789871/4503599627370496), by norm_num⟩
  | 6 => ⟨((-154516869869207/1125899906842624), (-6481649752685/4503599627370496)), (12455997/562949953421312), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1791692199/33554432)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-932927575/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((669856312970899/9007199254740992), (920764009632295/9007199254740992)), (141389289/9007199254740992), by norm_num⟩
  | 1 => ⟨((-382958719/2147483648), (-1052806695/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((459147451/2147483648), (631130049/2147483648)), (25/536870912), by norm_num⟩
  | 3 => ⟨((-183497917/1073741824), (-1008922507/4294967296)), (81/2147483648), by norm_num⟩
  | 4 => ⟨((880017575/8589934592), (1209645255/8589934592)), (197/8589934592), by norm_num⟩
  | 5 => ⟨((-844075993/17179869184), (-36257533/536870912)), (3/268435456), by norm_num⟩
  | 6 => ⟨((674668611/34359738368), (28980589/1073741824)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((-7222253/1073741824), (-158839811/17179869184)), (109/68719476736), by norm_num⟩
  | 8 => ⟨((277091301/137438953472), (23805077/8589934592)), (133/274877906944), by norm_num⟩
  | 9 => ⟨((-590609707/1099511627776), (-405917025/549755813888)), (9/68719476736), by norm_num⟩
  | 10 => ⟨((283244045/2199023255552), (194669303/1099511627776)), (35/1099511627776), by norm_num⟩
  | 11 => ⟨((-493956041/17592186044416), (-678976875/17592186044416)), (31/4398046511104), by norm_num⟩
  | 12 => ⟨((394818285/70368744177664), (1085410293/140737488355328)), (201/140737488355328), by norm_num⟩
  | 13 => ⟨((-582604861/562949953421312), (-400415417/281474976710656)), (75/281474976710656), by norm_num⟩
  | 14 => ⟨((798300253/4503599627370496), (548659563/2251799813685248)), (13/281474976710656), by norm_num⟩
  | 15 => ⟨((-510464107/18014398509481984), (-701668359/18014398509481984)), (135/18014398509481984), by norm_num⟩
  | 16 => ⟨((612019735/144115188075855872), (841263621/144115188075855872)), (41/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1226866158103/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222347234564243/79228162514264337593543950336), (22686683299/9903520314283042199192993792)), (92343/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472438020086965/9903520314283042199192993792), (1633145434163/39614081257132168796771975168)), (103895/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889527777800201/2475880078570760549798248448), (867425461569/1237940039285380274899124224)), (1725/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((885597005073981/77371252455336267181195264), (433609799797/38685626227668133590597632)), (110411/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549556522236101/9671406556917033397649408), (812799710701/4835703278458516698824704)), (25881/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258791375158841/604462909807314587353088), (1421962310871/604462909807314587353088)), (22649/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471949096146449/18889465931478580854784), (2309869345281/75557863725914323419136)), (73621/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297542677799663/4722366482869645213696), (865842666579/2361183241434822606848)), (110453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810726249376475/295147905179352825856), (2379903311861/590295810358705651712)), (75953/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911740011756065/36893488147419103232), (2973134117109/73786976294838206464)), (189933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911331428781993/4611686018427387904), (835594528589/2305843009213693952)), (213745/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796955606206075/576460752303423488), (3339383361647/1152921504606846976)), (26729/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194515275744181/144115188075855872), (2918594719559/144115188075855872)), (93601/72057594037927936), by norm_num⟩
  | 4 => ⟨((372884708139519/9007199254740992), (4371169064421/36028797018963968)), (281001/36028797018963968), by norm_num⟩
  | 3 => ⟨((186141735087027/1125899906842624), (1363053749033/2251799813685248)), (351599/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113849363703089/2251799813685248), (5434633320049/2251799813685248)), (44015/281474976710656), by norm_num⟩
  | 1 => ⟨((1107862681857887/1125899906842624), (16216255837731/2251799813685248)), (33093/70368744177664), by norm_num⟩
  | 0 => ⟨((272494893632073/281474976710656), (32083516576399/2251799813685248)), (133029/140737488355328), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272494893632073/281474976710656), (32083516576399/2251799813685248)), (507465363085699037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2109953340720771/2251799813685248), (62119869687853/2251799813685248)), (2090885/1125899906842624), by norm_num⟩
  | 2 => ⟨((1975328443841165/2251799813685248), (58206784535841/1125899906842624)), (252107/70368744177664), by norm_num⟩
  | 3 => ⟨((1726783312776071/2251799813685248), (51060274727535/562949953421312)), (14987985/2251799813685248), by norm_num⟩
  | 4 => ⟨((1305651668025601/2251799813685248), (313242872867893/2251799813685248)), (25705807/2251799813685248), by norm_num⟩
  | 5 => ⟨((356738012644687/1125899906842624), (363252609731553/2251799813685248)), (73923075/4503599627370496), by norm_num⟩
  | 6 => ⟨((669856312970899/9007199254740992), (920764009632295/9007199254740992)), (141389289/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-932927575/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1933560619/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((62707808549755/1125899906842624), (-232399034536491/2251799813685248)), (140499749/9007199254740992), by norm_num⟩
  | 1 => ⟨((-148604441/1073741824), (1101474583/4294967296)), (169/4294967296), by norm_num⟩
  | 2 => ⟨((738536327/4294967296), (-684265379/2147483648)), (213/4294967296), by norm_num⟩
  | 3 => ⟨((-611731277/4294967296), (283389265/1073741824)), (179/4294967296), by norm_num⟩
  | 4 => ⟨((380023779/4294967296), (-704195869/4294967296)), (113/4294967296), by norm_num⟩
  | 5 => ⟨((-188864723/4294967296), (699944399/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((625748275/34359738368), (-579765497/17179869184)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((-222132293/34359738368), (823236079/68719476736)), (69/34359738368), by norm_num⟩
  | 8 => ⟨((137994503/68719476736), (-1022832403/274877906944)), (87/137438953472), by norm_num⟩
  | 9 => ⟨((-152401537/274877906944), (1129619129/1099511627776)), (195/1099511627776), by norm_num⟩
  | 10 => ⟨((151481437/1099511627776), (-561399617/2199023255552)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((-547515971/17592186044416), (1014564103/17592186044416)), (179/17592186044416), by norm_num⟩
  | 12 => ⟨((113377173/17592186044416), (-840365695/70368744177664)), (75/35184372088832), by norm_num⟩
  | 13 => ⟨((-693493393/562949953421312), (642532401/281474976710656)), (29/70368744177664), by norm_num⟩
  | 14 => ⟨((123090453/562949953421312), (-912361735/2251799813685248)), (167/2251799813685248), by norm_num⟩
  | 15 => ⟨((-20391219/562949953421312), (302284499/4503599627370496)), (7/562949953421312), by norm_num⟩
  | 16 => ⟨((405362205/72057594037927936), (-375574381/36028797018963968)), (141/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-700758928839/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889330923687547/316912650057057350374175801344), (-1658435702273/633825300114114700748351602688)), (23091/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29525336755533/618970019642690137449562112), (-1865390364353/39614081257132168796771975168)), (103919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889389096243135/2475880078570760549798248448), (-495385977369/618970019642690137449562112)), (110427/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771055333597457/154742504910672534362390528), (-990528277833/77371252455336267181195264)), (110441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549426518300129/9671406556917033397649408), (-1856722863079/9671406556917033397649408)), (809/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((629338813528499/302231454903657293676544), (-406028755589/151115727451828646838272)), (90623/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471902888490571/18889465931478580854784), (-2638217002793/75557863725914323419136)), (147289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297404063644221/4722366482869645213696), (-1977814453761/4722366482869645213696)), (110491/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810630959328353/295147905179352825856), (-2718117085629/590295810358705651712)), (37991/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823241820026377/73786976294838206464), (-1697790446417/36893488147419103232)), (47503/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911197454262599/4611686018427387904), (-3817190469607/9223372036854775808)), (53461/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398410825232277/288230376151711744), (-3813645891657/1152921504606846976)), (26743/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194280895724407/144115188075855872), (-1666478289655/72057594037927936)), (187315/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491187348276543/36028797018963968), (-4991477892811/36028797018963968)), (140599/18014398509481984), by norm_num⟩
  | 3 => ⟨((93043417309769/562949953421312), (-3112722762531/4503599627370496)), (175947/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226820780948401/4503599627370496), (-6204638428739/2251799813685248)), (352489/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107204809061451/1125899906842624), (-18510198835329/2251799813685248)), (530227/1125899906842624), by norm_num⟩
  | 0 => ⟨((272166560322653/281474976710656), (-9151860264853/562949953421312)), (1066455/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((272166560322653/281474976710656), (-9151860264853/562949953421312)), (4068202976707076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104732670354891/2251799813685248), (-2212301745209/70368744177664)), (4194099/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965044958729885/2251799813685248), (-66170056240715/1125899906842624)), (1013009/281474976710656), by norm_num⟩
  | 3 => ⟨((853514544476161/1125899906842624), (-115487295668517/1125899906842624)), (15096689/2251799813685248), by norm_num⟩
  | 4 => ⟨((317590292807211/562949953421312), (-350191294825557/2251799813685248)), (25985827/2251799813685248), by norm_num⟩
  | 5 => ⟨((662218529965095/2251799813685248), (-790246842983215/4503599627370496)), (18701217/1125899906842624), by norm_num⟩
  | 6 => ⟨((62707808549755/1125899906842624), (-232399034536491/2251799813685248)), (140499749/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1933560619/33554432)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1995843615/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-964303552914057/9007199254740992), (-205015468909785/9007199254740992)), (253483175/9007199254740992), by norm_num⟩
  | 1 => ⟨((1179404153/4294967296), (62686717/1073741824)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-756277981/2147483648), (-321576509/4294967296)), (201/2147483648), by norm_num⟩
  | 3 => ⟨((646604907/2147483648), (274942487/4294967296)), (173/2147483648), by norm_num⟩
  | 4 => ⟨((-1658508841/8589934592), (-176303389/4294967296)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((1701596475/17179869184), (90441853/4294967296)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-727418131/17179869184), (-154652515/17179869184)), (395/34359738368), by norm_num⟩
  | 7 => ⟨((66635381/4294967296), (226671925/68719476736)), (291/68719476736), by norm_num⟩
  | 8 => ⟨((-683665511/137438953472), (-72675251/68719476736)), (375/274877906944), by norm_num⟩
  | 9 => ⟨((779363295/549755813888), (165696301/549755813888)), (215/549755813888), by norm_num⟩
  | 10 => ⟨((-799610953/2199023255552), (-340002097/4398046511104)), (111/1099511627776), by norm_num⟩
  | 11 => ⟨((1491608437/17592186044416), (317122967/17592186044416)), (417/17592186044416), by norm_num⟩
  | 12 => ⟨((-637650017/35184372088832), (-4236481/1099511627776)), (359/70368744177664), by norm_num⟩
  | 13 => ⟨((1006486155/281474976710656), (213983689/281474976710656)), (285/281474976710656), by norm_num⟩
  | 14 => ⟨((-737596005/1125899906842624), (-156816379/1125899906842624)), (105/562949953421312), by norm_num⟩
  | 15 => ⟨((1009011413/9007199254740992), (214520571/9007199254740992)), (289/9007199254740992), by norm_num⟩
  | 16 => ⟨((-323507897/18014398509481984), (-17194825/4503599627370496)), (373/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1909698424859/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778545976332013/633825300114114700748351602688), (-4519030765685/633825300114114700748351602688)), (138967/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889490690263539/39614081257132168796771975168), (-635362542403/4951760157141521099596496896)), (156381/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889249388644025/2475880078570760549798248448), (-337459979129/154742504910672534362390528)), (166205/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13835272474055/1208925819614629174706176), (-5397985041755/154742504910672534362390528)), (166261/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549294044343711/9671406556917033397649408), (-5059150647323/9671406556917033397649408)), (19491/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314640229343845/151115727451828646838272), (-4425296721627/604462909807314587353088)), (136497/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887420411490265/75557863725914323419136), (-7188369993729/75557863725914323419136)), (221919/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297259405033951/4722366482869645213696), (-5388882962991/4722366482869645213696)), (166537/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621060900202597/590295810358705651712), (-3702911948073/295147905179352825856)), (114573/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911493691006977/36893488147419103232), (-9251446244921/73786976294838206464)), (286671/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822104321029783/9223372036854775808), (-5199929231037/4611686018427387904)), (322833/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593347293111247/1152921504606846976), (-10389839270825/1152921504606846976)), (161621/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194015805569221/144115188075855872), (-9079843299795/144115188075855872)), (141649/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490777582738301/36028797018963968), (-3399311668797/9007199254740992)), (212935/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488161323598397/9007199254740992), (-8478591303861/4503599627370496)), (133489/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112845480340667/2251799813685248), (-8449090847821/1125899906842624)), (134097/562949953421312), by norm_num⟩
  | 1 => ⟨((34571222516979/35184372088832), (-25199990600159/1125899906842624)), (810675/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086504971125193/1125899906842624), (-24906091356789/562949953421312)), (822911/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086504971125193/1125899906842624), (-24906091356789/562949953421312)), (3139156343700218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((261571164446709/281474976710656), (-48069267802563/562949953421312)), (830525/281474976710656), by norm_num⟩
  | 2 => ⟨((964090111825139/1125899906842624), (-89340334975085/562949953421312)), (6741709/1125899906842624), by norm_num⟩
  | 3 => ⟨((1594356579035803/2251799813685248), (-612005617999679/2251799813685248)), (13685459/1125899906842624), by norm_num⟩
  | 4 => ⟨((962528734339143/2251799813685248), (-108330587107981/281474976710656)), (53637237/2251799813685248), by norm_num⟩
  | 5 => ⟨((155776310807349/4503599627370496), (-1481784336466223/4503599627370496)), (87140793/2251799813685248), by norm_num⟩
  | 6 => ⟨((-964303552914057/9007199254740992), (-205015468909785/9007199254740992)), (253483175/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1995843615/33554432)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-513377165/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-114104345791003/18014398509481984), (230763104917487/2251799813685248)), (303779051/18014398509481984), by norm_num⟩
  | 1 => ⟨((8974311/536870912), (-290392429/1073741824)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-94734885/4294967296), (191590567/536870912)), (1/16777216), by norm_num⟩
  | 3 => ⟨((83336931/4294967296), (-1348315973/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-109965469/8589934592), (1779141575/8589934592)), (151/4294967296), by norm_num⟩
  | 5 => ⟨((116082071/17179869184), (-1878102645/17179869184)), (321/17179869184), by norm_num⟩
  | 6 => ⟨((-102115747/34359738368), (1652140183/34359738368)), (285/34359738368), by norm_num⟩
  | 7 => ⟨((38498473/34359738368), (-155717595/8589934592)), (217/68719476736), by norm_num⟩
  | 8 => ⟨((-101599677/274877906944), (1643790641/274877906944)), (289/274877906944), by norm_num⟩
  | 9 => ⟨((119167721/1099511627776), (-1928025661/1099511627776)), (341/1099511627776), by norm_num⟩
  | 10 => ⟨((-62898089/2199023255552), (508817025/1099511627776)), (91/1099511627776), by norm_num⟩
  | 11 => ⟨((120721209/17592186044416), (-488289927/4398046511104)), (11/549755813888), by norm_num⟩
  | 12 => ⟨((-53098365/35184372088832), (859083407/35184372088832)), (39/8796093022208), by norm_num⟩
  | 13 => ⟨((43116809/140737488355328), (-1395181761/281474976710656)), (255/281474976710656), by norm_num⟩
  | 14 => ⟨((-8127695/140737488355328), (262997475/281474976710656)), (97/562949953421312), by norm_num⟩
  | 15 => ⟨((45758833/4503599627370496), (-1480672883/9007199254740992)), (275/9007199254740992), by norm_num⟩
  | 16 => ⟨((-15095023/9007199254740992), (244223789/9007199254740992)), (365/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (2126547336089/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55576719237323/19807040628566084398385987584), (2515821017699/633825300114114700748351602688)), (2889/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889388804402889/39614081257132168796771975168), (353716736289/4951760157141521099596496896)), (26005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944570858005867/1237940039285380274899124224), (3005893817803/2475880078570760549798248448)), (27635/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770807857271649/154742504910672534362390528), (3005108318643/154742504910672534362390528)), (3455/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((387298601811163/2417851639229258349412352), (2816454697097/9671406556917033397649408)), (12959/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258474427996295/604462909807314587353088), (1231781889825/302231454903657293676544)), (5671/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887281164689903/75557863725914323419136), (2000863908873/37778931862957161709568)), (73743/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297156104980543/4722366482869645213696), (2999928530867/4722366482869645213696)), (110651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810460352520031/295147905179352825856), (4122680894759/590295810358705651712)), (38051/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455703724527209/18446744073709551616), (2575010877491/36893488147419103232)), (190343/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821914065908121/9223372036854775808), (5789199668297/9223372036854775808)), (214257/9223372036854775808), by norm_num⟩
  | 6 => ⟨((6223288148025/4503599627370496), (5783485761315/1152921504606846976)), (214409/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193858776217387/144115188075855872), (5054128217589/144115188075855872)), (46945/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490552622845635/36028797018963968), (7568364471679/36028797018963968)), (70503/9007199254740992), by norm_num⟩
  | 3 => ⟨((185987322379271/1125899906842624), (9438042343645/9007199254740992)), (353115/9007199254740992), by norm_num⟩
  | 2 => ⟨((278152571273811/562949953421312), (18808986782739/4503599627370496)), (177009/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211989468634485/2251799813685248), (14023115541651/1125899906842624)), (266645/562949953421312), by norm_num⟩
  | 0 => ⟨((2172414067638087/2251799813685248), (6928304232459/281474976710656)), (2151337/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172414067638087/2251799813685248), (6928304232459/281474976710656)), (8206699379927825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261807841611753/281474976710656), (106944821563605/2251799813685248)), (2128447/1125899906842624), by norm_num⟩
  | 2 => ⟨((485759981641313/562949953421312), (198944810173327/2251799813685248)), (4161631/1125899906842624), by norm_num⟩
  | 3 => ⟨((1659039625115621/2251799813685248), (171666107706567/1125899906842624)), (1979339/281474976710656), by norm_num⟩
  | 4 => ⟨((1169968774112147/2251799813685248), (505907982128237/2251799813685248)), (14080729/1125899906842624), by norm_num⟩
  | 5 => ⟨((988439593300341/4503599627370496), (1051419470002421/4503599627370496)), (83835399/4503599627370496), by norm_num⟩
  | 6 => ⟨((-114104345791003/18014398509481984), (230763104917487/2251799813685248)), (303779051/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-513377165/8388608)), (1/16777216), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1053596767/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((870924193715269/9007199254740992), (56790499109923/18014398509481984)), (111293517/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1124623507/4294967296), (-9166689/1073741824)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((1522768457/4294967296), (12411927/1073741824)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-1374577809/4294967296), (-22408081/2147483648)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((232651607/1073741824), (1896319/268435456)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-2016103139/17179869184), (-32866093/8589934592)), (143/17179869184), by norm_num⟩
  | 6 => ⟨((1819902837/34359738368), (59335353/34359738368)), (131/34359738368), by norm_num⟩
  | 7 => ⟨((-1408110927/68719476736), (-45909461/68719476736)), (13/8589934592), by norm_num⟩
  | 8 => ⟨((1906617539/274877906944), (62162563/274877906944)), (143/274877906944), by norm_num⟩
  | 9 => ⟨((-1147381335/549755813888), (-18704371/274877906944)), (11/68719476736), by norm_num⟩
  | 10 => ⟨((621433251/1099511627776), (40521901/2199023255552)), (97/2199023255552), by norm_num⟩
  | 11 => ⟨((-1223907229/8796093022208), (-39903761/8796093022208)), (97/8796093022208), by norm_num⟩
  | 12 => ⟨((1104800739/35184372088832), (36020463/35184372088832)), (89/35184372088832), by norm_num⟩
  | 13 => ⟨((-920571035/140737488355328), (-60027829/281474976710656)), (151/281474976710656), by norm_num⟩
  | 14 => ⟨((1424544329/1125899906842624), (23222625/562949953421312)), (119/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1028730015/4503599627370496), (-33540285/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 16 => ⟨((696463131/18014398509481984), (11353597/9007199254740992)), (15/4503599627370496), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (42454768755/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778366706138083/633825300114114700748351602688), (50221363445/633825300114114700748351602688)), (92205/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472322416528347/9903520314283042199192993792), (28243795911/19807040628566084398385987584)), (25933/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889036656134253/2475880078570760549798248448), (30001886423/1237940039285380274899124224)), (110215/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885351552996595/77371252455336267181195264), (7498462471/19342813113834066795298816)), (13777/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549096530589429/9671406556917033397649408), (56221396983/9671406556917033397649408)), (3229/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258389113345775/604462909807314587353088), (24588328835/302231454903657293676544)), (90413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471785785444783/18889465931478580854784), (79880086991/75557863725914323419136)), (146921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81065820249887/295147905179352825856), (59882095797/4722366482869645213696)), (6887/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405194994134829/147573952589676412928), (20573114665/147573952589676412928)), (151515/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911320145650553/36893488147419103232), (25699371613/18446744073709551616)), (189395/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821719423228881/9223372036854775808), (28888407573/2305843009213693952)), (13317/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592969356538757/1152921504606846976), (57718409475/576460752303423488)), (53269/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193692924821335/144115188075855872), (100875963305/144115188075855872)), (93223/72057594037927936), by norm_num⟩
  | 4 => ⟨((745154422554767/18014398509481984), (75525918293/18014398509481984)), (139839/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487602573808923/9007199254740992), (94178500269/4503599627370496)), (349613/9007199254740992), by norm_num⟩
  | 2 => ⟨((556163645797669/1125899906842624), (375344186081/4503599627370496)), (174819/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211205102454827/2251799813685248), (139901051547/562949953421312)), (524525/1125899906842624), by norm_num⟩
  | 0 => ⟨((33923455296629/35184372088832), (1105634648545/2251799813685248)), (2098687/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((33923455296629/35184372088832), (1105634648545/2251799813685248)), (8005855568892668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093293952963097/2251799813685248), (2132023131157/2251799813685248)), (4049013/2251799813685248), by norm_num⟩
  | 2 => ⟨((1945943418841461/2251799813685248), (3963896880091/2251799813685248)), (1883917/562949953421312), by norm_num⟩
  | 3 => ⟨((1681623763285031/2251799813685248), (6850981157295/2251799813685248)), (13050765/2251799813685248), by norm_num⟩
  | 4 => ⟨((1255800594758091/2251799813685248), (10232501704555/2251799813685248)), (2446475/281474976710656), by norm_num⟩
  | 5 => ⟨((350148894257805/1125899906842624), (1426634557871/281474976710656)), (22007771/2251799813685248), by norm_num⟩
  | 6 => ⟨((870924193715269/9007199254740992), (56790499109923/18014398509481984)), (111293517/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1053596767/16777216)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile025Terms1
