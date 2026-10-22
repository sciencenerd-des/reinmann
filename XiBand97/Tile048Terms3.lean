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
namespace Reinmann.XiBand97.Tile048Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨48,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37559/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37559/1280))
  have he : value ((69/80), (37559/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-715655399/268435456), (-24347193063/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-575387419123089/9007199254740992), (-494460678873837/18014398509481984)), (28059555/18014398509481984), by norm_num⟩
  | 1 => ⟨((13569236295/68719476736), (5830379295/68719476736)), (333/68719476736), by norm_num⟩
  | 2 => ⟨((-20971542723/68719476736), (-563185935/4294967296)), (517/68719476736), by norm_num⟩
  | 3 => ⟨((21607976289/68719476736), (4642217691/34359738368)), (535/68719476736), by norm_num⟩
  | 4 => ⟨((-8348896505/34359738368), (-1793661495/17179869184)), (415/68719476736), by norm_num⟩
  | 5 => ⟨((5161358707/34359738368), (8870854125/137438953472)), (515/137438953472), by norm_num⟩
  | 6 => ⟨((-10386705/134217728), (-1142507779/34359738368)), (533/274877906944), by norm_num⟩
  | 7 => ⟨((18786448007/549755813888), (8072091539/549755813888)), (473/549755813888), by norm_num⟩
  | 8 => ⟨((-3629356771/274877906944), (-6237794409/1099511627776)), (367/1099511627776), by norm_num⟩
  | 9 => ⟨((19943992635/4398046511104), (8569461037/4398046511104)), (253/2199023255552), by norm_num⟩
  | 10 => ⟨((-12329545585/8796093022208), (-5297713573/8796093022208)), (315/8796093022208), by norm_num⟩
  | 11 => ⟨((1732324947/4398046511104), (186084745/1099511627776)), (89/8796093022208), by norm_num⟩
  | 12 => ⟨((-14279173211/140737488355328), (-6135422365/140737488355328)), (23/8796093022208), by norm_num⟩
  | 13 => ⟨((3395194661/140737488355328), (5835338769/562949953421312)), (351/562949953421312), by norm_num⟩
  | 14 => ⟨((-5996966191/1125899906842624), (-10307017065/4503599627370496)), (311/2251799813685248), by norm_num⟩
  | 15 => ⟨((19772668893/18014398509481984), (2123961821/4503599627370496)), (515/18014398509481984), by norm_num⟩
  | 16 => ⟨((-15279539741/72057594037927936), (-3282628079/36028797018963968)), (25/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (-3563643025009/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888924157893401/316912650057057350374175801344), (-2106634961879/316912650057057350374175801344)), (5789/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((14755516250047/309485009821345068724781056), (-4738815935037/39614081257132168796771975168)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888416053399963/2475880078570760549798248448), (-5033620607601/2475880078570760549798248448)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770081893748821/154742504910672534362390528), (-1258019555753/38685626227668133590597632)), (13851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548513497116671/9671406556917033397649408), (-4715934987677/9671406556917033397649408)), (6495/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628939156375429/302231454903657293676544), (-4124805259023/604462909807314587353088)), (11371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943155940223947/37778931862957161709568), (-1674934652817/18889465931478580854784)), (18485/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296428620389413/4722366482869645213696), (-2511059404763/2361183241434822606848)), (867/295147905179352825856), by norm_num⟩
  | 9 => ⟨((809959784096425/295147905179352825856), (-1725262988369/147573952589676412928)), (9543/295147905179352825856), by norm_num⟩
  | 8 => ⟨((56923819119323/2305843009213693952), (-1077472031625/9223372036854775808)), (23875/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910251529560417/4611686018427387904), (-4844131577183/4611686018427387904)), (26885/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591748598182513/1152921504606846976), (-9677040092445/1152921504606846976)), (13459/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192619833674183/144115188075855872), (-8454795619593/144115188075855872)), (5897/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488689393000169/36028797018963968), (-12656993217741/36028797018963968)), (35455/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485561171040053/9007199254740992), (-15777205758143/9007199254740992)), (11111/2251799813685248), by norm_num⟩
  | 2 => ⟨((555130217722327/1125899906842624), (-245488770951/35184372088832)), (22317/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102439254400977/1125899906842624), (-46805126674041/2251799813685248)), (134849/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157951263154681/2251799813685248), (-92300813391003/2251799813685248)), (273513/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2157951263154681/2251799813685248), (-92300813391003/2251799813685248)), (1043369301802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032115329646253/1125899906842624), (-176907961033485/2251799813685248)), (546651/2251799813685248), by norm_num⟩
  | 2 => ⟨((1878387129433067/2251799813685248), (-324343962388557/2251799813685248)), (1088127/2251799813685248), by norm_num⟩
  | 3 => ⟨((1520179183459319/2251799813685248), (-541116950767407/2251799813685248)), (33263/35184372088832), by norm_num⟩
  | 4 => ⟨((896232952480969/2251799813685248), (-365305441173899/1125899906842624)), (487183/281474976710656), by norm_num⟩
  | 5 => ⟨((239311898038365/4503599627370496), (-581577051584941/2251799813685248)), (11263107/4503599627370496), by norm_num⟩
  | 6 => ⟨((-575387419123089/9007199254740992), (-494460678873837/18014398509481984)), (28059555/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-24347193063/268435456)), (1/134217728), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-725947119/268435456), (-24697325959/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-750680646864665/18014398509481984), (943110009990463/18014398509481984)), (13789503/9007199254740992), by norm_num⟩
  | 1 => ⟨((2244715525/17179869184), (-1410062781/8589934592)), (83/17179869184), by norm_num⟩
  | 2 => ⟨((-7038292545/34359738368), (17684974775/68719476736)), (523/68719476736), by norm_num⟩
  | 3 => ⟨((1839043797/8589934592), (-9241856019/34359738368)), (549/68719476736), by norm_num⟩
  | 4 => ⟨((-1441577797/8589934592), (7244446523/34359738368)), (433/68719476736), by norm_num⟩
  | 5 => ⟨((7232094151/68719476736), (-2271492017/17179869184)), (545/137438953472), by norm_num⟩
  | 6 => ⟨((-7558729793/137438953472), (9496333441/137438953472)), (143/68719476736), by norm_num⟩
  | 7 => ⟨((13543059169/549755813888), (-17014684901/549755813888)), (515/549755813888), by norm_num⟩
  | 8 => ⟨((-5308022961/549755813888), (13337361523/1099511627776)), (203/549755813888), by norm_num⟩
  | 9 => ⟨((7397011241/2199023255552), (-2323289995/549755813888)), (71/549755813888), by norm_num⟩
  | 10 => ⟨((-579832149/549755813888), (5827729873/4398046511104)), (179/4398046511104), by norm_num⟩
  | 11 => ⟨((10577805669/35184372088832), (-6644659385/17592186044416)), (205/17592186044416), by norm_num⟩
  | 12 => ⟨((-11055549497/140737488355328), (13889527379/140737488355328)), (215/70368744177664), by norm_num⟩
  | 13 => ⟨((2666508577/140737488355328), (-6700081963/281474976710656)), (417/562949953421312), by norm_num⟩
  | 14 => ⟨((-4777612697/1125899906842624), (12004610423/2251799813685248)), (375/2251799813685248), by norm_num⟩
  | 15 => ⟨((7989427721/9007199254740992), (-2509359103/2251799813685248)), (315/9007199254740992), by norm_num⟩
  | 16 => ⟨((-3131350551/18014398509481984), (7868080953/36028797018963968)), (31/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (1460925088139/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444448098116885/158456325028528675187087900672), (3454263987205/633825300114114700748351602688)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888643352988239/39614081257132168796771975168), (1942564767461/19807040628566084398385987584)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944174826991051/1237940039285380274899124224), (4126810528233/2475880078570760549798248448)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770015773101051/154742504910672534362390528), (2062764453087/77371252455336267181195264)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193556475621955/1208925819614629174706176), (3866322061819/9671406556917033397649408)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((2456688726247/1180591620717411303424), (3381671006261/604462909807314587353088)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943112598190647/37778931862957161709568), (2746332465013/37778931862957161709568)), (577/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296364091474233/4722366482869645213696), (4117268089781/4722366482869645213696)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404957906659595/147573952589676412928), (5657620836277/590295810358705651712)), (19059/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821453461656105/73786976294838206464), (883324409583/9223372036854775808)), (23839/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910191165190149/4611686018427387904), (1985614480453/2305843009213693952)), (3355/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591629884114059/1152921504606846976), (7933139026305/1152921504606846976)), (13433/576460752303423488), by norm_num⟩
  | 5 => ⟨((596259109720437/72057594037927936), (6931024310831/144115188075855872)), (23537/144115188075855872), by norm_num⟩
  | 4 => ⟨((744270739001187/18014398509481984), (648476270273/2251799813685248)), (8841/9007199254740992), by norm_num⟩
  | 3 => ⟨((742692065084701/4503599627370496), (6466493152653/4503599627370496)), (11077/2251799813685248), by norm_num⟩
  | 2 => ⟨((277523776891463/562949953421312), (25756611652371/4503599627370496)), (88927/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204440627270257/2251799813685248), (9590602788039/562949953421312)), (67085/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078652571315817/1125899906842624), (75640164363635/2251799813685248)), (135735/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078652571315817/1125899906842624), (75640164363635/2251799813685248)), (517787937644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516058756168107/562949953421312), (1132281182503/17592186044416)), (538395/2251799813685248), by norm_num⟩
  | 2 => ⟨((470741329801593/562949953421312), (33214952206609/281474976710656)), (264101/562949953421312), by norm_num⟩
  | 3 => ⟨((1543188456189333/2251799813685248), (444391922969643/2251799813685248)), (2016059/2251799813685248), by norm_num⟩
  | 4 => ⟨((969867044504795/2251799813685248), (38068464244841/140737488355328)), (1779501/1125899906842624), by norm_num⟩
  | 5 => ⟨((505946257073579/4503599627370496), (262341962596085/1125899906842624)), (2495573/1125899906842624), by norm_num⟩
  | 6 => ⟨((-750680646864665/18014398509481984), (943110009990463/18014398509481984)), (13789503/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-24697325959/268435456)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-25032554985/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((316710297075515/9007199254740992), (974118554398939/18014398509481984)), (9365879/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3839578143/34359738368), (-184524131/1073741824)), (229/68719476736), by norm_num⟩
  | 2 => ⟨((1525298253/8589934592), (9382841941/34359738368)), (183/34359738368), by norm_num⟩
  | 3 => ⟨((-12926613215/68719476736), (-4969862795/17179869184)), (195/34359738368), by norm_num⟩
  | 4 => ⟨((10270368161/68719476736), (3948622873/17179869184)), (39/8589934592), by norm_num⟩
  | 5 => ⟨((-13055913149/137438953472), (-10039148837/68719476736)), (399/137438953472), by norm_num⟩
  | 6 => ⟨((1728849783/34359738368), (5317492569/68719476736)), (213/137438953472), by norm_num⟩
  | 7 => ⟨((-12558577543/549755813888), (-19313460145/549755813888)), (389/549755813888), by norm_num⟩
  | 8 => ⟨((4988979433/549755813888), (7672401999/549755813888)), (311/1099511627776), by norm_num⟩
  | 9 => ⟨((-7046775643/2199023255552), (-5418512569/1099511627776)), (221/2199023255552), by norm_num⟩
  | 10 => ⟨((4479006465/4398046511104), (3444064925/2199023255552)), (283/8796093022208), by norm_num⟩
  | 11 => ⟨((-5176190419/17592186044416), (-7960308165/17592186044416)), (329/35184372088832), by norm_num⟩
  | 12 => ⟨((10966807859/140737488355328), (16865525237/140737488355328)), (351/140737488355328), by norm_num⟩
  | 13 => ⟨((-5362016265/281474976710656), (-16492168333/562949953421312)), (345/562949953421312), by norm_num⟩
  | 14 => ⟨((4868793237/1125899906842624), (7487571249/1125899906842624)), (315/2251799813685248), by norm_num⟩
  | 15 => ⟨((-8252419731/9007199254740992), (-3172787265/2251799813685248)), (269/9007199254740992), by norm_num⟩
  | 16 => ⟨((3278329267/18014398509481984), (20166577441/72057594037927936)), (429/72057594037927936), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (323778902695/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444435252065431/158456325028528675187087900672), (765508092731/316912650057057350374175801344)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472146460362581/9903520314283042199192993792), (1721986477641/39614081257132168796771975168)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888288943523911/2475880078570760549798248448), (1829099270297/2475880078570760549798248448)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769955507135691/154742504910672534362390528), (1828524276931/154742504910672534362390528)), (13803/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548395777525435/9671406556917033397649408), (53550963247/302231454903657293676544)), (6471/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257776075282613/604462909807314587353088), (187352070079/75557863725914323419136)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886147181559817/75557863725914323419136), (304304122093/9444732965739290427392)), (2301/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648153176071961/2361183241434822606848), (912412187363/2361183241434822606848)), (13809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619753487504987/590295810358705651712), (2507509029311/590295810358705651712)), (1187/36893488147419103232), by norm_num⟩
  | 8 => ⟨((113834853964087/4611686018427387904), (3131951473505/73786976294838206464)), (11873/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820277131598017/9223372036854775808), (880025162527/2305843009213693952)), (6681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397881973966113/288230376151711744), (3515924364187/1152921504606846976)), (1671/72057594037927936), by norm_num⟩
  | 5 => ⟨((149054072702181/18014398509481984), (1535870949207/72057594037927936)), (23407/144115188075855872), by norm_num⟩
  | 4 => ⟨((744210100110349/18014398509481984), (4598244988037/36028797018963968)), (549/562949953421312), by norm_num⟩
  | 3 => ⟨((371311260090955/2251799813685248), (2865724187867/4503599627370496)), (21983/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219949335471135/4503599627370496), (2853491610843/1125899906842624)), (88071/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204171782584625/2251799813685248), (16999123947129/2251799813685248)), (66227/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078566363104611/1125899906842624), (33513934227565/2251799813685248)), (133155/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078566363104611/1125899906842624), (33513934227565/2251799813685248)), (507946018699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032973354563409/1125899906842624), (64209974498567/2251799813685248)), (129539/562949953421312), by norm_num⟩
  | 2 => ⟨((1893602112502367/2251799813685248), (58910381243585/1125899906842624)), (980331/2251799813685248), by norm_num⟩
  | 3 => ⟨((99138675835341/140737488355328), (198157618973433/2251799813685248)), (1751365/2251799813685248), by norm_num⟩
  | 4 => ⟨((549965335920287/1125899906842624), (69793358476425/562949953421312)), (1387821/1125899906842624), by norm_num⟩
  | 5 => ⟨((1005337747856455/4503599627370496), (136367105481455/1125899906842624)), (1699929/1125899906842624), by norm_num⟩
  | 6 => ⟨((316710297075515/9007199254740992), (974118554398939/18014398509481984)), (9365879/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-25032554985/268435456)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-25354097311/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((68661432535971/1125899906842624), (-113403175334443/9007199254740992)), (5281701/9007199254740992), by norm_num⟩
  | 1 => ⟨((-26979080235/137438953472), (348120441/8589934592)), (261/137438953472), by norm_num⟩
  | 2 => ⟨((10855288643/34359738368), (-4482225887/68719476736)), (53/17179869184), by norm_num⟩
  | 3 => ⟨((-11647275395/34359738368), (2404621425/34359738368)), (115/34359738368), by norm_num⟩
  | 4 => ⟨((18745566597/68719476736), (-1935044443/34359738368)), (187/68719476736), by norm_num⟩
  | 5 => ⟨((-24135860457/137438953472), (2491467111/68719476736)), (243/137438953472), by norm_num⟩
  | 6 => ⟨((25896779245/274877906944), (-668310271/34359738368)), (263/274877906944), by norm_num⟩
  | 7 => ⟨((-5954179761/137438953472), (2458523171/274877906944)), (61/137438953472), by norm_num⟩
  | 8 => ⟨((19165765289/1099511627776), (-247302525/68719476736)), (99/549755813888), by norm_num⟩
  | 9 => ⟨((-27418763801/4398046511104), (1415175323/1099511627776)), (143/2199023255552), by norm_num⟩
  | 10 => ⟨((17651519189/8796093022208), (-911054727/2199023255552)), (93/4398046511104), by norm_num⟩
  | 11 => ⟨((-20661108505/35184372088832), (4265559325/35184372088832)), (219/35184372088832), by norm_num⟩
  | 12 => ⟨((22168514227/140737488355328), (-4576768597/140737488355328)), (237/140737488355328), by norm_num⟩
  | 13 => ⟨((-10978106849/281474976710656), (2266469199/281474976710656)), (237/562949953421312), by norm_num⟩
  | 14 => ⟨((10096332211/1125899906842624), (-2084423689/1125899906842624)), (55/562949953421312), by norm_num⟩
  | 15 => ⟨((-4333178623/2251799813685248), (3578400545/9007199254740992)), (191/9007199254740992), by norm_num⟩
  | 16 => ⟨((6973981957/18014398509481984), (-5759213503/72057594037927936)), (155/36028797018963968), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-265202784723/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777687997089057/633825300114114700748351602688), (-313490265271/633825300114114700748351602688)), (5765/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944263141977507/19807040628566084398385987584), (-352592508599/39614081257132168796771975168)), (12971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888225770161773/2475880078570760549798248448), (-374523519431/2475880078570760549798248448)), (6891/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769892453425435/154742504910672534362390528), (-23400269453/9671406556917033397649408)), (13783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548336791704677/9671406556917033397649408), (-87719359177/2417851639229258349412352)), (12921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724589612211/604462909807314587353088), (-76722803095/151115727451828646838272)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943031877546179/37778931862957161709568), (-498461076897/75557863725914323419136)), (18373/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324060997522219/1180591620717411303424), (-186819217719/2361183241434822606848)), (13781/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619668076910585/590295810358705651712), (-513416108829/590295810358705651712)), (18949/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821251405266361/73786976294838206464), (-80158180727/9223372036854775808)), (2961/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820158284421421/9223372036854775808), (-360365179369/4611686018427387904)), (26651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795704956699465/576460752303423488), (-719864794723/1152921504606846976)), (26653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74520644825943/9007199254740992), (-314454668775/72057594037927936)), (23325/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488268737778719/36028797018963968), (-941422789375/36028797018963968)), (2187/2251799813685248), by norm_num⟩
  | 3 => ⟨((371264770712223/2251799813685248), (-586694607039/4503599627370496)), (21875/4503599627370496), by norm_num⟩
  | 2 => ⟨((554896868816495/1125899906842624), (-2336641963035/4503599627370496)), (87529/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203653931446069/2251799813685248), (-3479731178549/2251799813685248)), (32843/562949953421312), by norm_num⟩
  | 0 => ⟨((2156195600148885/2251799813685248), (-6859188978009/2251799813685248)), (131531/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156195600148885/2251799813685248), (-6859188978009/2251799813685248)), (501750950339889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032314770916359/1125899906842624), (-102624527591/17592186044416)), (252695/1125899906842624), by norm_num⟩
  | 2 => ⟨((946470144947087/1125899906842624), (-6022038160751/562949953421312)), (932661/2251799813685248), by norm_num⟩
  | 3 => ⟨((397753241677333/562949953421312), (-5062332180901/281474976710656)), (1588009/2251799813685248), by norm_num⟩
  | 4 => ⟨((1123404533390639/2251799813685248), (-7153598728141/281474976710656)), (2301143/2251799813685248), by norm_num⟩
  | 5 => ⟨((279501446711137/1125899906842624), (-114203903098813/4503599627370496)), (2413009/2251799813685248), by norm_num⟩
  | 6 => ⟨((68661432535971/1125899906842624), (-113403175334443/9007199254740992)), (5281701/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-25354097311/268435456)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-754332693/268435456), (-6415756709/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((232793508525861/18014398509481984), (-529579032930883/9007199254740992)), (2564351/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2893309495/68719476736), (26327813931/137438953472)), (1/268435456), by norm_num⟩
  | 2 => ⟨((4713340825/68719476736), (-1340289991/4294967296)), (419/68719476736), by norm_num⟩
  | 3 => ⟨((-4998867/67108864), (11644784479/34359738368)), (457/68719476736), by norm_num⟩
  | 4 => ⟨((1042354641/17179869184), (-18969915999/68719476736)), (187/34359738368), by norm_num⟩
  | 5 => ⟨((-1358436819/34359738368), (24722327057/137438953472)), (245/68719476736), by norm_num⟩
  | 6 => ⟨((1475306099/68719476736), (-6712310683/68719476736)), (267/137438953472), by norm_num⟩
  | 7 => ⟨((-2746679825/274877906944), (24993549941/549755813888)), (499/549755813888), by norm_num⟩
  | 8 => ⟨((2237237007/549755813888), (-10178924817/549755813888)), (51/137438953472), by norm_num⟩
  | 9 => ⟨((-3239615177/2199023255552), (7369759935/1099511627776)), (297/2199023255552), by norm_num⟩
  | 10 => ⟨((4221991597/8796093022208), (-2401138933/1099511627776)), (389/8796093022208), by norm_num⟩
  | 11 => ⟨((-2501028401/17592186044416), (22758232567/35184372088832)), (231/17592186044416), by norm_num⟩
  | 12 => ⟨((2716197325/70368744177664), (-24716172913/140737488355328)), (63/17592186044416), by norm_num⟩
  | 13 => ⟨((-2722964031/281474976710656), (24777746893/562949953421312)), (507/562949953421312), by norm_num⟩
  | 14 => ⟨((5069531247/2251799813685248), (-11532613053/1125899906842624)), (237/1125899906842624), by norm_num⟩
  | 15 => ⟨((-4404539255/9007199254740992), (5009915555/2251799813685248)), (207/4503599627370496), by norm_num⟩
  | 16 => ⟨((3587603525/36028797018963968), (-8161394263/18014398509481984)), (339/36028797018963968), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (-1764316219549/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777633629871505/633825300114114700748351602688), (-2085442074021/633825300114114700748351602688)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944232505550691/19807040628566084398385987584), (-586388473087/9903520314283042199192993792)), (12997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888160518437879/2475880078570760549798248448), (-2491436802819/2475880078570760549798248448)), (3453/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442456758487245/38685626227668133590597632), (-1245316855791/77371252455336267181195264)), (6907/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774137641435487/4835703278458516698824704), (-2334116158485/9671406556917033397649408)), (1619/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157208823936417/75557863725914323419136), (-1020749536629/302231454903657293676544)), (11335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942987837494217/37778931862957161709568), (-1657919121251/37778931862957161709568)), (2303/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296177638886597/4722366482869645213696), (-155342591091/295147905179352825856)), (13823/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809788185829009/295147905179352825856), (-3415268028731/590295810358705651712)), (4753/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821136066448267/73786976294838206464), (-4265684221387/73786976294838206464)), (23773/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910013778921363/4611686018427387904), (-1198555732311/2305843009213693952)), (13379/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591277976900237/1152921504606846976), (-2394194799335/576460752303423488)), (26773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192213515859777/144115188075855872), (-4183287252897/144115188075855872)), (23445/144115188075855872), by norm_num⟩
  | 4 => ⟨((372022708121405/9007199254740992), (-6261845685453/36028797018963968)), (17601/18014398509481984), by norm_num⟩
  | 3 => ⟨((742415997129559/4503599627370496), (-3902228828601/4503599627370496)), (44065/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109559635876823/2251799813685248), (-15540565121067/4503599627370496)), (44159/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202916889876443/2251799813685248), (-11570331965467/1125899906842624)), (132949/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154584536835295/2251799813685248), (-356286943703/17592186044416)), (267799/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154584536835295/2251799813685248), (-356286943703/17592186044416)), (1021572121627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060642649884321/2251799813685248), (-87271739582637/2251799813685248)), (523323/2251799813685248), by norm_num⟩
  | 2 => ⟨((1882330635357697/2251799813685248), (-79863168839713/1125899906842624)), (124795/281474976710656), by norm_num⟩
  | 3 => ⟨((1562153125903633/2251799813685248), (-267037750745189/2251799813685248)), (1810737/2251799813685248), by norm_num⟩
  | 4 => ⟨((526026606372785/1125899906842624), (-370507053536137/2251799813685248)), (2941811/2251799813685248), by norm_num⟩
  | 5 => ⟨((861124936449405/4503599627370496), (-346205851558057/2251799813685248)), (7433883/4503599627370496), by norm_num⟩
  | 6 => ⟨((232793508525861/18014398509481984), (-529579032930883/9007199254740992)), (2564351/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-6415756709/67108864)), (1/134217728), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-763070545/268435456), (-6490073955/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-816399804903329/18014398509481984), (-659832026160483/18014398509481984)), (24142061/18014398509481984), by norm_num⟩
  | 1 => ⟨((5132142209/34359738368), (4147908625/34359738368)), (305/68719476736), by norm_num⟩
  | 2 => ⟨((-8457351747/34359738368), (-13670830163/68719476736)), (63/8589934592), by norm_num⟩
  | 3 => ⟨((9291350559/34359738368), (15018942013/68719476736)), (139/17179869184), by norm_num⟩
  | 4 => ⟨((-7655693927/34359738368), (-6187497847/34359738368)), (115/17179869184), by norm_num⟩
  | 5 => ⟨((630797957/4294967296), (8157193405/68719476736)), (305/68719476736), by norm_num⟩
  | 6 => ⟨((-2772009549/34359738368), (-2240398229/34359738368)), (337/137438953472), by norm_num⟩
  | 7 => ⟨((10441247159/274877906944), (8438842375/274877906944)), (319/274877906944), by norm_num⟩
  | 8 => ⟨((-17206323657/1099511627776), (-13906523903/1099511627776)), (527/1099511627776), by norm_num⟩
  | 9 => ⟨((1575256551/274877906944), (10185252035/2199023255552)), (97/549755813888), by norm_num⟩
  | 10 => ⟨((-8306861783/4398046511104), (-13427571659/8796093022208)), (257/4398046511104), by norm_num⟩
  | 11 => ⟨((311114333/549755813888), (8046379217/17592186044416)), (155/8796093022208), by norm_num⟩
  | 12 => ⟨((-10937408941/70368744177664), (-8839851087/70368744177664)), (171/35184372088832), by norm_num⟩
  | 13 => ⟨((2772916585/70368744177664), (4482262631/140737488355328)), (349/281474976710656), by norm_num⟩
  | 14 => ⟨((-10444663665/1125899906842624), (-4220801835/562949953421312)), (165/562949953421312), by norm_num⟩
  | 15 => ⟨((18359417365/9007199254740992), (14838479245/9007199254740992)), (291/4503599627370496), by norm_num⟩
  | 16 => ⟨((-3781852787/9007199254740992), (-12226301733/36028797018963968)), (241/18014398509481984), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (-3206845636805/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777578136222449/633825300114114700748351602688), (-947581141411/158456325028528675187087900672)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944201151697551/19807040628566084398385987584), (-2131528975493/19807040628566084398385987584)), (6511/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888093515160705/2475880078570760549798248448), (-4528184517573/2475880078570760549798248448)), (865/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((884879803914375/77371252455336267181195264), (-2263353070575/77371252455336267181195264)), (13843/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548211622015625/9671406556917033397649408), (-4242216746931/9671406556917033397649408)), (6491/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628807219914521/302231454903657293676544), (-3710369971577/604462909807314587353088)), (2841/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885883588724755/75557863725914323419136), (-3013204639485/37778931862957161709568)), (18473/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296107840315687/4722366482869645213696), (-4517234003599/4722366482869645213696)), (6931/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619479207882589/590295810358705651712), (-775877250639/73786976294838206464)), (19071/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910506414385477/36893488147419103232), (-7752508410827/73786976294838206464)), (1491/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1819886469005089/9223372036854775808), (-4356482688015/4611686018427387904)), (6715/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198891729707883/144115188075855872), (-8702216957379/1152921504606846976)), (26889/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192083972847383/144115188075855872), (-7602361354785/144115188075855872)), (2945/18014398509481984), by norm_num⟩
  | 4 => ⟨((1487889701852077/36028797018963968), (-11379418767721/36028797018963968)), (8851/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484568711667849/9007199254740992), (-3545533380813/2251799813685248)), (44369/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109278666768459/2251799813685248), (-28238150083543/4503599627370496)), (44539/2251799813685248), by norm_num⟩
  | 1 => ⟨((2201986368650561/2251799813685248), (-42042991508555/2251799813685248)), (134473/2251799813685248), by norm_num⟩
  | 0 => ⟨((538094481061951/562949953421312), (-20708847970991/562949953421312)), (136193/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538094481061951/562949953421312), (-20708847970991/562949953421312)), (519535068992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1027149260455377/1125899906842624), (-158356056123541/2251799813685248)), (67595/281474976710656), by norm_num⟩
  | 2 => ⟨((1862983444180837/2251799813685248), (-288933865164021/2251799813685248)), (16605/35184372088832), by norm_num⟩
  | 3 => ⟨((188028733408467/281474976710656), (-478087798029269/2251799813685248)), (2031163/2251799813685248), by norm_num⟩
  | 4 => ⟨((451669712954369/1125899906842624), (-638737014366245/2251799813685248)), (894043/562949953421312), by norm_num⟩
  | 5 => ⟨((362409786518135/4503599627370496), (-1024951373310517/4503599627370496)), (9796131/4503599627370496), by norm_num⟩
  | 6 => ⟨((-816399804903329/18014398509481984), (-659832026160483/18014398509481984)), (24142061/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-6490073955/67108864)), (1/134217728), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile048Terms3
