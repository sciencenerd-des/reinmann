/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile005Terms0
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
  | 0 => ⟨((69/80), (2127/128)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (2127/128))
  have he : value ((69/80), (2127/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-320962607/536870912), (-6183763273/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((618152967018139/2251799813685248), (67074371139217/140737488355328)), (4957389/1125899906842624), by norm_num⟩
  | 1 => ⟨((-408621775/2147483648), (-2837671585/8589934592)), (7/2147483648), by norm_num⟩
  | 2 => ⟨((1132940125/17179869184), (3933848117/34359738368)), (41/34359738368), by norm_num⟩
  | 3 => ⟨((-2094118009/137438953472), (-1817823821/68719476736)), (5/17179869184), by norm_num⟩
  | 4 => ⟨((725765997/274877906944), (5040077825/1099511627776)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((-1609800495/4398046511104), (-698703147/1099511627776)), (17/2199023255552), by norm_num⟩
  | 6 => ⟨((743885783/17592186044416), (5165910575/70368744177664)), (65/70368744177664), by norm_num⟩
  | 7 => ⟨((-1178565333/281474976710656), (-4092270115/562949953421312)), (53/562949953421312), by norm_num⟩
  | 8 => ⟨((1633838475/4503599627370496), (709136373/1125899906842624)), (39/4503599627370496), by norm_num⟩
  | 9 => ⟨((-1006658251/36028797018963968), (-3495366241/72057594037927936)), (25/36028797018963968), by norm_num⟩
  | 10 => ⟨((2232839451/1152921504606846976), (484560651/144115188075855872)), (57/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-2251180175/18446744073709551616), (-3908326971/18446744073709551616)), (59/18446744073709551616), by norm_num⟩
  | 12 => ⟨((2080532255/295147905179352825856), (1806030547/147573952589676412928)), (57/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-1774910851/4722366482869645213696), (-1540732285/2361183241434822606848)), (51/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((2812055891/151115727451828646838272), (4882076523/151115727451828646838272)), (83/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-2079113187/2417851639229258349412352), (-451199677/302231454903657293676544)), (63/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((2882262887/77371252455336267181195264), (39093473/604462909807314587353088)), (45/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (1365415703457/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781047026207319/633825300114114700748351602688), (1619836813161/633825300114114700748351602688)), (5773/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946152275800447/19807040628566084398385987584), (1822216734359/39614081257132168796771975168)), (6495/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892239389223483/2475880078570760549798248448), (1935986948667/2475880078570760549798248448)), (3451/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773905183674217/154742504910672534362390528), (967926911621/77371252455336267181195264)), (6903/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552097782210253/9671406556917033397649408), (1814721513261/9671406556917033397649408)), (809/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630507256247859/302231454903657293676544), (1587739877777/604462909807314587353088)), (5665/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945704055380233/37778931862957161709568), (644953022225/18889465931478580854784)), (4603/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650125354786669/2361183241434822606848), (1934627005133/4722366482869645213696)), (6907/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625174803062451/590295810358705651712), (1329867515457/295147905179352825856)), (4749/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228516380661481/9223372036854775808), (3324103134977/73786976294838206464)), (2969/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913946351115919/4611686018427387904), (934709562489/2305843009213693952)), (3341/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599137864663025/1152921504606846976), (3737866024311/1152921504606846976)), (13371/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199085006543029/144115188075855872), (3269539011391/144115188075855872)), (5853/72057594037927936), by norm_num⟩
  | 4 => ⟨((749193126393445/18014398509481984), (2451060491423/18014398509481984)), (17573/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497680606749607/9007199254740992), (6123823012701/9007199254740992)), (10995/4503599627370496), by norm_num⟩
  | 2 => ⟨((561188641670415/1125899906842624), (3059040315567/1125899906842624)), (11013/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120607606316161/1125899906842624), (4581382404479/562949953421312)), (4141/140737488355328), by norm_num⟩
  | 0 => ⟨((69705123118007/70368744177664), (18268104111087/1125899906842624)), (33307/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69705123118007/70368744177664), (18268104111087/1125899906842624)), (127056123973655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((276116940141001/281474976710656), (18095824518069/562949953421312)), (67067/562949953421312), by norm_num⟩
  | 2 => ⟨((1082280219813213/1125899906842624), (4437840046785/70368744177664)), (135893/562949953421312), by norm_num⟩
  | 3 => ⟨((1035872455886135/1125899906842624), (34127271684741/281474976710656)), (278397/562949953421312), by norm_num⟩
  | 4 => ⟨((468246336860497/562949953421312), (3924805006857/17592186044416)), (1159563/1125899906842624), by norm_num⟩
  | 5 => ⟨((722909161429257/1125899906842624), (417861785388715/1125899906842624)), (1223191/562949953421312), by norm_num⟩
  | 6 => ⟨((618152967018139/2251799813685248), (67074371139217/140737488355328)), (4957389/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-6183763273/536870912)), (1/268435456), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-4900516451/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((180900479700647/562949953421312), (488389019750379/2251799813685248)), (5397871/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3032523957/8589934592), (-511694125/2147483648)), (47/8589934592), by norm_num⟩
  | 2 => ⟨((3331568085/17179869184), (2248613815/17179869184)), (53/17179869184), by norm_num⟩
  | 3 => ⟨((-2440067759/34359738368), (-411725795/8589934592)), (81/68719476736), by norm_num⟩
  | 4 => ⟨((2680688425/137438953472), (226163509/17179869184)), (23/68719476736), by norm_num⟩
  | 5 => ⟨((-4712059593/1099511627776), (-3180364931/1099511627776)), (21/274877906944), by norm_num⟩
  | 6 => ⟨((3451151049/4398046511104), (2329325331/4398046511104)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((-4333116517/35184372088832), (-2924600495/35184372088832)), (83/35184372088832), by norm_num⟩
  | 8 => ⟨((2380207527/140737488355328), (3213002043/281474976710656)), (47/140737488355328), by norm_num⟩
  | 9 => ⟨((-1162188995/562949953421312), (-784409673/562949953421312)), (47/1125899906842624), by norm_num⟩
  | 10 => ⟨((4085744357/18014398509481984), (689409685/4503599627370496)), (85/18014398509481984), by norm_num⟩
  | 11 => ⟨((-1632235985/72057594037927936), (-550831965/36028797018963968)), (35/72057594037927936), by norm_num⟩
  | 12 => ⟨((2390926015/1152921504606846976), (3227470751/2305843009213693952)), (105/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-1616431201/9223372036854775808), (-68187289/576460752303423488)), (73/18446744073709551616), by norm_num⟩
  | 14 => ⟨((1014760675/73786976294838206464), (2739616681/295147905179352825856)), (47/147573952589676412928), by norm_num⟩
  | 15 => ⟨((-4756601803/4722366482869645213696), (-1605214161/2361183241434822606848)), (113/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((2612830597/37778931862957161709568), (1763508003/37778931862957161709568)), (1/590295810358705651712), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (193343237441/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780507707968493/633825300114114700748351602688), (916949104535/633825300114114700748351602688)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891697918887215/39614081257132168796771975168), (515740007337/19807040628566084398385987584)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945797481598423/1237940039285380274899124224), (547920751309/1237940039285380274899124224)), (431/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((886630447008771/77371252455336267181195264), (1095722252909/154742504910672534362390528)), (13793/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775746952765849/4835703278458516698824704), (513556462635/4835703278458516698824704)), (3233/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630243132627871/302231454903657293676544), (898597140759/604462909807314587353088)), (2829/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945274990276035/37778931862957161709568), (1459982887837/75557863725914323419136)), (18391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299607349484799/4722366482869645213696), (547389710707/2361183241434822606848)), (13795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624290568905377/590295810358705651712), (1504984191295/590295810358705651712)), (9485/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114189145712335/4611686018427387904), (1880724094679/73786976294838206464)), (5929/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913325347358615/4611686018427387904), (1057559430725/4611686018427387904)), (13343/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199737106414437/144115188075855872), (528562371337/288230376151711744)), (26693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599000118907729/72057594037927936), (462247667781/36028797018963968)), (23365/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496761334382473/36028797018963968), (346441474759/4503599627370496)), (17531/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495653366710081/9007199254740992), (3460997240555/9007199254740992)), (21927/4503599627370496), by norm_num⟩
  | 2 => ⟨((2240711799556309/4503599627370496), (3455875693363/2251799813685248)), (87789/4503599627370496), by norm_num⟩
  | 1 => ⟨((1117590153012513/1125899906842624), (5171026156609/1125899906842624)), (131887/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218610873075511/2251799813685248), (643187599317/70368744177664)), (132295/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218610873075511/2251799813685248), (643187599317/70368744177664)), (504665379050826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((17075960740111/17592186044416), (5069662028035/281474976710656)), (526219/2251799813685248), by norm_num⟩
  | 2 => ⟨((1060427307742791/1125899906842624), (39367182469667/1125899906842624)), (8129/17592186044416), by norm_num⟩
  | 3 => ⟨((62336596992675/70368744177664), (148311710716087/2251799813685248)), (1016387/1125899906842624), by norm_num⟩
  | 4 => ⟨((1757312248110797/2251799813685248), (262765733515463/2251799813685248)), (241829/140737488355328), by norm_num⟩
  | 5 => ⟨((1340749958456257/2251799813685248), (51265818467099/281474976710656)), (3471097/1125899906842624), by norm_num⟩
  | 6 => ⟨((180900479700647/562949953421312), (488389019750379/2251799813685248)), (5397871/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-4900516451/268435456)), (1/134217728), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-320962607/268435456), (-6183763273/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-683563030960383/4503599627370496), (589213606340633/2251799813685248)), (30068947/4503599627370496), by norm_num⟩
  | 1 => ⟨((1807440901/8589934592), (-778983593/2147483648)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((-2505645129/17179869184), (2159801125/8589934592)), (57/8589934592), by norm_num⟩
  | 3 => ⟨((2315707809/34359738368), (-3992160161/34359738368)), (107/34359738368), by norm_num⟩
  | 4 => ⟨((-1605126339/68719476736), (21618395/536870912)), (19/17179869184), by norm_num⟩
  | 5 => ⟨((890071037/137438953472), (-1534436305/137438953472)), (43/137438953472), by norm_num⟩
  | 6 => ⟨((-1645200613/1099511627776), (1418120265/549755813888)), (81/1099511627776), by norm_num⟩
  | 7 => ⟨((1303275619/4398046511104), (-4493559147/8796093022208)), (131/8796093022208), by norm_num⟩
  | 8 => ⟨((-903361821/17592186044416), (1557348927/17592186044416)), (93/35184372088832), by norm_num⟩
  | 9 => ⟨((278294533/35184372088832), (-3838122731/281474976710656)), (117/281474976710656), by norm_num⟩
  | 10 => ⟨((-617277027/562949953421312), (266038395/140737488355328)), (33/562949953421312), by norm_num⟩
  | 11 => ⟨((1244694781/9007199254740992), (-2145789247/9007199254740992)), (135/18014398509481984), by norm_num⟩
  | 12 => ⟨((-2300684475/144115188075855872), (3966260711/144115188075855872)), (127/144115188075855872), by norm_num⟩
  | 13 => ⟨((245340455/144115188075855872), (-3383633759/1152921504606846976)), (55/576460752303423488), by norm_num⟩
  | 14 => ⟨((-3109614531/18446744073709551616), (1340203543/4611686018427387904)), (11/1152921504606846976), by norm_num⟩
  | 15 => ⟨((143694703/9223372036854775808), (-990888861/36893488147419103232)), (33/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-398406313/295147905179352825856), (2747327281/1180591620717411303424)), (93/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (2730831406915/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222514928541221/79228162514264337593543950336), (3236484956933/633825300114114700748351602688)), (5783/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891260842445867/39614081257132168796771975168), (1820323358323/19807040628566084398385987584)), (6507/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945565120081229/1237940039285380274899124224), (3867713819865/2475880078570760549798248448)), (6915/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886397900327821/77371252455336267181195264), (1933590651333/77371252455336267181195264)), (13833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387764371797947/2417851639229258349412352), (906229167519/2417851639229258349412352)), (3243/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630052003037475/302231454903657293676544), (3171236283259/604462909807314587353088)), (5677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889928072640131/75557863725914323419136), (5152198075687/75557863725914323419136)), (18457/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299140274282431/4722366482869645213696), (965805069749/1180591620717411303424)), (13849/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811823647140875/295147905179352825856), (5310419425535/590295810358705651712)), (19051/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826220670039611/73786976294838206464), (3317880791823/36893488147419103232)), (5957/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825742171616677/9223372036854775808), (7462120554477/9223372036854775808)), (13413/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399246409668563/288230376151711744), (7458231497021/1152921504606846976)), (13425/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197199905214079/144115188075855872), (1630394335259/36028797018963968)), (11761/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495554802877253/36028797018963968), (9773615510273/36028797018963968)), (4417/4503599627370496), by norm_num⟩
  | 3 => ⟨((1494134668833395/9007199254740992), (12201705893615/9007199254740992)), (22133/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118821448744715/2251799813685248), (12178735483319/2251799813685248)), (22205/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115249258214897/1125899906842624), (9105338449987/562949953421312)), (2093/35184372088832), by norm_num⟩
  | 0 => ⟨((276116940141001/281474976710656), (18095824518069/562949953421312)), (67699/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276116940141001/281474976710656), (18095824518069/562949953421312)), (258251192333030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1082280219813213/1125899906842624), (4437840046785/70368744177664)), (274347/1125899906842624), by norm_num⟩
  | 2 => ⟨((1035872455886135/1125899906842624), (34127271684741/281474976710656)), (562041/1125899906842624), by norm_num⟩
  | 3 => ⟨((468246336860497/562949953421312), (3924805006857/17592186044416)), (585245/562949953421312), by norm_num⟩
  | 4 => ⟨((722909161429257/1125899906842624), (417861785388715/1125899906842624)), (2469435/1125899906842624), by norm_num⟩
  | 5 => ⟨((618152967018139/2251799813685248), (67074371139217/140737488355328)), (625513/140737488355328), by norm_num⟩
  | 6 => ⟨((-683563030960383/4503599627370496), (589213606340633/2251799813685248)), (30068947/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-6183763273/268435456)), (1/134217728), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372626047/268435456), (-3589563419/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22916275735445/2251799813685248), (-140361077494771/562949953421312)), (11309357/2251799813685248), by norm_num⟩
  | 1 => ⟨((281389793/17179869184), (1723498837/4294967296)), (141/17179869184), by norm_num⟩
  | 2 => ⟨((-226439701/17179869184), (-5547728741/17179869184)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((121480213/17179869184), (5952483309/34359738368)), (127/34359738368), by norm_num⟩
  | 4 => ⟨((-48878715/17179869184), (-4790076155/68719476736)), (13/8589934592), by norm_num⟩
  | 5 => ⟨((251735223/274877906944), (3083732067/137438953472)), (17/34359738368), by norm_num⟩
  | 6 => ⟨((-270101475/1099511627776), (-3308716867/549755813888)), (37/274877906944), by norm_num⟩
  | 7 => ⟨((124203301/2199023255552), (6085913563/4398046511104)), (69/2199023255552), by norm_num⟩
  | 8 => ⟨((-199897501/17592186044416), (-2448725005/8796093022208)), (113/17592186044416), by norm_num⟩
  | 9 => ⟨((285975659/140737488355328), (1751587049/35184372088832)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((-184104027/562949953421312), (-2255256483/281474976710656)), (107/562949953421312), by norm_num⟩
  | 11 => ⟨((215493819/4503599627370496), (1319889195/1125899906842624)), (127/4503599627370496), by norm_num⟩
  | 12 => ⟨((-57803987/9007199254740992), (-5664745895/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 13 => ⟨((229001669/288230376151711744), (5610496497/288230376151711744)), (139/288230376151711744), by norm_num⟩
  | 14 => ⟨((-105303991/1152921504606846976), (-2579927363/1152921504606846976)), (65/1152921504606846976), by norm_num⟩
  | 15 => ⟨((90389459/9223372036854775808), (4429048437/18446744073709551616)), (113/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-72738111/73786976294838206464), (-7128278471/295147905179352825856)), (23/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582167559511033/10141204801825835211973625643008), (-1049638171415/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779824638811387/633825300114114700748351602688), (-1243599537659/316912650057057350374175801344)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945464689680057/19807040628566084398385987584), (-2797749609473/39614081257132168796771975168)), (13003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890778276394523/2475880078570760549798248448), (-743046835489/618970019642690137449562112)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443111019891203/38685626227668133590597632), (-2971713064507/154742504910672534362390528)), (3455/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550728006445243/9671406556917033397649408), (-1392738568763/4835703278458516698824704)), (12959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78738498007565/37778931862957161709568), (-2436788701607/604462909807314587353088)), (5671/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944730246994025/37778931862957161709568), (-494854646085/9444732965739290427392)), (4609/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298790012775307/4722366482869645213696), (-2968301605843/4722366482869645213696)), (1729/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811583185468277/295147905179352825856), (-4080072284203/590295810358705651712)), (19025/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114101284041445/4611686018427387904), (-5098077185127/73786976294838206464)), (1487/4611686018427387904), by norm_num⟩
  | 7 => ⟨((228133555538059/1152921504606846976), (-358285592575/576460752303423488)), (26781/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596313677226483/1152921504606846976), (-2864555713391/576460752303423488)), (26799/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299153480937177/36028797018963968), (-5009083749383/144115188075855872)), (23471/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494679795790951/36028797018963968), (-7505852033261/36028797018963968)), (2203/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493047838813547/9007199254740992), (-9368720054181/9007199254740992)), (44133/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117744991760493/2251799813685248), (-9348345178905/2251799813685248)), (11061/562949953421312), by norm_num⟩
  | 1 => ⟨((8700472144723/8796093022208), (-13971642257685/1125899906842624)), (66643/1125899906842624), by norm_num⟩
  | 0 => ⟨((550696567643967/562949953421312), (-27740152992325/1125899906842624)), (67199/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550696567643967/562949953421312), (-27740152992325/1125899906842624)), (256343843700218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1076736319990477/1125899906842624), (-6784087531205/140737488355328)), (269569/1125899906842624), by norm_num⟩
  | 2 => ⟨((256775839878431/281474976710656), (-25951413259559/281474976710656)), (270793/562949953421312), by norm_num⟩
  | 3 => ⟨((28981419972809/35184372088832), (-378787259237215/2251799813685248)), (2175983/2251799813685248), by norm_num⟩
  | 4 => ⟨((732046336071681/1125899906842624), (-624015265219839/2251799813685248)), (4316789/2251799813685248), by norm_num⟩
  | 5 => ⟨((779008991268039/2251799813685248), (-811454172401549/2251799813685248)), (2001493/562949953421312), by norm_num⟩
  | 6 => ⟨((-22916275735445/2251799813685248), (-140361077494771/562949953421312)), (11309357/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-372626047/268435456), (-3589563419/134217728)), (1/134217728), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-7992398087/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-68245418875801/4503599627370496), (478933078976467/2251799813685248)), (4884691/1125899906842624), by norm_num⟩
  | 1 => ⟨((466458799/17179869184), (-6547034297/17179869184)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((-417890985/17179869184), (5865355349/17179869184)), (123/17179869184), by norm_num⟩
  | 3 => ⟨((124793355/8589934592), (-875775499/4294967296)), (149/34359738368), by norm_num⟩
  | 4 => ⟨((-447199351/68719476736), (6276716173/68719476736)), (135/68719476736), by norm_num⟩
  | 5 => ⟨((320509469/137438953472), (-281159141/8589934592)), (49/68719476736), by norm_num⟩
  | 6 => ⟨((-47856323/68719476736), (2686770951/274877906944)), (119/549755813888), by norm_num⟩
  | 7 => ⟨((391986377/2199023255552), (-5501768335/2199023255552)), (31/549755813888), by norm_num⟩
  | 8 => ⟨((-351172651/8796093022208), (1232230689/2199023255552)), (113/8796093022208), by norm_num⟩
  | 9 => ⟨((559303931/70368744177664), (-490635779/4398046511104)), (91/35184372088832), by norm_num⟩
  | 10 => ⟨((-200427623/140737488355328), (5626248339/281474976710656)), (33/70368744177664), by norm_num⟩
  | 11 => ⟨((130588397/562949953421312), (-3665775905/1125899906842624)), (87/1125899906842624), by norm_num⟩
  | 12 => ⟨((-311977329/9007199254740992), (1094698115/2251799813685248)), (105/9007199254740992), by norm_num⟩
  | 13 => ⟨((343992821/72057594037927936), (-4828149449/72057594037927936)), (59/36028797018963968), by norm_num⟩
  | 14 => ⟨((-44025171/72057594037927936), (4943361425/576460752303423488)), (123/576460752303423488), by norm_num⟩
  | 15 => ⟨((168282703/2305843009213693952), (-4723901143/4611686018427387904)), (119/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-301522127/36893488147419103232), (4232047303/36893488147419103232)), (109/36893488147419103232), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (66837145489/316912650057057350374175801344)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889790927043933/316912650057057350374175801344), (1266677963471/316912650057057350374175801344)), (11557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472664069051099/9903520314283042199192993792), (2849631057757/39614081257132168796771975168)), (3251/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945244069311559/1237940039285380274899124224), (378406876919/309485009821345068724781056)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772153980429813/154742504910672534362390528), (1513358675751/77371252455336267181195264)), (13821/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387614019891215/2417851639229258349412352), (2836976333891/9671406556917033397649408)), (405/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259578073167825/604462909807314587353088), (310222900531/75557863725914323419136)), (11343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889073991707839/75557863725914323419136), (4031827119469/75557863725914323419136)), (18437/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324625050868613/1180591620717411303424), (1511466889001/2361183241434822606848)), (13833/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811383996360735/295147905179352825856), (4155012411691/590295810358705651712)), (19027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456280684078277/18446744073709551616), (2595741939637/36893488147419103232)), (11897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228063579510173/1152921504606846976), (5837283195109/9223372036854775808)), (837/288230376151711744), by norm_num⟩
  | 6 => ⟨((1595754151858487/1152921504606846976), (729170575405/144115188075855872)), (13401/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196124657457949/144115188075855872), (1274946959767/36028797018963968)), (11737/72057594037927936), by norm_num⟩
  | 4 => ⟨((373486633412749/9007199254740992), (1910218737429/9007199254740992)), (17627/18014398509481984), by norm_num⟩
  | 3 => ⟨((373033094372487/2251799813685248), (297990446987/281474976710656)), (22071/4503599627370496), by norm_num⟩
  | 2 => ⟨((139603900889585/281474976710656), (4756310149255/1125899906842624)), (22127/1125899906842624), by norm_num⟩
  | 1 => ⟨((34759186147917/35184372088832), (14211333208981/1125899906842624)), (66665/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098677020777979/1125899906842624), (28192804326755/1125899906842624)), (134463/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098677020777979/1125899906842624), (28192804326755/1125899906842624)), (512935642722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((267851599071671/281474976710656), (13755568357741/281474976710656)), (134579/562949953421312), by norm_num⟩
  | 2 => ⟨((2033722906401371/2251799813685248), (104718395185745/1125899906842624)), (538569/1125899906842624), by norm_num⟩
  | 3 => ⟨((908643180888131/1125899906842624), (94576879221915/562949953421312)), (2146011/2251799813685248), by norm_num⟩
  | 4 => ⟨((1403061286426553/2251799813685248), (305308263558407/1125899906842624)), (1046223/562949953421312), by norm_num⟩
  | 5 => ⟨((177161444434663/562949953421312), (760931238063939/2251799813685248)), (3742351/1125899906842624), by norm_num⟩
  | 6 => ⟨((-68245418875801/4503599627370496), (478933078976467/2251799813685248)), (4884691/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-7992398087/268435456)), (1/134217728), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-225263989/134217728), (-4340004565/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((127396924995611/1125899906842624), (-334352879036833/2251799813685248)), (25633125/4503599627370496), by norm_num⟩
  | 1 => ⟨((-945674779/4294967296), (2481920855/8589934592)), (97/8589934592), by norm_num⟩
  | 2 => ⟨((920099075/4294967296), (-4829594981/17179869184)), (191/17179869184), by norm_num⟩
  | 3 => ⟨((-2387240171/17179869184), (1566326315/8589934592)), (125/17179869184), by norm_num⟩
  | 4 => ⟨((1161338719/17179869184), (-3047930273/34359738368)), (123/34359738368), by norm_num⟩
  | 5 => ⟨((-7062065/268435456), (4744798761/137438953472)), (97/68719476736), by norm_num⟩
  | 6 => ⟨((1172662951/137438953472), (-12022073/1073741824)), (127/274877906944), by norm_num⟩
  | 7 => ⟨((-1303940993/549755813888), (855547387/274877906944)), (143/1099511627776), by norm_num⟩
  | 8 => ⟨((634338003/1099511627776), (-3329636687/4398046511104)), (141/4398046511104), by norm_num⟩
  | 9 => ⟨((-548606559/4398046511104), (1439816405/8796093022208)), (31/4398046511104), by norm_num⟩
  | 10 => ⟨((3416125027/140737488355328), (-560350671/17592186044416)), (195/140737488355328), by norm_num⟩
  | 11 => ⟨((-604315669/140737488355328), (1586024811/281474976710656)), (35/140737488355328), by norm_num⟩
  | 12 => ⟨((3135850649/4503599627370496), (-2057507851/2251799813685248)), (23/562949953421312), by norm_num⟩
  | 13 => ⟨((-938782093/9007199254740992), (2463831021/18014398509481984)), (7/1125899906842624), by norm_num⟩
  | 14 => ⟨((1043877487/72057594037927936), (-1369826797/72057594037927936)), (63/72057594037927936), by norm_num⟩
  | 15 => ⟨((-2166711249/1152921504606846976), (1421631929/576460752303423488)), (33/288230376151711744), by norm_num⟩
  | 16 => ⟨((2108112705/9223372036854775808), (-2766367999/9223372036854775808)), (65/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532090827/10141204801825835211973625643008), (-299479297933/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444844772839959/158456325028528675187087900672), (-354649966427/158456325028528675187087900672)), (11543/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472607084446855/9903520314283042199192993792), (-1595688111893/39614081257132168796771975168)), (25973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945123083893259/1237940039285380274899124224), (-1695128247967/2475880078570760549798248448)), (27599/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771912249928261/154742504910672534362390528), (-105925103901/9671406556917033397649408)), (13801/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550229712469303/9671406556917033397649408), (-1588529641607/9671406556917033397649408)), (3235/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259380257089249/604462909807314587353088), (-1389616609765/604462909807314587353088)), (22649/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888753018694883/75557863725914323419136), (-2257476882679/75557863725914323419136)), (36809/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298259891811127/4722366482869645213696), (-1692539009051/4722366482869645213696)), (6903/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101402390194687/36893488147419103232), (-2326317435715/590295810358705651712)), (18987/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824711566868235/73786976294838206464), (-2906511870629/73786976294838206464)), (47481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824047468253003/9223372036854775808), (-408490325615/1152921504606846976)), (53433/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797647364624653/576460752303423488), (-408193134209/144115188075855872)), (26727/576460752303423488), by norm_num⟩
  | 5 => ⟨((597862311630647/72057594037927936), (-2854679320185/144115188075855872)), (46797/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493350396572157/36028797018963968), (-4276678996257/36028797018963968)), (35121/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491394040384959/9007199254740992), (-5336515585263/9007199254740992)), (5493/562949953421312), by norm_num⟩
  | 2 => ⟨((1116103090151877/2251799813685248), (-10645078884679/4503599627370496)), (176027/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222454445094931/2251799813685248), (-15897902551585/2251799813685248)), (66169/562949953421312), by norm_num⟩
  | 0 => ⟨((548322332253467/562949953421312), (-7879482427769/562949953421312)), (265951/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548322332253467/562949953421312), (-7879482427769/562949953421312)), (1014522556785201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067929012082487/1125899906842624), (-15349485884089/562949953421312)), (1051053/2251799813685248), by norm_num⟩
  | 2 => ⟨((63256619274857/70368744177664), (-116473311324009/2251799813685248)), (2051189/2251799813685248), by norm_num⟩
  | 3 => ⟨((1813601467672155/2251799813685248), (-104701426694543/1125899906842624)), (974987/562949953421312), by norm_num⟩
  | 4 => ⟨((1441203036260987/2251799813685248), (-337306469192441/2251799813685248)), (875923/281474976710656), by norm_num⟩
  | 5 => ⟨((13623064742735/35184372088832), (-215883803078851/1125899906842624)), (5534551/1125899906842624), by norm_num⟩
  | 6 => ⟨((127396924995611/1125899906842624), (-334352879036833/2251799813685248)), (25633125/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-225263989/134217728), (-4340004565/134217728)), (1/67108864), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-240721955/134217728), (-4637822455/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-749277416319729/4503599627370496), (-4569398996069/9007199254740992)), (60059807/9007199254740992), by norm_num⟩
  | 1 => ⟨((5943598121/17179869184), (9061621/8589934592)), (15/1073741824), by norm_num⟩
  | 2 => ⟨((-1544920605/4294967296), (-18843111/17179869184)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((2141714723/8589934592), (13061049/17179869184)), (177/17179869184), by norm_num⟩
  | 4 => ⟨((-2226785283/17179869184), (-3394961/8589934592)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((7408751715/137438953472), (22590793/137438953472)), (39/17179869184), by norm_num⟩
  | 6 => ⟨((-5135355363/274877906944), (-1957343/34359738368)), (109/137438953472), by norm_num⟩
  | 7 => ⟨((6102097871/1099511627776), (18606539/1099511627776)), (261/1099511627776), by norm_num⟩
  | 8 => ⟨((-6344477903/4398046511104), (-19345605/4398046511104)), (137/2199023255552), by norm_num⟩
  | 9 => ⟨((1465885657/4398046511104), (17879135/17592186044416)), (1/68719476736), by norm_num⟩
  | 10 => ⟨((-4877157649/70368744177664), (-7435723/35184372088832)), (215/70368744177664), by norm_num⟩
  | 11 => ⟨((7375828525/562949953421312), (11245201/281474976710656)), (41/70368744177664), by norm_num⟩
  | 12 => ⟨((-5112534747/2251799813685248), (-15589159/2251799813685248)), (115/1125899906842624), by norm_num⟩
  | 13 => ⟨((6542287469/18014398509481984), (9974383/9007199254740992)), (297/18014398509481984), by norm_num⟩
  | 14 => ⟨((-7773888195/144115188075855872), (-23704167/144115188075855872)), (89/36028797018963968), by norm_num⟩
  | 15 => ⟨((1077689737/144115188075855872), (13144381/576460752303423488)), (199/576460752303423488), by norm_num⟩
  | 16 => ⟨((-4481985617/4611686018427387904), (-6833243/2305843009213693952)), (209/4611686018427387904), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509236873/10141204801825835211973625643008), (-1022075818985/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889594996553267/316912650057057350374175801344), (-605067369365/79228162514264337593543950336)), (11585/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472553744344469/9903520314283042199192993792), (-5444710469133/39614081257132168796771975168)), (26073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890018667258131/2475880078570760549798248448), (-5783942056555/2475880078570760549798248448)), (433/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771683844220197/154742504910672534362390528), (-5782746210939/154742504910672534362390528)), (13861/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550014620912479/9671406556917033397649408), (-677506748037/1208925819614629174706176)), (1625/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629595545693681/302231454903657293676544), (-4741276644661/604462909807314587353088)), (22761/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472110956158011/18889465931478580854784), (-1925548045571/18889465931478580854784)), (18503/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298026422749363/4722366482869645213696), (-5774559561739/4722366482869645213696)), (6943/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811057334322729/295147905179352825856), (-7936631954525/590295810358705651712)), (19107/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456075817826437/18446744073709551616), (-4957854383447/36893488147419103232)), (23905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227947859991587/1152921504606846976), (-11148185731525/9223372036854775808)), (13461/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594823581607761/1152921504606846976), (-1392431553927/144115188075855872)), (53917/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195305004191125/144115188075855872), (-4868597957721/72057594037927936)), (11815/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492706274055263/36028797018963968), (-14586143997837/36028797018963968)), (35527/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490563253499343/9007199254740992), (-9099146477565/4503599627370496)), (44553/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115234013693047/2251799813685248), (-4536678298837/562949953421312)), (22385/562949953421312), by norm_num⟩
  | 1 => ⟨((277457111689843/281474976710656), (-27091124660737/1125899906842624)), (67697/562949953421312), by norm_num⟩
  | 0 => ⟨((546734919582297/562949953421312), (-53666505999091/1125899906842624)), (275145/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546734919582297/562949953421312), (-53666505999091/1125899906842624)), (1049594883445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059415839762761/1125899906842624), (-52120712797567/562949953421312)), (280335/562949953421312), by norm_num⟩
  | 2 => ⟨((61700402938521/70368744177664), (-196171998529835/1125899906842624)), (1158945/1125899906842624), by norm_num⟩
  | 3 => ⟨((415708852240927/562949953421312), (-344013283056079/1125899906842624)), (1218111/562949953421312), by norm_num⟩
  | 4 => ⟨((1017693059436293/2251799813685248), (-508071334532459/1125899906842624)), (10173591/2251799813685248), by norm_num⟩
  | 5 => ⟨((2800639125435/4503599627370496), (-229621064763305/562949953421312)), (18377667/2251799813685248), by norm_num⟩
  | 6 => ⟨((-749277416319729/4503599627370496), (-4569398996069/9007199254740992)), (60059807/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-240721955/134217728), (-4637822455/134217728)), (1/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile005Terms0
