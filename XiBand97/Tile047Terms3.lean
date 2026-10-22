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
namespace Reinmann.XiBand97.Tile047Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨47,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37201/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37201/1280))
  have he : value ((69/80), (37201/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-376798807/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-370674249120447/18014398509481984), (-1196400719091957/18014398509481984)), (54703733/9007199254740992), by norm_num⟩
  | 1 => ⟨((1092691269/17179869184), (1763403613/8589934592)), (81/4294967296), by norm_num⟩
  | 2 => ⟨((-844388775/8589934592), (-2725377715/8589934592)), (503/17179869184), by norm_num⟩
  | 3 => ⟨((435006925/4294967296), (2808086073/8589934592)), (521/17179869184), by norm_num⟩
  | 4 => ⟨((-1344624873/17179869184), (-542494579/2147483648)), (405/17179869184), by norm_num⟩
  | 5 => ⟨((1662517027/34359738368), (2682998039/17179869184)), (503/34359738368), by norm_num⟩
  | 6 => ⟨((-1712970237/68719476736), (-5528840561/68719476736)), (521/68719476736), by norm_num⟩
  | 7 => ⟨((1512818207/137438953472), (610352889/17179869184)), (231/68719476736), by norm_num⟩
  | 8 => ⟨((-584523163/137438953472), (-3773253383/274877906944)), (359/274877906944), by norm_num⟩
  | 9 => ⟨((803015961/549755813888), (2591841421/549755813888)), (495/1099511627776), by norm_num⟩
  | 10 => ⟨((-1985725141/4398046511104), (-1602298373/1099511627776)), (307/2199023255552), by norm_num⟩
  | 11 => ⟨((1115992857/8796093022208), (1801008107/4398046511104)), (347/8796093022208), by norm_num⟩
  | 12 => ⟨((-1149860433/35184372088832), (-3711328345/35184372088832)), (359/35184372088832), by norm_num⟩
  | 13 => ⟨((1093620743/140737488355328), (1764903611/70368744177664)), (343/140737488355328), by norm_num⟩
  | 14 => ⟨((-1931673225/1125899906842624), (-1558683425/281474976710656)), (19/35184372088832), by norm_num⟩
  | 15 => ⟨((1592235719/4503599627370496), (5139153747/4503599627370496)), (503/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1230417051/18014398509481984), (-1985667801/9007199254740992)), (195/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-1218750731493/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444463345582249/158456325028528675187087900672), (-2881840726183/633825300114114700748351602688)), (46243/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888712056952363/39614081257132168796771975168), (-1620659489101/19807040628566084398385987584)), (813/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888422775144681/2475880078570760549798248448), (-860741125433/618970019642690137449562112)), (55295/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442522258171221/38685626227668133590597632), (-3441910880579/154742504910672534362390528)), (27653/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548520632771653/9671406556917033397649408), (-806418090083/2417851639229258349412352)), (25931/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157235624867827/75557863725914323419136), (-2821344655031/604462909807314587353088)), (45393/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886323574316977/75557863725914323419136), (-2291294244891/37778931862957161709568)), (36893/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296438115130247/4722366482869645213696), (-429388472191/590295810358705651712)), (865/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1619933798887073/590295810358705651712), (-4720295321819/590295810358705651712)), (38077/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910790880241337/36893488147419103232), (-5895905336925/73786976294838206464)), (95243/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455131866790699/2305843009213693952), (-1656690154741/2305843009213693952)), (53609/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591776019056217/1152921504606846976), (-6619101799405/1152921504606846976)), (107305/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298161801721143/36028797018963968), (-5783107914081/144115188075855872)), (93991/144115188075855872), by norm_num⟩
  | 4 => ⟨((23261518578491/562949953421312), (-8657474556161/36028797018963968)), (141183/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485632651254317/9007199254740992), (-10791821593437/9007199254740992)), (176823/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220698824715311/4503599627370496), (-10746901430373/2251799813685248)), (177341/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205232182975343/2251799813685248), (-8004221930017/562949953421312)), (534625/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159001164810851/2251799813685248), (-31571601581987/1125899906842624)), (134963/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159001164810851/2251799813685248), (-31571601581987/1125899906842624)), (514842988134288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2068256217646083/2251799813685248), (-15135254070143/281474976710656)), (2130971/2251799813685248), by norm_num⟩
  | 2 => ⟨((473290620386651/562949953421312), (-111212668714083/1125899906842624)), (4143723/2251799813685248), by norm_num⟩
  | 3 => ⟨((784836895652155/1125899906842624), (-374000656013205/2251799813685248)), (7786137/2251799813685248), by norm_num⟩
  | 4 => ⟨((516031510946333/1125899906842624), (-521413159470671/2251799813685248)), (420045/70368744177664), by norm_num⟩
  | 5 => ⟨((88072038361035/562949953421312), (-955913110477097/4503599627370496)), (579563/70368744177664), by norm_num⟩
  | 6 => ⟨((-370674249120447/18014398509481984), (-1196400719091957/18014398509481984)), (54703733/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-376798807/4194304)), (1/33554432), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-3057739899/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-602557553076649/9007199254740992), (3248784909801/2251799813685248)), (24662163/4503599627370496), by norm_num⟩
  | 1 => ⟨((225223985/1073741824), (-155434361/34359738368)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-2824754009/8589934592), (121840885/17179869184)), (465/17179869184), by norm_num⟩
  | 3 => ⟨((5904666571/17179869184), (-127343797/17179869184)), (61/2147483648), by norm_num⟩
  | 4 => ⟨((-2314255985/8589934592), (99821435/17179869184)), (3/134217728), by norm_num⟩
  | 5 => ⟨((1451267251/8589934592), (-125195813/34359738368)), (483/34359738368), by norm_num⟩
  | 6 => ⟨((-1516813357/17179869184), (130850249/68719476736)), (507/68719476736), by norm_num⟩
  | 7 => ⟨((2717691147/68719476736), (-58611457/68719476736)), (57/17179869184), by norm_num⟩
  | 8 => ⟨((-1065163109/68719476736), (45943971/137438953472)), (359/274877906944), by norm_num⟩
  | 9 => ⟨((742180615/137438953472), (-32012679/274877906944)), (251/549755813888), by norm_num⟩
  | 10 => ⟨((-3723364841/2199023255552), (10037557/274877906944)), (79/549755813888), by norm_num⟩
  | 11 => ⟨((4245305063/8796093022208), (-91556951/8796093022208)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((-4437043157/35184372088832), (95692097/35184372088832)), (95/8796093022208), by norm_num⟩
  | 13 => ⟨((4280714817/140737488355328), (-92320621/140737488355328)), (369/140737488355328), by norm_num⟩
  | 14 => ⟨((-3834901871/562949953421312), (82705935/562949953421312)), (663/1125899906842624), by norm_num⟩
  | 15 => ⟨((6412966739/4503599627370496), (-138306123/4503599627370496)), (139/1125899906842624), by norm_num⟩
  | 16 => ⟨((-5026955029/18014398509481984), (6775907/1125899906842624)), (437/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (2032093297229/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888893204793087/316912650057057350374175801344), (4804754707963/633825300114114700748351602688)), (46337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888636295718947/39614081257132168796771975168), (5404054676907/39614081257132168796771975168)), (52145/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888341717351051/2475880078570760549798248448), (5740220862615/2475880078570760549798248448)), (55421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770007343928329/154742504910672534362390528), (5738435502451/154742504910672534362390528)), (55441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774221689868285/4835703278458516698824704), (672235847583/1208925819614629174706176)), (51997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257816733354743/604462909807314587353088), (4703754926667/604462909807314587353088)), (22759/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886211389387027/75557863725914323419136), (955005974893/9444732965739290427392)), (74007/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162044110139731/590295810358705651712), (5726927192961/4722366482869645213696)), (13885/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101238426549537/36893488147419103232), (7869475303911/590295810358705651712)), (9553/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227678797668549/9223372036854775808), (9829273217247/73786976294838206464)), (47807/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820353513316551/9223372036854775808), (5523764000637/4611686018427387904)), (53841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795798755346955/576460752303423488), (11034531001335/1152921504606846976)), (26957/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192485903182077/144115188075855872), (9640604642277/144115188075855872)), (94513/144115188075855872), by norm_num⟩
  | 4 => ⟨((744242526499805/18014398509481984), (14431716122795/36028797018963968)), (142097/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485299749158869/9007199254740992), (8994313392813/4503599627370496)), (178197/9007199254740992), by norm_num⟩
  | 2 => ⟨((277497519813167/562949953421312), (17912230606683/2251799813685248)), (179061/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102011597206805/1125899906842624), (26677816009205/1125899906842624)), (270759/1125899906842624), by norm_num⟩
  | 0 => ⟨((539016548737977/562949953421312), (52596281553439/1125899906842624)), (550229/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539016548737977/562949953421312), (52596281553439/1125899906842624)), (2098957066062545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1029744281329271/1125899906842624), (25180094595521/281474976710656)), (1105081/1125899906842624), by norm_num⟩
  | 2 => ⟨((932790458482297/1125899906842624), (368474082010093/2251799813685248)), (2219123/1125899906842624), by norm_num⟩
  | 3 => ⟨((742654606395837/1125899906842624), (305275012288531/1125899906842624)), (550409/140737488355328), by norm_num⟩
  | 4 => ⟨((814180778393579/2251799813685248), (25170298522517/70368744177664)), (4098339/562949953421312), by norm_num⟩
  | 5 => ⟨((12560048936771/4503599627370496), (582451015232597/2251799813685248)), (23582183/2251799813685248), by norm_num⟩
  | 6 => ⟨((-602557553076649/9007199254740992), (3248784909801/2251799813685248)), (24662163/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-3057739899/33554432)), (1/33554432), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-774811029/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-357019283575457/18014398509481984), (276435551735727/4503599627370496)), (101845529/18014398509481984), by norm_num⟩
  | 1 => ⟨((1082064153/17179869184), (-3351314789/17179869184)), (155/8589934592), by norm_num⟩
  | 2 => ⟨((-1719429063/17179869184), (5325329401/17179869184)), (247/8589934592), by norm_num⟩
  | 3 => ⟨((1821479373/17179869184), (-1410348625/4294967296)), (525/17179869184), by norm_num⟩
  | 4 => ⟨((-1447189875/17179869184), (2241081925/8589934592)), (419/17179869184), by norm_num⟩
  | 5 => ⟨((919849465/17179869184), (-5697823197/34359738368)), (535/34359738368), by norm_num⟩
  | 6 => ⟨((-974443705/34359738368), (6035996279/68719476736)), (569/68719476736), by norm_num⟩
  | 7 => ⟨((884809871/68719476736), (-5480777455/137438953472)), (519/137438953472), by norm_num⟩
  | 8 => ⟨((-351496675/68719476736), (2177275723/137438953472)), (207/137438953472), by norm_num⟩
  | 9 => ⟨((1985911741/1099511627776), (-6150666179/1099511627776)), (587/1099511627776), by norm_num⟩
  | 10 => ⟨((-1262266883/2199023255552), (1954714821/1099511627776)), (375/2199023255552), by norm_num⟩
  | 11 => ⟨((1458746219/8796093022208), (-4517955581/8796093022208)), (435/8796093022208), by norm_num⟩
  | 12 => ⟨((-772662335/17592186044416), (4786102013/35184372088832)), (463/35184372088832), by norm_num⟩
  | 13 => ⟨((377778845/35184372088832), (-2340075359/70368744177664)), (455/140737488355328), by norm_num⟩
  | 14 => ⟨((-686058003/281474976710656), (4249648833/562949953421312)), (415/562949953421312), by norm_num⟩
  | 15 => ⟨((581421137/1125899906842624), (-1800748367/1125899906842624)), (177/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1847787671/18014398509481984), (5722875245/18014398509481984)), (565/18014398509481984), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (1226478757063/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777737754818971/633825300114114700748351602688), (362469344927/79228162514264337593543950336)), (46243/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888582004114085/39614081257132168796771975168), (3261447770157/39614081257132168796771975168)), (52033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((7376111828235/9671406556917033397649408), (866079762151/618970019642690137449562112)), (27/1208925819614629174706176), by norm_num⟩
  | 14 => ⟨((884975461922843/77371252455336267181195264), (865807282721/38685626227668133590597632)), (13827/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774195598199371/4835703278458516698824704), (1622809841237/4835703278458516698824704)), (6483/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257771782773647/604462909807314587353088), (2838760055429/604462909807314587353088)), (45393/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943069837130521/37778931862957161709568), (4610816381709/75557863725914323419136)), (18447/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296300256765737/4722366482869645213696), (3456215645343/4722366482869645213696)), (27681/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809872175980333/295147905179352825856), (2374608152697/295147905179352825856)), (76157/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821345114266191/73786976294838206464), (2965951640085/36893488147419103232)), (95247/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820261463451985/9223372036854775808), (6667047886827/9223372036854775808)), (107223/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397877573584251/288230376151711744), (6659126569163/1152921504606846976)), (107311/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149051876433327/18014398509481984), (5817834997729/144115188075855872)), (23499/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488389522932399/36028797018963968), (8708977799875/36028797018963968)), (17649/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485199165079457/9007199254740992), (2713794191709/2251799813685248)), (176837/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219835138168671/4503599627370496), (10808728833811/2251799813685248)), (354717/4503599627370496), by norm_num⟩
  | 1 => ⟨((275493106910595/281474976710656), (32194787248397/2251799813685248)), (267347/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078229621519301/1125899906842624), (31734503469345/1125899906842624)), (539959/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078229621519301/1125899906842624), (31734503469345/1125899906842624)), (2059780125144576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063366434177299/2251799813685248), (121563494079363/2251799813685248)), (2129267/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884138782147441/2251799813685248), (111390911296935/1125899906842624)), (4132073/2251799813685248), by norm_num⟩
  | 3 => ⟨((1554466426651489/2251799813685248), (372814554256175/2251799813685248)), (3866219/1125899906842624), by norm_num⟩
  | 4 => ⟨((1011357744094629/2251799813685248), (514724003826807/2251799813685248)), (1654519/281474976710656), by norm_num⟩
  | 5 => ⟨((336576849246785/2251799813685248), (924718270563635/4503599627370496)), (4485179/562949953421312), by norm_num⟩
  | 6 => ⟨((-357019283575457/18014398509481984), (276435551735727/4503599627370496)), (101845529/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-774811029/8388608)), (1/33554432), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-6278107605/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((215088145848191/4503599627370496), (719804818654471/18014398509481984)), (61092773/18014398509481984), by norm_num⟩
  | 1 => ⟨((-660268815/4294967296), (-1104813733/8589934592)), (189/17179869184), by norm_num⟩
  | 2 => ⟨((4250646653/17179869184), (444532277/2147483648)), (153/8589934592), by norm_num⟩
  | 3 => ⟨((-4560767917/17179869184), (-1907858933/8589934592)), (331/17179869184), by norm_num⟩
  | 4 => ⟨((1835068199/8589934592), (1535290249/8589934592)), (67/4294967296), by norm_num⟩
  | 5 => ⟨((-2362742665/17179869184), (-1976763467/17179869184)), (87/8589934592), by norm_num⟩
  | 6 => ⟨((1267562541/17179869184), (2120985379/34359738368)), (189/34359738368), by norm_num⟩
  | 7 => ⟨((-4663001623/137438953472), (-3901250607/137438953472)), (175/68719476736), by norm_num⟩
  | 8 => ⟨((3752405799/274877906944), (784852579/68719476736)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-2684117403/549755813888), (-280704777/68719476736)), (205/549755813888), by norm_num⟩
  | 10 => ⟨((431992031/274877906944), (1445686113/1099511627776)), (265/2199023255552), by norm_num⟩
  | 11 => ⟨((-4045174415/8796093022208), (-1692176029/4398046511104)), (39/1099511627776), by norm_num⟩
  | 12 => ⟨((4340304711/35184372088832), (1815634837/17592186044416)), (337/35184372088832), by norm_num⟩
  | 13 => ⟨((-537342381/17592186044416), (-3596494205/140737488355328)), (21/8796093022208), by norm_num⟩
  | 14 => ⟨((60325/8589934592), (826904875/140737488355328)), (311/562949953421312), by norm_num⟩
  | 15 => ⟨((-3393518465/2251799813685248), (-709787763/562949953421312)), (269/2251799813685248), by norm_num⟩
  | 16 => ⟨((2730828637/9007199254740992), (2284718671/9007199254740992)), (109/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (907511552149/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777687432378923/633825300114114700748351602688), (536374528485/316912650057057350374175801344)), (23077/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888525617955189/39614081257132168796771975168), (37704835141/1237940039285380274899124224)), (25963/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944112510587411/1237940039285380274899124224), (1281601552173/2475880078570760549798248448)), (55175/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884945828982577/77371252455336267181195264), (80074598191/9671406556917033397649408)), (13795/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774167998312349/4835703278458516698824704), (600342836465/4835703278458516698824704)), (6467/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628861922314261/302231454903657293676544), (131270858311/75557863725914323419136)), (22637/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886062452177875/75557863725914323419136), (1705709530869/75557863725914323419136)), (73579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81015183264173/295147905179352825856), (1278572404423/4722366482869645213696)), (6899/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404916622859761/147573952589676412928), (1756884528307/590295810358705651712)), (75901/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821249227388391/73786976294838206464), (1097189138865/36893488147419103232)), (94895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820155565288231/9223372036854775808), (2466302698851/9223372036854775808)), (106783/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49731464337113/36028797018963968), (2463340047041/1152921504606846976)), (1669/18014398509481984), by norm_num⟩
  | 5 => ⟨((596163634055841/72057594037927936), (538023566255/36028797018963968)), (93501/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488263414216159/36028797018963968), (3221496595377/36028797018963968)), (140325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485051122181595/9007199254740992), (2007634364773/4503599627370496)), (10971/562949953421312), by norm_num⟩
  | 2 => ⟨((69361489365541/140737488355328), (7995836728389/4503599627370496)), (43933/562949953421312), by norm_num⟩
  | 1 => ⟨((2203614557543787/2251799813685248), (5953685385623/1125899906842624)), (264091/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078039378616131/1125899906842624), (11735700292187/1125899906842624)), (530173/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078039378616131/1125899906842624), (11735700292187/1125899906842624)), (2022449497703170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2064182025637439/2251799813685248), (22473662132353/1125899906842624)), (1026325/1125899906842624), by norm_num⟩
  | 2 => ⟨((945649597074133/1125899906842624), (41202356569993/1125899906842624)), (961299/562949953421312), by norm_num⟩
  | 3 => ⟨((198187139201955/281474976710656), (69212177125377/1125899906842624)), (3370317/1125899906842624), by norm_num⟩
  | 4 => ⟨((138480326951839/281474976710656), (761444428755/8796093022208)), (5160461/1125899906842624), by norm_num⟩
  | 5 => ⟨((264081566453061/1125899906842624), (383606942522051/4503599627370496)), (23884561/4503599627370496), by norm_num⟩
  | 6 => ⟨((215088145848191/4503599627370496), (719804818654471/18014398509481984)), (61092773/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-6278107605/67108864)), (1/33554432), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-188583173/67108864), (-794325479/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((979666824954953/18014398509481984), (-232519648060371/9007199254740992)), (49624203/18014398509481984), by norm_num⟩
  | 1 => ⟨((-760996125/4294967296), (1444952889/17179869184)), (39/4294967296), by norm_num⟩
  | 2 => ⟨((4958797681/17179869184), (-2353898003/17179869184)), (1/67108864), by norm_num⟩
  | 3 => ⟨((-1346353463/4294967296), (1278204489/8589934592)), (35/2147483648), by norm_num⟩
  | 4 => ⟨((4386549557/17179869184), (-1041128405/8589934592)), (115/8589934592), by norm_num⟩
  | 5 => ⟨((-2858360385/17179869184), (1356838741/17179869184)), (151/17179869184), by norm_num⟩
  | 6 => ⟨((1552135679/17179869184), (-1473570535/34359738368)), (83/17179869184), by norm_num⟩
  | 7 => ⟨((-1444859395/34359738368), (2743448605/137438953472)), (311/137438953472), by norm_num⟩
  | 8 => ⟨((4707491393/274877906944), (-2234605101/274877906944)), (255/274877906944), by norm_num⟩
  | 9 => ⟨((-1704162379/274877906944), (101118877/34359738368)), (93/274877906944), by norm_num⟩
  | 10 => ⟨((2220930219/1099511627776), (-527128101/549755813888)), (61/549755813888), by norm_num⟩
  | 11 => ⟨((-5262549133/8796093022208), (2498086169/8796093022208)), (291/8796093022208), by norm_num⟩
  | 12 => ⟨((714412213/4398046511104), (-1356500983/17592186044416)), (159/17592186044416), by norm_num⟩
  | 13 => ⟨((-716191987/17592186044416), (339970089/17592186044416)), (321/140737488355328), by norm_num⟩
  | 14 => ⟨((666692181/70368744177664), (-2531783703/562949953421312)), (301/562949953421312), by norm_num⟩
  | 15 => ⟨((-4633914639/2251799813685248), (1099839429/1125899906842624)), (263/2251799813685248), by norm_num⟩
  | 16 => ⟨((3774435311/9007199254740992), (-895845759/4503599627370496)), (27/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197539410918425/1267650600228229401496703205376), (-577312814951/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777635713672973/633825300114114700748351602688), (-170597597647/158456325028528675187087900672)), (23067/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888467468459919/39614081257132168796771975168), (-191876022057/9903520314283042199192993792)), (51903/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472040820495935/618970019642690137449562112), (-407619748115/1237940039285380274899124224)), (27575/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769829968953667/154742504910672534362390528), (-407488421933/77371252455336267181195264)), (3447/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548278216456135/9671406556917033397649408), (-190940460443/2417851639229258349412352)), (51709/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673340220057/604462909807314587353088), (-83501599489/75557863725914323419136)), (707/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1885980482250923/75557863725914323419136), (-33906196813/2361183241434822606848)), (73533/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296181541964959/4722366482869645213696), (-406645911945/2361183241434822606848)), (13789/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809791110670217/295147905179352825856), (-1117534327709/590295810358705651712)), (37923/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910572050874809/36893488147419103232), (-1395805944217/73786976294838206464)), (23705/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910018794982343/4611686018427387904), (-1568754244271/9223372036854775808)), (106689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591289246552299/1152921504606846976), (-1566847202271/1152921504606846976)), (106711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149028095617159/18014398509481984), (-684424492769/72057594037927936)), (23349/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488110472165631/36028797018963968), (-1024498298873/18014398509481984)), (35035/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484861361584845/9007199254740992), (-1276889307781/4503599627370496)), (175259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109596184179871/2251799813685248), (-2542612653523/2251799813685248)), (87693/1125899906842624), by norm_num⟩
  | 1 => ⟨((550765530458463/562949953421312), (-473265659371/140737488355328)), (526797/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155015453393599/2251799813685248), (-14923599886977/2251799813685248)), (1056187/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2155015453393599/2251799813685248), (-14923599886977/2251799813685248)), (4029033669478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257786508280435/281474976710656), (-14282170280521/1125899906842624)), (2035583/2251799813685248), by norm_num⟩
  | 2 => ⟨((1888370635389653/2251799813685248), (-6540103227483/281474976710656)), (945047/562949953421312), by norm_num⟩
  | 3 => ⟨((791190710233691/1125899906842624), (-43876507359627/1125899906842624)), (6515837/2251799813685248), by norm_num⟩
  | 4 => ⟨((34642155369969/70368744177664), (-61665668163679/1125899906842624)), (4832723/1125899906842624), by norm_num⟩
  | 5 => ⟨((1077955684221115/4503599627370496), (-242861421784155/4503599627370496)), (5287625/1125899906842624), by norm_num⟩
  | 6 => ⟨((979666824954953/18014398509481984), (-232519648060371/9007199254740992)), (49624203/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-188583173/67108864), (-794325479/8388608)), (1/33554432), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-6428212711/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((64530376078733/36028797018963968), (-2098424084920557/36028797018963968)), (42332455/9007199254740992), by norm_num⟩
  | 1 => ⟨((-50707243/8589934592), (1648918023/8589934592)), (267/17179869184), by norm_num⟩
  | 2 => ⟨((167122801/17179869184), (-5434564809/17179869184)), (441/17179869184), by norm_num⟩
  | 3 => ⟨((-183603163/17179869184), (5970479683/17179869184)), (243/8589934592), by norm_num⟩
  | 4 => ⟨((75640759/8589934592), (-2459715881/8589934592)), (201/8589934592), by norm_num⟩
  | 5 => ⟨((-99719841/17179869184), (202670557/1073741824)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((219106885/68719476736), (-7125003663/68719476736)), (587/68719476736), by norm_num⟩
  | 7 => ⟨((-206325871/137438953472), (6709385641/137438953472)), (555/137438953472), by norm_num⟩
  | 8 => ⟨((170004103/274877906944), (-691032517/34359738368)), (459/274877906944), by norm_num⟩
  | 9 => ⟨((-62256199/274877906944), (8097886027/1099511627776)), (675/1099511627776), by norm_num⟩
  | 10 => ⟨((164149021/2199023255552), (-5337862261/2199023255552)), (447/2199023255552), by norm_num⟩
  | 11 => ⟨((-196730325/8796093022208), (1599338475/2199023255552)), (269/4398046511104), by norm_num⟩
  | 12 => ⟨((216130353/35184372088832), (-7028211609/35184372088832)), (593/35184372088832), by norm_num⟩
  | 13 => ⟨((-54794645/35184372088832), (7127335053/140737488355328)), (603/140737488355328), by norm_num⟩
  | 14 => ⟨((25799173/70368744177664), (-6711581035/562949953421312)), (285/281474976710656), by norm_num⟩
  | 15 => ⟨((-90698523/1125899906842624), (5898740321/2251799813685248)), (503/2251799813685248), by norm_num⟩
  | 16 => ⟨((18682971/1125899906842624), (-4860321453/9007199254740992)), (13/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1003046263423/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777582828912923/633825300114114700748351602688), (-148193556977/39614081257132168796771975168)), (23109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472101959220879/9903520314283042199192993792), (-2666829744327/39614081257132168796771975168)), (26001/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472024934517859/618970019642690137449562112), (-2832685066487/2475880078570760549798248448)), (55261/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769766216792341/154742504910672534362390528), (-2831761278363/154742504910672534362390528)), (55271/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774109113871089/4835703278458516698824704), (-2653795058711/9671406556917033397649408)), (51827/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257620629260037/604462909807314587353088), (-1160544984977/302231454903657293676544)), (45359/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471473603339379/18889465931478580854784), (-471241662133/9444732965739290427392)), (73727/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648058314445913/2361183241434822606848), (-1412921363325/2361183241434822606848)), (55313/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404873094872091/147573952589676412928), (-3882923698061/590295810358705651712)), (76083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227628865181117/9223372036854775808), (-2424871280393/36893488147419103232)), (95145/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819909057458773/9223372036854775808), (-2725293095641/4611686018427387904)), (13387/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591159212049337/1152921504606846976), (-5443875790761/1152921504606846976)), (3349/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192109300266829/144115188075855872), (-4755852193349/144115188075855872)), (93853/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487933919334411/36028797018963968), (-7118725203529/36028797018963968)), (140941/36028797018963968), by norm_num⟩
  | 3 => ⟨((742317413660489/4503599627370496), (-2218030031707/2251799813685248)), (176461/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109360943808523/2251799813685248), (-17665606778303/4503599627370496)), (353777/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202313279406591/2251799813685248), (-13151307156569/1125899906842624)), (266407/1125899906842624), by norm_num⟩
  | 0 => ⟨((1076673861806323/1125899906842624), (-25913378254325/1125899906842624)), (1074269/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076673861806323/1125899906842624), (-25913378254325/1125899906842624)), (4098011025435637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058007278414901/2251799813685248), (-49560812409645/1125899906842624)), (526013/562949953421312), by norm_num⟩
  | 2 => ⟨((469132384217851/562949953421312), (-90591101432129/1125899906842624)), (4031187/2251799813685248), by norm_num⟩
  | 3 => ⟨((1549221245563031/2251799813685248), (-75493779057069/562949953421312)), (7367459/2251799813685248), by norm_num⟩
  | 4 => ⟨((1025356465015465/2251799813685248), (-415513193356719/2251799813685248)), (12113523/2251799813685248), by norm_num⟩
  | 5 => ⟨((390223261035555/2251799813685248), (-756815302174255/4503599627370496)), (31004547/4503599627370496), by norm_num⟩
  | 6 => ⟨((64530376078733/36028797018963968), (-2098424084920557/36028797018963968)), (42332455/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-6428212711/67108864)), (1/33554432), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile047Terms3
