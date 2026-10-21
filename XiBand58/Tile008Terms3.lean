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
namespace Reinmann.XiBand58.Tile008Terms3
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
  | 0 => ⟨((15/16), (2991/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2991/160))
  have he : value ((15/16), (2991/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-24308947/8388608), (-484720403/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((163894587209647/9007199254740992), (-14651562070059/281474976710656)), (143553009/18014398509481984), by norm_num⟩
  | 1 => ⟨((-241568149/4294967296), (43190575/268435456)), (213/8589934592), by norm_num⟩
  | 2 => ⟨((186674351/2147483648), (-1068031207/4294967296)), (83/2147483648), by norm_num⟩
  | 3 => ⟨((-24042431/268435456), (1100443267/4294967296)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((74316175/1073741824), (-425189607/2147483648)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((-367543123/8589934592), (1051423301/8589934592)), (169/8589934592), by norm_num⟩
  | 6 => ⟨((94674283/4294967296), (-1083331353/17179869184)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((-334448261/34359738368), (956749487/34359738368)), (157/34359738368), by norm_num⟩
  | 8 => ⟨((516896887/137438953472), (-1478676641/137438953472)), (245/137438953472), by norm_num⟩
  | 9 => ⟨((-355055605/274877906944), (1015700505/274877906944)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((438996779/1099511627776), (-156978669/137438953472)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((-493439157/4398046511104), (1411571579/4398046511104)), (241/4398046511104), by norm_num⟩
  | 12 => ⟨((254206897/8796093022208), (-727204613/8796093022208)), (251/17592186044416), by norm_num⟩
  | 13 => ⟨((-120886817/17592186044416), (691637025/35184372088832)), (15/4398046511104), by norm_num⟩
  | 14 => ⟨((427047181/281474976710656), (-1221645375/281474976710656)), (107/140737488355328), by norm_num⟩
  | 15 => ⟨((-352005591/1125899906842624), (1006975391/1125899906842624)), (89/562949953421312), by norm_num⟩
  | 16 => ⟨((544032113/9007199254740992), (-778150921/4503599627370496)), (277/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (-1608083341321/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777498934996597/633825300114114700748351602688), (-1900497428733/633825300114114700748351602688)), (92387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944156769228289/19807040628566084398385987584), (-2137527059063/39614081257132168796771975168)), (25987/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((943999827349163/1237940039285380274899124224), (-1135225706659/1237940039285380274899124224)), (110459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769666255586167/154742504910672534362390528), (-2269696836291/154742504910672534362390528)), (110475/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548124643818907/9671406556917033397649408), (-531759844903/2417851639229258349412352)), (103587/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628769436463943/302231454903657293676544), (-930179214143/302231454903657293676544)), (2833/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((235720225261539/9444732965739290427392), (-3021581314431/75557863725914323419136)), (73673/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162002172830505/590295810358705651712), (-283109161609/590295810358705651712)), (55269/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619356260299989/590295810358705651712), (-1556034572655/295147905179352825856)), (152033/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820861288324909/73786976294838206464), (-3886891594993/73786976294838206464)), (47527/18446744073709551616), by norm_num⟩
  | 7 => ⟨((454929732074847/2305843009213693952), (-4368364384703/9223372036854775808)), (53491/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1590969966217487/1152921504606846976), (-4362884914775/1152921504606846976)), (3345/18014398509481984), by norm_num⟩
  | 5 => ⟨((297986175357831/36028797018963968), (-119105269499/4503599627370496)), (93725/72057594037927936), by norm_num⟩
  | 4 => ⟨((46490281169947/1125899906842624), (-5704763369769/36028797018963968)), (281435/36028797018963968), by norm_num⟩
  | 3 => ⟨((371083029927799/2251799813685248), (-7109496405647/9007199254740992)), (88063/2251799813685248), by norm_num⟩
  | 2 => ⟨((69316460981061/140737488355328), (-14154814699769/4503599627370496)), (88235/562949953421312), by norm_num⟩
  | 1 => ⟨((1100723039924193/1125899906842624), (-10536229211723/1125899906842624)), (1062277/2251799813685248), by norm_num⟩
  | 0 => ⟨((1075857096772047/1125899906842624), (-10377484221989/562949953421312)), (267309/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1075857096772047/1125899906842624), (-10377484221989/562949953421312)), (1019702912450694949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1027655937199927/1125899906842624), (-79329894098143/2251799813685248)), (4165689/2251799813685248), by norm_num⟩
  | 2 => ⟨((1873174357381399/2251799813685248), (-72407712419141/1125899906842624)), (7897909/2251799813685248), by norm_num⟩
  | 3 => ⟨((1548899082717325/2251799813685248), (-60232827694487/562949953421312)), (3538925/562949953421312), by norm_num⟩
  | 4 => ⟨((1039630813406141/2251799813685248), (-20715556284903/140737488355328)), (11251579/1125899906842624), by norm_num⟩
  | 5 => ⟨((3368742279929/17592186044416), (-612105015722887/4503599627370496)), (54807047/4503599627370496), by norm_num⟩
  | 6 => ⟨((163894587209647/9007199254740992), (-14651562070059/281474976710656)), (143553009/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-484720403/8388608)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-98634119/33554432), (-983382171/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-452340682839359/18014398509481984), (-419287528763203/9007199254740992)), (86159303/9007199254740992), by norm_num⟩
  | 1 => ⟨((338151835/4294967296), (1253770467/8589934592)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((-530136561/4294967296), (-122849689/536870912)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((69260005/536870912), (1027185305/4294967296)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((-217164345/2147483648), (-805183395/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((272367019/4294967296), (1009859151/8589934592)), (217/8589934592), by norm_num⟩
  | 6 => ⟨((-71167101/2147483648), (-1055469175/17179869184)), (229/17179869184), by norm_num⟩
  | 7 => ⟨((510043505/34359738368), (945547855/34359738368)), (207/34359738368), by norm_num⟩
  | 8 => ⟨((-399809615/68719476736), (-741189957/68719476736)), (41/17179869184), by norm_num⟩
  | 9 => ⟨((278577941/137438953472), (1032887477/274877906944)), (115/137438953472), by norm_num⟩
  | 10 => ⟨((-349391809/549755813888), (-323861271/274877906944)), (145/549755813888), by norm_num⟩
  | 11 => ⟨((398369453/2199023255552), (738520103/2199023255552)), (167/2199023255552), by norm_num⟩
  | 12 => ⟨((-416361705/8796093022208), (-385937585/4398046511104)), (11/549755813888), by norm_num⟩
  | 13 => ⟨((401692221/35184372088832), (93085005/4398046511104)), (171/35184372088832), by norm_num⟩
  | 14 => ⟨((-719716363/281474976710656), (-333562851/70368744177664)), (309/281474976710656), by norm_num⟩
  | 15 => ⟨((601777731/1125899906842624), (34862813/35184372088832)), (261/1125899906842624), by norm_num⟩
  | 16 => ⟨((-471717649/4503599627370496), (-218624297/1125899906842624)), (103/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-2690514685949/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111089455839639/39614081257132168796771975168), (-3179539241577/633825300114114700748351602688)), (46257/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944118635988029/19807040628566084398385987584), (-894017944931/9903520314283042199192993792)), (104099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887918389101969/2475880078570760549798248448), (-1899218314899/1237940039285380274899124224)), (27657/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442396182209903/38685626227668133590597632), (-1898577547063/77371252455336267181195264)), (55327/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774023967643281/4835703278458516698824704), (-3558471781543/9671406556917033397649408)), (51883/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257471476052659/604462909807314587353088), (-778075566505/151115727451828646838272)), (90823/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942825881798839/37778931862957161709568), (-5054941388817/75557863725914323419136)), (18455/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((647967200327211/2361183241434822606848), (-3788976196167/4722366482869645213696)), (13847/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404810356232651/147573952589676412928), (-5206221064505/590295810358705651712)), (152391/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820716643482453/73786976294838206464), (-6502348534497/73786976294838206464)), (190601/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454888673210777/2305843009213693952), (-1826921349157/2305843009213693952)), (214581/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795401924140281/576460752303423488), (-456148392579/72057594037927936)), (214773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191797237348893/144115188075855872), (-6375615907461/144115188075855872)), (11759/9007199254740992), by norm_num⟩
  | 4 => ⟨((1487463596757805/36028797018963968), (-9542534190039/36028797018963968)), (282651/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484043049519381/9007199254740992), (-11891686107789/9007199254740992)), (88519/2251799813685248), by norm_num⟩
  | 2 => ⟨((2217526806980693/4503599627370496), (-23674228035197/4503599627370496)), (710445/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100246094856459/1125899906842624), (-35239531968159/2251799813685248)), (1071421/2251799813685248), by norm_num⟩
  | 0 => ⟨((2149593719262429/2251799813685248), (-34699054442383/1125899906842624)), (2165977/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2149593719262429/2251799813685248), (-34699054442383/1125899906842624)), (8262546547896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1024943920929933/1125899906842624), (-33124112117063/562949953421312)), (533605/281474976710656), by norm_num⟩
  | 2 => ⟨((1858284573041135/2251799813685248), (-241231797919179/2251799813685248)), (8274493/2251799813685248), by norm_num⟩
  | 3 => ⟨((1507695645697351/2251799813685248), (-99537562325877/562949953421312)), (7714911/1125899906842624), by norm_num⟩
  | 4 => ⟨((469540526245439/1125899906842624), (-133291022043783/562949953421312)), (13059271/1125899906842624), by norm_num⟩
  | 5 => ⟨((132695916083615/1125899906842624), (-889393968381999/4503599627370496)), (68306067/4503599627370496), by norm_num⟩
  | 6 => ⟨((-452340682839359/18014398509481984), (-419287528763203/9007199254740992)), (86159303/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-983382171/16777216)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-99972929/33554432), (-124591263/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-439871265525121/9007199254740992), (-7920810271887/562949953421312)), (161355783/18014398509481984), by norm_num⟩
  | 1 => ⟨((666587143/4294967296), (384105857/8589934592)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-1059224911/4294967296), (-38147159/536870912)), (99/2147483648), by norm_num⟩
  | 3 => ⟨((561045631/2147483648), (323289933/4294967296)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((-13929947/67108864), (-128429101/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((283328777/2147483648), (326523677/8589934592)), (109/4294967296), by norm_num⟩
  | 6 => ⟨((-600289403/8589934592), (-172951637/8589934592)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((1090144021/34359738368), (314085493/34359738368)), (213/34359738368), by norm_num⟩
  | 8 => ⟨((-866134095/68719476736), (-249545151/68719476736)), (171/68719476736), by norm_num⟩
  | 9 => ⟨((305846753/68719476736), (44059329/34359738368)), (61/68719476736), by norm_num⟩
  | 10 => ⟨((-194399489/137438953472), (-224036671/549755813888)), (313/1099511627776), by norm_num⟩
  | 11 => ⟨((898635695/2199023255552), (258909309/2199023255552)), (183/2199023255552), by norm_num⟩
  | 12 => ⟨((-951970871/8796093022208), (-274275907/8796093022208)), (195/8796093022208), by norm_num⟩
  | 13 => ⟨((465448411/17592186044416), (33525523/4398046511104)), (193/35184372088832), by norm_num⟩
  | 14 => ⟨((-105658579/17592186044416), (-60883381/35184372088832)), (177/140737488355328), by norm_num⟩
  | 15 => ⟨((1432698247/1125899906842624), (412780079/1125899906842624)), (151/562949953421312), by norm_num⟩
  | 16 => ⟨((-569149019/2251799813685248), (-10248729/140737488355328)), (121/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (-3726870958465/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888682444515637/316912650057057350374175801344), (-4403971891653/633825300114114700748351602688)), (46317/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944081158513839/19807040628566084398385987584), (-2476589237805/19807040628566084398385987584)), (52121/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((943919203435873/1237940039285380274899124224), (-1315287671729/618970019642690137449562112)), (110789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769504361706409/154742504910672534362390528), (-5259349601147/154742504910672534362390528)), (55413/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((386993045633103/2417851639229258349412352), (-4928727205719/9671406556917033397649408)), (51969/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257404784267823/604462909807314587353088), (-4310723943037/604462909807314587353088)), (90985/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885542625151215/75557863725914323419136), (-1750335545213/18889465931478580854784)), (73961/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295851878997905/4722366482869645213696), (-5247871889357/4722366482869645213696)), (111005/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809563437099363/295147905179352825856), (-7210732607351/590295810358705651712)), (152735/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820571832956195/73786976294838206464), (-9005783661723/73786976294838206464)), (95537/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819389555580297/9223372036854775808), (-632563764049/576460752303423488)), (215171/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590635936704799/1152921504606846976), (-1263490479841/144115188075855872)), (107719/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191647203862429/144115188075855872), (-2207428970409/36028797018963968)), (94405/72057594037927936), by norm_num⟩
  | 4 => ⟨((743616175186043/18014398509481984), (-3303794687937/9007199254740992)), (35477/4503599627370496), by norm_num⟩
  | 3 => ⟨((46366975175959/281474976710656), (-16467621779813/9007199254740992)), (177913/4503599627370496), by norm_num⟩
  | 2 => ⟨((138555936890041/281474976710656), (-32781547310253/4503599627370496)), (714827/4503599627370496), by norm_num⟩
  | 1 => ⟨((2199464939659935/2251799813685248), (-24394667662153/1125899906842624)), (1080205/2251799813685248), by norm_num⟩
  | 0 => ⟨((1073612939364427/1125899906842624), (-24013563322565/562949953421312)), (548107/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1073612939364427/1125899906842624), (-24013563322565/562949953421312)), (2090862276317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((510852755065433/562949953421312), (-45796739384501/562949953421312)), (4368267/2251799813685248), by norm_num⟩
  | 2 => ⟨((919702344573961/1125899906842624), (-332468495224503/2251799813685248)), (8638757/2251799813685248), by norm_num⟩
  | 3 => ⟨((45420255197805/70368744177664), (-135790070101539/562949953421312)), (16664257/2251799813685248), by norm_num⟩
  | 4 => ⟨((50445438992587/140737488355328), (-350588586419447/1125899906842624)), (14775735/1125899906842624), by norm_num⟩
  | 5 => ⟨((70967500751213/2251799813685248), (-1005309692784495/4503599627370496)), (79176855/4503599627370496), by norm_num⟩
  | 6 => ⟨((-439871265525121/9007199254740992), (-7920810271887/562949953421312)), (161355783/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-124591263/2097152)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-50628539/16777216), (-1009533069/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-390258639988057/9007199254740992), (204464091331931/9007199254740992)), (80183449/9007199254740992), by norm_num⟩
  | 1 => ⟨((1198000051/8589934592), (-313827763/4294967296)), (31/1073741824), by norm_num⟩
  | 2 => ⟨((-964053351/4294967296), (126271575/1073741824)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((517194671/2147483648), (-270968347/2147483648)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((-104049089/536870912), (436106731/4294967296)), (11/268435456), by norm_num⟩
  | 5 => ⟨((1071747511/8589934592), (-561509365/8589934592)), (229/8589934592), by norm_num⟩
  | 6 => ⟨((-574970359/8589934592), (602476307/17179869184)), (247/17179869184), by norm_num⟩
  | 7 => ⟨((264394027/8589934592), (-554084691/34359738368)), (229/34359738368), by norm_num⟩
  | 8 => ⟨((-425525771/34359738368), (222941227/34359738368)), (93/34359738368), by norm_num⟩
  | 9 => ⟨((152190513/34359738368), (-637884557/274877906944)), (67/68719476736), by norm_num⟩
  | 10 => ⟨((-783811781/549755813888), (102663559/137438953472)), (87/274877906944), by norm_num⟩
  | 11 => ⟨((917451925/2199023255552), (-240335453/1099511627776)), (103/1099511627776), by norm_num⟩
  | 12 => ⟨((-984387941/8796093022208), (257869993/4398046511104)), (223/8796093022208), by norm_num⟩
  | 13 => ⟨((974960783/35184372088832), (-510800915/35184372088832)), (223/35184372088832), by norm_num⟩
  | 14 => ⟨((-448325385/70368744177664), (58721597/17592186044416)), (207/140737488355328), by norm_num⟩
  | 15 => ⟨((384827665/281474976710656), (-403237395/562949953421312)), (179/562949953421312), by norm_num⟩
  | 16 => ⟨((-309678117/1125899906842624), (648985551/4503599627370496)), (145/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (1731817698719/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777307401049761/633825300114114700748351602688), (255790786459/39614081257132168796771975168)), (23151/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944048868662245/19807040628566084398385987584), (71922267811/618970019642690137449562112)), (52103/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((235971239548267/309485009821345068724781056), (611150919709/309485009821345068724781056)), (27687/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884718006105107/77371252455336267181195264), (610939092979/19342813113834066795298816)), (55391/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547908254564567/9671406556917033397649408), (4580243289275/9671406556917033397649408)), (51947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78584312303119/37778931862957161709568), (2002956832955/302231454903657293676544)), (90943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471363062683187/18889465931478580854784), (6506237662651/75557863725914323419136)), (73925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295784343024931/4722366482869645213696), (2438364593103/2361183241434822606848)), (110947/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809517204790885/295147905179352825856), (6700713178051/590295810358705651712)), (19081/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910228423646811/36893488147419103232), (8368712140613/73786976294838206464)), (95477/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819261013506571/9223372036854775808), (2351234362859/2305843009213693952)), (215021/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590508413412815/1152921504606846976), (4696309812773/576460752303423488)), (107635/576460752303423488), by norm_num⟩
  | 5 => ⟨((148942095508873/18014398509481984), (4102350423169/72057594037927936)), (188641/144115188075855872), by norm_num⟩
  | 4 => ⟨((743534484636917/18014398509481984), (6139704582939/18014398509481984)), (283521/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483542949745525/9007199254740992), (15300978949543/9007199254740992)), (177691/4503599627370496), by norm_num⟩
  | 2 => ⟨((2216506321924847/4503599627370496), (15228737383475/2251799813685248)), (713715/4503599627370496), by norm_num⟩
  | 1 => ⟨((2198911308528097/2251799813685248), (45326278320219/2251799813685248)), (538989/1125899906842624), by norm_num⟩
  | 0 => ⟨((1073117341973537/1125899906842624), (89220454303865/2251799813685248)), (2185725/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1073117341973537/1125899906842624), (89220454303865/2251799813685248)), (8337879189498137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2042083404201737/2251799813685248), (42518884756253/562949953421312)), (542465/281474976710656), by norm_num⟩
  | 2 => ⟨((1839052883641615/2251799813685248), (308471857571783/2251799813685248)), (8526647/2251799813685248), by norm_num⟩
  | 3 => ⟨((1459703745395281/2251799813685248), (503860117353193/2251799813685248)), (16263601/2251799813685248), by norm_num⟩
  | 4 => ⟨((833493277268821/2251799813685248), (326621618842787/1125899906842624)), (3545455/281474976710656), by norm_num⟩
  | 5 => ⟨((238017885996545/4503599627370496), (967179842050293/4503599627370496)), (37453827/2251799813685248), by norm_num⟩
  | 6 => ⟨((-390258639988057/9007199254740992), (204464091331931/9007199254740992)), (80183449/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1009533069/16777216)), (1/16777216), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-102490855/33554432), (-1021833825/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-590468952101399/36028797018963968), (1592755200965663/36028797018963968)), (75389549/9007199254740992), by norm_num⟩
  | 1 => ⟨((458670819/8589934592), (-1237237503/8589934592)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((-93399613/1073741824), (503879903/2147483648)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((405739941/4294967296), (-1094459579/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-165242487/2147483648), (891463741/4294967296)), (175/4294967296), by norm_num⟩
  | 5 => ⟨((107675195/2147483648), (-1161789971/8589934592)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-467754907/17179869184), (630870647/8589934592)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((217712949/17179869184), (-587267849/17179869184)), (59/8589934592), by norm_num⟩
  | 8 => ⟨((-354664903/68719476736), (956687673/68719476736)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((513569997/274877906944), (-692662399/137438953472)), (283/274877906944), by norm_num⟩
  | 10 => ⟨((-167326063/274877906944), (451352193/274877906944)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((24780203/137438953472), (-1069490195/2199023255552)), (223/2199023255552), by norm_num⟩
  | 12 => ⟨((-215296783/4398046511104), (1161500767/8796093022208)), (61/2199023255552), by norm_num⟩
  | 13 => ⟨((431666279/35184372088832), (-1164394347/35184372088832)), (123/17592186044416), by norm_num⟩
  | 14 => ⟨((-200915773/70368744177664), (67744807/8796093022208)), (231/140737488355328), by norm_num⟩
  | 15 => ⟨((43640199/70368744177664), (-941734917/562949953421312)), (101/281474976710656), by norm_num⟩
  | 16 => ⟨((-568735925/4503599627370496), (1534131637/4503599627370496)), (331/4503599627370496), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (1254291866169/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777255084339337/633825300114114700748351602688), (2963977591389/633825300114114700748351602688)), (23123/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944019563736493/19807040628566084398385987584), (3333597528949/39614081257132168796771975168)), (104073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887707977222899/2475880078570760549798248448), (3540843747627/2475880078570760549798248448)), (110599/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884687224054039/77371252455336267181195264), (1769801385927/77371252455336267181195264)), (3457/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1547850936368017/9671406556917033397649408), (3317059596807/9671406556917033397649408)), (12967/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157162405147451/75557863725914323419136), (2901109747211/604462909807314587353088)), (90795/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885372142708817/75557863725914323419136), (588979311565/9444732965739290427392)), (147591/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295724912986327/4722366482869645213696), (1765858453099/2361183241434822606848)), (110737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618953749540177/590295810358705651712), (303287801571/36893488147419103232)), (38083/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820357603871887/73786976294838206464), (6060501337465/73786976294838206464)), (190519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454787883729001/2305843009213693952), (1702711399993/2305843009213693952)), (214477/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397600410232843/288230376151711744), (6801832784695/1152921504606846976)), (107329/576460752303423488), by norm_num⟩
  | 5 => ⟨((18616349582901/2251799813685248), (1485369566831/36028797018963968)), (47007/36028797018963968), by norm_num⟩
  | 4 => ⟨((1486939430442395/36028797018963968), (2223000378705/9007199254740992)), (282447/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483391557398949/9007199254740992), (2769925654811/2251799813685248)), (353771/9007199254740992), by norm_num⟩
  | 2 => ⟨((1108117462502801/2251799813685248), (2756727617527/562949953421312)), (709683/4503599627370496), by norm_num⟩
  | 1 => ⟨((2198581965146883/2251799813685248), (16408932693411/1125899906842624)), (534949/1125899906842624), by norm_num⟩
  | 0 => ⟨((1072941361762385/1125899906842624), (16147703532569/562949953421312)), (1080705/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1072941361762385/1125899906842624), (16147703532569/562949953421312)), (4122562412742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1021547444380227/1125899906842624), (7694084932539/140737488355328)), (2121743/1125899906842624), by norm_num⟩
  | 2 => ⟨((1847003348080685/2251799813685248), (111695510436215/1125899906842624)), (8164351/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492813792409657/2251799813685248), (366465936247931/2251799813685248)), (15013259/2251799813685248), by norm_num⟩
  | 4 => ⟨((930009729839667/2251799813685248), (121472921516925/562949953421312)), (24792479/2251799813685248), by norm_num⟩
  | 5 => ⟨((558510897092235/4503599627370496), (802707226361509/4503599627370496)), (31178355/2251799813685248), by norm_num⟩
  | 6 => ⟨((-590468952101399/36028797018963968), (1592755200965663/36028797018963968)), (75389549/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-1021833825/16777216)), (1/16777216), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-6479879/2097152), (-1033670289/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((562986262027533/36028797018963968), (1539947248995351/36028797018963968)), (236258061/18014398509481984), by norm_num⟩
  | 1 => ⟨((-442388267/8589934592), (-302518303/2147483648)), (373/8589934592), by norm_num⟩
  | 2 => ⟨((182254945/2147483648), (31157843/134217728)), (309/4294967296), by norm_num⟩
  | 3 => ⟨((-100113761/1073741824), (-1095372455/4294967296)), (171/2147483648), by norm_num⟩
  | 4 => ⟨((10311207/134217728), (451271115/2147483648)), (71/1073741824), by norm_num⟩
  | 5 => ⟨((-434995919/8589934592), (-594926391/4294967296)), (47/1073741824), by norm_num⟩
  | 6 => ⟨((238945931/8589934592), (163398361/2147483648)), (415/17179869184), by norm_num⟩
  | 7 => ⟨((-450015319/34359738368), (-1230935639/34359738368)), (49/4294967296), by norm_num⟩
  | 8 => ⟨((185397135/34359738368), (1014240765/68719476736)), (325/68719476736), by norm_num⟩
  | 9 => ⟨((-271572761/137438953472), (-1485676491/274877906944)), (239/137438953472), by norm_num⟩
  | 10 => ⟨((358023807/549755813888), (489654735/274877906944)), (79/137438953472), by norm_num⟩
  | 11 => ⟨((-53635821/274877906944), (-293422205/549755813888)), (95/549755813888), by norm_num⟩
  | 12 => ⟨((14731243/274877906944), (1289428961/8796093022208)), (105/2199023255552), by norm_num⟩
  | 13 => ⟨((-239024117/17592186044416), (-1307614617/35184372088832)), (107/8796093022208), by norm_num⟩
  | 14 => ⟨((225081285/70368744177664), (1231338417/140737488355328)), (405/140737488355328), by norm_num⟩
  | 15 => ⟨((-395643305/562949953421312), (-1082210813/562949953421312)), (357/562949953421312), by norm_num⟩
  | 16 => ⟨((81498487/562949953421312), (445848787/1125899906842624)), (37/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98746931018139/633825300114114700748351602688), (1589580489603/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888601727177833/316912650057057350374175801344), (469508484879/158456325028528675187087900672)), (184771/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((471995302795205/9903520314283042199192993792), (1056114893783/19807040628566084398385987584)), (207891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((471911667023929/618970019642690137449562112), (140221073411/154742504910672534362390528)), (13807/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((110582087121501/9671406556917033397649408), (560685572069/38685626227668133590597632)), (220943/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((386948492186775/2417851639229258349412352), (1050863353303/4835703278458516698824704)), (207167/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257249664898401/604462909807314587353088), (1838167105147/604462909807314587353088)), (181305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885292087652701/75557863725914323419136), (2985440393711/75557863725914323419136)), (294681/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295665314220555/4722366482869645213696), (2237697690299/4722366482869645213696)), (110533/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404718129816651/147573952589676412928), (1537294641629/295147905179352825856)), (304053/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910128570596711/36893488147419103232), (3839872001635/73786976294838206464)), (380199/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819039989700935/9223372036854775808), (2157617238597/4611686018427387904)), (427907/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795145967634559/576460752303423488), (4309464769009/1152921504606846976)), (53517/144115188075855872), by norm_num⟩
  | 5 => ⟨((1191352444076565/144115188075855872), (3764300635029/144115188075855872)), (374877/144115188075855872), by norm_num⟩
  | 4 => ⟨((1486802647406953/36028797018963968), (5633513547881/36028797018963968)), (35177/2251799813685248), by norm_num⟩
  | 3 => ⟨((370806934355745/2251799813685248), (1754826720147/2251799813685248)), (704447/9007199254740992), by norm_num⟩
  | 2 => ⟨((1107964310810923/2251799813685248), (13971079685149/4503599627370496)), (1411623/4503599627370496), by norm_num⟩
  | 1 => ⟨((68692980128733/70368744177664), (20788555766857/2251799813685248)), (2124291/2251799813685248), by norm_num⟩
  | 0 => ⟨((1072639015610059/1125899906842624), (40909466122063/2251799813685248)), (2138103/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1072639015610059/1125899906842624), (40909466122063/2251799813685248)), (8156215672019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1021526029724667/1125899906842624), (77948473400907/2251799813685248)), (518951/140737488355328), by norm_num⟩
  | 2 => ⟨((462739374941749/562949953421312), (141444890566915/2251799813685248)), (15641823/2251799813685248), by norm_num⟩
  | 3 => ⟨((1512584283991903/2251799813685248), (232532642917385/2251799813685248)), (27679909/2251799813685248), by norm_num⟩
  | 4 => ⟨((992024145566163/2251799813685248), (78098687781733/562949953421312)), (21451587/1125899906842624), by norm_num⟩
  | 5 => ⟨((393694599078839/2251799813685248), (34406159706407/281474976710656)), (99411523/4503599627370496), by norm_num⟩
  | 6 => ⟨((562986262027533/36028797018963968), (1539947248995351/36028797018963968)), (236258061/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6479879/2097152), (-1033670289/16777216)), (1/8388608), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile008Terms3
