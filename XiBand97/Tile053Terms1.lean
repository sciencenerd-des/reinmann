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
namespace Reinmann.XiBand97.Tile053Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨53,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77087/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77087/2560))
  have he : value ((69/80), (77087/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-17760513005/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1329537479791529/9007199254740992), (255174031507195/9007199254740992)), (7181029/2251799813685248), by norm_num⟩
  | 1 => ⟨((22287692467/68719476736), (-4277608135/68719476736)), (121/17179869184), by norm_num⟩
  | 2 => ⟨((-12242766415/34359738368), (4699432863/68719476736)), (267/34359738368), by norm_num⟩
  | 3 => ⟨((17933404841/68719476736), (-3441903129/68719476736)), (393/68719476736), by norm_num⟩
  | 4 => ⟨((-2462732367/17179869184), (1890658537/68719476736)), (217/68719476736), by norm_num⟩
  | 5 => ⟨((17315763469/274877906944), (-830840281/68719476736)), (383/274877906944), by norm_num⟩
  | 6 => ⟨((-12682207023/549755813888), (4868113827/1099511627776)), (563/1099511627776), by norm_num⟩
  | 7 => ⟨((1990404069/274877906944), (-764024239/549755813888)), (355/2199023255552), by norm_num⟩
  | 8 => ⟨((-17493458957/8796093022208), (3357465671/8796093022208)), (49/1099511627776), by norm_num⟩
  | 9 => ⟨((2135392109/4398046511104), (-1639356909/17592186044416)), (385/35184372088832), by norm_num⟩
  | 10 => ⟨((-15014195277/140737488355328), (2881628233/140737488355328)), (85/35184372088832), by norm_num⟩
  | 11 => ⟨((5998101613/281474976710656), (-4604788637/1125899906842624)), (273/562949953421312), by norm_num⟩
  | 12 => ⟨((-8786117521/2251799813685248), (1686292461/2251799813685248)), (201/2251799813685248), by norm_num⟩
  | 13 => ⟨((23760090285/36028797018963968), (-4560200911/36028797018963968)), (273/18014398509481984), by norm_num⟩
  | 14 => ⟨((-14916072667/144115188075855872), (2862795863/144115188075855872)), (345/144115188075855872), by norm_num⟩
  | 15 => ⟨((546232691/36028797018963968), (-3354776229/1152921504606846976)), (407/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-19203134297/9223372036854775808), (3685598391/9223372036854775808)), (449/9223372036854775808), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (3845272579769/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779034773939559/633825300114114700748351602688), (4552028376185/633825300114114700748351602688)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472510117591517/9903520314283042199192993792), (320009370455/2475880078570760549798248448)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889833395501019/2475880078570760549798248448), (5439104039619/2475880078570760549798248448)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771498732123891/154742504910672534362390528), (5437916802283/154742504910672534362390528)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((193730155988671/1208925819614629174706176), (5096785636309/9671406556917033397649408)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259039559537995/604462909807314587353088), (557303268579/75557863725914323419136)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888197903117429/75557863725914323419136), (3621288880919/37778931862957161709568)), (18495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297842259511299/4722366482869645213696), (5429864359635/4722366482869645213696)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621861895542421/590295810358705651712), (3731350882089/295147905179352825856)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823987981539719/73786976294838206464), (4661667596957/36893488147419103232)), (5973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823229108619711/9223372036854775808), (2620455070285/2305843009213693952)), (26905/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594470971382859/1152921504606846976), (5236578476933/576460752303423488)), (6735/288230376151711744), by norm_num⟩
  | 5 => ⟨((597498887543025/72057594037927936), (4577134040209/72057594037927936)), (23611/144115188075855872), by norm_num⟩
  | 4 => ⟨((746124018310091/18014398509481984), (428497456899/1125899906842624)), (17747/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489995009794367/9007199254740992), (8552906759843/4503599627370496)), (22251/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114672583986637/2251799813685248), (8527354684795/1125899906842624)), (22353/1125899906842624), by norm_num⟩
  | 1 => ⟨((277250820581093/281474976710656), (25454385233831/1125899906842624)), (67569/1125899906842624), by norm_num⟩
  | 0 => ⟨((545943550186097/562949953421312), (25199276677611/562949953421312)), (137187/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((545943550186097/562949953421312), (25199276677611/562949953421312)), (523326878074264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056645815981215/1125899906842624), (6109505155781/70368744177664)), (8699/35184372088832), by norm_num⟩
  | 2 => ⟨((983164581568541/1125899906842624), (91739352975703/562949953421312)), (570829/1125899906842624), by norm_num⟩
  | 3 => ⟨((103578052680713/140737488355328), (160218296552951/562949953421312)), (1182973/1125899906842624), by norm_num⟩
  | 4 => ⟨((1037283719566969/2251799813685248), (471661086316307/1125899906842624)), (2414617/1125899906842624), by norm_num⟩
  | 5 => ⟨((165290708674323/4503599627370496), (869076128376591/2251799813685248)), (4247629/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1329537479791529/9007199254740992), (255174031507195/9007199254740992)), (7181029/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-17760513005/268435456)), (1/134217728), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-2326519835/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1206230116099673/9007199254740992), (-270567186261831/9007199254740992)), (11668433/9007199254740992), by norm_num⟩
  | 1 => ⟨((-21190242645/68719476736), (594142885/8589934592)), (207/68719476736), by norm_num⟩
  | 2 => ⟨((24396168415/68719476736), (-684032275/8589934592)), (241/68719476736), by norm_num⟩
  | 3 => ⟨((-18724751239/68719476736), (4200113385/68719476736)), (187/68719476736), by norm_num⟩
  | 4 => ⟨((2694708317/17179869184), (-4835559235/137438953472)), (109/68719476736), by norm_num⟩
  | 5 => ⟨((-9927672321/137438953472), (1113428661/68719476736)), (203/274877906944), by norm_num⟩
  | 6 => ⟨((3809885049/137438953472), (-854588079/137438953472)), (157/549755813888), by norm_num⟩
  | 7 => ⟨((-20051621759/2199023255552), (562217649/274877906944)), (209/2199023255552), by norm_num⟩
  | 8 => ⟨((5771320669/2199023255552), (-2589107955/4398046511104)), (243/8796093022208), by norm_num⟩
  | 9 => ⟨((-1476550771/2199023255552), (5299236783/35184372088832)), (251/35184372088832), by norm_num⟩
  | 10 => ⟨((21759256283/140737488355328), (-610097181/17592186044416)), (117/70368744177664), by norm_num⟩
  | 11 => ⟨((-9109552573/281474976710656), (2043346435/281474976710656)), (99/281474976710656), by norm_num⟩
  | 12 => ⟨((3495919993/562949953421312), (-1568326347/1125899906842624)), (153/2251799813685248), by norm_num⟩
  | 13 => ⟨((-19814531107/18014398509481984), (4444559837/18014398509481984)), (219/18014398509481984), by norm_num⟩
  | 14 => ⟨((26071225115/144115188075855872), (-2923993493/72057594037927936)), (291/144115188075855872), by norm_num⟩
  | 15 => ⟨((-16008323815/576460752303423488), (3590796709/576460752303423488)), (181/576460752303423488), by norm_num⟩
  | 16 => ⟨((9215131945/2305843009213693952), (-4134057487/4611686018427387904)), (105/2305843009213693952), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-143714398195/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778905678032105/633825300114114700748351602688), (-340206797787/633825300114114700748351602688)), (5765/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889895891997559/39614081257132168796771975168), (-11958318639/1237940039285380274899124224)), (3243/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944840312368707/1237940039285380274899124224), (-203250241435/1237940039285380274899124224)), (6891/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771346909965599/154742504910672534362390528), (-50800983897/19342813113834066795298816)), (13783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699921952749/9671406556917033397649408), (-95227252265/2417851639229258349412352)), (6461/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258916905994669/604462909807314587353088), (-166598523121/302231454903657293676544)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888000477236705/75557863725914323419136), (-135315222495/18889465931478580854784)), (9187/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40552994971435/147573952589676412928), (-405784467181/4722366482869645213696)), (6891/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405415811119835/147573952589676412928), (-278845912553/295147905179352825856)), (9475/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911871839366251/36893488147419103232), (-87090286061/9223372036854775808)), (23689/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911479887895065/4611686018427387904), (-391636637599/4611686018427387904)), (6663/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594208512357177/1152921504606846976), (-391299859067/576460752303423488)), (13327/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194775841380285/144115188075855872), (-684017780739/144115188075855872)), (11663/72057594037927936), by norm_num⟩
  | 4 => ⟨((372982633565633/9007199254740992), (-1024514671349/36028797018963968)), (17497/18014398509481984), by norm_num⟩
  | 3 => ⟨((93101562125927/562949953421312), (-319500427749/2251799813685248)), (21877/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228685384686265/4503599627370496), (-2548095993135/4503599627370496)), (87537/4503599627370496), by norm_num⟩
  | 1 => ⟨((554304082217925/562949953421312), (-1901218189237/1125899906842624)), (131385/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182984414900441/2251799813685248), (-3763203503591/1125899906842624)), (263091/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182984414900441/2251799813685248), (-3763203503591/1125899906842624)), (1003612526900481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058123435292609/1125899906842624), (-3648199341927/562949953421312)), (511861/2251799813685248), by norm_num⟩
  | 2 => ⟨((497189830142765/562949953421312), (-13714345997727/1125899906842624)), (242183/562949953421312), by norm_num⟩
  | 3 => ⟨((878055695266707/1125899906842624), (-48449303997195/2251799813685248)), (1734743/2251799813685248), by norm_num⟩
  | 4 => ⟨((342124093600059/562949953421312), (-75568329028011/2251799813685248)), (1390199/1125899906842624), by norm_num⟩
  | 5 => ⟨((414573210071213/1125899906842624), (-1435171208185/35184372088832)), (3566103/2251799813685248), by norm_num⟩
  | 6 => ⟨((1206230116099673/9007199254740992), (-270567186261831/9007199254740992)), (11668433/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-2326519835/33554432)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-19382565905/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1137168244455157/9007199254740992), (-14496174632931/2251799813685248)), (11644263/4503599627370496), by norm_num⟩
  | 1 => ⟨((20803912031/68719476736), (530400217/34359738368)), (107/17179869184), by norm_num⟩
  | 2 => ⟨((-12471400579/34359738368), (-1271844173/68719476736)), (515/68719476736), by norm_num⟩
  | 3 => ⟨((19936741663/68719476736), (1016583043/68719476736)), (207/34359738368), by norm_num⟩
  | 4 => ⟨((-23903109295/137438953472), (-1218829837/137438953472)), (499/137438953472), by norm_num⟩
  | 5 => ⟨((11463430557/137438953472), (584525261/137438953472)), (481/274877906944), by norm_num⟩
  | 6 => ⟨((-9162701981/274877906944), (-58401265/34359738368)), (193/274877906944), by norm_num⟩
  | 7 => ⟨((12554971295/1099511627776), (640183393/1099511627776)), (531/2199023255552), by norm_num⟩
  | 8 => ⟨((-30105506319/8796093022208), (-383773183/2199023255552)), (639/8796093022208), by norm_num⟩
  | 9 => ⟨((16042189175/17592186044416), (1635996269/35184372088832)), (171/8796093022208), by norm_num⟩
  | 10 => ⟨((-30773991671/140737488355328), (-98073693/8796093022208)), (329/70368744177664), by norm_num⟩
  | 11 => ⟨((26833748783/562949953421312), (684132203/281474976710656)), (9/8796093022208), by norm_num⟩
  | 12 => ⟨((-335127705/35184372088832), (-8544153/17592186044416)), (463/2251799813685248), by norm_num⟩
  | 13 => ⟨((15824760903/9007199254740992), (1613822747/18014398509481984)), (343/9007199254740992), by norm_num⟩
  | 14 => ⟨((-21683496779/72057594037927936), (-1105650839/72057594037927936)), (59/9007199254740992), by norm_num⟩
  | 15 => ⟨((27730535693/576460752303423488), (1413991957/576460752303423488)), (303/288230376151711744), by norm_num⟩
  | 16 => ⟨((-16623730113/2305843009213693952), (-847651157/2305843009213693952)), (365/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-4025911938409/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444691713477891/158456325028528675187087900672), (-4764508064811/633825300114114700748351602688)), (11585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889739057794967/39614081257132168796771975168), (-5359067768809/39614081257132168796771975168)), (13037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889513131442365/2475880078570760549798248448), (-2846402134989/1237940039285380274899124224)), (13855/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442794613332359/38685626227668133590597632), (-5691448325473/154742504910672534362390528)), (3465/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549540970970273/9671406556917033397649408), (-5334292235437/9671406556917033397649408)), (12999/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629388400872689/302231454903657293676544), (-2333032636133/302231454903657293676544)), (11379/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235971361613173/9444732965739290427392), (-1894913885907/18889465931478580854784)), (18501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297521976861843/4722366482869645213696), (-2841189494741/2361183241434822606848)), (13885/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405355366670249/147573952589676412928), (-7809432319905/590295810358705651712)), (19105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911718692909421/36893488147419103232), (-9756033170791/73786976294838206464)), (11951/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822609607532457/9223372036854775808), (-10967622687033/9223372036854775808)), (13459/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796925685415323/576460752303423488), (-10957731747961/1152921504606846976)), (13477/576460752303423488), by norm_num⟩
  | 5 => ⟨((298613878746395/36028797018963968), (-4788445608217/72057594037927936)), (11813/72057594037927936), by norm_num⟩
  | 4 => ⟨((372858608231273/9007199254740992), (-14343096849515/36028797018963968)), (35519/36028797018963968), by norm_num⟩
  | 3 => ⟨((744488822121637/4503599627370496), (-17889969561201/9007199254740992)), (44541/9007199254740992), by norm_num⟩
  | 2 => ⟨((556827351248475/1125899906842624), (-17831654511415/2251799813685248)), (22377/1125899906842624), by norm_num⟩
  | 1 => ⟨((276868814746873/281474976710656), (-26601825645733/1125899906842624)), (33833/562949953421312), by norm_num⟩
  | 0 => ⟨((1088826778835279/1125899906842624), (-52621826165987/1125899906842624)), (17185/140737488355328), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1088826778835279/1125899906842624), (-52621826165987/1125899906842624)), (65555573046636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1050514961882035/1125899906842624), (-50889118235579/562949953421312)), (139379/562949953421312), by norm_num⟩
  | 2 => ⟨((970976966135981/1125899906842624), (-47481823009807/281474976710656)), (285293/562949953421312), by norm_num⟩
  | 3 => ⟨((402666296974843/562949953421312), (-327586892386961/1125899906842624)), (294163/281474976710656), by norm_num⟩
  | 4 => ⟨((240362136778131/562949953421312), (-937264139330935/2251799813685248)), (4735953/2251799813685248), by norm_num⟩
  | 5 => ⟨((20392239838529/2251799813685248), (-800365325144623/2251799813685248)), (7986691/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1137168244455157/9007199254740992), (-14496174632931/2251799813685248)), (11644263/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-19382565905/268435456)), (1/134217728), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-5021473149/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((443961300957107/4503599627370496), (572195485457965/9007199254740992)), (13119405/9007199254740992), by norm_num⟩
  | 1 => ⟨((-16833532547/68719476736), (-338996021/2147483648)), (251/68719476736), by norm_num⟩
  | 2 => ⟨((10457439241/34359738368), (6738987735/34359738368)), (79/17179869184), by norm_num⟩
  | 3 => ⟨((-17323840207/68719476736), (-11163836957/68719476736)), (33/8589934592), by norm_num⟩
  | 4 => ⟨((10762031433/68719476736), (6935273173/68719476736)), (83/34359738368), by norm_num⟩
  | 5 => ⟨((-10697057389/137438953472), (-3446701285/68719476736)), (167/137438953472), by norm_num⟩
  | 6 => ⟨((17720792693/549755813888), (11419641257/549755813888)), (279/549755813888), by norm_num⟩
  | 7 => ⟨((-3145322543/274877906944), (-4053820357/549755813888)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((7815832903/2199023255552), (5036682581/2199023255552)), (251/4398046511104), by norm_num⟩
  | 9 => ⟨((-17263657915/17592186044416), (-695315891/1099511627776)), (279/17592186044416), by norm_num⟩
  | 10 => ⟨((17159431341/70368744177664), (1382236065/8796093022208)), (279/70368744177664), by norm_num⟩
  | 11 => ⟨((-15505303653/281474976710656), (-4995967403/140737488355328)), (127/140737488355328), by norm_num⟩
  | 12 => ⟨((12843077385/1125899906842624), (2069085437/281474976710656)), (53/281474976710656), by norm_num⟩
  | 13 => ⟨((-9819645661/4503599627370496), (-12655961013/9007199254740992)), (327/9007199254740992), by norm_num⟩
  | 14 => ⟨((6971686515/18014398509481984), (4492697383/18014398509481984)), (117/18014398509481984), by norm_num⟩
  | 15 => ⟨((-4619730715/72057594037927936), (-11908195843/288230376151711744)), (313/288230376151711744), by norm_num⟩
  | 16 => ⟨((5739799787/576460752303423488), (7397688759/1152921504606846976)), (49/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (2912776335/39614081257132168796771975168)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778662903123059/633825300114114700748351602688), (441181314069/316912650057057350374175801344)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889622799425455/39614081257132168796771975168), (248118109271/9903520314283042199192993792)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889390498809931/2475880078570760549798248448), (1054271470071/2475880078570760549798248448)), (431/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771056823335451/154742504910672534362390528), (527006131279/77371252455336267181195264)), (431/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549428007488079/9671406556917033397649408), (987861176273/9671406556917033397649408)), (3233/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258679022586575/604462909807314587353088), (864103308505/604462909807314587353088)), (2829/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235951749371429/9444732965739290427392), (701826024017/37778931862957161709568)), (9195/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297406045870185/4722366482869645213696), (526143948383/2361183241434822606848)), (6897/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621264890082505/590295810358705651712), (1446163151217/590295810358705651712)), (18969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823245902630363/73786976294838206464), (903302784327/36893488147419103232)), (23715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822400007124527/9223372036854775808), (1015461062883/4611686018427387904)), (26685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593649030458335/1152921504606846976), (2029037381109/1152921504606846976)), (6673/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194286617269479/144115188075855872), (1773289677207/144115188075855872)), (23363/144115188075855872), by norm_num⟩
  | 4 => ⟨((745598671521087/18014398509481984), (2655704212799/36028797018963968)), (35059/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488709633292803/9007199254740992), (51753752755/140737488355328)), (21925/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113429023367825/2251799813685248), (825295219309/562949953421312)), (43889/2251799813685248), by norm_num⟩
  | 1 => ⟨((553620943919437/562949953421312), (9848426573347/2251799813685248)), (32967/562949953421312), by norm_num⟩
  | 0 => ⟨((2177553093090195/2251799813685248), (19477468254721/2251799813685248)), (264543/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177553093090195/2251799813685248), (19477468254721/2251799813685248)), (1009151467330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526396493223065/562949953421312), (18835253909281/1125899906842624)), (516219/2251799813685248), by norm_num⟩
  | 2 => ⟨((984117947595861/1125899906842624), (70448973636499/2251799813685248)), (61417/140737488355328), by norm_num⟩
  | 3 => ⟨((429544120409933/562949953421312), (30788749037119/562949953421312)), (1779341/2251799813685248), by norm_num⟩
  | 4 => ⟨((1304273697481565/2251799813685248), (93970172966859/1125899906842624)), (1454995/1125899906842624), by norm_num⟩
  | 5 => ⟨((92470936702979/281474976710656), (435430624706851/4503599627370496)), (7713525/4503599627370496), by norm_num⟩
  | 6 => ⟨((443961300957107/4503599627370496), (572195485457965/9007199254740992)), (13119405/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-5021473149/67108864)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-10366445217/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-32515261502629/1125899906842624), (-950920184021893/9007199254740992)), (21234903/9007199254740992), by norm_num⟩
  | 1 => ⟨((636291497/8589934592), (18608567161/68719476736)), (209/34359738368), by norm_num⟩
  | 2 => ⟨((-6528221865/68719476736), (-23865016191/68719476736)), (269/34359738368), by norm_num⟩
  | 3 => ⟨((5581519493/68719476736), (20404185981/68719476736)), (231/34359738368), by norm_num⟩
  | 4 => ⟨((-3579078709/68719476736), (-6541962965/34359738368)), (595/137438953472), by norm_num⟩
  | 5 => ⟨((1836031127/68719476736), (26847685925/274877906944)), (613/274877906944), by norm_num⟩
  | 6 => ⟨((-6279102479/549755813888), (-11477159127/274877906944)), (263/274877906944), by norm_num⟩
  | 7 => ⟨((575199281/137438953472), (16821903959/1099511627776)), (387/1099511627776), by norm_num⟩
  | 8 => ⟨((-5901428105/4398046511104), (-21573665875/4398046511104)), (249/2199023255552), by norm_num⟩
  | 9 => ⟨((6727495211/17592186044416), (24593493521/17592186044416)), (571/17592186044416), by norm_num⟩
  | 10 => ⟨((-6902273807/70368744177664), (-25232426161/70368744177664)), (589/70368744177664), by norm_num⟩
  | 11 => ⟨((6437811915/281474976710656), (11767253685/140737488355328)), (551/281474976710656), by norm_num⟩
  | 12 => ⟨((-172006891/35184372088832), (-20121606519/1125899906842624)), (237/562949953421312), by norm_num⟩
  | 13 => ⟨((1086003605/1125899906842624), (7940138725/2251799813685248)), (47/562949953421312), by norm_num⟩
  | 14 => ⟨((-6366958283/36028797018963968), (-11637744983/18014398509481984)), (553/36028797018963968), by norm_num⟩
  | 15 => ⟨((2177456741/72057594037927936), (1990015101/18014398509481984)), (95/36028797018963968), by norm_num⟩
  | 16 => ⟨((-5585066269/1152921504606846976), (-10208575909/576460752303423488)), (245/576460752303423488), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-2393955201241/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111159538514217/39614081257132168796771975168), (-708119477491/158456325028528675187087900672)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944749266051943/19807040628566084398385987584), (-3185916965063/39614081257132168796771975168)), (813/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((59039319004189/77371252455336267181195264), (-3384272260957/2475880078570760549798248448)), (13823/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885462122103127/77371252455336267181195264), (-1691706205923/77371252455336267181195264)), (13827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549303408293199/9671406556917033397649408), (-792758946307/2417851639229258349412352)), (6483/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258569692277825/604462909807314587353088), (-346717903717/75557863725914323419136)), (2837/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943717879985827/37778931862957161709568), (-1126405322369/18889465931478580854784)), (9223/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324317967138671/1180591620717411303424), (-1688859505519/2361183241434822606848)), (865/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621079583028197/590295810358705651712), (-290120759741/36893488147419103232)), (19037/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911506525334297/36893488147419103232), (-2899384919545/36893488147419103232)), (23809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822136376518933/9223372036854775808), (-6518606743879/9223372036854775808)), (13401/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593383313860871/1152921504606846976), (-6512349644403/1152921504606846976)), (3353/144115188075855872), by norm_num⟩
  | 5 => ⟨((149256471783045/18014398509481984), (-5691272964987/144115188075855872)), (11747/72057594037927936), by norm_num⟩
  | 4 => ⟨((186355051367739/4503599627370496), (-2130714787325/9007199254740992)), (17645/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488255332151213/9007199254740992), (-2657255276023/2251799813685248)), (11049/2251799813685248), by norm_num⟩
  | 2 => ⟨((17390040352773/35184372088832), (-10592262178281/2251799813685248)), (44323/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106512102101045/1125899906842624), (-3949185458205/281474976710656)), (133605/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174395636661649/2251799813685248), (-31228351198493/1125899906842624)), (67441/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174395636661649/2251799813685248), (-31228351198493/1125899906842624)), (257267000438499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2097919857861413/2251799813685248), (-60309793236027/1125899906842624)), (535947/2251799813685248), by norm_num⟩
  | 2 => ⟨((974047208528131/1125899906842624), (-224753749572985/2251799813685248)), (1056063/2251799813685248), by norm_num⟩
  | 3 => ⟨((207864703772801/281474976710656), (-97220348384129/562949953421312)), (254759/281474976710656), by norm_num⟩
  | 4 => ⟨((580439320281861/1125899906842624), (-574365200167093/2251799813685248)), (3714109/2251799813685248), by norm_num⟩
  | 5 => ⟨((903938110989069/4503599627370496), (-296104604283569/1125899906842624)), (357763/140737488355328), by norm_num⟩
  | 6 => ⟨((-32515261502629/1125899906842624), (-950920184021893/9007199254740992)), (21234903/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-10366445217/134217728)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5332979217/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-554539502158717/9007199254740992), (92514074441393/1125899906842624)), (20978935/9007199254740992), by norm_num⟩
  | 1 => ⟨((11165325453/68719476736), (-7450865059/34359738368)), (425/68719476736), by norm_num⟩
  | 2 => ⟨((-3683241747/17179869184), (9831630023/34359738368)), (141/17179869184), by norm_num⟩
  | 3 => ⟨((6480190753/34359738368), (-17297490183/68719476736)), (249/34359738368), by norm_num⟩
  | 4 => ⟨((-2137699363/17179869184), (11412267063/68719476736)), (165/34359738368), by norm_num⟩
  | 5 => ⟨((2256604469/34359738368), (-188235169/2147483648)), (175/68719476736), by norm_num⟩
  | 6 => ⟨((-7940411419/274877906944), (2649404813/68719476736)), (155/137438953472), by norm_num⟩
  | 7 => ⟨((5987200273/549755813888), (-998847313/68719476736)), (235/549755813888), by norm_num⟩
  | 8 => ⟨((-3950141191/1099511627776), (5272030645/1099511627776)), (39/274877906944), by norm_num⟩
  | 9 => ⟨((9266354723/8796093022208), (-386477531/274877906944)), (23/549755813888), by norm_num⟩
  | 10 => ⟨((-2445444135/8796093022208), (3263796355/8796093022208)), (195/17592186044416), by norm_num⟩
  | 11 => ⟨((9387152391/140737488355328), (-6264251413/70368744177664)), (47/17592186044416), by norm_num⟩
  | 12 => ⟨((-8257744441/562949953421312), (11021145737/562949953421312)), (333/562949953421312), by norm_num⟩
  | 13 => ⟨((13410868303/4503599627370496), (-4474682375/1125899906842624)), (17/140737488355328), by norm_num⟩
  | 14 => ⟨((-10112014369/18014398509481984), (6747967611/9007199254740992)), (103/4503599627370496), by norm_num⟩
  | 15 => ⟨((3558158085/36028797018963968), (-18995491609/144115188075855872)), (291/72057594037927936), by norm_num⟩
  | 16 => ⟨((-4695091587/288230376151711744), (48955265/2251799813685248)), (193/288230376151711744), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (1441877794323/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111153260710037/39614081257132168796771975168), (3411639513805/633825300114114700748351602688)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472346361460615/9903520314283042199192993792), (3837322454943/39614081257132168796771975168)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944568969376641/1237940039285380274899124224), (2038103628597/1237940039285380274899124224)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770803845334775/154742504910672534362390528), (4075141159433/154742504910672534362390528)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549190396882407/9671406556917033397649408), (1909656189833/4835703278458516698824704)), (12975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629235334977045/302231454903657293676544), (1670383090083/302231454903657293676544)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943637295729707/37778931862957161709568), (5426622906347/75557863725914323419136)), (9231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297150767363683/4722366482869645213696), (2034055479507/2361183241434822606848)), (13853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810456352047203/295147905179352825856), (5590637426039/590295810358705651712)), (9529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822803905707465/73786976294838206464), (6983776196695/73786976294838206464)), (23837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455475084686307/2305843009213693952), (7850535873577/9223372036854775808)), (26837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199143292645205/144115188075855872), (7842775625277/1152921504606846976)), (26863/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596921687184283/72057594037927936), (6853705523267/144115188075855872)), (11767/72057594037927936), by norm_num⟩
  | 4 => ⟨((745262860518175/18014398509481984), (641445613203/2251799813685248)), (35359/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487858329016481/9007199254740992), (6399226266607/4503599627370496)), (11075/2251799813685248), by norm_num⟩
  | 2 => ⟨((556280075970881/1125899906842624), (25505686235247/4503599627370496)), (88905/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211790009443041/2251799813685248), (9507760849529/562949953421312)), (134123/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085910518853445/1125899906842624), (75155508555667/2251799813685248)), (67831/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085910518853445/1125899906842624), (75155508555667/2251799813685248)), (258754732372093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1046087276659329/1125899906842624), (72486156890487/1125899906842624)), (541487/2251799813685248), by norm_num⟩
  | 2 => ⟨((1934531374999045/2251799813685248), (269391074628339/2251799813685248)), (134491/281474976710656), by norm_num⟩
  | 3 => ⟨((203717048217549/281474976710656), (462870174201085/2251799813685248)), (263263/281474976710656), by norm_num⟩
  | 4 => ⟨((542186715266893/1125899906842624), (670003043951707/2251799813685248)), (3914423/2251799813685248), by norm_num⟩
  | 5 => ⟨((645671656534449/4503599627370496), (1290582750424803/4503599627370496)), (12198903/4503599627370496), by norm_num⟩
  | 6 => ⟨((-554539502158717/9007199254740992), (92514074441393/1125899906842624)), (20978935/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5332979217/67108864)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-1368099821/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1726609399401611/18014398509481984), (118407081166525/9007199254740992)), (1918209/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4459137851/17179869184), (-152898941/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((6037784577/17179869184), (3312464063/68719476736)), (219/68719476736), by norm_num⟩
  | 3 => ⟨((-10900415825/34359738368), (-747526581/17179869184)), (25/8589934592), by norm_num⟩
  | 4 => ⟨((29518873267/137438953472), (506084877/17179869184)), (273/137438953472), by norm_num⟩
  | 5 => ⟨((-15987718137/137438953472), (-2192805205/137438953472)), (75/68719476736), by norm_num⟩
  | 6 => ⟨((3607961943/68719476736), (1979408859/274877906944)), (137/274877906944), by norm_num⟩
  | 7 => ⟨((-11166333789/549755813888), (-3063050605/1099511627776)), (107/549755813888), by norm_num⟩
  | 8 => ⟨((15119496231/2199023255552), (1036861851/1099511627776)), (147/2199023255552), by norm_num⟩
  | 9 => ⟨((-9098745513/4398046511104), (-1247943975/4398046511104)), (179/8796093022208), by norm_num⟩
  | 10 => ⟨((19711887693/35184372088832), (1351797973/17592186044416)), (49/8796093022208), by norm_num⟩
  | 11 => ⟨((-19411193247/140737488355328), (-83198563/4398046511104)), (195/140737488355328), by norm_num⟩
  | 12 => ⟨((17522161925/562949953421312), (300407847/70368744177664)), (89/281474976710656), by norm_num⟩
  | 13 => ⟨((-14600275115/2251799813685248), (-4005019227/4503599627370496)), (299/4503599627370496), by norm_num⟩
  | 14 => ⟨((5648325423/4503599627370496), (3098798035/18014398509481984)), (233/18014398509481984), by norm_num⟩
  | 15 => ⟨((-16315678717/72057594037927936), (-1118893419/36028797018963968)), (85/36028797018963968), by norm_num⟩
  | 16 => ⟨((22091838515/576460752303423488), (757504887/144115188075855872)), (29/72057594037927936), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (44388167593/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778366683855217/633825300114114700748351602688), (210033818367/633825300114114700748351602688)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889289639804963/39614081257132168796771975168), (236240190189/39614081257132168796771975168)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889036626546109/2475880078570760549798248448), (7842044505/77371252455336267181195264)), (13781/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442675768641755/38685626227668133590597632), (125439101765/77371252455336267181195264)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549096499175887/9671406556917033397649408), (117563459677/4835703278458516698824704)), (1615/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258389083908991/604462909807314587353088), (102832343319/302231454903657293676544)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887143090291569/75557863725914323419136), (167035681019/37778931862957161709568)), (18371/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297053082189665/4722366482869645213696), (62609136959/1180591620717411303424)), (13779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779913870451/590295810358705651712), (172080142513/295147905179352825856)), (9473/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455660051300685/18446744073709551616), (53739450409/9223372036854775808)), (23683/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821719315712807/9223372036854775808), (483263842001/9223372036854775808)), (26645/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592969235729977/1152921504606846976), (241387656255/576460752303423488)), (13323/576460752303423488), by norm_num⟩
  | 5 => ⟨((149211600524477/18014398509481984), (421879469059/144115188075855872)), (23317/144115188075855872), by norm_num⟩
  | 4 => ⟨((745154317213273/18014398509481984), (631723008339/36028797018963968)), (8745/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487602258606117/9007199254740992), (393869577813/4503599627370496)), (43731/9007199254740992), by norm_num⟩
  | 2 => ⟨((139040862378253/281474976710656), (98109338389/281474976710656)), (87481/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211203540752897/2251799813685248), (2340353954039/2251799813685248)), (65637/1125899906842624), by norm_num⟩
  | 0 => ⟨((271387062068369/281474976710656), (1155984652267/562949953421312)), (131381/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((271387062068369/281474976710656), (1155984652267/562949953421312)), (501178745750045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((130829753045297/140737488355328), (8916438178371/2251799813685248)), (507769/2251799813685248), by norm_num⟩
  | 2 => ⟨((972938421671659/1125899906842624), (16577465159457/2251799813685248)), (237017/562949953421312), by norm_num⟩
  | 3 => ⟨((1681393636369607/2251799813685248), (7162649490215/562949953421312)), (413123/562949953421312), by norm_num⟩
  | 4 => ⟨((627556607493295/1125899906842624), (21393079791909/1125899906842624)), (1254923/1125899906842624), by norm_num⟩
  | 5 => ⟨((1397529671526991/4503599627370496), (95392981180309/4503599627370496)), (1446633/1125899906842624), by norm_num⟩
  | 6 => ⟨((1726609399401611/18014398509481984), (118407081166525/9007199254740992)), (1918209/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1368099821/16777216)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile053Terms1
