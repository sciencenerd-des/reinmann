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
namespace Reinmann.XiBand97.Tile043Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35769/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35769/1280))
  have he : value ((69/80), (35769/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-649938377/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-402123245497565/9007199254740992), (-1438907951259231/18014398509481984)), (296071223/9007199254740992), by norm_num⟩
  | 1 => ⟨((531636417/4294967296), (951170911/4294967296)), (393/4294967296), by norm_num⟩
  | 2 => ⟨((-737004567/4294967296), (-659301435/2147483648)), (547/4294967296), by norm_num⟩
  | 3 => ⟨((340568425/2147483648), (152330977/536870912)), (127/1073741824), by norm_num⟩
  | 4 => ⟨((-472128087/4294967296), (-422351149/2147483648)), (177/2147483648), by norm_num⟩
  | 5 => ⟨((130901701/2147483648), (468402413/4294967296)), (197/4294967296), by norm_num⟩
  | 6 => ⟨((-30244715/1073741824), (-865791499/17179869184)), (183/8589934592), by norm_num⟩
  | 7 => ⟨((191671213/17179869184), (685852499/34359738368)), (291/34359738368), by norm_num⟩
  | 8 => ⟨((-132856361/34359738368), (-237698363/34359738368)), (405/137438953472), by norm_num⟩
  | 9 => ⟨((654855197/549755813888), (146453289/68719476736)), (501/549755813888), by norm_num⟩
  | 10 => ⟨((-363128827/1099511627776), (-162421895/274877906944)), (279/1099511627776), by norm_num⟩
  | 11 => ⟨((732223193/8796093022208), (1310048333/8796093022208)), (565/8796093022208), by norm_num⟩
  | 12 => ⟨((-338358961/17592186044416), (-1210741745/35184372088832)), (525/35184372088832), by norm_num⟩
  | 13 => ⟨((577310917/140737488355328), (1032888895/140737488355328)), (225/70368744177664), by norm_num⟩
  | 14 => ⟨((-228663677/281474976710656), (-818221743/562949953421312)), (359/562949953421312), by norm_num⟩
  | 15 => ⟨((338128177/2251799813685248), (604957967/2251799813685248)), (533/4503599627370496), by norm_num⟩
  | 16 => ⟨((-468745185/18014398509481984), (-419324909/9007199254740992)), (371/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-2710042490877/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889137715761127/316912650057057350374175801344), (-801379469365/158456325028528675187087900672)), (185031/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944593348227923/19807040628566084398385987584), (-3605449665823/39614081257132168796771975168)), (208201/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888926871688545/2475880078570760549798248448), (-3829854950631/2475880078570760549798248448)), (55315/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885296447700861/77371252455336267181195264), (-14956261745/604462909807314587353088)), (221313/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548992755723139/9671406556917033397649408), (-3588385435307/9671406556917033397649408)), (207537/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258297858287135/604462909807314587353088), (-3138720217471/604462909807314587353088)), (181651/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886994005533941/75557863725914323419136), (-5098326639505/75557863725914323419136)), (295289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296940531705705/4722366482869645213696), (-1910956856501/2361183241434822606848)), (221559/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620623960995875/590295810358705651712), (-2626078460623/295147905179352825856)), (304793/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911221736421979/36893488147419103232), (-3280368452263/36893488147419103232)), (381217/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227686941644769/1152921504606846976), (-7374701458629/9223372036854775808)), (429179/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398185596590493/288230376151711744), (-3683523933305/576460752303423488)), (429567/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193490869758489/144115188075855872), (-402347790135/9007199254740992)), (376307/144115188075855872), by norm_num⟩
  | 4 => ⟨((744999436280749/18014398509481984), (-9639162596581/36028797018963968)), (282667/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487203100909769/9007199254740992), (-12018925838917/9007199254740992)), (88525/1125899906842624), by norm_num⟩
  | 2 => ⟨((138988738501067/281474976710656), (-11973975135153/2251799813685248)), (710501/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209864096707671/2251799813685248), (-17848902080441/1125899906842624)), (1071521/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168067878436085/2251799813685248), (-17625728100921/562949953421312)), (4332425/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168067878436085/2251799813685248), (-17625728100921/562949953421312)), (16526889809615325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085242052296075/2251799813685248), (-135762600911189/2251799813685248)), (4306973/1125899906842624), by norm_num⟩
  | 2 => ⟨((1922818763259293/2251799813685248), (-251441431719269/2251799813685248)), (531009/70368744177664), by norm_num⟩
  | 3 => ⟨((1613824275440195/2251799813685248), (-429413218557243/2251799813685248)), (32814335/2251799813685248), by norm_num⟩
  | 4 => ⟨((537355289093795/1125899906842624), (-615505403358605/2251799813685248)), (29775063/1125899906842624), by norm_num⟩
  | 5 => ⟨((344682471588993/2251799813685248), (-36720080749459/140737488355328)), (89397447/2251799813685248), by norm_num⟩
  | 6 => ⟨((-402123245497565/9007199254740992), (-1438907951259231/18014398509481984)), (296071223/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-649938377/8388608)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1328299483/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1261333642950129/18014398509481984), (231367529383437/4503599627370496)), (571026683/18014398509481984), by norm_num⟩
  | 1 => ⟨((852019145/4294967296), (-625146457/4294967296)), (97/1073741824), by norm_num⟩
  | 2 => ⟨((-603488003/2147483648), (442793321/2147483648)), (69/536870912), by norm_num⟩
  | 3 => ⟨((1139873509/4294967296), (-209087991/1073741824)), (523/4294967296), by norm_num⟩
  | 4 => ⟨((-807376209/4294967296), (296195443/2147483648)), (93/1073741824), by norm_num⟩
  | 5 => ⟨((228746905/2147483648), (-671347905/8589934592)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((-432059189/8589934592), (158505987/4294967296)), (201/8589934592), by norm_num⟩
  | 7 => ⟨((699494777/34359738368), (-256617873/17179869184)), (327/34359738368), by norm_num⟩
  | 8 => ⟨((-123863621/17179869184), (363526591/68719476736)), (465/137438953472), by norm_num⟩
  | 9 => ⟨((623879225/274877906944), (-457754839/274877906944)), (295/274877906944), by norm_num⟩
  | 10 => ⟨((-353516589/549755813888), (518766847/1099511627776)), (21/68719476736), by norm_num⟩
  | 11 => ⟨((91053447/549755813888), (-534464419/4398046511104)), (87/1099511627776), by norm_num⟩
  | 12 => ⟨((-687930243/17592186044416), (504750575/17592186044416)), (165/8796093022208), by norm_num⟩
  | 13 => ⟨((149927165/17592186044416), (-880040655/140737488355328)), (289/70368744177664), by norm_num⟩
  | 14 => ⟨((-970915759/562949953421312), (712383693/562949953421312)), (235/281474976710656), by norm_num⟩
  | 15 => ⟨((733549729/2251799813685248), (-538222663/2251799813685248)), (357/2251799813685248), by norm_num⟩
  | 16 => ⟨((-64946965/1125899906842624), (762449815/18014398509481984)), (127/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1633859380425/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778192371034867/633825300114114700748351602688), (3864820033427/633825300114114700748351602688)), (185161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944546567451397/19807040628566084398385987584), (4346984003517/39614081257132168796771975168)), (208355/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944413651526487/1237940039285380274899124224), (4617517524995/2475880078570760549798248448)), (110717/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885246573771495/77371252455336267181195264), (4616220697405/154742504910672534362390528)), (110749/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48403095370083/302231454903657293676544), (540791170137/1208925819614629174706176)), (103861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258215677310657/604462909807314587353088), (3784161026463/604462909807314587353088)), (181825/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943430052715715/37778931862957161709568), (3073340144167/37778931862957161709568)), (36949/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162104974437631/590295810358705651712), (4607752312831/4722366482869645213696)), (110903/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620484943855043/590295810358705651712), (1582997961065/147573952589676412928)), (76291/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911134472696657/36893488147419103232), (988686383023/9223372036854775808)), (381725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821298152295221/9223372036854775808), (8890620964609/9223372036854775808)), (429815/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592543711723655/1152921504606846976), (4440590895737/576460752303423488)), (215141/576460752303423488), by norm_num⟩
  | 5 => ⟨((298328894544051/36028797018963968), (3880211919907/72057594037927936)), (5891/2251799813685248), by norm_num⟩
  | 4 => ⟨((1489733043182387/36028797018963968), (11619437411285/36028797018963968)), (566589/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486865776848185/9007199254740992), (7243624700083/4503599627370496)), (177521/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111565075167819/2251799813685248), (1803972232249/281474976710656)), (712859/2251799813685248), by norm_num⟩
  | 1 => ⟨((552198095957193/562949953421312), (21509336246417/1125899906842624)), (1076247/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082888782034859/1125899906842624), (10616860151877/281474976710656)), (4360883/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082888782034859/1125899906842624), (10616860151877/281474976710656)), (16635448464400481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519959466924819/562949953421312), (163380473721027/2251799813685248)), (8717555/2251799813685248), by norm_num⟩
  | 2 => ⟨((7457632387885/8796093022208), (75451843903371/562949953421312)), (17368667/2251799813685248), by norm_num⟩
  | 3 => ⟨((1578195746836701/2251799813685248), (511765497157669/2251799813685248)), (34107341/2251799813685248), by norm_num⟩
  | 4 => ⟨((989785094441771/2251799813685248), (22417238370931/70368744177664)), (63312043/2251799813685248), by norm_num⟩
  | 5 => ⟨((413075063196247/4503599627370496), (1261255897480603/4503599627370496)), (95996381/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1261333642950129/18014398509481984), (231367529383437/4503599627370496)), (571026683/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1328299483/16777216)), (1/8388608), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-169387143/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((456209607720357/9007199254740992), (588461654536575/9007199254740992)), (366280179/18014398509481984), by norm_num⟩
  | 1 => ⟨((-157191201/1073741824), (-811039423/4294967296)), (127/2147483648), by norm_num⟩
  | 2 => ⟨((28396313/134217728), (586051361/2147483648)), (369/4294967296), by norm_num⟩
  | 3 => ⟨((-875476279/4294967296), (-1129270869/4294967296)), (179/2147483648), by norm_num⟩
  | 4 => ⟨((316306489/2147483648), (816003157/4294967296)), (65/1073741824), by norm_num⟩
  | 5 => ⟨((-365697337/4294967296), (-14740953/134217728)), (303/8589934592), by norm_num⟩
  | 6 => ⟨((704667503/17179869184), (908945797/17179869184)), (147/8589934592), by norm_num⟩
  | 7 => ⟨((-581928871/34359738368), (-750626075/34359738368)), (245/34359738368), by norm_num⟩
  | 8 => ⟨((840995387/137438953472), (271198551/34359738368)), (89/34359738368), by norm_num⟩
  | 9 => ⟨((-540175403/274877906944), (-348384281/137438953472)), (231/274877906944), by norm_num⟩
  | 10 => ⟨((156130773/274877906944), (402784035/549755813888)), (269/1099511627776), by norm_num⟩
  | 11 => ⟨((-656401421/4398046511104), (-846687709/4398046511104)), (71/1099511627776), by norm_num⟩
  | 12 => ⟨((316207355/8796093022208), (407873707/8796093022208)), (275/17592186044416), by norm_num⟩
  | 13 => ⟨((-562434959/70368744177664), (-181370253/17592186044416)), (247/70368744177664), by norm_num⟩
  | 14 => ⟨((928940641/562949953421312), (299558547/140737488355328)), (205/281474976710656), by norm_num⟩
  | 15 => ⟨((-357997839/1125899906842624), (-923557935/2251799813685248)), (159/1125899906842624), by norm_num⟩
  | 16 => ⟨((258686711/4503599627370496), (667356443/9007199254740992)), (231/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (593551339243/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778123370878541/633825300114114700748351602688), (1403904386789/633825300114114700748351602688)), (184677/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944507956329891/19807040628566084398385987584), (1579051349587/39614081257132168796771975168)), (207779/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944372893489163/1237940039285380274899124224), (1677315532841/2475880078570760549798248448)), (110393/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885206115009901/77371252455336267181195264), (209604488043/19342813113834066795298816)), (220809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774411913579961/4835703278458516698824704), (785762120313/4835703278458516698824704)), (103517/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629075245342277/302231454903657293676544), (343643624923/151115727451828646838272)), (181179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886755366622421/75557863725914323419136), (1116364617613/37778931862957161709568)), (147231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296762281058383/4722366482869645213696), (1673712333843/4722366482869645213696)), (220887/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810190024433545/295147905179352825856), (574999769223/147573952589676412928)), (303785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822140354071595/73786976294838206464), (2872967225813/73786976294838206464)), (379831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455289239084449/2305843009213693952), (1614648505137/4611686018427387904)), (427445/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796203421752755/576460752303423488), (3225811647343/1152921504606846976)), (13363/36028797018963968), by norm_num⟩
  | 5 => ⟨((149150084378283/18014398509481984), (2818669014275/144115188075855872)), (93589/36028797018963968), by norm_num⟩
  | 4 => ⟨((93098148198475/2251799813685248), (4220183291903/36028797018963968)), (561919/36028797018963968), by norm_num⟩
  | 3 => ⟨((11614682136071/70368744177664), (1315392737809/2251799813685248)), (351537/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111403790591509/2251799813685248), (327571129685/140737488355328)), (704089/2251799813685248), by norm_num⟩
  | 1 => ⟨((2208433475416471/2251799813685248), (15621629468377/2251799813685248)), (1058683/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082776929848267/1125899906842624), (15419195000991/1125899906842624)), (4255253/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082776929848267/1125899906842624), (15419195000991/1125899906842624)), (16232501992232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041094435760535/1125899906842624), (59314503971225/2251799813685248)), (8301099/2251799813685248), by norm_num⟩
  | 2 => ⟨((120236939468855/140737488355328), (109693587625405/2251799813685248)), (15788999/2251799813685248), by norm_num⟩
  | 3 => ⟨((1638218116593111/2251799813685248), (187430107067675/2251799813685248)), (28516467/2251799813685248), by norm_num⟩
  | 4 => ⟨((1176227361065365/2251799813685248), (136358212274091/1125899906842624)), (46239491/2251799813685248), by norm_num⟩
  | 5 => ⟨((290686709525467/1125899906842624), (142453391467563/1125899906842624)), (59506555/2251799813685248), by norm_num⟩
  | 6 => ⟨((456209607720357/9007199254740992), (588461654536575/9007199254740992)), (366280179/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-169387143/2097152)), (1/8388608), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1380445557/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((586714229718887/9007199254740992), (-200506132967283/4503599627370496)), (289514377/18014398509481984), by norm_num⟩
  | 1 => ⟨((-411878645/2147483648), (281514203/2147483648)), (205/4294967296), by norm_num⟩
  | 2 => ⟨((1212751537/4294967296), (-51806337/268435456)), (19/268435456), by norm_num⟩
  | 3 => ⟨((-595145483/2147483648), (25423433/134217728)), (75/1073741824), by norm_num⟩
  | 4 => ⟨((876184779/4294967296), (-598861977/4294967296)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((-515974523/4294967296), (705325019/8589934592)), (265/8589934592), by norm_num⟩
  | 6 => ⟨((506418499/8589934592), (-43266385/1073741824)), (263/17179869184), by norm_num⟩
  | 7 => ⟨((-852067639/34359738368), (145594549/8589934592)), (223/34359738368), by norm_num⟩
  | 8 => ⟨((1254430585/137438953472), (-428694265/68719476736)), (331/137438953472), by norm_num⟩
  | 9 => ⟨((-51299921/17179869184), (140251567/68719476736)), (219/274877906944), by norm_num⟩
  | 10 => ⟨((966716717/1099511627776), (-660739489/1099511627776)), (65/274877906944), by norm_num⟩
  | 11 => ⟨((-1035068503/4398046511104), (353728565/2199023255552)), (35/549755813888), by norm_num⟩
  | 12 => ⟨((507949341/8796093022208), (-694354783/17592186044416)), (277/17592186044416), by norm_num⟩
  | 13 => ⟨((-230096283/17592186044416), (157268099/17592186044416)), (253/70368744177664), by norm_num⟩
  | 14 => ⟨((774290817/281474976710656), (-132304663/70368744177664)), (215/281474976710656), by norm_num⟩
  | 15 => ⟨((-303980275/562949953421312), (207766937/562949953421312)), (85/562949953421312), by norm_num⟩
  | 16 => ⟨((895051371/9007199254740992), (-152939267/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-390495659303/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444513033596075/158456325028528675187087900672), (-230888346123/158456325028528675187087900672)), (92291/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888935822298235/39614081257132168796771975168), (-1038769587811/39614081257132168796771975168)), (207667/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888660756945147/2475880078570760549798248448), (-1103406900881/2475880078570760549798248448)), (55165/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885163637072527/77371252455336267181195264), (-275771386063/38685626227668133590597632)), (220675/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744259771073/9671406556917033397649408), (-1033801386367/9671406556917033397649408)), (206899/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258080947907183/604462909807314587353088), (-226058762017/151115727451828646838272)), (181053/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886642507030339/75557863725914323419136), (-734371289801/37778931862957161709568)), (294241/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648338882619653/2361183241434822606848), (-275249448395/1180591620717411303424)), (55177/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620264048815675/590295810358705651712), (-1512963944041/590295810358705651712)), (303517/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821995667418885/73786976294838206464), (-29528811171/1152921504606846976)), (379461/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820994614164341/9223372036854775808), (-2124204661555/9223372036854775808)), (53373/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199030629784601/144115188075855872), (-530467490051/288230376151711744)), (427097/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298264924554581/36028797018963968), (-927006539117/72057594037927936)), (373837/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489360108265025/36028797018963968), (-2775781836859/36028797018963968)), (561011/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486418581548845/9007199254740992), (-3460580257985/9007199254740992)), (350855/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222292378811463/4503599627370496), (-430862221951/281474976710656)), (43899/140737488355328), by norm_num⟩
  | 1 => ⟨((551919056085735/562949953421312), (-10272546712629/2251799813685248)), (131909/140737488355328), by norm_num⟩
  | 0 => ⟨((541025241233917/562949953421312), (-10137047982409/1125899906842624)), (1058693/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((541025241233917/562949953421312), (-10137047982409/1125899906842624)), (4038593294383811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2079635107440713/2251799813685248), (-1217781171477/70368744177664)), (8215945/2251799813685248), by norm_num⟩
  | 2 => ⟨((119997445239683/140737488355328), (-17994782392235/562949953421312)), (3864983/562949953421312), by norm_num⟩
  | 3 => ⟨((1634719933686793/2251799813685248), (-61371790556911/1125899906842624)), (6837915/562949953421312), by norm_num⟩
  | 4 => ⟨((1180053066324541/2251799813685248), (-178214224514465/2251799813685248)), (42694333/2251799813685248), by norm_num⟩
  | 5 => ⟨((302150511171697/1125899906842624), (-93392956524305/1125899906842624)), (103011497/4503599627370496), by norm_num⟩
  | 6 => ⟨((586714229718887/9007199254740992), (-200506132967283/4503599627370496)), (289514377/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1380445557/16777216)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-702246733/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-151570497899119/4503599627370496), (-1217182116712909/18014398509481984)), (487080491/18014398509481984), by norm_num⟩
  | 1 => ⟨((216514889/2147483648), (869358003/4294967296)), (175/2147483648), by norm_num⟩
  | 2 => ⟨((-648620641/4294967296), (-651090957/2147483648)), (527/4294967296), by norm_num⟩
  | 3 => ⟨((647697929/4294967296), (650164731/2147483648)), (33/268435456), by norm_num⟩
  | 4 => ⟨((-485082397/4294967296), (-486929867/2147483648)), (397/4294967296), by norm_num⟩
  | 5 => ⟨((581270797/8589934592), (583484607/4294967296)), (239/4294967296), by norm_num⟩
  | 6 => ⟨((-580443895/17179869184), (-145663639/2147483648)), (15/536870912), by norm_num⟩
  | 7 => ⟨((248407787/17179869184), (498707731/17179869184)), (413/34359738368), by norm_num⟩
  | 8 => ⟨((-93020403/17179869184), (-746997423/68719476736)), (311/68719476736), by norm_num⟩
  | 9 => ⟨((61925383/34359738368), (248644921/68719476736)), (13/8589934592), by norm_num⟩
  | 10 => ⟨((-593637979/1099511627776), (-1191797783/1099511627776)), (125/274877906944), by norm_num⟩
  | 11 => ⟨((646683801/4398046511104), (1298293485/4398046511104)), (547/4398046511104), by norm_num⟩
  | 12 => ⟨((-645763845/17592186044416), (-1296446565/17592186044416)), (549/17592186044416), by norm_num⟩
  | 13 => ⟨((595241721/70368744177664), (597508741/35184372088832)), (127/17592186044416), by norm_num⟩
  | 14 => ⟨((-509481381/281474976710656), (-511421777/140737488355328)), (437/281474976710656), by norm_num⟩
  | 15 => ⟨((101751321/281474976710656), (408555393/562949953421312)), (351/1125899906842624), by norm_num⟩
  | 16 => ⟨((-76204929/1125899906842624), (-76495161/562949953421312)), (33/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-2648111968151/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444494797328589/158456325028528675187087900672), (-3131269207767/633825300114114700748351602688)), (185017/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888853512429477/39614081257132168796771975168), (-214958665/2417851639229258349412352)), (208183/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236071621514509/309485009821345068724781056), (-3741013552253/2475880078570760549798248448)), (221241/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885119558912223/77371252455336267181195264), (-3739903677487/154742504910672534362390528)), (221293/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548661218834195/9671406556917033397649408), (-438122603335/1208925819614629174706176)), (207517/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258007893065235/604462909807314587353088), (-766419942387/151115727451828646838272)), (1419/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1886523054893809/75557863725914323419136), (-1244880227725/18889465931478580854784)), (295255/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648293765571721/2361183241434822606848), (-1866354471943/2361183241434822606848)), (55383/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620138930266799/590295810358705651712), (-5129337382205/590295810358705651712)), (304753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821837701762375/73786976294838206464), (-6406968509455/73786976294838206464)), (381161/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820814751635577/9223372036854775808), (-7201377366813/9223372036854775808)), (429109/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592062492942903/1152921504606846976), (-7193306683613/1152921504606846976)), (26843/72057594037927936), by norm_num⟩
  | 5 => ⟨((298224240334881/36028797018963968), (-1571268387873/36028797018963968)), (188115/72057594037927936), by norm_num⟩
  | 4 => ⟨((744555002296065/18014398509481984), (-4704747510681/18014398509481984)), (565199/36028797018963968), by norm_num⟩
  | 3 => ⟨((743047751063255/4503599627370496), (-5865110795209/4503599627370496)), (176999/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221615059058275/4503599627370496), (-11682859889431/2251799813685248)), (88781/281474976710656), by norm_num⟩
  | 1 => ⟨((1103291499958873/1125899906842624), (-17406266817753/1125899906842624)), (2142037/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080804730620137/1125899906842624), (-34342724674065/1125899906842624)), (4329445/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080804730620137/1125899906842624), (-34342724674065/1125899906842624)), (16515522011763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072936387863017/2251799813685248), (-131868842210687/2251799813685248)), (4288099/1125899906842624), by norm_num⟩
  | 2 => ⟨((950278939222523/1125899906842624), (-121394326344015/1125899906842624)), (8397215/1125899906842624), by norm_num⟩
  | 3 => ⟨((1577926198346387/2251799813685248), (-409835620252691/2251799813685248)), (31971123/2251799813685248), by norm_num⟩
  | 4 => ⟨((515562226643945/1125899906842624), (-574376423944989/2251799813685248)), (881947/35184372088832), by norm_num⟩
  | 5 => ⟨((325654775050495/2251799813685248), (-263013422650773/1125899906842624)), (80488389/2251799813685248), by norm_num⟩
  | 6 => ⟨((-151570497899119/4503599627370496), (-1217182116712909/18014398509481984)), (487080491/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-702246733/8388608)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1427367829/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1261705753617115/18014398509481984), (164279525485931/9007199254740992)), (454542651/18014398509481984), by norm_num⟩
  | 1 => ⟨((114479407/536870912), (-238491393/4294967296)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((-1394140493/4294967296), (363046199/4294967296)), (253/2147483648), by norm_num⟩
  | 3 => ⟨((1414830671/4294967296), (-92108525/1073741824)), (515/4294967296), by norm_num⟩
  | 4 => ⟨((-1076870931/4294967296), (280426471/4294967296)), (393/4294967296), by norm_num⟩
  | 5 => ⟨((1311423085/8589934592), (-341505873/8589934592)), (15/268435456), by norm_num⟩
  | 6 => ⟨((-1330885669/17179869184), (173287049/8589934592)), (489/17179869184), by norm_num⟩
  | 7 => ⟨((578844469/17179869184), (-301472177/34359738368)), (107/8589934592), by norm_num⟩
  | 8 => ⟨((-881152487/68719476736), (114729851/34359738368)), (327/68719476736), by norm_num⟩
  | 9 => ⟨((149038251/34359738368), (-310486761/274877906944)), (111/68719476736), by norm_num⟩
  | 10 => ⟨((-726000479/549755813888), (94528391/274877906944)), (543/1099511627776), by norm_num⟩
  | 11 => ⟨((401877227/1099511627776), (-209304587/2199023255552)), (603/4398046511104), by norm_num⟩
  | 12 => ⟨((-1631365647/17592186044416), (212410837/8796093022208)), (307/8796093022208), by norm_num⟩
  | 13 => ⟨((1528224405/70368744177664), (-198981403/35184372088832)), (577/70368744177664), by norm_num⟩
  | 14 => ⟨((-166168339/35184372088832), (346173341/281474976710656)), (63/35184372088832), by norm_num⟩
  | 15 => ⟨((539630119/562949953421312), (-70262167/281474976710656)), (411/1125899906842624), by norm_num⟩
  | 16 => ⟨((-821458003/4503599627370496), (26739343/562949953421312)), (157/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (940108469547/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777909030212151/633825300114114700748351602688), (1111557261847/158456325028528675187087900672)), (185275/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888774307559565/39614081257132168796771975168), (5000846589719/39614081257132168796771975168)), (52123/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888488445943977/2475880078570760549798248448), (5311973695331/2475880078570760549798248448)), (55397/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770154174738775/154742504910672534362390528), (5310369958859/154742504910672534362390528)), (221661/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774290571047323/4835703278458516698824704), (2488384139691/4835703278458516698824704)), (207885/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257937383741969/604462909807314587353088), (4352969151175/604462909807314587353088)), (90989/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471601912264099/18889465931478580854784), (7070382556431/75557863725914323419136)), (73965/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296500252994273/4722366482869645213696), (2649997314123/2361183241434822606848)), (27753/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810008874178017/295147905179352825856), (7282956993013/590295810358705651712)), (152745/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821684465614631/73786976294838206464), (9096896046465/73786976294838206464)), (11943/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820639947422495/9223372036854775808), (5112331522581/4611686018427387904)), (215189/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591884678908785/1152921504606846976), (10212989680047/1152921504606846976)), (107729/288230376151711744), by norm_num⟩
  | 5 => ⟨((596368998888743/72057594037927936), (8923244292523/144115188075855872)), (188829/72057594037927936), by norm_num⟩
  | 4 => ⟨((744432415530539/18014398509481984), (13358650242141/36028797018963968)), (141925/9007199254740992), by norm_num⟩
  | 3 => ⟨((185722164452635/1125899906842624), (16652495599811/9007199254740992)), (711753/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110471872837493/2251799813685248), (4145973041073/562949953421312)), (714951/2251799813685248), by norm_num⟩
  | 1 => ⟨((137843090053739/140737488355328), (386011848927/17592186044416)), (1080445/1125899906842624), by norm_num⟩
  | 0 => ⟨((134942533700819/140737488355328), (48727772056293/1125899906842624)), (2193105/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((134942533700819/140737488355328), (48727772056293/1125899906842624)), (8366031651023482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032980632527207/1125899906842624), (93442750751253/1125899906842624)), (1098859/281474976710656), by norm_num⟩
  | 2 => ⟨((1879949421927215/2251799813685248), (171462047717539/1125899906842624)), (549685/70368744177664), by norm_num⟩
  | 3 => ⟨((1517280920359855/2251799813685248), (286295411812393/1125899906842624)), (17363963/1125899906842624), by norm_num⟩
  | 4 => ⟨((876756951479479/2251799813685248), (771632652759833/2251799813685248)), (1007207/35184372088832), by norm_num⟩
  | 5 => ⟨((76954354516451/2251799813685248), (75110394825521/281474976710656)), (11796925/281474976710656), by norm_num⟩
  | 6 => ⟨((-1261705753617115/18014398509481984), (164279525485931/9007199254740992)), (454542651/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1427367829/16777216)), (1/8388608), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile043Terms2
