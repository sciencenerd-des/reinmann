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
namespace Reinmann.XiBand97.Tile005Terms2
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-6183763273/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-818396264794063/18014398509481984), (-22357928765775/281474976710656)), (74101117/18014398509481984), by norm_num⟩
  | 1 => ⟨((1081979873/8589934592), (3783529123/17179869184)), (99/8589934592), by norm_num⟩
  | 2 => ⟨((-1499942597/8589934592), (-5245085089/17179869184)), (277/17179869184), by norm_num⟩
  | 3 => ⟨((2772482619/17179869184), (2423743961/8589934592)), (129/8589934592), by norm_num⟩
  | 4 => ⟨((-1921738511/17179869184), (-1680011293/8589934592)), (181/17179869184), by norm_num⟩
  | 5 => ⟨((2131276209/34359738368), (931596073/8589934592)), (203/34359738368), by norm_num⟩
  | 6 => ⟨((-492429365/17179869184), (-1721955177/34359738368)), (95/34359738368), by norm_num⟩
  | 7 => ⟨((3120695095/274877906944), (21313721/1073741824)), (303/274877906944), by norm_num⟩
  | 8 => ⟨((-2163101007/549755813888), (-3782027679/549755813888)), (53/137438953472), by norm_num⟩
  | 9 => ⟨((1332753213/1099511627776), (4660447685/2199023255552)), (33/274877906944), by norm_num⟩
  | 10 => ⟨((-1478070611/4398046511104), (-5168601877/8796093022208)), (295/8796093022208), by norm_num⟩
  | 11 => ⟨((2980423205/35184372088832), (5211057191/35184372088832)), (75/8796093022208), by norm_num⟩
  | 12 => ⟨((-1377247961/70368744177664), (-4816039467/140737488355328)), (35/17592186044416), by norm_num⟩
  | 13 => ⟨((2349872101/562949953421312), (1027145901/140737488355328)), (241/562949953421312), by norm_num⟩
  | 14 => ⟨((-116343373/140737488355328), (-406836163/281474976710656)), (193/2251799813685248), by norm_num⟩
  | 15 => ⟨((688154291/4503599627370496), (150398581/562949953421312)), (9/562949953421312), by norm_num⟩
  | 16 => ⟨((-1907968827/72057594037927936), (-833986819/18014398509481984)), (101/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-340360946257/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778275379215149/633825300114114700748351602688), (-3220711414533/633825300114114700748351602688)), (11565/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889186634706979/39614081257132168796771975168), (-113204334241/1237940039285380274899124224)), (26027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944463401120945/1237940039285380274899124224), (-1924003799653/1237940039285380274899124224)), (27659/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770592821640837/154742504910672534362390528), (-961737663429/38685626227668133590597632)), (13833/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((12101505328061/75557863725914323419136), (-3605393540573/9671406556917033397649408)), (25943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258297789195509/604462909807314587353088), (-1576798498167/302231454903657293676544)), (22707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886993884686765/75557863725914323419136), (-640311430499/9444732965739290427392)), (36913/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296940433576745/4722366482869645213696), (-240001787595/295147905179352825856)), (1731/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810311906953281/295147905179352825856), (-5277050733533/590295810358705651712)), (38101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822443270765685/73786976294838206464), (-3295916467309/36893488147419103232)), (23827/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227686910101877/1152921504606846976), (-7409655300303/9223372036854775808)), (26825/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592742102826603/1152921504606846976), (-3700982613787/576460752303423488)), (53699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193490586661823/144115188075855872), (-3234038152679/72057594037927936)), (47041/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489998378129841/36028797018963968), (-4842424034593/18014398509481984)), (70671/36028797018963968), by norm_num⟩
  | 3 => ⟨((743601180618557/4503599627370496), (-12075889215901/9007199254740992)), (88531/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111908986871075/2251799813685248), (-12030723468073/2251799813685248)), (22205/562949953421312), by norm_num⟩
  | 1 => ⟨((276232554105517/281474976710656), (-35866975013627/2251799813685248)), (66977/562949953421312), by norm_num⟩
  | 0 => ⟨((1084028494987551/1125899906842624), (-35418482037745/1125899906842624)), (135409/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084028494987551/1125899906842624), (-35418482037745/1125899906842624)), (516544344188499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1042600058798297/1125899906842624), (-136405176143201/2251799813685248)), (134633/281474976710656), by norm_num⟩
  | 2 => ⟨((961331716086409/1125899906842624), (-126313221808599/1125899906842624)), (531311/562949953421312), by norm_num⟩
  | 3 => ⟨((403323436137791/562949953421312), (-215701068181431/1125899906842624)), (4106069/2251799813685248), by norm_num⟩
  | 4 => ⟨((1073189938227459/2251799813685248), (-309076483509069/1125899906842624)), (7456847/2251799813685248), by norm_num⟩
  | 5 => ⟨((683563030960359/4503599627370496), (-589213606340625/2251799813685248)), (22403565/4503599627370496), by norm_num⟩
  | 6 => ⟨((-818396264794063/18014398509481984), (-22357928765775/281474976710656)), (74101117/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-6183763273/134217728)), (1/67108864), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-327980683/134217728), (-3159487825/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1562931174291575/18014398509481984), (-68582303135951/18014398509481984)), (64226935/18014398509481984), by norm_num⟩
  | 1 => ⟨((4222981891/17179869184), (11581677/1073741824)), (175/17179869184), by norm_num⟩
  | 2 => ⟨((-5982304323/17179869184), (-262506895/17179869184)), (125/8589934592), by norm_num⟩
  | 3 => ⟨((1412428703/4294967296), (247912679/17179869184)), (119/8589934592), by norm_num⟩
  | 4 => ⟨((-4001711849/17179869184), (-351194755/34359738368)), (339/34359738368), by norm_num⟩
  | 5 => ⟨((1133770341/8589934592), (199001933/34359738368)), (97/17179869184), by norm_num⟩
  | 6 => ⟨((-4282951013/68719476736), (-187938311/68719476736)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((6934007979/274877906944), (304268189/274877906944)), (151/137438953472), by norm_num⟩
  | 8 => ⟨((-613922623/68719476736), (-215514173/549755813888)), (27/68719476736), by norm_num⟩
  | 9 => ⟨((6184440063/2199023255552), (271376725/2199023255552)), (137/1099511627776), by norm_num⟩
  | 10 => ⟨((-7008735245/8796093022208), (-307547263/8796093022208)), (313/8796093022208), by norm_num⟩
  | 11 => ⟨((3610407677/17592186044416), (158426729/17592186044416)), (325/35184372088832), by norm_num⟩
  | 12 => ⟨((-6819370139/140737488355328), (-299237815/140737488355328)), (309/140737488355328), by norm_num⟩
  | 13 => ⟨((5944840147/562949953421312), (260862945/562949953421312)), (271/562949953421312), by norm_num⟩
  | 14 => ⟨((-2406142919/1125899906842624), (-105582911/1125899906842624)), (221/2251799813685248), by norm_num⟩
  | 15 => ⟨((7271590641/18014398509481984), (319081507/18014398509481984)), (21/1125899906842624), by norm_num⟩
  | 16 => ⟨((-5150491909/72057594037927936), (-7062703/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322343873/5070602400912917605986812821504), (-2017576250565/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444547042338221/158456325028528675187087900672), (-596560604089/79228162514264337593543950336)), (181/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((944544087743851/19807040628566084398385987584), (-5367873774543/39614081257132168796771975168)), (3259/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888821725513535/2475880078570760549798248448), (-5701940658623/2475880078570760549798248448)), (13855/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442621805908063/38685626227668133590597632), (-2850168701295/77371252455336267181195264)), (3465/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548893130434179/9671406556917033397649408), (-5342363156391/9671406556917033397649408)), (12999/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78638133040487/37778931862957161709568), (-584108117631/75557863725914323419136)), (22759/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886850400584297/75557863725914323419136), (-3795106729189/37778931862957161709568)), (18501/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296831915291265/4722366482869645213696), (-2844933875239/2361183241434822606848)), (27769/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620473132248337/590295810358705651712), (-7819031947611/590295810358705651712)), (19105/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911126359288277/36893488147419103232), (-2441746995679/18446744073709551616)), (11951/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910638944987235/4611686018427387904), (-10978512639327/9223372036854775808)), (53837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592520945741807/1152921504606846976), (-2741708089631/288230376151711744)), (26955/576460752303423488), by norm_num⟩
  | 5 => ⟨((596646424287251/72057594037927936), (-2395711485973/36028797018963968)), (11813/36028797018963968), by norm_num⟩
  | 4 => ⟨((372423337037755/9007199254740992), (-14348024075285/36028797018963968)), (555/281474976710656), by norm_num⟩
  | 3 => ⟨((1486806397638625/9007199254740992), (-2236143311101/1125899906842624)), (44543/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111491136539631/2251799813685248), (-17820411042897/2251799813685248)), (44757/1125899906842624), by norm_num⟩
  | 1 => ⟨((552124584499521/562949953421312), (-26559093848461/1125899906842624)), (67673/562949953421312), by norm_num⟩
  | 0 => ⟨((1082451972398117/1125899906842624), (-52434000417417/1125899906842624)), (275007/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082451972398117/1125899906842624), (-52434000417417/1125899906842624)), (1049068455222701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((259559695547651/281474976710656), (-100821195254775/1125899906842624)), (554405/1125899906842624), by norm_num⟩
  | 2 => ⟨((948374583693147/1125899906842624), (-92971386127799/562949953421312)), (280443/281474976710656), by norm_num⟩
  | 3 => ⟨((768131901588245/1125899906842624), (-626497606605811/2251799813685248)), (4520635/2251799813685248), by norm_num⟩
  | 4 => ⟨((109224142056801/281474976710656), (-213710292974503/562949953421312)), (4341885/1125899906842624), by norm_num⟩
  | 5 => ⟨((7274406886385/1125899906842624), (-663428733072569/2251799813685248)), (26665005/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1562931174291575/18014398509481984), (-68582303135951/18014398509481984)), (64226935/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-327980683/134217728), (-3159487825/67108864)), (1/67108864), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-6446457269/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-918720797185401/18014398509481984), (18312670175369/281474976710656)), (16971701/4503599627370496), by norm_num⟩
  | 1 => ⟨((2532429357/17179869184), (-3230616741/17179869184)), (189/17179869184), by norm_num⟩
  | 2 => ⟨((-1829915573/8589934592), (4668841695/17179869184)), (69/4294967296), by norm_num⟩
  | 3 => ⟨((3526090861/17179869184), (-4498229393/17179869184)), (67/4294967296), by norm_num⟩
  | 4 => ⟨((-318491045/2147483648), (50787325/268435456)), (49/4294967296), by norm_num⟩
  | 5 => ⟨((2945784069/34359738368), (-939483199/8589934592)), (229/34359738368), by norm_num⟩
  | 6 => ⟨((-1419068513/34359738368), (3620607607/68719476736)), (223/68719476736), by norm_num⟩
  | 7 => ⟨((18310873/1073741824), (-2989971993/137438953472)), (93/68719476736), by norm_num⟩
  | 8 => ⟨((-846803683/137438953472), (4321065303/549755813888)), (271/549755813888), by norm_num⟩
  | 9 => ⟨((135976525/68719476736), (-2775441137/1099511627776)), (175/1099511627776), by norm_num⟩
  | 10 => ⟨((-2515345329/4398046511104), (3208822671/4398046511104)), (51/1099511627776), by norm_num⟩
  | 11 => ⟨((2643739309/17592186044416), (-843153675/4398046511104)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((-2547129811/70368744177664), (3249370093/70368744177664)), (105/35184372088832), by norm_num⟩
  | 13 => ⟨((283159695/35184372088832), (-2889811553/281474976710656)), (47/70368744177664), by norm_num⟩
  | 14 => ⟨((-3741425305/2251799813685248), (596616407/281474976710656)), (313/2251799813685248), by norm_num⟩
  | 15 => ⟨((720940669/2251799813685248), (-919703047/2251799813685248)), (243/9007199254740992), by norm_num⟩
  | 16 => ⟨((-2083786549/36028797018963968), (2658283713/36028797018963968)), (177/36028797018963968), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (728040401353/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778118069471169/633825300114114700748351602688), (1722006245615/316912650057057350374175801344)), (723/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889009655955085/39614081257132168796771975168), (3873665738363/39614081257132168796771975168)), (26033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236092343805401/309485009821345068724781056), (2057361086515/1237940039285380274899124224)), (13833/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770404756552027/154742504910672534362390528), (2056771933247/77371252455336267181195264)), (27673/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774408178449045/4835703278458516698824704), (3855195775177/9671406556917033397649408)), (811/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258143490719367/604462909807314587353088), (843011274561/151115727451828646838272)), (22715/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471685780872853/18889465931478580854784), (5477228113669/75557863725914323419136)), (18463/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296752339894207/4722366482869645213696), (4105869898979/4722366482869645213696)), (27707/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101272821767473/36893488147419103232), (5642239504997/590295810358705651712)), (38117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455529970971327/18446744073709551616), (1761951180455/18446744073709551616)), (11919/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910565697883345/4611686018427387904), (7921917122579/9223372036854775808)), (53677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592378125176119/1152921504606846976), (123646013043/18014398509481984)), (53729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193172003285727/144115188075855872), (3457271057357/72057594037927936)), (1471/4503599627370496), by norm_num⟩
  | 4 => ⟨((744760150153893/18014398509481984), (2588141737967/9007199254740992)), (70725/36028797018963968), by norm_num⟩
  | 3 => ⟨((743302208050031/4503599627370496), (806692472159/562949953421312)), (88611/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222621067649783/4503599627370496), (25713478577471/4503599627370496)), (177841/4503599627370496), by norm_num⟩
  | 1 => ⟨((276007828854869/281474976710656), (38319240027337/2251799813685248)), (268311/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082226095364893/1125899906842624), (37819452527559/1125899906842624)), (542851/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082226095364893/1125899906842624), (37819452527559/1125899906842624)), (2070812233931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519488012828643/562949953421312), (36352430788023/562949953421312)), (540029/1125899906842624), by norm_num⟩
  | 2 => ⟨((1908136200146191/2251799813685248), (33545880795957/281474976710656)), (2132837/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584937908353121/2251799813685248), (454819183293541/2251799813685248)), (2061519/1125899906842624), by norm_num⟩
  | 4 => ⟨((127962511911215/281474976710656), (160063110554307/562949953421312)), (3734789/1125899906842624), by norm_num⟩
  | 5 => ⟨((141673050031667/1125899906842624), (1164271321320691/4503599627370496)), (22078381/4503599627370496), by norm_num⟩
  | 6 => ⟨((-918720797185401/18014398509481984), (18312670175369/281474976710656)), (16971701/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-6446457269/134217728)), (1/67108864), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-820880567/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((82255708412947/4503599627370496), (691361279302337/9007199254740992)), (26598977/9007199254740992), by norm_num⟩
  | 1 => ⟨((-461953953/8589934592), (-485341811/2147483648)), (151/17179869184), by norm_num⟩
  | 2 => ⟨((680097613/8589934592), (2858118693/8589934592)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-333750987/4294967296), (-1402592681/4294967296)), (111/8589934592), by norm_num⟩
  | 4 => ⟨((982709415/17179869184), (2064924281/8589934592)), (165/17179869184), by norm_num⟩
  | 5 => ⟨((-1157411163/34359738368), (-4864034833/34359738368)), (197/34359738368), by norm_num⟩
  | 6 => ⟨((567987757/34359738368), (4773951253/68719476736)), (49/17179869184), by norm_num⟩
  | 7 => ⟨((-477830083/68719476736), (-2008086879/68719476736)), (167/137438953472), by norm_num⟩
  | 8 => ⟨((703470761/274877906944), (46192885/4294967296)), (31/68719476736), by norm_num⟩
  | 9 => ⟨((-920589657/1099511627776), (-967197377/274877906944)), (41/274877906944), by norm_num⟩
  | 10 => ⟨((271062007/1099511627776), (1139141463/1099511627776)), (195/4398046511104), by norm_num⟩
  | 11 => ⟨((-1160909875/17592186044416), (-1219684555/4398046511104)), (105/8796093022208), by norm_num⟩
  | 12 => ⟨((1139409429/70368744177664), (598547791/8796093022208)), (13/4398046511104), by norm_num⟩
  | 13 => ⟨((-1032283549/281474976710656), (-1084546121/70368744177664)), (95/140737488355328), by norm_num⟩
  | 14 => ⟨((868427405/1125899906842624), (1824788499/562949953421312)), (81/562949953421312), by norm_num⟩
  | 15 => ⟨((-681875067/4503599627370496), (-358198559/562949953421312)), (1/35184372088832), by norm_num⟩
  | 16 => ⟨((1003869763/36028797018963968), (4218775197/36028797018963968)), (95/18014398509481984), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1741836483341/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778050317086493/633825300114114700748351602688), (1029895557797/316912650057057350374175801344)), (11551/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888933677778097/39614081257132168796771975168), (1158377096741/19807040628566084398385987584)), (3249/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888658345141711/2475880078570760549798248448), (2460913671681/2475880078570760549798248448)), (27621/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770324712599729/154742504910672534362390528), (2460196605483/154742504910672534362390528)), (27625/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548741699345339/9671406556917033397649408), (2305672703503/9671406556917033397649408)), (25903/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258078548697041/604462909807314587353088), (2016702303747/604462909807314587353088)), (11335/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943319155394625/37778931862957161709568), (1637857213047/37778931862957161709568)), (36847/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324168589505037/1180591620717411303424), (2455537996125/4722366482869645213696)), (13821/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620258941880933/590295810358705651712), (3374338234435/590295810358705651712)), (9505/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821988651706145/73786976294838206464), (2107442565713/36893488147419103232)), (47543/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910492926999055/4611686018427387904), (2368786202165/4611686018427387904)), (53511/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592235196102719/1152921504606846976), (4732360813821/1152921504606846976)), (26771/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193049872288241/144115188075855872), (2067479853111/72057594037927936)), (11721/36028797018963968), by norm_num⟩
  | 4 => ⟨((744671474687783/18014398509481984), (6190745110999/36028797018963968)), (17599/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486392916039215/9007199254740992), (1929501391567/2251799813685248)), (88119/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222228469241487/4503599627370496), (7687445618013/2251799813685248)), (176607/4503599627370496), by norm_num⟩
  | 1 => ⟨((551887291273631/562949953421312), (2863760920509/281474976710656)), (265841/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163723567662325/2251799813685248), (11303617079561/562949953421312)), (535423/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163723567662325/2251799813685248), (11303617079561/562949953421312)), (2042476662642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1039092218738009/1125899906842624), (86891925387805/2251799813685248)), (32827/70368744177664), by norm_num⟩
  | 2 => ⟨((1914601965622393/2251799813685248), (20048123947987/281474976710656)), (126251/140737488355328), by norm_num⟩
  | 3 => ⟨((1616474661343299/2251799813685248), (68183996258599/562949953421312)), (3722807/2251799813685248), by norm_num⟩
  | 4 => ⟨((563683636041701/1125899906842624), (195785969234577/1125899906842624)), (6246707/2251799813685248), by norm_num⟩
  | 5 => ⟨((992653411174409/4503599627370496), (392082267183351/2251799813685248)), (16854729/4503599627370496), by norm_num⟩
  | 6 => ⟨((82255708412947/4503599627370496), (691361279302337/9007199254740992)), (26598977/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-820880567/16777216)), (1/67108864), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-346794327/134217728), (-6681445055/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((75193847909919/1125899906842624), (158440999799169/4503599627370496)), (31969447/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3437204543/17179869184), (-1810633913/17179869184)), (93/17179869184), by norm_num⟩
  | 2 => ⟨((2574236145/8589934592), (339010903/2147483648)), (141/17179869184), by norm_num⟩
  | 3 => ⟨((-5141148199/17179869184), (-2708229075/17179869184)), (143/17179869184), by norm_num⟩
  | 4 => ⟨((481296987/2147483648), (2028282311/17179869184)), (109/17179869184), by norm_num⟩
  | 5 => ⟨((-4613878135/34359738368), (-2430476311/34359738368)), (133/34359738368), by norm_num⟩
  | 6 => ⟨((4607314545/68719476736), (2427018775/68719476736)), (135/68719476736), by norm_num⟩
  | 7 => ⟨((-1971754411/68719476736), (-2077342421/137438953472)), (117/137438953472), by norm_num⟩
  | 8 => ⟨((1476712081/137438953472), (1555790433/274877906944)), (89/274877906944), by norm_num⟩
  | 9 => ⟨((-983074231/274877906944), (-2071436271/1099511627776)), (121/1099511627776), by norm_num⟩
  | 10 => ⟨((2356021761/2199023255552), (620546849/1099511627776)), (147/4398046511104), by norm_num⟩
  | 11 => ⟨((-1283274623/4398046511104), (-168999293/1099511627776)), (81/8796093022208), by norm_num⟩
  | 12 => ⟨((320362267/4398046511104), (675035515/17592186044416)), (41/17592186044416), by norm_num⟩
  | 13 => ⟨((-4724773329/281474976710656), (-1244446571/140737488355328)), (153/281474976710656), by norm_num⟩
  | 14 => ⟨((1011011139/281474976710656), (1065151073/562949953421312)), (133/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1615316639/2251799813685248), (-212727163/562949953421312)), (27/1125899906842624), by norm_num⟩
  | 16 => ⟨((4839056187/36028797018963968), (2549094511/36028797018963968)), (41/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027131871/5070602400912917605986812821504), (315777534469/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777984147540441/633825300114114700748351602688), (186696122009/158456325028528675187087900672)), (23069/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888859362789627/39614081257132168796771975168), (839945273229/39614081257132168796771975168)), (12977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944289775796699/1237940039285380274899124224), (892206757075/2475880078570760549798248448)), (13789/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442561526438295/38685626227668133590597632), (222985601085/38685626227668133590597632)), (27579/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548668203653191/9671406556917033397649408), (835915238873/9671406556917033397649408)), (25857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014438030609/604462909807314587353088), (731145192159/604462909807314587353088)), (11313/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886534501982037/75557863725914323419136), (1187584995743/75557863725914323419136)), (36771/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296596825717911/4722366482869645213696), (890228809793/4722366482869645213696)), (27581/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405038215328237/147573952589676412928), (1223317706391/590295810358705651712)), (4741/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227732104923735/9223372036854775808), (47750863445/2305843009213693952)), (5927/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820838647353421/9223372036854775808), (107343322535/576460752303423488)), (53353/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592089339480425/1152921504606846976), (1715572843359/1152921504606846976)), (13341/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192923762755677/144115188075855872), (1498968747461/144115188075855872)), (46707/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489156805711351/36028797018963968), (2244145295915/36028797018963968)), (35043/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486165501495533/9007199254740992), (2797658997795/9007199254740992)), (21913/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221789351226293/4503599627370496), (5572814277333/4503599627370496)), (10965/281474976710656), by norm_num⟩
  | 1 => ⟨((2206929472780751/2251799813685248), (4151593003817/1125899906842624)), (131753/1125899906842624), by norm_num⟩
  | 0 => ⟨((135164898330853/140737488355328), (16383568672185/2251799813685248)), (264205/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135164898330853/140737488355328), (16383568672185/2251799813685248)), (1007862095359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038444066807589/1125899906842624), (31469701779549/2251799813685248)), (1022665/2251799813685248), by norm_num⟩
  | 2 => ⟨((957561580566023/1125899906842624), (29025248957361/1125899906842624)), (1915041/2251799813685248), by norm_num⟩
  | 3 => ⟨((406822005194069/562949953421312), (98742217133225/2251799813685248)), (3356169/2251799813685248), by norm_num⟩
  | 4 => ⟨((1171647790839707/2251799813685248), (142714308891267/2251799813685248)), (1286271/562949953421312), by norm_num⟩
  | 5 => ⟨((1201164653801049/4503599627370496), (74256558561489/1125899906842624)), (3003155/1125899906842624), by norm_num⟩
  | 6 => ⟨((75193847909919/1125899906842624), (158440999799169/4503599627370496)), (31969447/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-346794327/134217728), (-6681445055/134217728)), (1/67108864), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-6790262791/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((308787300758825/4503599627370496), (-417443386480939/18014398509481984)), (848455/562949953421312), by norm_num⟩
  | 1 => ⟨((-1793117267/8589934592), (1212039715/17179869184)), (81/17179869184), by norm_num⟩
  | 2 => ⟨((5459185753/17179869184), (-922520527/8589934592)), (125/17179869184), by norm_num⟩
  | 3 => ⟨((-2770102253/8589934592), (936211481/8589934592)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((131775601/536870912), (-712579215/8589934592)), (25/4294967296), by norm_num⟩
  | 5 => ⟨((-5135280307/34359738368), (1735570727/34359738368)), (123/34359738368), by norm_num⟩
  | 6 => ⟨((651436505/8589934592), (-1761328007/68719476736)), (127/68719476736), by norm_num⟩
  | 7 => ⟨((-2266643493/68719476736), (1532115039/137438953472)), (113/137438953472), by norm_num⟩
  | 8 => ⟨((1725211743/137438953472), (-1166139653/274877906944)), (11/34359738368), by norm_num⟩
  | 9 => ⟨((-2334420383/549755813888), (1577928151/1099511627776)), (121/1099511627776), by norm_num⟩
  | 10 => ⟨((1421439047/1099511627776), (-240201883/549755813888)), (149/4398046511104), by norm_num⟩
  | 11 => ⟨((-3147347689/8796093022208), (2127418247/17592186044416)), (167/17592186044416), by norm_num⟩
  | 12 => ⟨((1597028443/17592186044416), (-1079495431/35184372088832)), (43/17592186044416), by norm_num⟩
  | 13 => ⟨((-5984232527/281474976710656), (2022491115/281474976710656)), (41/70368744177664), by norm_num⟩
  | 14 => ⟨((1301366443/281474976710656), (-439822827/281474976710656)), (145/1125899906842624), by norm_num⟩
  | 15 => ⟨((-4226175291/4503599627370496), (89270031/281474976710656)), (15/562949953421312), by norm_num⟩
  | 16 => ⟨((3216671375/18014398509481984), (-543569225/9007199254740992)), (93/18014398509481984), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (-106136061705/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777919496468783/633825300114114700748351602688), (-125492231969/158456325028528675187087900672)), (23063/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888786655719793/39614081257132168796771975168), (-564587290837/39614081257132168796771975168)), (25947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944251166459087/1237940039285380274899124224), (-149928352133/618970019642690137449562112)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885084461855391/77371252455336267181195264), (-599532838669/154742504910672534362390528)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193574485548731/1208925819614629174706176), (-280935128671/4835703278458516698824704)), (3231/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257951197552973/604462909807314587353088), (-30715298903/37778931862957161709568)), (11309/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886431809051585/75557863725914323419136), (-798238530659/75557863725914323419136)), (36757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296519869709953/4722366482869645213696), (-149591186303/1180591620717411303424)), (13785/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620047150204183/590295810358705651712), (-822241369167/590295810358705651712)), (37911/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113857803465191/4611686018427387904), (-128379634699/9223372036854775808)), (47393/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820690378188133/9223372036854775808), (-1154366313857/9223372036854775808)), (53323/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591941335884637/1152921504606846976), (-1153054773997/1152921504606846976)), (53331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149099319728389/18014398509481984), (-1007449447441/144115188075855872)), (23337/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488963593386679/36028797018963968), (-1508232210517/36028797018963968)), (17507/9007199254740992), by norm_num⟩
  | 3 => ⟨((742962512194709/4503599627370496), (-1880153059437/9007199254740992)), (87565/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221311499669391/4503599627370496), (-3744939316329/4503599627370496)), (21903/562949953421312), by norm_num⟩
  | 1 => ⟨((2206220409384927/2251799813685248), (-5579148344263/2251799813685248)), (8221/70368744177664), by norm_num⟩
  | 0 => ⟨((2161250847300655/2251799813685248), (-5503094401671/1125899906842624)), (527109/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161250847300655/2251799813685248), (-5503094401671/1125899906842624)), (2010761269576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074289224281245/2251799813685248), (-21127219864047/2251799813685248)), (254245/562949953421312), by norm_num⟩
  | 2 => ⟨((477643416657581/562949953421312), (-38923499537281/2251799813685248)), (946353/1125899906842624), by norm_num⟩
  | 3 => ⟨((1620382360203459/2251799813685248), (-66050465744839/2251799813685248)), (409653/281474976710656), by norm_num⟩
  | 4 => ⟨((1164080533847943/2251799813685248), (-11882385028823/281474976710656)), (4908801/2251799813685248), by norm_num⟩
  | 5 => ⟨((1195530128716473/4503599627370496), (-98282648563519/2251799813685248)), (343107/140737488355328), by norm_num⟩
  | 6 => ⟨((308787300758825/4503599627370496), (-417443386480939/18014398509481984)), (848455/562949953421312), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-6790262791/134217728)), (1/67108864), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile005Terms2
