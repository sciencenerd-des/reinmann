/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile061Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨61,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79951/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79951/2560))
  have he : value ((69/80), (79951/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2567700857/1073741824), (-23243914313/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((80470547648771/4503599627370496), (404170477744371/4503599627370496)), (7801745/18014398509481984), by norm_num⟩
  | 1 => ⟨((-6808829739/137438953472), (-68395905057/274877906944)), (83/68719476736), by norm_num⟩
  | 2 => ⟨((9439042273/137438953472), (2963026797/8589934592)), (231/137438953472), by norm_num⟩
  | 3 => ⟨((-8723527385/137438953472), (-2738418227/8589934592)), (429/274877906944), by norm_num⟩
  | 4 => ⟨((12093376823/274877906944), (7592507493/34359738368)), (299/274877906944), by norm_num⟩
  | 5 => ⟨((-13411984077/549755813888), (-67362882075/549755813888)), (167/274877906944), by norm_num⟩
  | 6 => ⟨((12395305265/1099511627776), (62256522379/1099511627776)), (311/1099511627776), by norm_num⟩
  | 7 => ⟨((-9819166739/2199023255552), (-98635275333/4398046511104)), (495/4398046511104), by norm_num⟩
  | 8 => ⟨((13612255481/8796093022208), (68368763001/8796093022208)), (345/8796093022208), by norm_num⟩
  | 9 => ⟨((-8386930229/17592186044416), (-10531025625/4398046511104)), (427/35184372088832), by norm_num⟩
  | 10 => ⟨((9301403267/70368744177664), (93434249221/140737488355328)), (119/35184372088832), by norm_num⟩
  | 11 => ⟨((-9377805745/281474976710656), (-94201725695/562949953421312)), (241/281474976710656), by norm_num⟩
  | 12 => ⟨((541683301/70368744177664), (87060880759/2251799813685248)), (447/2251799813685248), by norm_num⟩
  | 13 => ⟨((-7393796979/4503599627370496), (-37136002483/4503599627370496)), (383/9007199254740992), by norm_num⟩
  | 14 => ⟨((5857130891/18014398509481984), (14708980239/9007199254740992)), (305/36028797018963968), by norm_num⟩
  | 15 => ⟨((-17322042723/288230376151711744), (-87001499149/288230376151711744)), (453/288230376151711744), by norm_num⟩
  | 16 => ⟨((12006725075/1152921504606846976), (60304843839/1152921504606846976)), (79/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (1790134657725/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778278535084197/633825300114114700748351602688), (2117423866149/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889190360191753/39614081257132168796771975168), (2381605348619/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888930992114931/2475880078570760549798248448), (632459583481/618970019642690137449562112)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770597271750459/154742504910672534362390528), (632286019325/38685626227668133590597632)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548997130267953/9671406556917033397649408), (2370335165103/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314575489376773/151115727451828646838272), (2073306132437/604462909807314587353088)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887001175339157/75557863725914323419136), (210483806721/4722366482869645213696)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296946353584077/4722366482869645213696), (315574673963/590295810358705651712)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810316343768855/295147905179352825856), (867339754957/147573952589676412928)), (2377/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911227730824087/36893488147419103232), (4333757065739/73786976294838206464)), (743/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821510503889743/9223372036854775808), (4871434904723/9223372036854775808)), (3345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592759207453859/1152921504606846976), (2433193621091/576460752303423488)), (6695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298376916163477/36028797018963968), (1063104127255/36028797018963968)), (5863/144115188075855872), by norm_num⟩
  | 4 => ⟨((745014102384121/18014398509481984), (3183647911405/18014398509481984)), (4401/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487246981702659/9007199254740992), (7939329446847/9007199254740992)), (5509/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111964553799381/2251799813685248), (7909714467937/2251799813685248)), (22083/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210081452291709/2251799813685248), (5895390286267/562949953421312)), (33243/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168713832542431/2251799813685248), (23287870563361/1125899906842624)), (66965/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168713832542431/2251799813685248), (23287870563361/1125899906842624)), (255451210982512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521932540276035/562949953421312), (11214302158273/281474976710656)), (8235/140737488355328), by norm_num⟩
  | 2 => ⟨((1932040549287753/2251799813685248), (166355369313193/2251799813685248)), (254819/2251799813685248), by norm_num⟩
  | 3 => ⟨((1645397851387639/2251799813685248), (285465268405741/2251799813685248)), (59365/281474976710656), by norm_num⟩
  | 4 => ⟨((1166108840549061/2251799813685248), (417180902517169/2251799813685248)), (407233/1125899906842624), by norm_num⟩
  | 5 => ⟨((1053175255966497/4503599627370496), (864159123874065/4503599627370496)), (572669/1125899906842624), by norm_num⟩
  | 6 => ⟨((80470547648771/4503599627370496), (404170477744371/4503599627370496)), (7801745/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-23243914313/268435456)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-11876079505/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1358351157036019/18014398509481984), (-194026341686165/4503599627370496)), (2351021/9007199254740992), by norm_num⟩
  | 1 => ⟨((-58723428711/274877906944), (16776062633/137438953472)), (205/274877906944), by norm_num⟩
  | 2 => ⟨((20797000229/68719476736), (-1485317641/8589934592)), (293/274877906944), by norm_num⟩
  | 3 => ⟨((-39281559043/137438953472), (11221924695/68719476736)), (279/274877906944), by norm_num⟩
  | 4 => ⟨((13911629657/68719476736), (-3974263349/34359738368)), (25/34359738368), by norm_num⟩
  | 5 => ⟨((-63063383651/549755813888), (18015897525/274877906944)), (229/549755813888), by norm_num⟩
  | 6 => ⟨((59557340027/1099511627776), (-34028587515/1099511627776)), (109/549755813888), by norm_num⟩
  | 7 => ⟨((-6026380375/274877906944), (3443223151/274877906944)), (89/1099511627776), by norm_num⟩
  | 8 => ⟨((68296085179/8796093022208), (-4877692889/1099511627776)), (127/4398046511104), by norm_num⟩
  | 9 => ⟨((-21499708875/8796093022208), (49136158511/35184372088832)), (161/17592186044416), by norm_num⟩
  | 10 => ⟨((24365304831/35184372088832), (-13921321997/35184372088832)), (23/8796093022208), by norm_num⟩
  | 11 => ⟨((-25102584283/140737488355328), (28685145635/281474976710656)), (3/4398046511104), by norm_num⟩
  | 12 => ⟨((47413984507/1125899906842624), (-13545189565/562949953421312)), (183/1125899906842624), by norm_num⟩
  | 13 => ⟨((-82667036061/9007199254740992), (47232506859/9007199254740992)), (321/9007199254740992), by norm_num⟩
  | 14 => ⟨((66918099909/36028797018963968), (-19117109815/18014398509481984)), (131/18014398509481984), by norm_num⟩
  | 15 => ⟨((-50558200965/144115188075855872), (7221713417/36028797018963968)), (25/18014398509481984), by norm_num⟩
  | 16 => ⟨((17905271203/288230376151711744), (-5115163705/144115188075855872)), (143/576460752303423488), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-169044221295/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889100016737591/316912650057057350374175801344), (-799732829891/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236137772399491/4951760157141521099596496896), (-224877277643/9903520314283042199192993792)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888837474670103/2475880078570760549798248448), (-119436287105/309485009821345068724781056)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885251975421611/77371252455336267181195264), (-955222518953/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548909850596391/9671406556917033397649408), (-895236702169/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112898156667/302231454903657293676544), (-48940488927/37778931862957161709568)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943438902016075/37778931862957161709568), (-1271919915583/75557863725914323419136)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296854166567813/4722366482869645213696), (-953473989765/4722366482869645213696)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620506484632837/590295810358705651712), (-1310270040699/590295810358705651712)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822298538268041/73786976294838206464), (-204587915921/9223372036854775808)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821335104875935/9223372036854775808), (-1839733016305/9223372036854775808)), (6671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796292615235163/576460752303423488), (-1837787226189/1152921504606846976)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193357030862709/144115188075855872), (-802938773593/72057594037927936)), (365/9007199254740992), by norm_num⟩
  | 4 => ⟨((744902718475443/18014398509481984), (-2404450605499/36028797018963968)), (8763/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486974071144007/9007199254740992), (-2997938611273/9007199254740992)), (685/562949953421312), by norm_num⟩
  | 2 => ⟨((2223399851123917/4503599627370496), (-5973064584211/4503599627370496)), (21937/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209328689762393/2251799813685248), (-4451389629413/1125899906842624)), (16475/1125899906842624), by norm_num⟩
  | 0 => ⟨((135460691760769/140737488355328), (-17579567398967/2251799813685248)), (33043/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((135460691760769/140737488355328), (-17579567398967/2251799813685248)), (126049046043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2085970643310917/2251799813685248), (-16920440946813/1125899906842624)), (128249/2251799813685248), by norm_num⟩
  | 2 => ⟨((1931845048138757/2251799813685248), (-62697479362811/2251799813685248)), (241465/2251799813685248), by norm_num⟩
  | 3 => ⟨((3233606365397/4398046511104), (-107577782271509/2251799813685248)), (427759/2251799813685248), by norm_num⟩
  | 4 => ⟨((1212123631741843/2251799813685248), (-158190324113295/2251799813685248)), (669881/2251799813685248), by norm_num⟩
  | 5 => ⟨((160340576369929/562949953421312), (-340609727392807/4503599627370496)), (1630603/4503599627370496), by norm_num⟩
  | 6 => ⟨((1358351157036019/18014398509481984), (-194026341686165/4503599627370496)), (2351021/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-11876079505/134217728)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-48462689713/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-996859867177865/18014398509481984), (-1106312721402895/18014398509481984)), (8512473/18014398509481984), by norm_num⟩
  | 1 => ⟨((43965081889/274877906944), (6099042979/34359738368)), (377/274877906944), by norm_num⟩
  | 2 => ⟨((-63537715513/274877906944), (-70514006307/274877906944)), (547/274877906944), by norm_num⟩
  | 3 => ⟨((61215872827/274877906944), (67937230789/274877906944)), (529/274877906944), by norm_num⟩
  | 4 => ⟨((-44234157489/274877906944), (-1534092603/8589934592)), (3/2147483648), by norm_num⟩
  | 5 => ⟨((6392657977/68719476736), (3547278347/34359738368)), (223/274877906944), by norm_num⟩
  | 6 => ⟨((-49272421533/1099511627776), (-54682416809/1099511627776)), (27/68719476736), by norm_num⟩
  | 7 => ⟨((20345087949/1099511627776), (22578930457/1099511627776)), (179/1099511627776), by norm_num⟩
  | 8 => ⟨((-14701216905/2199023255552), (-65261502917/8796093022208)), (519/8796093022208), by norm_num⟩
  | 9 => ⟨((37770650799/17592186044416), (41917778869/17592186044416)), (335/17592186044416), by norm_num⟩
  | 10 => ⟨((-43668488939/70368744177664), (-48463185679/70368744177664)), (389/70368744177664), by norm_num⟩
  | 11 => ⟨((11474378831/70368744177664), (50936953885/281474976710656)), (411/281474976710656), by norm_num⟩
  | 12 => ⟨((-44220294017/1125899906842624), (-3067223603/70368744177664)), (199/562949953421312), by norm_num⟩
  | 13 => ⟨((39327104293/4503599627370496), (43645127273/4503599627370496)), (89/1125899906842624), by norm_num⟩
  | 14 => ⟨((-64954258039/36028797018963968), (-18021520463/9007199254740992)), (591/36028797018963968), by norm_num⟩
  | 15 => ⟨((25032260399/72057594037927936), (13890371675/36028797018963968)), (229/72057594037927936), by norm_num⟩
  | 16 => ⟨((-36176269247/576460752303423488), (-10037084499/144115188075855872)), (333/576460752303423488), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-3001477259971/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222264709187055/79228162514264337593543950336), (-3549639950019/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472252297156779/9903520314283042199192993792), (-3992469720781/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944369112434903/1237940039285380274899124224), (-2120459584805/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885202099171833/77371252455336267181195264), (-4239704593873/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548815798929691/9671406556917033397649408), (-3973432923807/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629071483939429/302231454903657293676544), (-3475464073051/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235842776128755/9444732965739290427392), (-88206432969/1180591620717411303424)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648375798685895/2361183241434822606848), (-528974299345/590295810358705651712)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810182017665513/295147905179352825856), (-5815282996583/590295810358705651712)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822118354937229/73786976294838206464), (-7263955072765/73786976294838206464)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821129486614363/9223372036854775808), (-2041218633541/2305843009213693952)), (839/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592375980172411/1152921504606846976), (-2039009408321/288230376151711744)), (6719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193169861769243/144115188075855872), (-890825087243/18014398509481984)), (5887/144115188075855872), by norm_num⟩
  | 4 => ⟨((744758280245147/18014398509481984), (-10670059783201/36028797018963968)), (8845/36028797018963968), by norm_num⟩
  | 3 => ⟨((743299411010901/4503599627370496), (-6651452347373/4503599627370496)), (5541/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222607137110815/4503599627370496), (-26502007896573/4503599627370496)), (22243/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208034933286409/2251799813685248), (-39494237797569/2251799813685248)), (33563/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082184956294643/1125899906842624), (-77957753887299/2251799813685248)), (8491/281474976710656), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082184956294643/1125899906842624), (-77957753887299/2251799813685248)), (32390595556163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1038817855543295/1125899906842624), (-9366364182401/140737488355328)), (135285/2251799813685248), by norm_num⟩
  | 2 => ⟨((1906968618932117/2251799813685248), (-34567713506559/281474976710656)), (267651/2251799813685248), by norm_num⟩
  | 3 => ⟨((1580981566684197/2251799813685248), (-468386537628219/2251799813685248)), (519069/2251799813685248), by norm_num⟩
  | 4 => ⟨((506287626392569/1125899906842624), (-164426357434799/562949953421312)), (944813/2251799813685248), by norm_num⟩
  | 5 => ⟨((131612989450073/1125899906842624), (-147876431494681/562949953421312)), (2803275/4503599627370496), by norm_num⟩
  | 6 => ⟨((-996859867177865/18014398509481984), (-1106312721402895/18014398509481984)), (8512473/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-48462689713/536870912)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2726851779/1073741824), (-98738463131/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-936800627972531/18014398509481984), (267229100127595/4503599627370496)), (8126819/18014398509481984), by norm_num⟩
  | 1 => ⟨((42089115673/274877906944), (-24012444421/137438953472)), (367/274877906944), by norm_num⟩
  | 2 => ⟨((-61964416393/274877906944), (35351588669/137438953472)), (543/274877906944), by norm_num⟩
  | 3 => ⟨((15204203579/68719476736), (-69393730435/274877906944)), (535/274877906944), by norm_num⟩
  | 4 => ⟨((-44767849665/274877906944), (51081401201/274877906944)), (99/68719476736), by norm_num⟩
  | 5 => ⟨((52726480627/549755813888), (-60162427523/549755813888)), (117/137438953472), by norm_num⟩
  | 6 => ⟨((-6468746033/137438953472), (29524099447/549755813888)), (231/549755813888), by norm_num⟩
  | 7 => ⟨((43535606779/2199023255552), (-49675376707/2199023255552)), (391/2199023255552), by norm_num⟩
  | 8 => ⟨((-64093968791/8796093022208), (73133057741/8796093022208)), (289/4398046511104), by norm_num⟩
  | 9 => ⟨((2621121945/1099511627776), (-47852405751/17592186044416)), (95/4398046511104), by norm_num⟩
  | 10 => ⟨((-24696747597/35184372088832), (7044924437/8796093022208)), (225/35184372088832), by norm_num⟩
  | 11 => ⟨((13221466597/70368744177664), (-60344291251/281474976710656)), (121/70368744177664), by norm_num⟩
  | 12 => ⟨((-51906402147/1125899906842624), (59226694443/1125899906842624)), (477/1125899906842624), by norm_num⟩
  | 13 => ⟨((47026225769/4503599627370496), (-26829136573/2251799813685248)), (217/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4945209007/2251799813685248), (45141003145/18014398509481984)), (367/18014398509481984), by norm_num⟩
  | 15 => ⟨((15531590571/36028797018963968), (-35443981125/72057594037927936)), (579/144115188075855872), by norm_num⟩
  | 16 => ⟨((-22865910343/288230376151711744), (52181319801/576460752303423488)), (107/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (2983527660731/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889022959142383/316912650057057350374175801344), (1764070229167/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888928486929123/39614081257132168796771975168), (1984136613163/19807040628566084398385987584)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944326253674791/1237940039285380274899124224), (2107598474117/1237940039285380274899124224)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885159256179317/77371252455336267181195264), (2106983634601/77371252455336267181195264)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96795968863597/604462909807314587353088), (3949288152597/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258072741396365/604462909807314587353088), (1727160694537/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471657038443371/18889465931478580854784), (1402706218545/18889465931478580854784)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324166527710559/1180591620717411303424), (2102989041545/2361183241434822606848)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620246580553553/590295810358705651712), (1444935774473/147573952589676412928)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910985835104519/36893488147419103232), (7219466634297/73786976294838206464)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820964650099385/9223372036854775808), (1014342233285/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796105686636317/576460752303423488), (8105792337785/1152921504606846976)), (6719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18641032638377/2251799813685248), (7082514325935/144115188075855872)), (2943/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489301416885897/36028797018963968), (10603687915045/36028797018963968)), (2211/9007199254740992), by norm_num⟩
  | 3 => ⟨((743165397008139/4503599627370496), (6609759217839/4503599627370496)), (11081/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222073781231363/4503599627370496), (26333981550803/4503599627370496)), (695/140737488355328), by norm_num⟩
  | 1 => ⟨((2207241634456715/2251799813685248), (39239100122139/2251799813685248)), (33559/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162810162451617/2251799813685248), (604963306657/17592186044416)), (67915/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162810162451617/2251799813685248), (604963306657/17592186044416)), (259075173384856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((16208394253891/17592186044416), (148750221745569/2251799813685248)), (67567/1125899906842624), by norm_num⟩
  | 2 => ⟨((1901655502032765/2251799813685248), (274099220337791/2251799813685248)), (16679/140737488355328), by norm_num⟩
  | 3 => ⟨((1572592396668827/2251799813685248), (462956153820083/2251799813685248)), (515705/2251799813685248), by norm_num⟩
  | 4 => ⟨((1003072489824995/2251799813685248), (646630595725123/2251799813685248)), (932359/2251799813685248), by norm_num⟩
  | 5 => ⟨((522269598693625/4503599627370496), (1152175886522533/4503599627370496)), (2732243/4503599627370496), by norm_num⟩
  | 6 => ⟨((-936800627972531/18014398509481984), (267229100127595/4503599627370496)), (8126819/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-98738463131/1073741824)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1387177309/536870912), (-100458526305/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1050064750190411/18014398509481984), (431993691983145/9007199254740992)), (4590755/18014398509481984), by norm_num⟩
  | 1 => ⟨((-11999942251/68719476736), (-4936742573/34359738368)), (53/68719476736), by norm_num⟩
  | 2 => ⟨((17974307141/68719476736), (59156636209/274877906944)), (5/4294967296), by norm_num⟩
  | 3 => ⟨((-71794949329/274877906944), (-59072481429/274877906944)), (161/137438953472), by norm_num⟩
  | 4 => ⟨((3360600731/17179869184), (22120667387/137438953472)), (243/274877906944), by norm_num⟩
  | 5 => ⟨((-32215872219/274877906944), (-53014077763/549755813888)), (293/549755813888), by norm_num⟩
  | 6 => ⟨((32170042709/549755813888), (13234665309/274877906944)), (295/1099511627776), by norm_num⟩
  | 7 => ⟨((-27535095767/1099511627776), (-45311444567/2199023255552)), (255/2199023255552), by norm_num⟩
  | 8 => ⟨((20621943761/2199023255552), (33935239213/4398046511104)), (193/4398046511104), by norm_num⟩
  | 9 => ⟨((-13728404993/4398046511104), (-45182618365/17592186044416)), (259/17592186044416), by norm_num⟩
  | 10 => ⟨((65802601443/70368744177664), (3383875701/4398046511104)), (39/8796093022208), by norm_num⟩
  | 11 => ⟨((-17920634257/70368744177664), (-14744997305/70368744177664)), (171/140737488355328), by norm_num⟩
  | 12 => ⟨((8947570401/140737488355328), (58896085733/1125899906842624)), (43/140737488355328), by norm_num⟩
  | 13 => ⟨((-65980370265/4503599627370496), (-54288278405/4503599627370496)), (319/4503599627370496), by norm_num⟩
  | 14 => ⟨((56474149893/18014398509481984), (46466613627/18014398509481984)), (275/18014398509481984), by norm_num⟩
  | 15 => ⟨((-22557524461/36028797018963968), (-37120409089/72057594037927936)), (111/36028797018963968), by norm_num⟩
  | 16 => ⟨((67576304039/576460752303423488), (27800701879/288230376151711744)), (335/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (896830206925/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777983843578941/633825300114114700748351602688), (530229998833/316912650057057350374175801344)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944429502068213/19807040628566084398385987584), (1192751354829/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888579148241151/2475880078570760549798248448), (1266964446891/2475880078570760549798248448)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770245677361023/154742504910672534362390528), (633294513417/77371252455336267181195264)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548667775451681/9671406556917033397649408), (1187028482623/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314503509198531/151115727451828646838272), (259562841333/151115727451828646838272)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471633450055691/18889465931478580854784), (26350180343/1180591620717411303424)), (4599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296596255917497/4722366482869645213696), (1264155462975/4722366482869645213696)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810076003637499/295147905179352825856), (1737153010577/590295810358705651712)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910927833081747/36893488147419103232), (2169851340529/73786976294838206464)), (1483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910418591216173/4611686018427387904), (2438898568967/9223372036854775808)), (6675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592087693657747/1152921504606846976), (1218085630767/576460752303423488)), (1669/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192922119695723/144115188075855872), (1064292827821/72057594037927936)), (1461/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489153936561213/36028797018963968), (3186760129693/36028797018963968)), (8771/36028797018963968), by norm_num⟩
  | 3 => ⟨((743080605075937/4503599627370496), (993191400105/2251799813685248)), (10971/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221778666077869/4503599627370496), (7913567553095/4503599627370496)), (10983/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103454115810939/1125899906842624), (11790756477623/2251799813685248)), (2063/140737488355328), by norm_num⟩
  | 0 => ⟨((2162575292075821/2251799813685248), (23265012262189/2251799813685248)), (66261/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162575292075821/2251799813685248), (23265012262189/2251799813685248)), (252765664107512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519161450840551/562949953421312), (44686335243727/2251799813685248)), (128641/2251799813685248), by norm_num⟩
  | 2 => ⟨((1914229185857303/2251799813685248), (5151306634117/140737488355328)), (30297/281474976710656), by norm_num⟩
  | 3 => ⟨((1624247478834387/2251799813685248), (17516266667043/281474976710656)), (214913/1125899906842624), by norm_num⟩
  | 4 => ⟨((1162866877560287/2251799813685248), (101077375704987/1125899906842624)), (336787/1125899906842624), by norm_num⟩
  | 5 => ⟨((1164750812607081/4503599627370496), (104396076031007/1125899906842624)), (408315/1125899906842624), by norm_num⟩
  | 6 => ⟨((1050064750190411/18014398509481984), (431993691983145/9007199254740992)), (4590755/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-100458526305/1073741824)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2819539303/1073741824), (-102094649811/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((874807267664657/18014398509481984), (-7552569596659/140737488355328)), (2406433/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10159951611/68719476736), (5613761621/34359738368)), (225/274877906944), by norm_num⟩
  | 2 => ⟨((15466100323/68719476736), (-68364892861/274877906944)), (43/34359738368), by norm_num⟩
  | 3 => ⟨((-62782519277/274877906944), (69379483423/274877906944)), (351/274877906944), by norm_num⟩
  | 4 => ⟨((47785697159/274877906944), (-13201712125/68719476736)), (269/274877906944), by norm_num⟩
  | 5 => ⟨((-58193850881/549755813888), (32154327025/274877906944)), (165/274877906944), by norm_num⟩
  | 6 => ⟨((59057494915/1099511627776), (-16315761683/274877906944)), (337/1099511627776), by norm_num⟩
  | 7 => ⟨((-12842990599/549755813888), (7096243219/274877906944)), (295/2199023255552), by norm_num⟩
  | 8 => ⟨((19550386523/2199023255552), (-2700583963/274877906944)), (113/2199023255552), by norm_num⟩
  | 9 => ⟨((-52908080387/17592186044416), (58467473567/17592186044416)), (77/4398046511104), by norm_num⟩
  | 10 => ⟨((32215967575/35184372088832), (-71202214061/70368744177664)), (377/70368744177664), by norm_num⟩
  | 11 => ⟨((-17833133843/70368744177664), (39413952423/140737488355328)), (211/140737488355328), by norm_num⟩
  | 12 => ⟨((2262224005/35184372088832), (-2499930469/35184372088832)), (27/70368744177664), by norm_num⟩
  | 13 => ⟨((-33907159347/2251799813685248), (9367500807/562949953421312)), (51/562949953421312), by norm_num⟩
  | 14 => ⟨((58989204247/18014398509481984), (-65187580325/18014398509481984)), (357/18014398509481984), by norm_num⟩
  | 15 => ⟨((-47891721577/72057594037927936), (26462006795/36028797018963968)), (73/18014398509481984), by norm_num⟩
  | 16 => ⟨((36451855231/288230376151711744), (-40282086717/288230376151711744)), (7/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-544017850655/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222239843010949/79228162514264337593543950336), (-1286462173423/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944392884027585/19807040628566084398385987584), (-361735480453/9903520314283042199192993792)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944250667314011/1237940039285380274899124224), (-48030130045/77371252455336267181195264)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110635491465841/9671406556917033397649408), (-768250650605/77371252455336267181195264)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774297412305701/4835703278458516698824704), (-179997296451/1208925819614629174706176)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314487551129809/151115727451828646838272), (-1259489691523/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943215036129541/37778931862957161709568), (-2045749860301/75557863725914323419136)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296518459518431/4722366482869645213696), (-1533507073487/4722366482869645213696)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620045036582339/590295810358705651712), (-1053632215993/295147905179352825856)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821721951917023/73786976294838206464), (-2632120341905/73786976294838206464)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910343376416245/4611686018427387904), (-2958442536395/9223372036854775808)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795968631462105/576460752303423488), (-2955080108693/1152921504606846976)), (835/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192790491812471/144115188075855872), (-161369834563/9007199254740992)), (731/18014398509481984), by norm_num⟩
  | 4 => ⟨((186119561682673/4503599627370496), (-3865333000697/36028797018963968)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((371478601408221/2251799813685248), (-4818493927577/9007199254740992)), (10981/9007199254740992), by norm_num⟩
  | 2 => ⟨((555321265356625/1125899906842624), (-9597582556835/4503599627370496)), (21991/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206167857600313/2251799813685248), (-3574562593925/562949953421312)), (33059/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161094806765995/2251799813685248), (-1762896071157/140737488355328)), (66413/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161094806765995/2251799813685248), (-1762896071157/140737488355328)), (253345498091887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2073690182403079/2251799813685248), (-54140308865351/2251799813685248)), (129141/2251799813685248), by norm_num⟩
  | 2 => ⟨((1908366708902989/2251799813685248), (-49857996383173/1125899906842624)), (7627/70368744177664), by norm_num⟩
  | 3 => ⟨((201612072394433/281474976710656), (-84507814497539/1125899906842624)), (217649/1125899906842624), by norm_num⟩
  | 4 => ⟨((285645850551441/562949953421312), (-242121638143163/2251799813685248)), (21529/70368744177664), by norm_num⟩
  | 5 => ⟨((553723264280035/2251799813685248), (-245709377339807/2251799813685248)), (847289/2251799813685248), by norm_num⟩
  | 6 => ⟨((874807267664657/18014398509481984), (-7552569596659/140737488355328)), (2406433/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-102094649811/1073741824)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨61,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile061Terms2
