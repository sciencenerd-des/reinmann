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
namespace Reinmann.XiBand97.Tile055Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨55,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77803/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77803/2560))
  have he : value ((69/80), (77803/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-22619432719/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-698729881223339/9007199254740992), (-218571321784801/4503599627370496)), (18699893/9007199254740992), by norm_num⟩
  | 1 => ⟨((7390177111/34359738368), (2311738517/17179869184)), (397/68719476736), by norm_num⟩
  | 2 => ⟨((-10244960857/34359738368), (-6409500141/34359738368)), (553/68719476736), by norm_num⟩
  | 3 => ⟨((9468354311/34359738368), (11847271871/68719476736)), (513/68719476736), by norm_num⟩
  | 4 => ⟨((-13125926191/68719476736), (-8211903095/68719476736)), (357/68719476736), by norm_num⟩
  | 5 => ⟨((14557117971/137438953472), (2276822991/34359738368)), (199/68719476736), by norm_num⟩
  | 6 => ⟨((-13453633705/274877906944), (-8416924997/274877906944)), (185/137438953472), by norm_num⟩
  | 7 => ⟨((10657540881/549755813888), (3333810189/274877906944)), (295/549755813888), by norm_num⟩
  | 8 => ⟨((-14774488827/2199023255552), (-2310821133/549755813888)), (411/2199023255552), by norm_num⟩
  | 9 => ⟨((4551509011/2199023255552), (11390145089/8796093022208)), (127/2199023255552), by norm_num⟩
  | 10 => ⟨((-20191140085/35184372088832), (-1579009391/4398046511104)), (283/17592186044416), by norm_num⟩
  | 11 => ⟨((10178495871/70368744177664), (6367918007/70368744177664)), (573/140737488355328), by norm_num⟩
  | 12 => ⟨((-18813855241/562949953421312), (-11770411767/562949953421312)), (133/140737488355328), by norm_num⟩
  | 13 => ⟨((16050179343/2251799813685248), (1255173497/281474976710656)), (57/281474976710656), by norm_num⟩
  | 14 => ⟨((-6357220891/4503599627370496), (-3977234151/4503599627370496)), (363/9007199254740992), by norm_num⟩
  | 15 => ⟨((18801022877/72057594037927936), (11762383523/72057594037927936)), (539/72057594037927936), by norm_num⟩
  | 16 => ⟨((-13031875999/288230376151711744), (-127391609/4503599627370496)), (375/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-3364052256153/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778272453354163/633825300114114700748351602688), (-994774960563/158456325028528675187087900672)), (11575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889183180745439/39614081257132168796771975168), (-4475538951353/39614081257132168796771975168)), (13025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236115364718921/309485009821345068724781056), (-594262278605/309485009821345068724781056)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442647173970729/38685626227668133590597632), (-4752791319077/154742504910672534362390528)), (13847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548988557935787/9671406556917033397649408), (-4454353583221/9671406556917033397649408)), (6493/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629146962350327/302231454903657293676544), (-3896171458795/604462909807314587353088)), (11367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886987125434743/75557863725914323419136), (-6328677006171/75557863725914323419136)), (18479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648467472535569/2361183241434822606848), (-1186058022505/1180591620717411303424)), (13867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405153896767983/147573952589676412928), (-1629905642861/147573952589676412928)), (19077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911215984244407/36893488147419103232), (-8143985840893/73786976294838206464)), (2983/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821481167390601/9223372036854775808), (-2288591824475/2305843009213693952)), (26871/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592726245038591/1152921504606846976), (-571553269903/72057594037927936)), (26901/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74592172101179/9007199254740992), (-7991049661085/144115188075855872)), (23573/144115188075855872), by norm_num⟩
  | 4 => ⟨((93123170369859/2251799813685248), (-11965202849165/36028797018963968)), (17713/18014398509481984), by norm_num⟩
  | 3 => ⟨((92947562124183/562949953421312), (-3729787384811/2251799813685248)), (44401/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111857471821369/2251799813685248), (-14863211256127/2251799813685248)), (11145/562949953421312), by norm_num⟩
  | 1 => ⟨((1104827766938409/1125899906842624), (-22155296006143/1125899906842624)), (67317/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083724039654645/1125899906842624), (-43754459080769/1125899906842624)), (136431/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083724039654645/1125899906842624), (-43754459080769/1125899906842624)), (520442966941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082855384052941/2251799813685248), (-168461721542865/2251799813685248)), (273245/1125899906842624), by norm_num⟩
  | 2 => ⟨((1913983282643423/2251799813685248), (-77911322665077/562949953421312)), (1092747/2251799813685248), by norm_num⟩
  | 3 => ⟨((791857517123461/1125899906842624), (-529784106751645/2251799813685248)), (1080047/1125899906842624), by norm_num⟩
  | 4 => ⟨((989200770155337/2251799813685248), (-186301430897297/562949953421312)), (4054853/2251799813685248), by norm_num⟩
  | 5 => ⟨((375865199591831/4503599627370496), (-654727894743159/2251799813685248)), (6246349/2251799813685248), by norm_num⟩
  | 6 => ⟨((-698729881223339/9007199254740992), (-218571321784801/4503599627370496)), (18699893/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-22619432719/268435456)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-11557011341/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-443384787684583/18014398509481984), (375072271049263/4503599627370496)), (16978947/9007199254740992), by norm_num⟩
  | 1 => ⟨((599004601/8589934592), (-8107450587/34359738368)), (369/68719476736), by norm_num⟩
  | 2 => ⟨((-6788431315/68719476736), (11485068595/34359738368)), (525/68719476736), by norm_num⟩
  | 3 => ⟨((6411024729/68719476736), (-10846549867/34359738368)), (249/34359738368), by norm_num⟩
  | 4 => ⟨((-4540950203/68719476736), (7682647455/34359738368)), (177/34359738368), by norm_num⟩
  | 5 => ⟨((1286548071/34359738368), (-8706631715/68719476736)), (403/137438953472), by norm_num⟩
  | 6 => ⟨((-4860086883/274877906944), (8222581719/137438953472)), (191/137438953472), by norm_num⟩
  | 7 => ⟨((491773679/68719476736), (-13312187571/549755813888)), (311/549755813888), by norm_num⟩
  | 8 => ⟨((-2786599499/1099511627776), (18858133733/2199023255552)), (443/2199023255552), by norm_num⟩
  | 9 => ⟨((7017805231/8796093022208), (-23746273839/8796093022208)), (35/549755813888), by norm_num⟩
  | 10 => ⟨((-3976587885/17592186044416), (13455651983/17592186044416)), (319/17592186044416), by norm_num⟩
  | 11 => ⟨((256057315/4398046511104), (-6931405955/35184372088832)), (165/35184372088832), by norm_num⟩
  | 12 => ⟨((-967286669/70368744177664), (6546050615/140737488355328)), (313/281474976710656), by norm_num⟩
  | 13 => ⟨((6745918765/2251799813685248), (-2853285839/281474976710656)), (137/562949953421312), by norm_num⟩
  | 14 => ⟨((-5460750589/9007199254740992), (18477640031/9007199254740992)), (223/4503599627370496), by norm_num⟩
  | 15 => ⟨((4125725717/36028797018963968), (-3490073087/9007199254740992)), (339/36028797018963968), by norm_num⟩
  | 16 => ⟨((-2922265289/144115188075855872), (4944060821/72057594037927936)), (241/144115188075855872), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (151277977275/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778195984104519/633825300114114700748351602688), (2862729383817/633825300114114700748351602688)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889097399558199/39614081257132168796771975168), (3219881927029/39614081257132168796771975168)), (13009/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944416049632771/1237940039285380274899124224), (3420271276005/2475880078570760549798248448)), (13825/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770498241612353/154742504910672534362390528), (854827914599/38685626227668133590597632)), (13827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548904143767733/9671406556917033397649408), (3204585394461/9671406556917033397649408)), (6483/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258220448712677/604462909807314587353088), (1401496640863/302231454903657293676544)), (2837/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471717112707713/18889465931478580854784), (2276477155069/37778931862957161709568)), (18447/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296846571870143/4722366482869645213696), (3413045418185/4722366482869645213696)), (865/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101280943808941/36893488147419103232), (1172556142465/147573952589676412928)), (19039/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911141449632029/36893488147419103232), (5858713807557/73786976294838206464)), (11905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113832223528581/576460752303423488), (6585464962815/9223372036854775808)), (6701/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398140822233207/288230376151711744), (3289242878237/576460752303423488)), (13413/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193335124198599/144115188075855872), (718541439077/18014398509481984)), (23497/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489767178634453/36028797018963968), (8606830412603/36028797018963968)), (17647/18014398509481984), by norm_num⟩
  | 3 => ⟨((185864605007859/1125899906842624), (5365583204533/4503599627370496)), (44203/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223257319459555/4503599627370496), (2672549920219/562949953421312)), (88661/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104522629602359/1125899906842624), (15933199628545/1125899906842624)), (33409/562949953421312), by norm_num⟩
  | 0 => ⟨((2166528903042185/2251799813685248), (62919795161101/2251799813685248)), (67465/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166528903042185/2251799813685248), (62919795161101/2251799813685248)), (257358553172874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2082728916927427/2251799813685248), (118236631241/2199023255552)), (133591/562949953421312), by norm_num⟩
  | 2 => ⟨((479960599349859/562949953421312), (223967482202821/2251799813685248)), (522975/1125899906842624), by norm_num⟩
  | 3 => ⟨((1614545562919353/2251799813685248), (381900971266251/2251799813685248)), (1991579/2251799813685248), by norm_num⟩
  | 4 => ⟨((273215785871857/562949953421312), (136911930377907/562949953421312)), (1765735/1125899906842624), by norm_num⟩
  | 5 => ⟨((794415043540249/4503599627370496), (531578346190043/2251799813685248)), (5145587/2251799813685248), by norm_num⟩
  | 6 => ⟨((-443384787684583/18014398509481984), (375072271049263/4503599627370496)), (16978947/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-11557011341/134217728)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-23580334503/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1478291343239115/18014398509481984), (89877884977527/9007199254740992)), (3240469/4503599627370496), by norm_num⟩
  | 1 => ⟨((-8149741265/34359738368), (-1981967929/68719476736)), (145/68719476736), by norm_num⟩
  | 2 => ⟨((23555781987/68719476736), (11188719/268435456)), (53/17179869184), by norm_num⟩
  | 3 => ⟨((-22694988997/68719476736), (-344955279/8589934592)), (103/34359738368), by norm_num⟩
  | 4 => ⟨((16399238811/68719476736), (249262249/8589934592)), (151/68719476736), by norm_num⟩
  | 5 => ⟨((-4739989671/34359738368), (-2305473807/137438953472)), (177/137438953472), by norm_num⟩
  | 6 => ⟨((2283388713/34359738368), (555306365/68719476736)), (43/68719476736), by norm_num⟩
  | 7 => ⟨((-30170707421/1099511627776), (-1834333525/549755813888)), (143/549755813888), by norm_num⟩
  | 8 => ⟨((21801140161/2199023255552), (662738227/549755813888)), (209/2199023255552), by norm_num⟩
  | 9 => ⟨((-1750372217/549755813888), (-3405439741/8796093022208)), (271/8796093022208), by norm_num⟩
  | 10 => ⟨((8094762275/8796093022208), (984298685/8796093022208)), (79/8796093022208), by norm_num⟩
  | 11 => ⟨((-17015907103/70368744177664), (-2069082997/70368744177664)), (21/8796093022208), by norm_num⟩
  | 12 => ⟨((16394099109/281474976710656), (498368255/70368744177664)), (41/70368744177664), by norm_num⟩
  | 13 => ⟨((-7290006317/562949953421312), (-3545771149/2251799813685248)), (147/1125899906842624), by norm_num⟩
  | 14 => ⟨((24080946713/9007199254740992), (2928170511/9007199254740992)), (245/9007199254740992), by norm_num⟩
  | 15 => ⟨((-18560770209/36028797018963968), (-2256933693/36028797018963968)), (191/36028797018963968), by norm_num⟩
  | 16 => ⟨((26823763009/288230376151711744), (3261688703/288230376151711744)), (139/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (78809921003/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889062204389955/316912650057057350374175801344), (46601526485/158456325028528675187087900672)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944508568792373/19807040628566084398385987584), (209661703533/39614081257132168796771975168)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888747164577989/2475880078570760549798248448), (111354470659/1237940039285380274899124224)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442603423289447/38685626227668133590597632), (111322637855/77371252455336267181195264)), (13781/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774412644833445/4835703278458516698824704), (104331163507/4835703278458516698824704)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629075930557571/302231454903657293676544), (91255973075/302231454903657293676544)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378881769055/37778931862957161709568), (296455242811/75557863725914323419136)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648382113649827/2361183241434822606848), (55557664411/1180591620717411303424)), (6889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620382966039455/590295810358705651712), (19086703813/36893488147419103232)), (18945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822144361630277/73786976294838206464), (381464437927/73786976294838206464)), (11841/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821161960463717/9223372036854775808), (428777067189/9223372036854775808)), (26643/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592412465840197/1152921504606846976), (428314525697/1152921504606846976)), (6661/288230376151711744), by norm_num⟩
  | 5 => ⟨((596603144121581/72057594037927936), (374255524251/144115188075855872)), (5829/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489580173831407/36028797018963968), (280172798075/18014398509481984)), (34977/36028797018963968), by norm_num⟩
  | 3 => ⟨((92918373534455/562949953421312), (43663738347/562949953421312)), (43727/9007199254740992), by norm_num⟩
  | 2 => ⟨((555711024116991/1125899906842624), (347954538671/1125899906842624)), (5467/281474976710656), by norm_num⟩
  | 1 => ⟨((276063259996179/281474976710656), (2074226158447/2251799813685248)), (131255/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165769554415467/2251799813685248), (2047381250343/1125899906842624)), (262707/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165769554415467/2251799813685248), (2047381250343/1125899906842624)), (1002147683150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083018644573291/2251799813685248), (3938321649487/1125899906842624)), (506297/2251799813685248), by norm_num⟩
  | 2 => ⟨((963430364848759/1125899906842624), (7286258196089/1125899906842624)), (940239/2251799813685248), by norm_num⟩
  | 3 => ⟨((824358340127163/1125899906842624), (24939347981389/2251799813685248)), (405323/562949953421312), by norm_num⟩
  | 4 => ⟨((1206876696656027/2251799813685248), (18260024164533/1125899906842624)), (602515/562949953421312), by norm_num⟩
  | 5 => ⟨((323123227508361/1125899906842624), (78293274599697/4503599627370496)), (1330785/1125899906842624), by norm_num⟩
  | 6 => ⟨((1478291343239115/18014398509481984), (89877884977527/9007199254740992)), (3240469/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-23580334503/268435456)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-12010713823/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((69048379495587/18014398509481984), (-354912841886569/4503599627370496)), (7091101/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1551122589/137438953472), (31891455257/137438953472)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1141796453/68719476736), (-11737805495/34359738368)), (473/68719476736), by norm_num⟩
  | 3 => ⟨((-560324997/34359738368), (11520417343/34359738368)), (233/34359738368), by norm_num⟩
  | 4 => ⟨((824921381/68719476736), (-4240145735/17179869184)), (345/68719476736), by norm_num⟩
  | 5 => ⟨((-242893067/34359738368), (19975760607/137438953472)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((953578419/274877906944), (-19605802723/274877906944)), (201/137438953472), by norm_num⟩
  | 7 => ⟨((-200553819/137438953472), (8246869965/274877906944)), (85/137438953472), by norm_num⟩
  | 8 => ⟨((295259241/549755813888), (-24282405381/2199023255552)), (251/1099511627776), by norm_num⟩
  | 9 => ⟨((-1545551677/8796093022208), (31776915961/8796093022208)), (659/8796093022208), by norm_num⟩
  | 10 => ⟨((113769565/2199023255552), (-18713037999/17592186044416)), (195/8796093022208), by norm_num⟩
  | 11 => ⟨((-974509213/70368744177664), (10018072455/35184372088832)), (419/70368744177664), by norm_num⟩
  | 12 => ⟨((956460971/281474976710656), (-1229066793/17592186044416)), (413/281474976710656), by norm_num⟩
  | 13 => ⟨((-433267841/562949953421312), (17816183007/1125899906842624)), (47/140737488355328), by norm_num⟩
  | 14 => ⟨((1457977965/9007199254740992), (-7494094815/2251799813685248)), (635/9007199254740992), by norm_num⟩
  | 15 => ⟨((-572390287/18014398509481984), (5884241303/9007199254740992)), (501/36028797018963968), by norm_num⟩
  | 16 => ⟨((105335517/18014398509481984), (-17325789455/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-1982831630481/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778049644133597/633825300114114700748351602688), (-2344777489289/633825300114114700748351602688)), (11555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944466441826867/19807040628566084398385987584), (-1318646094609/19807040628566084398385987584)), (13001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236082181505367/309485009821345068724781056), (-2801396952503/2475880078570760549798248448)), (13815/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221290470506451/19342813113834066795298816), (-700145132135/38685626227668133590597632)), (6909/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548740751212417/9671406556917033397649408), (-164042318245/604462909807314587353088)), (12957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157259707532915/75557863725914323419136), (-2295725635823/604462909807314587353088)), (2835/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886636756911461/75557863725914323419136), (-466116197611/9444732965739290427392)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((1296673096320015/4722366482869645213696), (-698819097411/1180591620717411303424)), (3457/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810128525387181/295147905179352825856), (-240074848201/36893488147419103232)), (19021/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821986053778467/73786976294838206464), (-4798038091655/73786976294838206464)), (11893/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820982610100803/9223372036854775808), (-5393040678443/9223372036854775808)), (26773/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592231551542089/1152921504606846976), (-673388264769/144115188075855872)), (13395/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193046233749217/144115188075855872), (-4707049246045/144115188075855872)), (11731/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489336595458697/36028797018963968), (-7047256066399/36028797018963968)), (1101/1125899906842624), by norm_num⟩
  | 3 => ⟨((1486383412161965/9007199254740992), (-137278242955/140737488355328)), (22055/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111102401898795/2251799813685248), (-4375500424715/1125899906842624)), (88431/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207502115987147/2251799813685248), (-13039788747511/1125899906842624)), (133175/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163583822522311/2251799813685248), (-51469095359901/2251799813685248)), (67119/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163583822522311/2251799813685248), (-51469095359901/2251799813685248)), (256038667918968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1038823669153441/1125899906842624), (-98905507855331/2251799813685248)), (264095/1125899906842624), by norm_num⟩
  | 2 => ⟨((59769358391603/70368744177664), (-182512463044587/2251799813685248)), (1021081/2251799813685248), by norm_num⟩
  | 3 => ⟨((402433911998827/562949953421312), (-310042560575031/2251799813685248)), (1900081/2251799813685248), by norm_num⟩
  | 4 => ⟨((1108056964875349/2251799813685248), (-221638957033475/1125899906842624)), (101245/70368744177664), by norm_num⟩
  | 5 => ⟨((915973899670441/4503599627370496), (-436252971576057/2251799813685248)), (8928107/4503599627370496), by norm_num⟩
  | 6 => ⟨((69048379495587/18014398509481984), (-354912841886569/4503599627370496)), (7091101/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-12010713823/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-3054986305/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-169666500790745/2251799813685248), (-82219200677551/18014398509481984)), (14062711/9007199254740992), by norm_num⟩
  | 1 => ⟨((31022669199/137438953472), (1879171089/137438953472)), (645/137438953472), by norm_num⟩
  | 2 => ⟨((-23233902833/68719476736), (-703686685/34359738368)), (485/68719476736), by norm_num⟩
  | 3 => ⟨((23200850853/68719476736), (1405371275/68719476736)), (243/34359738368), by norm_num⟩
  | 4 => ⟨((-17375884419/68719476736), (-1052529021/68719476736)), (183/34359738368), by norm_num⟩
  | 5 => ⟨((10410699547/68719476736), (1261238063/137438953472)), (55/17179869184), by norm_num⟩
  | 6 => ⟨((-10395889541/137438953472), (-1259443857/274877906944)), (441/274877906944), by norm_num⟩
  | 7 => ⟨((17796172463/549755813888), (1077987603/549755813888)), (379/549755813888), by norm_num⟩
  | 8 => ⟨((-26656284097/2199023255552), (-807340563/1099511627776)), (285/1099511627776), by norm_num⟩
  | 9 => ⟨((17745575681/4398046511104), (1074922747/4398046511104)), (381/4398046511104), by norm_num⟩
  | 10 => ⟨((-2658049689/2199023255552), (-644036153/8796093022208)), (229/8796093022208), by norm_num⟩
  | 11 => ⟨((23164524329/70368744177664), (350792707/17592186044416)), (501/70368744177664), by norm_num⟩
  | 12 => ⟨((-23131571045/281474976710656), (-175146839/35184372088832)), (251/140737488355328), by norm_num⟩
  | 13 => ⟨((10660922141/562949953421312), (645776047/562949953421312)), (29/70368744177664), by norm_num⟩
  | 14 => ⟨((-1140616733/281474976710656), (-1105469797/4503599627370496)), (399/4503599627370496), by norm_num⟩
  | 15 => ⟨((14579124731/18014398509481984), (441558873/9007199254740992)), (5/281474976710656), by norm_num⟩
  | 16 => ⟨((-10918788619/72057594037927936), (-1322792167/144115188075855872)), (241/72057594037927936), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-501683365413/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888986185260997/316912650057057350374175801344), (-2372868961841/316912650057057350374175801344)), (11585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888845466730005/39614081257132168796771975168), (-5337729610185/39614081257132168796771975168)), (3259/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888563923757935/2475880078570760549798248448), (-5669839630045/2475880078570760549798248448)), (13855/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442557376938231/38685626227668133590597632), (-5668154501007/154742504910672534362390528)), (3465/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548651613046531/9671406556917033397649408), (-2656052386349/4835703278458516698824704)), (12999/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257998892189355/604462909807314587353088), (-1161575506987/151115727451828646838272)), (2845/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886507312457643/75557863725914323419136), (-471680381633/4722366482869645213696)), (4625/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296574748938417/4722366482869645213696), (-5657230127897/4722366482869645213696)), (3471/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620119771869407/590295810358705651712), (-1943481158223/147573952589676412928)), (597/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821811383180865/73786976294838206464), (-9710258562727/73786976294838206464)), (23901/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820781889706317/9223372036854775808), (-10914218259001/9223372036854775808)), (13459/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592025573141429/1152921504606846976), (-10901947207015/1152921504606846976)), (26953/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192860103813649/144115188075855872), (-9525408820435/144115188075855872)), (23625/144115188075855872), by norm_num⟩
  | 4 => ⟨((186130705484379/4503599627370496), (-3565137039003/9007199254740992)), (17759/18014398509481984), by norm_num⟩
  | 3 => ⟨((742999620269661/4503599627370496), (-8888751203411/4503599627370496)), (44539/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110687690708555/2251799813685248), (-4426335148733/562949953421312)), (2797/140737488355328), by norm_num⟩
  | 1 => ⟨((275763320759757/281474976710656), (-3297250060917/140737488355328)), (67663/1125899906842624), by norm_num⟩
  | 0 => ⟨((540048678534385/562949953421312), (-26019165331013/562949953421312)), (137473/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540048678534385/562949953421312), (-26019165331013/562949953421312)), (524417881492232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033752916946941/1125899906842624), (-12480341963067/140737488355328)), (276469/1125899906842624), by norm_num⟩
  | 2 => ⟨((940293639771411/1125899906842624), (-91671309894649/562949953421312)), (278359/562949953421312), by norm_num⟩
  | 3 => ⟨((1510858305599365/2251799813685248), (-612473269565701/2251799813685248)), (555599/562949953421312), by norm_num⟩
  | 4 => ⟨((423565474620099/1125899906842624), (-205471268062349/562949953421312)), (1047803/562949953421312), by norm_num⟩
  | 5 => ⟨((37424084430707/4503599627370496), (-618389145597735/2251799813685248)), (12425973/4503599627370496), by norm_num⟩
  | 6 => ⟨((-169666500790745/2251799813685248), (-82219200677551/18014398509481984)), (14062711/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-3054986305/33554432)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-12418966053/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-192869861583705/18014398509481984), (322359829147503/4503599627370496)), (27528473/18014398509481984), by norm_num⟩
  | 1 => ⟨((2239977345/68719476736), (-14975459791/68719476736)), (321/68719476736), by norm_num⟩
  | 2 => ⟨((-3409830643/68719476736), (22796561675/68719476736)), (491/68719476736), by norm_num⟩
  | 3 => ⟨((865108825/17179869184), (-11567440587/34359738368)), (501/68719476736), by norm_num⟩
  | 4 => ⟨((-2633843229/68719476736), (17608666207/68719476736)), (383/68719476736), by norm_num⟩
  | 5 => ⟨((3207517923/137438953472), (-10721995873/68719476736)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((-3255120095/274877906944), (2720279751/34359738368)), (477/274877906944), by norm_num⟩
  | 7 => ⟨((2831510333/549755813888), (-18930177689/549755813888)), (417/549755813888), by norm_num⟩
  | 8 => ⟨((-4310298371/2199023255552), (14408337681/1099511627776)), (637/2199023255552), by norm_num⟩
  | 9 => ⟨((2916177801/4398046511104), (-19496225493/4398046511104)), (433/4398046511104), by norm_num⟩
  | 10 => ⟨((-3551347499/17592186044416), (11871339193/8796093022208)), (529/17592186044416), by norm_num⟩
  | 11 => ⟨((3931693507/70368744177664), (-26285497119/70368744177664)), (147/17592186044416), by norm_num⟩
  | 12 => ⟨((-3990043033/281474976710656), (26675595255/281474976710656)), (599/281474976710656), by norm_num⟩
  | 13 => ⟨((1868888545/562949953421312), (-24989061013/1125899906842624)), (563/1125899906842624), by norm_num⟩
  | 14 => ⟨((-1625678031/2251799813685248), (21737073415/4503599627370496)), (123/1125899906842624), by norm_num⟩
  | 15 => ⟨((1319843531/9007199254740992), (-8823867699/9007199254740992)), (401/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1004573311/36028797018963968), (26864463197/144115188075855872)), (613/144115188075855872), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (2239543867139/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777915871450439/633825300114114700748351602688), (661993091615/158456325028528675187087900672)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888782378898023/39614081257132168796771975168), (2978288906789/39614081257132168796771975168)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472124380776053/618970019642690137449562112), (3163584135895/2475880078570760549798248448)), (3455/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770163815337143/154742504910672534362390528), (1581315353361/77371252455336267181195264)), (13823/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96786923645321/604462909807314587353088), (1481976809139/4835703278458516698824704)), (6481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314486603267331/151115727451828646838272), (1296223569775/302231454903657293676544)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886423441106499/75557863725914323419136), (4210829417903/75557863725914323419136)), (18441/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648256537673315/2361183241434822606848), (3156462861675/4722366482869645213696)), (13835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405009241672373/147573952589676412928), (2168720897617/295147905179352825856)), (19031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821710866148693/73786976294838206464), (1354440754749/18446744073709551616)), (2975/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455168227777161/2305843009213693952), (6089433902501/9223372036854775808)), (26791/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591921712254689/1152921504606846976), (6082503691331/1152921504606846976)), (26811/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192774967693945/144115188075855872), (5314403386959/144115188075855872)), (23483/144115188075855872), by norm_num⟩
  | 4 => ⟨((744464692947095/18014398509481984), (7956053233219/36028797018963968)), (35269/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485873863314283/9007199254740992), (4958951066583/4503599627370496)), (44165/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221184121128099/4503599627370496), (9877258012339/2251799813685248)), (88567/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102983609525721/1125899906842624), (14714634732153/1125899906842624)), (133447/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160499070334739/2251799813685248), (58052805552393/2251799813685248)), (16831/140737488355328), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160499070334739/2251799813685248), (58052805552393/2251799813685248)), (64205170214605287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1035701769832535/1125899906842624), (111398030734361/2251799813685248)), (530641/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899948244459487/2251799813685248), (51236853687547/562949953421312)), (257191/562949953421312), by norm_num⟩
  | 3 => ⟨((792210716762809/1125899906842624), (345847333759091/2251799813685248)), (1923299/2251799813685248), by norm_num⟩
  | 4 => ⟨((530860000568701/1125899906842624), (486693288635457/2251799813685248)), (3297349/2251799813685248), by norm_num⟩
  | 5 => ⟨((790815416362641/4503599627370496), (114737552561995/562949953421312)), (9069473/4503599627370496), by norm_num⟩
  | 6 => ⟨((-192869861583705/18014398509481984), (322359829147503/4503599627370496)), (27528473/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-12418966053/134217728)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile055Terms2
