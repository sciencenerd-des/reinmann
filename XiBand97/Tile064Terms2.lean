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
namespace Reinmann.XiBand97.Tile064Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨64,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (16205/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (16205/512))
  have he : value ((69/80), (16205/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/1073741824), (-94224620441/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1611828365282935/18014398509481984), (86341569787347/4503599627370496)), (242659/1125899906842624), by norm_num⟩
  | 1 => ⟨((-68190569271/274877906944), (-14611185465/274877906944)), (83/137438953472), by norm_num⟩
  | 2 => ⟨((47266100831/137438953472), (20255404019/274877906944)), (29/34359738368), by norm_num⟩
  | 3 => ⟨((-87366305405/274877906944), (-18719968249/274877906944)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((60557708267/274877906944), (3243923303/68719476736)), (151/274877906944), by norm_num⟩
  | 5 => ⟨((-33580323797/274877906944), (-14390504265/549755813888)), (169/549755813888), by norm_num⟩
  | 6 => ⟨((3879351127/68719476736), (1662456243/137438953472)), (79/549755813888), by norm_num⟩
  | 7 => ⟨((-98339155971/4398046511104), (-21071119683/4398046511104)), (253/4398046511104), by norm_num⟩
  | 8 => ⟨((17040877175/2199023255552), (14605387199/8796093022208)), (177/8796093022208), by norm_num⟩
  | 9 => ⟨((-83995277995/35184372088832), (-562426831/1099511627776)), (55/8796093022208), by norm_num⟩
  | 10 => ⟨((23288436049/35184372088832), (1247502631/8796093022208)), (123/70368744177664), by norm_num⟩
  | 11 => ⟨((-93918916579/562949953421312), (-20123995495/562949953421312)), (125/281474976710656), by norm_num⟩
  | 12 => ⟨((86799509637/2251799813685248), (18598520985/2251799813685248)), (233/2251799813685248), by norm_num⟩
  | 13 => ⟨((-37024514079/4503599627370496), (-15866476779/9007199254740992)), (201/9007199254740992), by norm_num⟩
  | 14 => ⟨((29329642909/18014398509481984), (12568918451/36028797018963968)), (161/36028797018963968), by norm_num⟩
  | 15 => ⟨((-21685076575/72057594037927936), (-4646458873/72057594037927936)), (15/18014398509481984), by norm_num⟩
  | 16 => ⟨((60123798753/1152921504606846976), (6441359735/576460752303423488)), (21/144115188075855872), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (68738230377/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889140440434819/316912650057057350374175801344), (162611196749/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889193129377553/39614081257132168796771975168), (91449854241/9903520314283042199192993792)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888934106494239/2475880078570760549798248448), (194283557851/1237940039285380274899124224)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770600579567539/154742504910672534362390528), (48557569175/19342813113834066795298816)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549000436723531/9671406556917033397649408), (182034293817/4835703278458516698824704)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258305055863265/604462909807314587353088), (159223439723/302231454903657293676544)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943503297286047/37778931862957161709568), (258632075059/37778931862957161709568)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296950754002713/4722366482869645213696), (387762685823/4722366482869645213696)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620639283429623/590295810358705651712), (532872559257/590295810358705651712)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822464523309449/73786976294838206464), (665639321525/73786976294838206464)), (5923/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910760909720799/4611686018427387904), (93528014645/1152921504606846976)), (833/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592771921620095/1152921504606846976), (23357804807/36028797018963968)), (833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193520359058491/144115188075855872), (81643556941/18014398509481984)), (729/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490050375582163/36028797018963968), (244496305181/9007199254740992)), (8749/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487280149309131/9007199254740992), (609723510721/4503599627370496)), (5469/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224011717245123/4503599627370496), (2429814699703/4503599627370496)), (5471/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105122873295155/1125899906842624), (452763507897/281474976710656)), (32845/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169202112210871/2251799813685248), (447141538855/140737488355328)), (65769/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169202112210871/2251799813685248), (447141538855/140737488355328)), (250888833052825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089611426167183/2251799813685248), (6891840844087/1125899906842624)), (31783/562949953421312), by norm_num⟩
  | 2 => ⟨((484755116324239/562949953421312), (25581793350557/2251799813685248)), (59377/562949953421312), by norm_num⟩
  | 3 => ⟨((834698074367733/1125899906842624), (44056865574163/2251799813685248)), (414433/2251799813685248), by norm_num⟩
  | 4 => ⟨((154595363955267/281474976710656), (65324067679441/2251799813685248)), (315353/1125899906842624), by norm_num⟩
  | 5 => ⟨((1354752102318587/4503599627370496), (143512551431139/4503599627370496)), (729403/2251799813685248), by norm_num⟩
  | 6 => ⟨((1611828365282935/18014398509481984), (86341569787347/4503599627370496)), (242659/1125899906842624), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-94224620441/1073741824)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-96284908695/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-213531386864287/18014398509481984), (-774897050087095/9007199254740992)), (8210915/18014398509481984), by norm_num⟩
  | 1 => ⟨((2307815455/68719476736), (66999776079/274877906944)), (357/274877906944), by norm_num⟩
  | 2 => ⟨((-13077067085/274877906944), (-94912329817/274877906944)), (127/68719476736), by norm_num⟩
  | 3 => ⟨((6175020161/137438953472), (89635626451/274877906944)), (241/137438953472), by norm_num⟩
  | 4 => ⟨((-1093446845/34359738368), (-63489213241/274877906944)), (343/274877906944), by norm_num⟩
  | 5 => ⟨((9913498215/549755813888), (71951394463/549755813888)), (195/274877906944), by norm_num⟩
  | 6 => ⟨((-4681175905/549755813888), (-16987804243/274877906944)), (185/549755813888), by norm_num⟩
  | 7 => ⟨((7578725737/2199023255552), (55005798477/2199023255552)), (601/4398046511104), by norm_num⟩
  | 8 => ⟨((-2684018361/2199023255552), (-38960790561/4398046511104)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((13518927353/35184372088832), (98119317077/35184372088832)), (541/35184372088832), by norm_num⟩
  | 10 => ⟨((-15320802149/140737488355328), (-27799295845/35184372088832)), (77/17592186044416), by norm_num⟩
  | 11 => ⟨((3946100099/140737488355328), (57280971595/281474976710656)), (637/562949953421312), by norm_num⟩
  | 12 => ⟨((-14906857943/2251799813685248), (-54096404361/1125899906842624)), (151/562949953421312), by norm_num⟩
  | 13 => ⟨((12995171951/9007199254740992), (47158970677/4503599627370496)), (33/562949953421312), by norm_num⟩
  | 14 => ⟨((-5259727797/18014398509481984), (-38174692861/18014398509481984)), (429/36028797018963968), by norm_num⟩
  | 15 => ⟨((7947696523/144115188075855872), (57683759583/144115188075855872)), (651/288230376151711744), by norm_num⟩
  | 16 => ⟨((-5629379961/576460752303423488), (-81715198693/1152921504606846976)), (463/1152921504606846976), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-2224489144757/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778196666488747/633825300114114700748351602688), (-1315481967655/316912650057057350374175801344)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889098205004199/39614081257132168796771975168), (-739800671665/9903520314283042199192993792)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944416502553067/1237940039285380274899124224), (-196460549689/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((442624800926939/38685626227668133590597632), (-3142487034625/154742504910672534362390528)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((1548905105458073/9671406556917033397649408), (-1472572509123/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39319417183349/18889465931478580854784), (-2576065644605/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886870026991203/75557863725914323419136), (-2092175956175/37778931862957161709568)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296847851694593/4722366482869645213696), (-3136729220695/4722366482869645213696)), (3459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405124254817591/147573952589676412928), (-4310510083799/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822285534675467/73786976294838206464), (-1346100253199/18446744073709551616)), (2975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227664858411421/1152921504606846976), (-6052317061087/9223372036854775808)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796283493204573/576460752303423488), (-755738132909/144115188075855872)), (6703/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149167351973955/18014398509481984), (-5282961127441/144115188075855872)), (5871/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489773625703421/36028797018963968), (-7910049305443/36028797018963968)), (8817/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486926484274871/9007199254740992), (-4931209078465/4503599627370496)), (11041/9007199254740992), by norm_num⟩
  | 2 => ⟨((277910167228419/562949953421312), (-4912394616013/1125899906842624)), (5535/1125899906842624), by norm_num⟩
  | 1 => ⟨((276136627535499/281474976710656), (-3660853258505/281474976710656)), (16679/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166670813798963/2251799813685248), (-14456773870811/562949953421312)), (33655/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166670813798963/2251799813685248), (-14456773870811/562949953421312)), (128383640769576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2083275082396799/2251799813685248), (-111281899277947/2251799813685248)), (132989/2251799813685248), by norm_num⟩
  | 2 => ⟨((960931647104531/1125899906842624), (-51476780146839/562949953421312)), (259217/2251799813685248), by norm_num⟩
  | 3 => ⟨((810720552761775/1125899906842624), (-175737352258451/1125899906842624)), (61235/281474976710656), by norm_num⟩
  | 4 => ⟨((556340926830809/1125899906842624), (-126542228574655/562949953421312)), (429209/1125899906842624), by norm_num⟩
  | 5 => ⟨((872061478732187/4503599627370496), (-1000452993032179/4503599627370496)), (2468517/4503599627370496), by norm_num⟩
  | 6 => ⟨((-213531386864287/18014398509481984), (-774897050087095/9007199254740992)), (8210915/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-96284908695/1073741824)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-98227400133/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-692789920804427/9007199254740992), (272867153966439/9007199254740992)), (4139757/9007199254740992), by norm_num⟩
  | 1 => ⟨((61109021645/274877906944), (-12034416435/137438953472)), (367/274877906944), by norm_num⟩
  | 2 => ⟨((-44156947579/137438953472), (34783937387/274877906944)), (533/274877906944), by norm_num⟩
  | 3 => ⟨((85086662799/274877906944), (-33512836751/274877906944)), (129/68719476736), by norm_num⟩
  | 4 => ⟨((-30741510891/137438953472), (12108069609/137438953472)), (375/274877906944), by norm_num⟩
  | 5 => ⟨((17770878975/137438953472), (-27997457953/549755813888)), (109/137438953472), by norm_num⟩
  | 6 => ⟨((-68485928937/1099511627776), (52684285/2147483648)), (211/549755813888), by norm_num⟩
  | 7 => ⟨((7069635529/274877906944), (-11137987251/1099511627776)), (351/2199023255552), by norm_num⟩
  | 8 => ⟨((-81735499487/8796093022208), (16096461895/4398046511104)), (509/8796093022208), by norm_num⟩
  | 9 => ⟨((52499106519/17592186044416), (-10338835303/8796093022208)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((-60696773919/70368744177664), (2988307757/8796093022208)), (381/70368744177664), by norm_num⟩
  | 11 => ⟨((63794996775/281474976710656), (-12563375047/140737488355328)), (201/140737488355328), by norm_num⟩
  | 12 => ⟨((-61463752325/1125899906842624), (24208549613/1125899906842624)), (389/1125899906842624), by norm_num⟩
  | 13 => ⟨((54662490417/4503599627370496), (-21529756339/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 14 => ⟨((-45141405291/18014398509481984), (35559428387/36028797018963968)), (575/36028797018963968), by norm_num⟩
  | 15 => ⟨((69586902915/144115188075855872), (-27407991343/144115188075855872)), (445/144115188075855872), by norm_num⟩
  | 16 => ⟨((-25141502363/288230376151711744), (9902410515/288230376151711744)), (81/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (3603524572927/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((6945760516849/2475880078570760549798248448), (4261639745043/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944502835122707/19807040628566084398385987584), (1198321470235/9903520314283042199192993792)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236091783497757/309485009821345068724781056), (636446099929/309485009821345068724781056)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770399995757749/154742504910672534362390528), (5090109418481/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548811598151485/9671406556917033397649408), (4770427339727/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314534757892335/151115727451828646838272), (4172574077703/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943367662163519/37778931862957161709568), (3388763879205/37778931862957161709568)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296746007147805/4722366482869645213696), (5080604681549/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620355656287085/590295810358705651712), (6981703666089/590295810358705651712)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822106843970613/73786976294838206464), (8720940686559/73786976294838206464)), (2985/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56909847288257/288230376151711744), (612659564221/576460752303423488)), (6723/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592359831154563/1152921504606846976), (2447982051193/288230376151711744)), (6731/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193153739034411/144115188075855872), (4277996757897/72057594037927936)), (5899/144115188075855872), by norm_num⟩
  | 4 => ⟨((93093025298349/2251799813685248), (6405063057135/18014398509481984)), (4433/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486556706416369/9007199254740992), (15970947522505/9007199254740992)), (5557/4503599627370496), by norm_num⟩
  | 2 => ⟨((69453195632219/140737488355328), (7954243369443/1125899906842624)), (11161/2251799813685248), by norm_num⟩
  | 1 => ⟨((275978301611013/281474976710656), (23706943892263/1125899906842624)), (8431/562949953421312), by norm_num⟩
  | 0 => ⟨((540937624229607/562949953421312), (46792940167733/1125899906842624)), (34205/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540937624229607/562949953421312), (46792940167733/1125899906842624)), (130481724265670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037627294290595/1125899906842624), (22481627124417/281474976710656)), (68579/1125899906842624), by norm_num⟩
  | 2 => ⟨((949092915304419/1125899906842624), (331504422836685/2251799813685248)), (8585/70368744177664), by norm_num⟩
  | 3 => ⟨((1551298762853595/2251799813685248), (279446243128925/1125899906842624)), (272023/1125899906842624), by norm_num⟩
  | 4 => ⟨((116249623285137/281474976710656), (192514720276365/562949953421312)), (509833/1125899906842624), by norm_num⟩
  | 5 => ⟨((120749505559971/2251799813685248), (636071141257473/2251799813685248)), (3079297/4503599627370496), by norm_num⟩
  | 6 => ⟨((-692789920804427/9007199254740992), (272867153966439/9007199254740992)), (4139757/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-98227400133/1073741824)), (1/536870912), by norm_num⟩, -15, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-2726851779/1073741824), (-25016209851/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((350435651658819/9007199254740992), (1236510050115085/18014398509481984)), (1471455/4503599627370496), by norm_num⟩
  | 1 => ⟨((-15744573859/137438953472), (-55554632411/274877906944)), (133/137438953472), by norm_num⟩
  | 2 => ⟨((46358936981/274877906944), (20447153143/68719476736)), (197/137438953472), by norm_num⟩
  | 3 => ⟨((-45500353693/274877906944), (-80273859637/274877906944)), (389/274877906944), by norm_num⟩
  | 4 => ⟨((33493253745/274877906944), (59090370331/274877906944)), (9/8589934592), by norm_num⟩
  | 5 => ⟨((-19723768373/274877906944), (-69595195879/549755813888)), (171/274877906944), by norm_num⟩
  | 6 => ⟨((19358477471/549755813888), (34153134585/549755813888)), (169/549755813888), by norm_num⟩
  | 7 => ⟨((-16285673041/1099511627776), (-28731948781/1099511627776)), (143/1099511627776), by norm_num⟩
  | 8 => ⟨((5994021313/1099511627776), (42299734969/4398046511104)), (423/8796093022208), by norm_num⟩
  | 9 => ⟨((-15688026663/8796093022208), (-27677552989/8796093022208)), (279/17592186044416), by norm_num⟩
  | 10 => ⟨((18476974885/35184372088832), (65195892695/70368744177664)), (331/70368744177664), by norm_num⟩
  | 11 => ⟨((-9891695467/70368744177664), (-69805573721/281474976710656)), (89/70368744177664), by norm_num⟩
  | 12 => ⟨((9708497901/281474976710656), (68512750743/1125899906842624)), (11/35184372088832), by norm_num⟩
  | 13 => ⟨((-8795716815/1125899906842624), (-62071265803/4503599627370496)), (321/4503599627370496), by norm_num⟩
  | 14 => ⟨((29598230217/18014398509481984), (52218587005/18014398509481984)), (271/18014398509481984), by norm_num⟩
  | 15 => ⟨((-46480097475/144115188075855872), (-10250296201/18014398509481984)), (427/144115188075855872), by norm_num⟩
  | 16 => ⟨((17107226345/288230376151711744), (60362743365/576460752303423488)), (79/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (1374432115001/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889025587715969/316912650057057350374175801344), (1625320795913/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888934690677313/39614081257132168796771975168), (1828083713419/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888659484283793/2475880078570760549798248448), (970917944673/1237940039285380274899124224)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885162961234047/77371252455336267181195264), (1941270203119/154742504910672534362390528)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548742908685129/9671406556917033397649408), (909669996893/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9828747514779/4722366482869645213696), (795660960233/302231454903657293676544)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886640292757691/75557863725914323419136), (646193142527/18889465931478580854784)), (4603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648337983658995/2361183241434822606848), (968797548139/2361183241434822606848)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620261353988719/590295810358705651712), (332824337973/73786976294838206464)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821991965368265/73786976294838206464), (1662923635767/36893488147419103232)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910494995800311/4611686018427387904), (3738286328141/9223372036854775808)), (6683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592239844758795/1152921504606846976), (3734175703633/1152921504606846976)), (3343/576460752303423488), by norm_num⟩
  | 5 => ⟨((298263628317705/36028797018963968), (203924065283/9007199254740992)), (2927/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489351053857247/36028797018963968), (1221238636831/9007199254740992)), (2197/9007199254740992), by norm_num⟩
  | 3 => ⟨((743202519177633/4503599627370496), (6090085188915/9007199254740992)), (10997/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111129327460707/2251799813685248), (12131975297565/4503599627370496)), (5507/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207609177375531/2251799813685248), (9038962646189/1125899906842624)), (16567/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163901817871763/2251799813685248), (35678391289597/2251799813685248)), (33319/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163901817871763/2251799813685248), (35678391289597/2251799813685248)), (127101902488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2078869578607237/2251799813685248), (34285701287073/1125899906842624)), (65093/1125899906842624), by norm_num⟩
  | 2 => ⟨((1917131647925017/2251799813685248), (126610724370321/2251799813685248)), (124153/1125899906842624), by norm_num⟩
  | 3 => ⟨((812541918182611/1125899906842624), (215587038582979/2251799813685248)), (56341/281474976710656), by norm_num⟩
  | 4 => ⟨((1152153796373469/2251799813685248), (77792663806485/562949953421312)), (736871/2251799813685248), by norm_num⟩
  | 5 => ⟨((1093020068964329/4503599627370496), (159213287770837/1125899906842624)), (1915413/4503599627370496), by norm_num⟩
  | 6 => ⟨((350435651658819/9007199254740992), (1236510050115085/18014398509481984)), (1471455/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-25016209851/268435456)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-1387177309/536870912), (-101808008579/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((573033515151991/9007199254740992), (-731874675949035/18014398509481984)), (132493/562949953421312), by norm_num⟩
  | 1 => ⟨((-52388152929/274877906944), (4181862997/34359738368)), (49/68719476736), by norm_num⟩
  | 2 => ⟨((78470440241/274877906944), (-50110967775/274877906944)), (37/34359738368), by norm_num⟩
  | 3 => ⟨((-78358810117/274877906944), (50039681141/274877906944)), (149/137438953472), by norm_num⟩
  | 4 => ⟨((1833922003/8589934592), (-18738185969/137438953472)), (225/274877906944), by norm_num⟩
  | 5 => ⟨((-17580605861/137438953472), (11226917691/137438953472)), (17/34359738368), by norm_num⟩
  | 6 => ⟨((70222384489/1099511627776), (-44843786213/1099511627776)), (137/549755813888), by norm_num⟩
  | 7 => ⟨((-60104989583/2199023255552), (38382850751/2199023255552)), (237/2199023255552), by norm_num⟩
  | 8 => ⟨((22507307137/2199023255552), (-14373093093/2199023255552)), (179/4398046511104), by norm_num⟩
  | 9 => ⟨((-29967051725/8796093022208), (19136861711/8796093022208)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((71818611197/70368744177664), (-22931565697/35184372088832)), (145/35184372088832), by norm_num⟩
  | 11 => ⟨((-78236120511/281474976710656), (24980665979/140737488355328)), (159/140737488355328), by norm_num⟩
  | 12 => ⟨((19531205931/281474976710656), (-3118141137/70368744177664)), (5/17592186044416), by norm_num⟩
  | 13 => ⟨((-72012632553/4503599627370496), (45987032801/4503599627370496)), (297/4503599627370496), by norm_num⟩
  | 14 => ⟨((7704663123/2251799813685248), (-39361382379/18014398509481984)), (1/70368744177664), by norm_num⟩
  | 15 => ⟨((-12309924253/18014398509481984), (31444310273/72057594037927936)), (103/36028797018963968), by norm_num⟩
  | 16 => ⟨((18438618685/144115188075855872), (-367963809/4503599627370496)), (311/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (-740296421723/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888992017850105/316912650057057350374175801344), (-218841519719/158456325028528675187087900672)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472214807706529/9903520314283042199192993792), (-492283627823/19807040628566084398385987584)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888579403183351/2475880078570760549798248448), (-522913563701/1237940039285380274899124224)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885122974065021/77371252455336267181195264), (-1045517249229/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548668046100333/9671406556917033397649408), (-979843303489/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258014290399411/604462909807314587353088), (-214258479209/151115727451828646838272)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886534243776517/75557863725914323419136), (-1392063594871/75557863725914323419136)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296596616065547/4722366482869645213696), (-521754273359/2361183241434822606848)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620152547078485/590295810358705651712), (-1433948706449/590295810358705651712)), (4743/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821856407713673/73786976294838206464), (-895561783167/36893488147419103232)), (2965/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820838108351679/9223372036854775808), (-2013211202193/9223372036854775808)), (417/576460752303423488), by norm_num⟩
  | 6 => ⟨((99505545869899/72057594037927936), (-251370015711/144115188075855872)), (3337/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192923158210607/144115188075855872), (-439265248583/36028797018963968)), (5841/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489155750041211/36028797018963968), (-657635402977/9007199254740992)), (4383/18014398509481984), by norm_num⟩
  | 3 => ⟨((371540980636745/2251799813685248), (-3279358484379/9007199254740992)), (10963/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221785419755785/4503599627370496), (-6379234619/4398046511104)), (21945/4503599627370496), by norm_num⟩
  | 1 => ⟨((275865207169553/281474976710656), (-9732813902063/2251799813685248)), (4121/281474976710656), by norm_num⟩
  | 0 => ⟨((2162615163323349/2251799813685248), (-19204428039011/2251799813685248)), (33069/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162615163323349/2251799813685248), (-19204428039011/2251799813685248)), (126148228171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038399485193635/1125899906842624), (-2305477324611/140737488355328)), (64083/1125899906842624), by norm_num⟩
  | 2 => ⟨((1914794219015141/2251799813685248), (-68041756179629/2251799813685248)), (240611/2251799813685248), by norm_num⟩
  | 3 => ⟨((12704445900117/17592186044416), (-28929294822875/562949953421312)), (6621/35184372088832), by norm_num⟩
  | 4 => ⟨((584207214960297/1125899906842624), (-41783398615479/562949953421312)), (655577/2251799813685248), by norm_num⟩
  | 5 => ⟨((593862133535031/2251799813685248), (-173444639534103/2251799813685248)), (777649/2251799813685248), by norm_num⟩
  | 6 => ⟨((573033515151991/9007199254740992), (-731874675949035/18014398509481984)), (132493/562949953421312), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-101808008579/1073741824)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2819539303/1073741824), (-103466110505/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-84034561601109/2251799813685248), (-1117093037780743/18014398509481984)), (3685613/9007199254740992), by norm_num⟩
  | 1 => ⟨((31231092327/274877906944), (51895367715/274877906944)), (43/34359738368), by norm_num⟩
  | 2 => ⟨((-1485683771/8589934592), (-78998305711/274877906944)), (263/137438953472), by norm_num⟩
  | 3 => ⟨((48247440813/274877906944), (10021338095/34359738368)), (67/34359738368), by norm_num⟩
  | 4 => ⟨((-18361302015/137438953472), (-61020377373/274877906944)), (205/137438953472), by norm_num⟩
  | 5 => ⟨((44721116777/549755813888), (18577790807/137438953472)), (251/274877906944), by norm_num⟩
  | 6 => ⟨((-45384814489/1099511627776), (-37707000637/549755813888)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((39478596013/2199023255552), (32799945571/1099511627776)), (7/34359738368), by norm_num⟩
  | 8 => ⟨((-30048367843/4398046511104), (-12482521281/1099511627776)), (343/4398046511104), by norm_num⟩
  | 9 => ⟨((40659080051/17592186044416), (67561450879/17592186044416)), (233/8796093022208), by norm_num⟩
  | 10 => ⟨((-49514992605/70368744177664), (-82276941251/70368744177664)), (285/35184372088832), by norm_num⟩
  | 11 => ⟨((27409001089/140737488355328), (45544362499/140737488355328)), (317/140737488355328), by norm_num⟩
  | 12 => ⟨((-27815772937/562949953421312), (-46220277847/562949953421312)), (323/562949953421312), by norm_num⟩
  | 13 => ⟨((26057152255/2251799813685248), (21649026613/1125899906842624)), (19/140737488355328), by norm_num⟩
  | 14 => ⟨((-11333083529/4503599627370496), (-37663398445/9007199254740992)), (531/18014398509481984), by norm_num⟩
  | 15 => ⟨((4600510279/9007199254740992), (15288941553/18014398509481984)), (433/72057594037927936), by norm_num⟩
  | 16 => ⟨((-28012713539/288230376151711744), (-46547525607/288230376151711744)), (331/288230376151711744), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-2751825486141/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444478488622399/158456325028528675187087900672), (-3253679444083/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944390058627127/19807040628566084398385987584), (-3659549867371/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944247489807253/1237940039285380274899124224), (-3887229517495/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770161113966141/154742504910672534362390528), (-3886057417717/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193573509772023/1208925819614629174706176), (-1820966933325/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257943882977551/604462909807314587353088), (-3185447613389/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886419016040373/75557863725914323419136), (-2587009918519/37778931862957161709568)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324127370602845/1180591620717411303424), (-1939237424895/2361183241434822606848)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101251973846133/36893488147419103232), (-5329589634727/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910851734234603/36893488147419103232), (-6657020199767/73786976294838206464)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820663674355855/9223372036854775808), (-7482323320857/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591911335119879/1152921504606846976), (-7473800321591/1152921504606846976)), (6713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596382304151263/72057594037927936), (-204062413173/4503599627370496)), (2941/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488911296822119/36028797018963968), (-9775865480795/36028797018963968)), (2209/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485846809282721/9007199254740992), (-3046602916469/2251799813685248)), (11069/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221116763895647/4503599627370496), (-24272794254117/4503599627370496)), (11105/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205833335442835/2251799813685248), (-18079963883493/1125899906842624)), (16749/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160101555040129/2251799813685248), (-71327646806391/2251799813685248)), (16933/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160101555040129/2251799813685248), (-71327646806391/2251799813685248)), (64594270946311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((32341845138727/35184372088832), (-34211513796087/562949953421312)), (134239/2251799813685248), by norm_num⟩
  | 2 => ⟨((1894337335883693/2251799813685248), (-251580668453805/2251799813685248)), (263105/2251799813685248), by norm_num⟩
  | 3 => ⟨((1565512657012775/2251799813685248), (-423286875096291/2251799813685248)), (125367/562949953421312), by norm_num⟩
  | 4 => ⟨((126102356370251/281474976710656), (-294280582351649/1125899906842624)), (442899/1125899906842624), by norm_num⟩
  | 5 => ⟨((596244146908201/4503599627370496), (-1054714711828883/4503599627370496)), (2513467/4503599627370496), by norm_num⟩
  | 6 => ⟨((-84034561601109/2251799813685248), (-1117093037780743/18014398509481984)), (3685613/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-103466110505/1073741824)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile064Terms2
