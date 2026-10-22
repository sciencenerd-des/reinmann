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
namespace Reinmann.XiBand97.Tile004Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10277/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10277/640))
  have he : value ((69/80), (10277/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1493900685/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((353589115154743/4503599627370496), (-26458699995455/562949953421312)), (40174287/4503599627370496), by norm_num⟩
  | 1 => ⟨((-233735369/1073741824), (559685465/4294967296)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((40503253/134217728), (-193972201/1073741824)), (19/536870912), by norm_num⟩
  | 3 => ⟨((-1197854533/4294967296), (179268379/1073741824)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((207572373/1073741824), (-248518743/2147483648)), (101/4294967296), by norm_num⟩
  | 5 => ⟨((-920820513/8589934592), (551232211/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((851018857/17179869184), (-509446737/17179869184)), (107/17179869184), by norm_num⟩
  | 7 => ⟨((-337075041/17179869184), (100891877/8589934592)), (87/34359738368), by norm_num⟩
  | 8 => ⟨((934570457/137438953472), (-559463361/137438953472)), (123/137438953472), by norm_num⟩
  | 9 => ⟨((-1151635337/549755813888), (689405247/549755813888)), (77/274877906944), by norm_num⟩
  | 10 => ⟨((1277204459/2199023255552), (-764574885/2199023255552)), (173/2199023255552), by norm_num⟩
  | 11 => ⟨((-40240485/274877906944), (770855165/8796093022208)), (177/8796093022208), by norm_num⟩
  | 12 => ⟨((1190083359/35184372088832), (-356210723/17592186044416)), (83/17592186044416), by norm_num⟩
  | 13 => ⟨((-507632569/70368744177664), (37985609/8796093022208)), (9/8796093022208), by norm_num⟩
  | 14 => ⟨((804260763/562949953421312), (-120363967/140737488355328)), (29/140737488355328), by norm_num⟩
  | 15 => ⟨((-594635819/2251799813685248), (711935525/4503599627370496)), (87/2251799813685248), by norm_num⟩
  | 16 => ⟨((824340283/18014398509481984), (-246738051/9007199254740992)), (61/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-351322620271/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778280567403359/633825300114114700748351602688), (-207777358441/158456325028528675187087900672)), (92283/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889192759333029/39614081257132168796771975168), (-934804302169/39614081257132168796771975168)), (103823/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472233422580489/618970019642690137449562112), (-496493689701/1237940039285380274899124224)), (55159/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885300068773499/77371252455336267181195264), (-992715034027/154742504910672534362390528)), (110325/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999994885605/9671406556917033397649408), (-930381081411/9671406556917033397649408)), (103437/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629152320917025/302231454903657293676544), (-203448575063/151115727451828646838272)), (90515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887005870408263/75557863725914323419136), (-1321873837717/75557863725914323419136)), (36775/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162118770747789/590295810358705651712), (-247732866003/1180591620717411303424)), (110337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101289900127067/36893488147419103232), (-1361761117775/590295810358705651712)), (151733/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822463312418309/73786976294838206464), (-850523871673/36893488147419103232)), (189695/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910760153684687/4611686018427387904), (-478023439719/2305843009213693952)), (26681/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796385111327833/576460752303423488), (-1910114549089/1152921504606846976)), (106749/576460752303423488), by norm_num⟩
  | 5 => ⟨((596759331367907/72057594037927936), (-834563169965/72057594037927936)), (46717/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490047412950219/36028797018963968), (-312406065145/4503599627370496)), (8763/1125899906842624), by norm_num⟩
  | 3 => ⟨((1487275717199823/9007199254740992), (-3116304179403/9007199254740992)), (175361/4503599627370496), by norm_num⟩
  | 2 => ⟨((278000084786263/562949953421312), (-6209399853495/4503599627370496)), (702049/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210223792180087/2251799813685248), (-9256291156421/2251799813685248)), (527299/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169136863362039/2251799813685248), (-9141309638689/1125899906842624)), (1057673/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169136863362039/2251799813685248), (-9141309638689/1125899906842624)), (4034702305320357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522340002121309/562949953421312), (-17611469364353/1125899906842624)), (4109735/2251799813685248), by norm_num⟩
  | 2 => ⟨((121130455378447/140737488355328), (-16341017330631/562949953421312)), (7755107/2251799813685248), by norm_num⟩
  | 3 => ⟨((833091344090203/1125899906842624), (-7032223232551/140737488355328)), (13799611/2251799813685248), by norm_num⟩
  | 4 => ⟨((613621375158951/1125899906842624), (-83254069306069/1125899906842624)), (10900323/1125899906842624), by norm_num⟩
  | 5 => ⟨((1313082805139993/4503599627370496), (-90747811923053/1125899906842624)), (53974017/4503599627370496), by norm_num⟩
  | 6 => ⟨((353589115154743/4503599627370496), (-26458699995455/562949953421312)), (40174287/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1493900685/33554432)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1526565885/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((22626623656493/4503599627370496), (-780907473046009/9007199254740992)), (15540703/1125899906842624), by norm_num⟩
  | 1 => ⟨((-61136295/4294967296), (1054991471/4294967296)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((86606083/4294967296), (-1494507957/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((-40895585/2147483648), (705709981/2147483648)), (231/4294967296), by norm_num⟩
  | 4 => ⟨((115865917/8589934592), (-1999426935/8589934592)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((-16413643/2147483648), (1132960615/8589934592)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((31002235/8589934592), (-267493261/4294967296)), (45/4294967296), by norm_num⟩
  | 7 => ⟨((-50191969/34359738368), (866131973/34359738368)), (147/34359738368), by norm_num⟩
  | 8 => ⟨((35551139/68719476736), (-306742083/34359738368)), (105/68719476736), by norm_num⟩
  | 9 => ⟨((-44766205/274877906944), (1545005801/549755813888)), (267/549755813888), by norm_num⟩
  | 10 => ⟨((12683221/274877906944), (-1750932421/2199023255552)), (305/2199023255552), by norm_num⟩
  | 11 => ⟨((-104536061/8796093022208), (901957291/4398046511104)), (79/2199023255552), by norm_num⟩
  | 12 => ⟨((98724321/35184372088832), (-1703624955/35184372088832)), (75/8796093022208), by norm_num⟩
  | 13 => ⟨((-2689491/4398046511104), (742574301/70368744177664)), (263/140737488355328), by norm_num⟩
  | 14 => ⟨((34833837/281474976710656), (-1202212239/562949953421312)), (215/562949953421312), by norm_num⟩
  | 15 => ⟨((-52635569/2251799813685248), (908299669/2251799813685248)), (327/4503599627370496), by norm_num⟩
  | 16 => ⟨((37281949/9007199254740992), (-1286703371/18014398509481984)), (117/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-1970736146939/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222274683070119/79228162514264337593543950336), (-2330843349241/633825300114114700748351602688)), (46215/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472274786750601/9903520314283042199192993792), (-2621640270683/39614081257132168796771975168)), (103999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888834064521537/2475880078570760549798248448), (-2784798303801/2475880078570760549798248448)), (27629/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442625082229177/38685626227668133590597632), (-2784017300975/154742504910672534362390528)), (55267/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387226557548675/2417851639229258349412352), (-163074167187/604462909807314587353088)), (103647/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258222403805963/604462909807314587353088), (-570552275153/151115727451828646838272)), (11339/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471717967595173/18889465931478580854784), (-3707035610675/75557863725914323419136)), (36861/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648424674254055/2361183241434822606848), (-1389458724673/2361183241434822606848)), (110617/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405124815711365/147573952589676412928), (-954700977495/147573952589676412928)), (152153/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911144308459543/36893488147419103232), (-4770195633863/73786976294838206464)), (2973/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821322716090157/9223372036854775808), (-5361923308463/9223372036854775808)), (214169/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592571310804247/1152921504606846976), (-1339061249115/288230376151711744)), (107155/576460752303423488), by norm_num⟩
  | 5 => ⟨((74583945832141/9007199254740992), (-4680333363567/144115188075855872)), (5865/4503599627370496), by norm_num⟩
  | 4 => ⟨((744890582962445/18014398509481984), (-7007755742889/36028797018963968)), (140919/18014398509481984), by norm_num⟩
  | 3 => ⟨((743468881886311/4503599627370496), (-8737431958297/9007199254740992)), (352855/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111654714445147/2251799813685248), (-8704117375945/2251799813685248)), (353693/2251799813685248), by norm_num⟩
  | 1 => ⟨((552287220085007/562949953421312), (-12973167312567/1125899906842624)), (532641/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083418395260687/1125899906842624), (-3201995192593/140737488355328)), (2147453/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083418395260687/1125899906842624), (-3201995192593/140737488355328)), (8191883095748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083913915568987/2251799813685248), (-98597766202361/2251799813685248)), (4230571/2251799813685248), by norm_num⟩
  | 2 => ⟨((1924227749584327/2251799813685248), (-182493360008633/2251799813685248)), (8200793/2251799813685248), by norm_num⟩
  | 3 => ⟨((407379530756105/562949953421312), (-311891656895375/2251799813685248)), (3836217/562949953421312), by norm_num⟩
  | 4 => ⟨((284000923625359/562949953421312), (-451401678108645/2251799813685248)), (26459437/2251799813685248), by norm_num⟩
  | 5 => ⟨((965219831991259/4503599627370496), (-910905082981317/4503599627370496)), (9326285/562949953421312), by norm_num⟩
  | 6 => ⟨((22626623656493/4503599627370496), (-780907473046009/9007199254740992)), (15540703/1125899906842624), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1526565885/33554432)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1557363455/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1128519660374599/18014398509481984), (-485824250237605/9007199254740992)), (272672531/18014398509481984), by norm_num⟩
  | 1 => ⟨((777683581/4294967296), (334790395/2147483648)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((-561948665/2147483648), (-967668703/4294967296)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((541413517/2147483648), (466153715/2147483648)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-391221585/2147483648), (-336839383/2147483648)), (197/4294967296), by norm_num⟩
  | 5 => ⟨((56538791/536870912), (380309/4194304)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-217890833/4294967296), (-750410679/17179869184)), (223/17179869184), by norm_num⟩
  | 7 => ⟨((719754869/34359738368), (154926131/8589934592)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((-1040179573/137438953472), (-895588227/137438953472)), (271/137438953472), by norm_num⟩
  | 9 => ⟨((668112369/274877906944), (575240649/274877906944)), (11/17179869184), by norm_num⟩
  | 10 => ⟨((-772437249/1099511627776), (-332531865/549755813888)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((811865749/4398046511104), (349505713/2199023255552)), (109/2199023255552), by norm_num⟩
  | 12 => ⟨((-97774743/2199023255552), (-168366907/4398046511104)), (53/4398046511104), by norm_num⟩
  | 13 => ⟨((695643953/70368744177664), (598945173/70368744177664)), (95/35184372088832), by norm_num⟩
  | 14 => ⟨((-574477039/281474976710656), (-989242407/562949953421312)), (317/562949953421312), by norm_num⟩
  | 15 => ⟨((55348407/140737488355328), (762474217/2251799813685248)), (247/2251799813685248), by norm_num⟩
  | 16 => ⟨((-319954945/4503599627370496), (-275479243/4503599627370496)), (45/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-1583162032425/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444529227812241/158456325028528675187087900672), (-468074110755/79228162514264337593543950336)), (92569/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236126036128169/4951760157141521099596496896), (-526467736937/4951760157141521099596496896)), (26041/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944368606573407/1237940039285380274899124224), (-4473836336061/2475880078570760549798248448)), (55351/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770403123798813/154742504910672534362390528), (-69883668565/2417851639229258349412352)), (110733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387203681211715/2417851639229258349412352), (-1047914706539/2417851639229258349412352)), (25961/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629070980708463/302231454903657293676544), (-3666340586253/604462909807314587353088)), (90897/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886740448702707/75557863725914323419136), (-2977626321275/37778931862957161709568)), (147769/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648375084012573/2361183241434822606848), (-558026046919/590295810358705651712)), (110881/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620361892919019/590295810358705651712), (-6134662565899/590295810358705651712)), (152549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911057705866041/36893488147419103232), (-957861884787/9223372036854775808)), (190817/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910562905761109/4611686018427387904), (-1076661369269/1152921504606846976)), (107425/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592371851071423/1152921504606846976), (-8603965257725/1152921504606846976)), (215077/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596582869691821/72057594037927936), (-3758993780661/72057594037927936)), (188447/144115188075855872), by norm_num⟩
  | 4 => ⟨((93094335087917/2251799813685248), (-11256040683883/36028797018963968)), (283181/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486588053532637/9007199254740992), (-14033457390531/9007199254740992)), (44359/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111290160578753/2251799813685248), (-27957345095351/4503599627370496)), (712433/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103990808179811/1125899906842624), (-41662830709925/2251799813685248)), (537697/1125899906842624), by norm_num⟩
  | 0 => ⟨((541052882727131/562949953421312), (-82237335775725/2251799813685248)), (2177879/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541052882727131/562949953421312), (-82237335775725/2251799813685248)), (8307949074752043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2077026804379901/2251799813685248), (-79038549197561/1125899906842624)), (67897/35184372088832), by norm_num⟩
  | 2 => ⟨((1904721703505335/2251799813685248), (-291615949632689/2251799813685248)), (8626379/2251799813685248), by norm_num⟩
  | 3 => ⟨((1573374721941119/2251799813685248), (-493336241506005/2251799813685248)), (16827821/2251799813685248), by norm_num⟩
  | 4 => ⟨((991263679344111/2251799813685248), (-344703275613417/1125899906842624)), (30889285/2251799813685248), by norm_num⟩
  | 5 => ⟨((450592709022455/4503599627370496), (-1213933264191251/4503599627370496)), (46109519/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1128519660374599/18014398509481984), (-485824250237605/9007199254740992)), (272672531/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1557363455/33554432)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-49577983/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1403768403259773/18014398509481984), (55684361105677/4503599627370496)), (120858139/9007199254740992), by norm_num⟩
  | 1 => ⟨((492728997/2147483648), (-156363681/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-1450810465/4294967296), (230201659/4294967296)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((1423940961/4294967296), (-112969123/2147483648)), (63/1073741824), by norm_num⟩
  | 4 => ⟨((-1048176817/4294967296), (166315345/4294967296)), (47/1073741824), by norm_num⟩
  | 5 => ⟨((1234517071/8589934592), (-97941077/4294967296)), (223/8589934592), by norm_num⟩
  | 6 => ⟨((-1211653395/17179869184), (96127175/8589934592)), (221/17179869184), by norm_num⟩
  | 7 => ⟨((1019325567/34359738368), (-80868743/17179869184)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((-750335483/68719476736), (238113079/137438953472)), (279/137438953472), by norm_num⟩
  | 9 => ⟨((490959343/137438953472), (-9737631/17179869184)), (23/34359738368), by norm_num⟩
  | 10 => ⟨((-1156479861/1099511627776), (91749953/549755813888)), (219/1099511627776), by norm_num⟩
  | 11 => ⟨((619124433/2199023255552), (-98237141/2199023255552)), (59/1099511627776), by norm_num⟩
  | 12 => ⟨((-303829019/4398046511104), (192835511/17592186044416)), (117/8796093022208), by norm_num⟩
  | 13 => ⟨((550526773/35184372088832), (-21838169/8796093022208)), (107/35184372088832), by norm_num⟩
  | 14 => ⟨((-1852562845/562949953421312), (146974071/281474976710656)), (181/281474976710656), by norm_num⟩
  | 15 => ⟨((1454602201/2251799813685248), (-115401649/1125899906842624)), (143/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1070746855/9007199254740992), (169896557/9007199254740992)), (53/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (971824302341/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778041262946245/633825300114114700748351602688), (4596883996921/633825300114114700748351602688)), (92653/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944461496675455/19807040628566084398385987584), (1292582030009/9903520314283042199192993792)), (13033/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888646329129601/2475880078570760549798248448), (5492047512733/2475880078570760549798248448)), (55407/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770311950556571/154742504910672534362390528), (686305418791/19342813113834066795298816)), (27713/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548728942890997/9671406556917033397649408), (5024986895/9444732965739290427392)), (25991/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258066595456973/604462909807314587353088), (4500684603985/604462909807314587353088)), (91009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886617404485851/75557863725914323419136), (3655209497251/37778931862957161709568)), (147965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648328691384169/2361183241434822606848), (5480020809271/4722366482869645213696)), (1735/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1620233498452003/590295810358705651712), (941311362489/73786976294838206464)), (38197/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910976849287799/36893488147419103232), (587894368435/4611686018427387904)), (95573/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820942209926199/9223372036854775808), (5286374059879/4611686018427387904)), (215261/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398046540389773/288230376151711744), (10561066909219/1152921504606846976)), (53885/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193000918955765/144115188075855872), (4613900859709/72057594037927936)), (188911/144115188075855872), by norm_num⟩
  | 4 => ⟨((744628731766979/18014398509481984), (13815462788707/36028797018963968)), (283993/36028797018963968), by norm_num⟩
  | 3 => ⟨((371566262917585/2251799813685248), (17223462603701/9007199254740992)), (178045/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110955040528533/2251799813685248), (8577385718025/1125899906842624)), (178871/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103458098193945/1125899906842624), (6390201678663/281474976710656)), (135189/281474976710656), by norm_num⟩
  | 0 => ⟨((1080921813031353/1125899906842624), (50438481972427/1125899906842624)), (549077/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080921813031353/1125899906842624), (50438481972427/1125899906842624)), (2094562532665061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((258870242003285/281474976710656), (1513235519673/17592186044416)), (137935/70368744177664), by norm_num⟩
  | 2 => ⟨((1887985731341113/2251799813685248), (178138927906601/1125899906842624)), (4439121/1125899906842624), by norm_num⟩
  | 3 => ⟨((381645405412277/562949953421312), (298715500409999/1125899906842624)), (17697059/2251799813685248), by norm_num⟩
  | 4 => ⟨((876422333291787/2251799813685248), (810042864834097/2251799813685248)), (33385541/2251799813685248), by norm_num⟩
  | 5 => ⟨((24857152652655/1125899906842624), (630553083226693/2251799813685248)), (100015203/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1403768403259773/18014398509481984), (55684361105677/4503599627370496)), (120858139/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-49577983/1048576)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-403533209/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-378150514831033/9007199254740992), (565048429586357/9007199254740992)), (61742717/4503599627370496), by norm_num⟩
  | 1 => ⟨((270089555/2147483648), (-807158383/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-809115997/4294967296), (1209015209/4294967296)), (269/4294967296), by norm_num⟩
  | 3 => ⟨((807964969/4294967296), (-603647647/2147483648)), (271/4294967296), by norm_num⟩
  | 4 => ⟨((-605111683/4294967296), (904183369/4294967296)), (205/4294967296), by norm_num⟩
  | 5 => ⟨((725101039/8589934592), (-135434565/1073741824)), (31/1073741824), by norm_num⟩
  | 6 => ⟨((-90508691/2147483648), (1081935193/17179869184)), (249/17179869184), by norm_num⟩
  | 7 => ⟨((309874065/17179869184), (-926053765/34359738368)), (215/34359738368), by norm_num⟩
  | 8 => ⟨((-464149869/68719476736), (21673509/2147483648)), (163/68719476736), by norm_num⟩
  | 9 => ⟨((154496527/68719476736), (-923420877/274877906944)), (219/274877906944), by norm_num⟩
  | 10 => ⟨((-740528371/1099511627776), (1106528689/1099511627776)), (265/1099511627776), by norm_num⟩
  | 11 => ⟨((403349953/2199023255552), (-150675623/549755813888)), (291/4398046511104), by norm_num⟩
  | 12 => ⟨((-805552315/17592186044416), (1203690205/17592186044416)), (293/17592186044416), by norm_num⟩
  | 13 => ⟨((46408059/4398046511104), (-1109518029/70368744177664)), (17/4398046511104), by norm_num⟩
  | 14 => ⟨((-317773989/140737488355328), (474831281/140737488355328)), (235/281474976710656), by norm_num⟩
  | 15 => ⟨((253857545/562949953421312), (-189662319/281474976710656)), (95/562949953421312), by norm_num⟩
  | 16 => ⟨((-760489241/9007199254740992), (284088765/2251799813685248)), (287/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1407195280431/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777978508367723/633825300114114700748351602688), (1663942954045/316912650057057350374175801344)), (5783/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888852708959969/39614081257132168796771975168), (935756298397/9903520314283042199192993792)), (104115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944286034257371/1237940039285380274899124224), (496989405871/309485009821345068724781056)), (110647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885119079064051/77371252455336267181195264), (1987367735505/77371252455336267181195264)), (55337/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548660259565235/9671406556917033397649408), (3725061373461/9671406556917033397649408)), (51893/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629003497102247/302231454903657293676544), (3258175999933/604462909807314587353088)), (45421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471630370698727/18889465931478580854784), (5292188094869/75557863725914323419136)), (147673/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296586254663321/4722366482869645213696), (3967087564979/4722366482869645213696)), (110803/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810068508516817/295147905179352825856), (5451410161463/590295810358705651712)), (9527/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821835073481497/73786976294838206464), (6809262827845/73786976294838206464)), (190657/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820811469903631/9223372036854775808), (7653550706089/9223372036854775808)), (107325/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398014701491507/288230376151711744), (1911242627817/288230376151711744)), (214851/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596446640284979/72057594037927936), (6679706475349/144115188075855872)), (94111/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489103577192189/36028797018963968), (5000149623599/18014398509481984)), (141393/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486085888871133/9007199254740992), (6233362202115/4503599627370496)), (354279/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110795561577561/2251799813685248), (3104090535369/562949953421312)), (355475/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206535418936089/2251799813685248), (36998059731467/2251799813685248)), (1072425/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080734083130019/1125899906842624), (72996713077307/2251799813685248)), (1084477/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080734083130019/1125899906842624), (72996713077307/2251799813685248)), (4136951450828170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2072393862577933/2251799813685248), (70068427308375/1125899906842624)), (4304515/2251799813685248), by norm_num⟩
  | 2 => ⟨((949280206359051/1125899906842624), (128971836512161/1125899906842624)), (8458899/2251799813685248), by norm_num⟩
  | 3 => ⟨((49099567499087/70368744177664), (434960197917071/2251799813685248)), (16201841/2251799813685248), by norm_num⟩
  | 4 => ⟨((1012272743633105/2251799813685248), (606984190115027/2251799813685248)), (28868699/2251799813685248), by norm_num⟩
  | 5 => ⟨((582881565638703/4503599627370496), (545726620755055/2251799813685248)), (5189831/281474976710656), by norm_num⟩
  | 6 => ⟨((-378150514831033/9007199254740992), (565048429586357/9007199254740992)), (61742717/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-403533209/8388608)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-820210751/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((250946630420845/18014398509481984), (1279405466881265/18014398509481984)), (198396167/18014398509481984), by norm_num⟩
  | 1 => ⟨((-91077405/2147483648), (-928682959/4294967296)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((277287203/4294967296), (1413698053/4294967296)), (7/134217728), by norm_num⟩
  | 3 => ⟨((-140701185/2147483648), (-1434678481/4294967296)), (229/4294967296), by norm_num⟩
  | 4 => ⟨((214183957/4294967296), (1091977707/4294967296)), (11/268435456), by norm_num⟩
  | 5 => ⟨((-260835145/8589934592), (-332455063/2147483648)), (27/1073741824), by norm_num⟩
  | 6 => ⟨((264706151/17179869184), (1349555865/17179869184)), (221/17179869184), by norm_num⟩
  | 7 => ⟨((-230258233/34359738368), (-1173929461/34359738368)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((175256589/68719476736), (446756823/34359738368)), (149/68719476736), by norm_num⟩
  | 9 => ⟨((-118571693/137438953472), (-1209032153/274877906944)), (203/274877906944), by norm_num⟩
  | 10 => ⟨((18049709/68719476736), (1472370207/1099511627776)), (249/1099511627776), by norm_num⟩
  | 11 => ⟨((-624463/8589934592), (-1630059685/4398046511104)), (139/2199023255552), by norm_num⟩
  | 12 => ⟨((81117509/4398046511104), (206781387/2199023255552)), (285/17592186044416), by norm_num⟩
  | 13 => ⟨((-151977893/35184372088832), (-387415737/17592186044416)), (269/70368744177664), by norm_num⟩
  | 14 => ⟨((66100015/70368744177664), (1347995319/281474976710656)), (59/70368744177664), by norm_num⟩
  | 15 => ⟨((-214659177/1125899906842624), (-273600133/281474976710656)), (193/1125899906842624), by norm_num⟩
  | 16 => ⟨((81691835/2251799813685248), (52061359/281474976710656)), (37/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (1793842139425/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888958609590207/316912650057057350374175801344), (2120987440677/633825300114114700748351602688)), (92409/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944391984479279/19807040628566084398385987584), (1192784004351/19807040628566084398385987584)), (51987/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472124827830109/618970019642690137449562112), (633496779909/618970019642690137449562112)), (13811/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885082857276117/77371252455336267181195264), (79163240699/4835703278458516698824704)), (110505/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548592676680611/9671406556917033397649408), (2374086386133/9671406556917033397649408)), (103617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257948191864779/604462909807314587353088), (1038257543043/302231454903657293676544)), (90685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886426552174113/75557863725914323419136), (843204507873/18889465931478580854784)), (36849/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296515601379871/4722366482869645213696), (2528285120247/4722366482869645213696)), (55289/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620040752750609/590295810358705651712), (1737117354975/295147905179352825856)), (76047/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821716067130315/73786976294838206464), (4339559709313/73786976294838206464)), (11887/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1820679405064401/9223372036854775808), (1219390532179/2305843009213693952)), (214069/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198991125996079/144115188075855872), (1218003647097/288230376151711744)), (214197/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596391125471155/72057594037927936), (4256779529265/144115188075855872)), (11723/9007199254740992), by norm_num⟩
  | 4 => ⟨((2908090046051/70368744177664), (3186361083951/18014398509481984)), (281641/36028797018963968), by norm_num⟩
  | 3 => ⟨((742946441977209/4503599627370496), (3972081851279/4503599627370496)), (22035/562949953421312), by norm_num⟩
  | 2 => ⟨((2221231477643665/4503599627370496), (3955820979781/1125899906842624)), (706649/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206061348872303/2251799813685248), (23572923116429/2251799813685248)), (531905/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160778557950443/2251799813685248), (46501459535829/2251799813685248)), (267881/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160778557950443/2251799813685248), (46501459535829/2251799813685248)), (1021884919286632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((518119057741843/562949953421312), (22310899056781/562949953421312)), (4201357/2251799813685248), by norm_num⟩
  | 2 => ⟨((951948144413611/1125899906842624), (164273245625747/2251799813685248)), (504161/140737488355328), by norm_num⟩
  | 3 => ⟨((798879935400099/1125899906842624), (2170203063787/17592186044416)), (14817523/2251799813685248), by norm_num⟩
  | 4 => ⟨((1099419021287193/2251799813685248), (98551236271945/562949953421312)), (12341659/1125899906842624), by norm_num⟩
  | 5 => ⟨((935540219192559/4503599627370496), (769866685805771/4503599627370496)), (65490007/4503599627370496), by norm_num⟩
  | 6 => ⟨((250946630420845/18014398509481984), (1279405466881265/18014398509481984)), (198396167/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-820210751/16777216)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile004Terms2
