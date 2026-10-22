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
namespace Reinmann.XiBand97.Tile058Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨58,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78877/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78877/2560))
  have he : value ((69/80), (78877/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/1073741824), (-5732918379/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-339157611966481/4503599627370496), (234096984953265/4503599627370496)), (4689641/9007199254740992), by norm_num⟩
  | 1 => ⟨((57394077759/274877906944), (-9903788153/68719476736)), (399/274877906944), by norm_num⟩
  | 2 => ⟨((-79565086359/274877906944), (54918262681/274877906944)), (555/274877906944), by norm_num⟩
  | 3 => ⟨((73533753707/274877906944), (-25377625959/137438953472)), (515/274877906944), by norm_num⟩
  | 4 => ⟨((-25484857029/137438953472), (35180859765/274877906944)), (359/274877906944), by norm_num⟩
  | 5 => ⟨((56527221749/549755813888), (-39016822009/549755813888)), (25/34359738368), by norm_num⟩
  | 6 => ⟨((-3265140365/68719476736), (36059200227/1099511627776)), (93/274877906944), by norm_num⟩
  | 7 => ⟨((41384646183/2199023255552), (-14282475983/1099511627776)), (37/274877906944), by norm_num⟩
  | 8 => ⟨((-7171412705/1099511627776), (9899857959/2199023255552)), (103/2199023255552), by norm_num⟩
  | 9 => ⟨((35348227535/17592186044416), (-48796861385/35184372088832)), (255/17592186044416), by norm_num⟩
  | 10 => ⟨((-19601219403/35184372088832), (54117451023/140737488355328)), (71/17592186044416), by norm_num⟩
  | 11 => ⟨((79048901613/562949953421312), (-54561976139/562949953421312)), (575/562949953421312), by norm_num⟩
  | 12 => ⟨((-36528348853/1125899906842624), (50425973235/2251799813685248)), (267/1125899906842624), by norm_num⟩
  | 13 => ⟨((62324977275/9007199254740992), (-43018610677/9007199254740992)), (229/4503599627370496), by norm_num⟩
  | 14 => ⟨((-49371865459/36028797018963968), (8519493915/9007199254740992)), (365/36028797018963968), by norm_num⟩
  | 15 => ⟨((73006867929/288230376151711744), (-50391579195/288230376151711744)), (271/144115188075855872), by norm_num⟩
  | 16 => ⟨((-25302252333/576460752303423488), (34928781043/1152921504606846976)), (189/576460752303423488), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (3305316392729/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778272747031913/633825300114114700748351602688), (1954812668683/316912650057057350374175801344)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889183527430361/39614081257132168796771975168), (4397397419511/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236115413456169/309485009821345068724781056), (4671093222153/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770589109997675/154742504910672534362390528), (2334904618811/77371252455336267181195264)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774494485939871/4835703278458516698824704), (547072780127/1208925819614629174706176)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314573578147919/151115727451828646838272), (3828145894787/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943493901940629/37778931862957161709568), (6218181143109/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648467747984471/2361183241434822606848), (4661400164001/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620616412823883/590295810358705651712), (3202896815685/295147905179352825856)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((7118879308327/288230376151711744), (8001797111517/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821482583995965/9223372036854775808), (8994538978663/9223372036854775808)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592727836729587/1152921504606846976), (8985191520639/1152921504606846976)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596738171412161/72057594037927936), (3925767475593/72057594037927936)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489973501440441/36028797018963968), (11756307825251/36028797018963968)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487165146111445/9007199254740992), (14658690721079/9007199254740992)), (5549/4503599627370496), by norm_num⟩
  | 2 => ⟨((34745707577501/70368744177664), (1825467830983/281474976710656)), (5571/1125899906842624), by norm_num⟩
  | 1 => ⟨((552419024947219/562949953421312), (21768569496337/1125899906842624)), (8411/562949953421312), by norm_num⟩
  | 0 => ⟨((67734662351781/70368744177664), (21495458239433/562949953421312)), (34085/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((67734662351781/70368744177664), (21495458239433/562949953421312)), (130023960593795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2083090693682995/2251799813685248), (165526626681731/2251799813685248)), (136443/2251799813685248), by norm_num⟩
  | 2 => ⟨((478713488179857/562949953421312), (153125057343863/1125899906842624)), (272501/2251799813685248), by norm_num⟩
  | 3 => ⟨((793337956994427/1125899906842624), (520849357093463/2251799813685248)), (268787/1125899906842624), by norm_num⟩
  | 4 => ⟨((997538231238911/2251799813685248), (91750954580225/281474976710656)), (1006263/2251799813685248), by norm_num⟩
  | 5 => ⟨((405289412816833/4503599627370496), (1300649684970371/4503599627370496)), (773777/1125899906842624), by norm_num⟩
  | 6 => ⟨((-339157611966481/4503599627370496), (234096984953265/4503599627370496)), (4689641/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-5732918379/67108864)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-11716545423/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1226696290175585/18014398509481984), (970913805536019/18014398509481984)), (5206375/18014398509481984), by norm_num⟩
  | 1 => ⟨((-26515901935/137438953472), (-41973967739/274877906944)), (227/274877906944), by norm_num⟩
  | 2 => ⟨((9390650899/34359738368), (29730301375/137438953472)), (81/68719476736), by norm_num⟩
  | 3 => ⟨((-35474289915/137438953472), (-56154857719/274877906944)), (77/68719476736), by norm_num⟩
  | 4 => ⟨((50253115779/274877906944), (1242958533/8589934592)), (55/68719476736), by norm_num⟩
  | 5 => ⟨((-28475559641/274877906944), (-45076053783/549755813888)), (251/549755813888), by norm_num⟩
  | 6 => ⟨((53784890369/1099511627776), (10642506423/274877906944)), (239/1099511627776), by norm_num⟩
  | 7 => ⟨((-21769152729/1099511627776), (-8614997489/549755813888)), (195/2199023255552), by norm_num⟩
  | 8 => ⟨((3854790875/549755813888), (48816251689/8796093022208)), (279/8796093022208), by norm_num⟩
  | 9 => ⟨((-38831804251/17592186044416), (-7683714205/4398046511104)), (177/17592186044416), by norm_num⟩
  | 10 => ⟨((44007514391/70368744177664), (8707840647/17592186044416)), (101/35184372088832), by norm_num⟩
  | 11 => ⟨((-45339155277/281474976710656), (-17942669323/140737488355328)), (105/140737488355328), by norm_num⟩
  | 12 => ⟨((42818499913/1125899906842624), (8472568359/281474976710656)), (25/140737488355328), by norm_num⟩
  | 13 => ⟨((-74654735585/9007199254740992), (-59088230727/9007199254740992)), (351/9007199254740992), by norm_num⟩
  | 14 => ⟨((60432226587/36028797018963968), (47831303935/36028797018963968)), (143/18014398509481984), by norm_num⟩
  | 15 => ⟨((-22828985437/72057594037927936), (-4517209619/18014398509481984)), (109/72057594037927936), by norm_num⟩
  | 16 => ⟨((64679386171/1152921504606846976), (25596437141/576460752303423488)), (311/1152921504606846976), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (436067687805/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889099903006887/316912650057057350374175801344), (1031498276963/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944550955356965/19807040628566084398385987584), (1160189933499/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888837172722015/2475880078570760549798248448), (616197321095/1237940039285380274899124224)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770503630143315/154742504910672534362390528), (1232049239491/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774454765015663/4835703278458516698824704), (288669826325/2417851639229258349412352)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258225495926785/604462909807314587353088), (252494421455/151115727451828646838272)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886877278641931/75557863725914323419136), (205065810571/9444732965739290427392)), (4599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324213434989111/1180591620717411303424), (1229793834685/4722366482869645213696)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620505845184773/590295810358705651712), (844995224645/295147905179352825856)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911148829894217/36893488147419103232), (263878124727/9223372036854775808)), (5931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821334007917553/9223372036854775808), (2372893108721/9223372036854775808)), (3337/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398145999489855/288230376151711744), (2370383137427/1152921504606846976)), (1669/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193355800308235/144115188075855872), (129454064027/9007199254740992)), (1461/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489803287875219/36028797018963968), (1550632912871/18014398509481984)), (4385/18014398509481984), by norm_num⟩
  | 3 => ⟨((743485428150795/4503599627370496), (483343300081/1125899906842624)), (5485/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111695922317379/2251799813685248), (1926015862323/1125899906842624)), (10981/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209312768307909/2251799813685248), (5741397555003/1125899906842624)), (16501/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167323759147761/2251799813685248), (22674024210695/2251799813685248)), (1035/35184372088832), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167323759147761/2251799813685248), (22674024210695/2251799813685248)), (3948211804139603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2085788504398989/2251799813685248), (10911705181045/562949953421312)), (128845/2251799813685248), by norm_num⟩
  | 2 => ⟨((120698135933729/140737488355328), (80858019764259/2251799813685248)), (30461/281474976710656), by norm_num⟩
  | 3 => ⟨((206661367197841/281474976710656), (34672397436135/562949953421312)), (435481/2251799813685248), by norm_num⟩
  | 4 => ⟨((37666205182497/70368744177664), (50913549345769/562949953421312)), (86639/281474976710656), by norm_num⟩
  | 5 => ⟨((626751012443191/2251799813685248), (436039089487831/4503599627370496)), (433687/1125899906842624), by norm_num⟩
  | 6 => ⟨((1226696290175585/18014398509481984), (970913805536019/18014398509481984)), (5206375/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-11716545423/134217728)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-373528745/4194304)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((686612777307223/18014398509481984), (-330361575244287/4503599627370496)), (3135389/9007199254740992), by norm_num⟩
  | 1 => ⟨((-30282076723/274877906944), (14570125839/68719476736)), (139/137438953472), by norm_num⟩
  | 2 => ⟨((43763229665/274877906944), (-21056540117/68719476736)), (101/68719476736), by norm_num⟩
  | 3 => ⟨((-10541000255/68719476736), (81148305165/274877906944)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((30467409437/274877906944), (-58637192363/274877906944)), (285/274877906944), by norm_num⟩
  | 5 => ⟨((-35224855909/549755813888), (16948328477/137438953472)), (83/137438953472), by norm_num⟩
  | 6 => ⟨((33937642899/1099511627776), (-65315959965/1099511627776)), (161/549755813888), by norm_num⟩
  | 7 => ⟨((-3503300163/274877906944), (3371203679/137438953472)), (67/549755813888), by norm_num⟩
  | 8 => ⟨((20251679701/4398046511104), (-304500997/34359738368)), (195/4398046511104), by norm_num⟩
  | 9 => ⟨((-26015503581/17592186044416), (25034555221/8796093022208)), (63/4398046511104), by norm_num⟩
  | 10 => ⟨((30077790727/70368744177664), (-28943668553/35184372088832)), (293/70368744177664), by norm_num⟩
  | 11 => ⟨((-15806544883/140737488355328), (60842154295/281474976710656)), (155/140737488355328), by norm_num⟩
  | 12 => ⟨((30457860613/1125899906842624), (-29309407411/562949953421312)), (301/1125899906842624), by norm_num⟩
  | 13 => ⟨((-27087550807/4503599627370496), (52132359029/4503599627370496)), (269/4503599627370496), by norm_num⟩
  | 14 => ⟨((44738909625/36028797018963968), (-86103941835/36028797018963968)), (447/36028797018963968), by norm_num⟩
  | 15 => ⟨((-34483221563/144115188075855872), (66365973793/144115188075855872)), (347/144115188075855872), by norm_num⟩
  | 16 => ⟨((1557333277/36028797018963968), (-11988896021/144115188075855872)), (63/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-355482177549/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444530727902363/158456325028528675187087900672), (-840808461737/316912650057057350374175801344)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889015370629489/39614081257132168796771975168), (-1891409992083/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944372588692611/1237940039285380274899124224), (-2009112161051/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770411582570785/154742504910672534362390528), (-125533598957/9671406556917033397649408)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548823179985277/9671406556917033397649408), (-1882393713391/9671406556917033397649408)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629074942125067/302231454903657293676544), (-1646484473427/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886754305946289/75557863725914323419136), (-1337196995863/37778931862957161709568)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81047588737937/295147905179352825856), (-2004795646407/4722366482869645213696)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620378757949413/590295810358705651712), (-344371279651/73786976294838206464)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911069290309641/36893488147419103232), (-3441278837467/73786976294838206464)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821154741861789/9223372036854775808), (-3868094768443/9223372036854775808)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796202177718005/576460752303423488), (-1931959507595/576460752303423488)), (6687/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298299547743675/36028797018963968), (-3376237118217/144115188075855872)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489566033117537/36028797018963968), (-5054985875583/36028797018963968)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((743336412184481/4503599627370496), (-98474487187/140737488355328)), (10999/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222791421567707/4503599627370496), (-12555766581487/4503599627370496)), (11017/2251799813685248), by norm_num⟩
  | 1 => ⟨((276050168078061/281474976710656), (-9355838177469/1125899906842624)), (33147/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165458405231355/2251799813685248), (-36938125639819/2251799813685248)), (66675/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165458405231355/2251799813685248), (-36938125639819/2251799813685248)), (254344948775481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1040910841889917/1125899906842624), (-17760898227745/562949953421312)), (130425/2251799813685248), by norm_num⟩
  | 2 => ⟨((961216513264907/1125899906842624), (-8210104386103/140737488355328)), (124695/1125899906842624), by norm_num⟩
  | 3 => ⟨((1633578984572601/2251799813685248), (-112147630368765/1125899906842624)), (227461/1125899906842624), by norm_num⟩
  | 4 => ⟨((1162746314719213/2251799813685248), (-325432147256831/2251799813685248)), (750679/2251799813685248), by norm_num⟩
  | 5 => ⟨((1106735067968251/4503599627370496), (-168041149845717/1125899906842624)), (31007/70368744177664), by norm_num⟩
  | 6 => ⟨((686612777307223/18014398509481984), (-330361575244287/4503599627370496)), (3135389/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-373528745/4194304)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-2726851779/1073741824), (-48706043429/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1317759795071787/18014398509481984), (-532622577762225/18014398509481984)), (494949/1125899906842624), by norm_num⟩
  | 1 => ⟨((14801266883/68719476736), (23929972521/274877906944)), (179/137438953472), by norm_num⟩
  | 2 => ⟨((-87162854303/274877906944), (-35230171931/274877906944)), (529/274877906944), by norm_num⟩
  | 3 => ⟨((42774284291/137438953472), (34577697159/274877906944)), (521/274877906944), by norm_num⟩
  | 4 => ⟨((-31486567493/137438953472), (-25452979831/274877906944)), (193/137438953472), by norm_num⟩
  | 5 => ⟨((74168221317/549755813888), (7494474595/137438953472)), (457/549755813888), by norm_num⟩
  | 6 => ⟨((-72794600621/1099511627776), (-29422697501/1099511627776)), (451/1099511627776), by norm_num⟩
  | 7 => ⟨((61239788441/2199023255552), (24752382113/2199023255552)), (191/1099511627776), by norm_num⟩
  | 8 => ⟨((-90158410081/8796093022208), (-1138779355/274877906944)), (565/8796093022208), by norm_num⟩
  | 9 => ⟨((1843513451/549755813888), (23844027175/17592186044416)), (93/4398046511104), by norm_num⟩
  | 10 => ⟨((-4342490291/4398046511104), (-14041456607/35184372088832)), (55/8796093022208), by norm_num⟩
  | 11 => ⟨((74392422863/281474976710656), (30068517933/281474976710656)), (473/281474976710656), by norm_num⟩
  | 12 => ⟨((-36507324939/562949953421312), (-29511638749/1125899906842624)), (233/562949953421312), by norm_num⟩
  | 13 => ⟨((66149901893/4503599627370496), (26736990607/4503599627370496)), (53/562949953421312), by norm_num⟩
  | 14 => ⟨((-13912453543/4503599627370496), (-11246491047/9007199254740992)), (179/9007199254740992), by norm_num⟩
  | 15 => ⟨((21847664271/36028797018963968), (35322247059/144115188075855872)), (141/36028797018963968), by norm_num⟩
  | 16 => ⟨((-64329114283/576460752303423488), (-6500262567/144115188075855872)), (417/576460752303423488), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (-224495448589/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778042919124009/633825300114114700748351602688), (-1061899288287/158456325028528675187087900672)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472231236934999/9903520314283042199192993792), (-149296047059/1237940039285380274899124224)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888648527082527/2475880078570760549798248448), (-5074748359481/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885157142485893/77371252455336267181195264), (-5073266740695/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774365638141443/4835703278458516698824704), (-4754613724203/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258068781924873/604462909807314587353088), (-2079356792217/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117913826789459/4722366482869645213696), (-1688740074727/18889465931478580854784)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296660487849769/4722366482869645213696), (-2531820251331/2361183241434822606848)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810119076255617/295147905179352825856), (-6958315321753/590295810358705651712)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910980046060037/36893488147419103232), (-4345805767645/36893488147419103232)), (2985/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820950193181259/9223372036854775808), (-9769429153055/9223372036854775808)), (3361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398048782700061/288230376151711744), (-2439661008993/288230376151711744)), (6731/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193009873308147/144115188075855872), (-4263345063591/72057594037927936)), (5899/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489273100184743/36028797018963968), (-6382906511327/18014398509481984)), (4433/18014398509481984), by norm_num⟩
  | 3 => ⟨((743144219899963/4503599627370496), (-15914932950785/9007199254740992)), (11113/9007199254740992), by norm_num⟩
  | 2 => ⟨((277746039725405/562949953421312), (-7925771978067/1125899906842624)), (11161/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103515985347385/1125899906842624), (-2952404027061/140737488355328)), (16861/1125899906842624), by norm_num⟩
  | 0 => ⟨((270273432991553/281474976710656), (-5826058047419/140737488355328)), (34201/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((270273432991553/281474976710656), (-5826058047419/140737488355328)), (130466465476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036141224681613/1125899906842624), (-179014558544167/2251799813685248)), (2141/35184372088832), by norm_num⟩
  | 2 => ⟨((473211285464191/562949953421312), (-329486418461385/2251799813685248)), (68497/562949953421312), by norm_num⟩
  | 3 => ⟨((192862472164781/281474976710656), (-276963681541361/1125899906842624)), (270403/1125899906842624), by norm_num⟩
  | 4 => ⟨((920909659319645/2251799813685248), (-379542799478301/1125899906842624)), (1007175/2251799813685248), by norm_num⟩
  | 5 => ⟨((241463430659047/4503599627370496), (-1241760934664123/4503599627370496)), (751421/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1317759795071787/18014398509481984), (-532622577762225/18014398509481984)), (494949/1125899906842624), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-48706043429/536870912)), (1/536870912), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-1387177309/536870912), (-1548578813/16777216)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-497423378950239/18014398509481984), (632787515940203/9007199254740992)), (3756243/9007199254740992), by norm_num⟩
  | 1 => ⟨((1421115179/17179869184), (-57851012689/274877906944)), (345/274877906944), by norm_num⟩
  | 2 => ⟨((-34058244849/274877906944), (86653072885/274877906944)), (519/274877906944), by norm_num⟩
  | 3 => ⟨((34009794425/274877906944), (-21632450587/68719476736)), (65/34359738368), by norm_num⟩
  | 4 => ⟨((-12735529847/137438953472), (16201257595/68719476736)), (391/274877906944), by norm_num⟩
  | 5 => ⟨((30521790227/549755813888), (-77655408399/549755813888)), (471/549755813888), by norm_num⟩
  | 6 => ⟨((-30478370677/1099511627776), (77544937719/1099511627776)), (59/137438953472), by norm_num⟩
  | 7 => ⟨((26087153909/2199023255552), (-33186267511/1099511627776)), (203/1099511627776), by norm_num⟩
  | 8 => ⟨((-19537532223/4398046511104), (49708586311/4398046511104)), (153/2199023255552), by norm_num⟩
  | 9 => ⟨((6503246203/4398046511104), (-16545957365/4398046511104)), (409/17592186044416), by norm_num⟩
  | 10 => ⟨((-31171175253/70368744177664), (9913451695/8796093022208)), (123/17592186044416), by norm_num⟩
  | 11 => ⟨((33956543895/281474976710656), (-21598579771/70368744177664)), (269/140737488355328), by norm_num⟩
  | 12 => ⟨((-8477059537/281474976710656), (21567854161/281474976710656)), (539/1125899906842624), by norm_num⟩
  | 13 => ⟨((31255385649/4503599627370496), (-9940233351/562949953421312)), (249/2251799813685248), by norm_num⟩
  | 14 => ⟨((-26752219289/18014398509481984), (17016158775/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 15 => ⟨((10685664895/36028797018963968), (-54374246415/72057594037927936)), (43/9007199254740992), by norm_num⟩
  | 16 => ⟨((-16005695595/288230376151711744), (40722671209/288230376151711744)), (517/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (316744604295/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444494908203209/158456325028528675187087900672), (2996286072773/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472213508931565/9903520314283042199192993792), (3370061857885/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888573560628119/2475880078570760549798248448), (1789873237819/1237940039285380274899124224)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770239742870359/154742504910672534362390528), (1789342284501/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548661843601167/9671406556917033397649408), (419236108775/1208925819614629174706176)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157251059811013/75557863725914323419136), (2933525255927/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235815509848991/9444732965739290427392), (2382432667141/37778931862957161709568)), (2307/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324147090626547/1180591620717411303424), (892950202717/1180591620717411303424)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202517522042675/73786976294838206464), (2454112214741/295147905179352825856)), (2381/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821839413540929/73786976294838206464), (383173802987/4611686018427387904)), (5955/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910408444500073/4611686018427387904), (6890945992695/9223372036854775808)), (419/576460752303423488), by norm_num⟩
  | 6 => ⟨((796032447119339/576460752303423488), (3441612414789/576460752303423488)), (6709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298224839647875/36028797018963968), (6014144916785/144115188075855872)), (5877/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489114190698923/36028797018963968), (9003887486693/36028797018963968)), (8829/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486101763153373/9007199254740992), (5612292696807/4503599627370496)), (11057/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110815324156417/2251799813685248), (11179280997261/2251799813685248)), (22181/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103306994547285/1125899906842624), (33312065700389/2251799813685248)), (1045/70368744177664), by norm_num⟩
  | 0 => ⟨((270212685786373/281474976710656), (65725481053653/2251799813685248)), (33779/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((270212685786373/281474976710656), (65725481053653/2251799813685248)), (128856663230514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((518322437967113/562949953421312), (15773923287651/281474976710656)), (133655/2251799813685248), by norm_num⟩
  | 2 => ⟨((950929586013533/1125899906842624), (116187640838369/1125899906842624)), (65275/562949953421312), by norm_num⟩
  | 3 => ⟨((1582320958121889/2251799813685248), (98131516425965/562949953421312)), (247469/1125899906842624), by norm_num⟩
  | 4 => ⟨((1043459941676349/2251799813685248), (275824794281275/1125899906842624)), (868131/2251799813685248), by norm_num⟩
  | 5 => ⟨((174192078832731/1125899906842624), (63907129311509/281474976710656)), (614959/1125899906842624), by norm_num⟩
  | 6 => ⟨((-497423378950239/18014398509481984), (632787515940203/9007199254740992)), (3756243/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-1548578813/16777216)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2819539303/1073741824), (-50361594559/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((589243884820009/9007199254740992), (278845438662061/9007199254740992)), (1857387/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6843438067/34359738368), (-3238491801/34359738368)), (87/137438953472), by norm_num⟩
  | 2 => ⟨((83340002985/274877906944), (19719321905/137438953472)), (267/274877906944), by norm_num⟩
  | 3 => ⟨((-42288418175/137438953472), (-40023945331/274877906944)), (273/274877906944), by norm_num⟩
  | 4 => ⟨((64374018995/274877906944), (15231724951/137438953472)), (209/274877906944), by norm_num⟩
  | 5 => ⟨((-78395258095/549755813888), (-37098662703/549755813888)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((79558707427/1099511627776), (37649237003/1099511627776)), (131/549755813888), by norm_num⟩
  | 7 => ⟨((-69205219965/2199023255552), (-32749699091/2199023255552)), (115/1099511627776), by norm_num⟩
  | 8 => ⟨((3292138203/274877906944), (6231699607/1099511627776)), (11/274877906944), by norm_num⟩
  | 9 => ⟨((-71274585793/17592186044416), (-2108061031/1099511627776)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((86798830275/70368744177664), (20537725149/35184372088832)), (295/70368744177664), by norm_num⟩
  | 11 => ⟨((-24023726031/70368744177664), (-22737296377/140737488355328)), (165/140737488355328), by norm_num⟩
  | 12 => ⟨((48760515293/562949953421312), (23074736331/562949953421312)), (169/562949953421312), by norm_num⟩
  | 13 => ⟨((-91355374083/4503599627370496), (-21615862309/2251799813685248)), (319/4503599627370496), by norm_num⟩
  | 14 => ⟨((9933338793/2251799813685248), (18802850803/9007199254740992)), (279/18014398509481984), by norm_num⟩
  | 15 => ⟨((-64516848719/72057594037927936), (-7632760155/18014398509481984)), (229/72057594037927936), by norm_num⟩
  | 16 => ⟨((1534554637/9007199254740992), (11619054777/144115188075855872)), (11/18014398509481984), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (143938520577/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777919383075017/633825300114114700748351602688), (680755095803/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472196630484241/9903520314283042199192993792), (765676179041/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502182462471/2475880078570760549798248448), (203328287511/618970019642690137449562112)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885084381957849/77371252455336267181195264), (406534129739/77371252455336267181195264)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548595724666839/9671406556917033397649408), (761991400433/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257951047889205/604462909807314587353088), (666482498935/604462909807314587353088)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886431547293029/75557863725914323419136), (135318356515/9444732965739290427392)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324129914293631/1180591620717411303424), (811484078559/4722366482869645213696)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405011707912957/147573952589676412928), (1115098722541/590295810358705651712)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455431104460197/18446744073709551616), (696418192195/36893488147419103232)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820689831795565/9223372036854775808), (782758172883/4611686018427387904)), (6669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591940722031173/1152921504606846976), (1563737581637/1152921504606846976)), (6671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192793945019921/144115188075855872), (683135989327/72057594037927936)), (2919/72057594037927936), by norm_num⟩
  | 4 => ⟨((744481261662081/18014398509481984), (1022708954235/18014398509481984)), (8759/36028797018963968), by norm_num⟩
  | 3 => ⟨((742961711992763/4503599627370496), (159362809011/562949953421312)), (10955/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221307515027683/4503599627370496), (2539384039859/2251799813685248)), (5481/1125899906842624), by norm_num⟩
  | 1 => ⟨((2206212489018173/2251799813685248), (3783129397453/1125899906842624)), (32925/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080613664734247/1125899906842624), (932887914043/140737488355328)), (66009/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080613664734247/1125899906842624), (932887914043/140737488355328)), (251804360396575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129637433510169/140737488355328), (1790730102123/140737488355328)), (3987/70368744177664), by norm_num⟩
  | 2 => ⟨((955120495564463/1125899906842624), (52783810712897/2251799813685248)), (238291/2251799813685248), by norm_num⟩
  | 3 => ⟨((101203337752205/140737488355328), (44777425719185/1125899906842624)), (415465/2251799813685248), by norm_num⟩
  | 4 => ⟨((290208025950777/562949953421312), (8049782953515/140737488355328)), (630563/2251799813685248), by norm_num⟩
  | 5 => ⟨((295528629964777/1125899906842624), (132792571336711/2251799813685248)), (180565/562949953421312), by norm_num⟩
  | 6 => ⟨((589243884820009/9007199254740992), (278845438662061/9007199254740992)), (1857387/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-50361594559/536870912)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile058Terms2
