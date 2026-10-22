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
namespace Reinmann.XiBand97.Tile019Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5507/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5507/256))
  have he : value ((69/80), (5507/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-2001291981/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-823292472892675/9007199254740992), (-77630707764927/18014398509481984)), (135379683/9007199254740992), by norm_num⟩
  | 1 => ⟨((1088453019/4294967296), (6414593/536870912)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((-1508916283/4294967296), (-71140113/4294967296)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((348633689/1073741824), (65747425/4294967296)), (235/4294967296), by norm_num⟩
  | 4 => ⟨((-1933235669/8589934592), (-91145285/8589934592)), (41/1073741824), by norm_num⟩
  | 5 => ⟨((1072013483/8589934592), (25270839/4294967296)), (23/1073741824), by norm_num⟩
  | 6 => ⟨((-990750831/17179869184), (-46710429/17179869184)), (343/34359738368), by norm_num⟩
  | 7 => ⟨((784841309/34359738368), (37002517/34359738368)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((-1088021081/137438953472), (-51296381/137438953472)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((1340726657/549755813888), (63210563/549755813888)), (239/549755813888), by norm_num⟩
  | 10 => ⟨((-371728361/549755813888), (-35051379/1099511627776)), (267/2199023255552), by norm_num⟩
  | 11 => ⟨((1499127071/8796093022208), (17669647/2199023255552)), (271/8796093022208), by norm_num⟩
  | 12 => ⟨((-346371901/8796093022208), (-65320885/35184372088832)), (253/35184372088832), by norm_num⟩
  | 13 => ⟨((1181965325/140737488355328), (55725523/140737488355328)), (217/140737488355328), by norm_num⟩
  | 14 => ⟨((-1872630703/1125899906842624), (-88287975/1125899906842624)), (173/562949953421312), by norm_num⟩
  | 15 => ⟨((1384542605/4503599627370496), (16319083/1125899906842624)), (129/2251799813685248), by norm_num⟩
  | 16 => ⟨((-959691803/18014398509481984), (-90492211/36028797018963968)), (45/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-1007726765447/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778268756319623/633825300114114700748351602688), (-1191968824515/158456325028528675187087900672)), (46335/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889178816418731/39614081257132168796771975168), (-670339021455/4951760157141521099596496896)), (26071/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888918009439753/2475880078570760549798248448), (-1424122039711/618970019642690137449562112)), (27709/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770583482716873/154742504910672534362390528), (-2847460270801/77371252455336267181195264)), (27719/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774491673461877/4835703278458516698824704), (-5337322688881/9671406556917033397649408)), (25997/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258289041664805/604462909807314587353088), (-72945192841/9444732965739290427392)), (91031/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235872323087041/9444732965739290427392), (-3791589407375/37778931862957161709568)), (37001/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20264500156375/73786976294838206464), (-5684653680777/4722366482869645213696)), (3471/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810302595988015/295147905179352825856), (-7811963091733/590295810358705651712)), (152835/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911208843705863/36893488147419103232), (-4879151220093/36893488147419103232)), (191211/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455365833575987/2305843009213693952), (-342779626307/288230376151711744)), (215343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592706207907231/1152921504606846976), (-342422673525/36028797018963968)), (215631/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298363686956927/36028797018963968), (-9574991810031/144115188075855872)), (94501/72057594037927936), by norm_num⟩
  | 4 => ⟨((372483946558513/9007199254740992), (-14336819781759/36028797018963968)), (284153/36028797018963968), by norm_num⟩
  | 3 => ⟨((743554362601271/4503599627370496), (-17876146809891/9007199254740992)), (356331/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111792381778399/2251799813685248), (-17808912106773/2251799813685248)), (89511/562949953421312), by norm_num⟩
  | 1 => ⟨((69043645201929/70368744177664), (-6636392521365/281474976710656)), (270679/562949953421312), by norm_num⟩
  | 0 => ⟨((541669690196925/562949953421312), (-52421688534483/1125899906842624)), (1099957/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((541669690196925/562949953421312), (-52421688534483/1125899906842624)), (4196002964500045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039946954935655/1125899906842624), (-25220039201977/281474976710656)), (2219183/1125899906842624), by norm_num⟩
  | 2 => ⟨((475758482850687/562949953421312), (-93178808567465/562949953421312)), (4497211/1125899906842624), by norm_num⟩
  | 3 => ⟨((1546594629348413/2251799813685248), (-157493959555281/562949953421312)), (2272521/281474976710656), by norm_num⟩
  | 4 => ⟨((885995894777979/2251799813685248), (-432683776812961/1125899906842624)), (35145591/2251799813685248), by norm_num⟩
  | 5 => ⟨((32087863650537/4503599627370496), (-680977141331089/2251799813685248)), (6833723/281474976710656), by norm_num⟩
  | 6 => ⟨((-823292472892675/9007199254740992), (-77630707764927/18014398509481984)), (135379683/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-2001291981/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-511262913/8388608)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-60356878659091/2251799813685248), (744027615769747/9007199254740992)), (409547685/18014398509481984), by norm_num⟩
  | 1 => ⟨((163082041/2147483648), (-502583735/2147483648)), (279/4294967296), by norm_num⟩
  | 2 => ⟨((-462046215/4294967296), (1423926945/4294967296)), (199/2147483648), by norm_num⟩
  | 3 => ⟨((436358501/4294967296), (-1344762941/4294967296)), (189/2147483648), by norm_num⟩
  | 4 => ⟨((-154537091/2147483648), (952500077/4294967296)), (269/4294967296), by norm_num⟩
  | 5 => ⟨((350269239/8589934592), (-1079454371/8589934592)), (307/8589934592), by norm_num⟩
  | 6 => ⟨((-330795827/17179869184), (1019441509/17179869184)), (73/4294967296), by norm_num⟩
  | 7 => ⟨((133887879/17179869184), (-825227225/34359738368)), (119/17179869184), by norm_num⟩
  | 8 => ⟨((-379332925/137438953472), (1169022393/137438953472)), (339/137438953472), by norm_num⟩
  | 9 => ⟨((477658269/549755813888), (-736019965/274877906944)), (429/549755813888), by norm_num⟩
  | 10 => ⟨((-67665389/274877906944), (834120635/1099511627776)), (245/1099511627776), by norm_num⟩
  | 11 => ⟨((69712903/1099511627776), (-859360623/4398046511104)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((-263348703/17592186044416), (811583995/17592186044416)), (121/8796093022208), by norm_num⟩
  | 13 => ⟨((114788163/35184372088832), (-1415009603/140737488355328)), (53/17592186044416), by norm_num⟩
  | 14 => ⟨((-371679263/562949953421312), (572717727/281474976710656)), (345/562949953421312), by norm_num⟩
  | 15 => ⟨((280812439/2251799813685248), (-432701735/1125899906842624)), (131/1125899906842624), by norm_num⟩
  | 16 => ⟨((-397800775/18014398509481984), (612968165/9007199254740992)), (373/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (2454855595035/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444548964581601/158456325028528675187087900672), (2903424614157/633825300114114700748351602688)), (138729/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944548625549053/19807040628566084398385987584), (3265654040469/39614081257132168796771975168)), (78049/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944415966150983/1237940039285380274899124224), (1734445995049/1237940039285380274899124224)), (82943/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885249032140621/77371252455336267181195264), (3467918697055/154742504910672534362390528)), (82961/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548903966512577/9671406556917033397649408), (3250139965351/9671406556917033397649408)), (77795/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314555070654119/151115727451828646838272), (2842839005979/604462909807314587353088)), (136179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943434080161571/37778931862957161709568), (1154419095659/18889465931478580854784)), (110681/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648423167991445/2361183241434822606848), (3461563152307/4722366482869645213696)), (166085/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620494747374549/590295810358705651712), (4756897756663/590295810358705651712)), (228469/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911141206766393/36893488147419103232), (5941997262677/73786976294838206464)), (142869/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821314969929957/9223372036854775808), (6679079090153/9223372036854775808)), (160833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796281303731591/576460752303423488), (6672000228329/1152921504606846976)), (160965/576460752303423488), by norm_num⟩
  | 5 => ⟨((596667221909251/72057594037927936), (182188894495/4503599627370496)), (281985/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489765990414929/36028797018963968), (8729176128423/36028797018963968)), (105893/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486915062612161/9007199254740992), (10883706983187/9007199254740992)), (265253/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111626446428575/2251799813685248), (21684307177447/4503599627370496)), (266035/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104518228445177/1125899906842624), (32319332499199/2251799813685248)), (802027/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166502749372787/2251799813685248), (63813976993715/2251799813685248)), (1619809/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166502749372787/2251799813685248), (63813976993715/2251799813685248)), (6179080967429732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082628265123217/2251799813685248), (122793470152245/2251799813685248)), (3208711/1125899906842624), by norm_num⟩
  | 2 => ⟨((1919470029311525/2251799813685248), (227136666552167/2251799813685248)), (12570499/2251799813685248), by norm_num⟩
  | 3 => ⟨((806637896063113/1125899906842624), (387229825098077/2251799813685248)), (11983267/1125899906842624), by norm_num⟩
  | 4 => ⟨((544611432399259/1125899906842624), (554852610807899/2251799813685248)), (5322985/281474976710656), by norm_num⟩
  | 5 => ⟨((390152367959273/2251799813685248), (268388933426563/1125899906842624)), (62182361/2251799813685248), by norm_num⟩
  | 6 => ⟨((-60356878659091/2251799813685248), (744027615769747/9007199254740992)), (409547685/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-511262913/8388608)), (3/33554432), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1043154683/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1181001383364133/18014398509481984), (7086988417095/140737488355328)), (19652879/1125899906842624), by norm_num⟩
  | 1 => ⟨((-406924849/2147483648), (-312561511/2147483648)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((1176164091/4294967296), (225854741/1073741824)), (319/4294967296), by norm_num⟩
  | 3 => ⟨((-70823989/268435456), (-870405553/4294967296)), (309/4294967296), by norm_num⟩
  | 4 => ⟨((818830631/4294967296), (628948907/4294967296)), (225/4294967296), by norm_num⟩
  | 5 => ⟨((-236672493/2147483648), (-727158463/8589934592)), (131/4294967296), by norm_num⟩
  | 6 => ⟨((114011915/2147483648), (700586095/17179869184)), (127/8589934592), by norm_num⟩
  | 7 => ⟨((-753227015/34359738368), (-578558361/34359738368)), (53/8589934592), by norm_num⟩
  | 8 => ⟨((544276523/68719476736), (418062187/68719476736)), (309/137438953472), by norm_num⟩
  | 9 => ⟨((-699182885/274877906944), (-67130841/34359738368)), (25/34359738368), by norm_num⟩
  | 10 => ⟨((404179693/549755813888), (310452939/549755813888)), (233/1099511627776), by norm_num⟩
  | 11 => ⟨((-849621505/4398046511104), (-652599569/4398046511104)), (247/4398046511104), by norm_num⟩
  | 12 => ⟨((818574001/17592186044416), (157187947/4398046511104)), (15/1099511627776), by norm_num⟩
  | 13 => ⟨((-727994823/70368744177664), (-559177357/70368744177664)), (215/70368744177664), by norm_num⟩
  | 14 => ⟨((1202386101/562949953421312), (230890063/140737488355328)), (357/562949953421312), by norm_num⟩
  | 15 => ⟨((-115844761/281474976710656), (-711848659/2251799813685248)), (277/2251799813685248), by norm_num⟩
  | 16 => ⟨((669668851/9007199254740992), (514376815/9007199254740992)), (101/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (106649496409/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((27783185650365/9903520314283042199192993792), (1009015975255/633825300114114700748351602688)), (184599/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472254128859751/9903520314283042199192993792), (1134898153405/39614081257132168796771975168)), (207687/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888746464889359/2475880078570760549798248448), (602761386131/1237940039285380274899124224)), (110341/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770412950025547/154742504910672534362390528), (301294525241/38685626227668133590597632)), (220699/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548824546856799/9671406556917033397649408), (1129488392723/9671406556917033397649408)), (206923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258151165072365/604462909807314587353088), (987936420121/604462909807314587353088)), (45269/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886756546145427/75557863725914323419136), (1604710901973/75557863725914323419136)), (294281/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296763238806529/4722366482869645213696), (300733361007/1180591620717411303424)), (55185/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810190742207529/295147905179352825856), (826529765291/295147905179352825856)), (75891/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822142326205837/73786976294838206464), (2064864548021/73786976294838206464)), (379527/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910579709445899/4611686018427387904), (580241758675/2305843009213693952)), (213533/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592409610288879/1152921504606846976), (2318462654203/1152921504606846976)), (427189/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193203437328413/144115188075855872), (2025840960935/144115188075855872)), (373929/144115188075855872), by norm_num⟩
  | 4 => ⟨((186196899392307/4503599627370496), (94785706963/1125899906842624)), (561171/36028797018963968), by norm_num⟩
  | 3 => ⟨((743343264635799/4503599627370496), (3781615347893/9007199254740992)), (1371/17592186044416), by norm_num⟩
  | 2 => ⟨((555706387673467/1125899906842624), (7533871746779/4503599627370496)), (1405371/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104234602407553/1125899906842624), (11227688957921/2251799813685248)), (527937/562949953421312), by norm_num⟩
  | 0 => ⟨((270707500629075/281474976710656), (11082284812549/1125899906842624)), (2119189/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((270707500629075/281474976710656), (11082284812549/1125899906842624)), (8084064487937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((260324650128215/281474976710656), (10658345753941/562949953421312)), (4117963/1125899906842624), by norm_num⟩
  | 2 => ⟨((1925301472193295/2251799813685248), (9857466414119/281474976710656)), (15546003/2251799813685248), by norm_num⟩
  | 3 => ⟨((1643381831331911/2251799813685248), (134851025273969/2251799813685248)), (13836353/1125899906842624), by norm_num⟩
  | 4 => ⟨((297819440723755/562949953421312), (6150960986987/70368744177664)), (21852971/1125899906842624), by norm_num⟩
  | 5 => ⟨((306510453373755/1125899906842624), (416520324747149/4503599627370496)), (26942267/1125899906842624), by norm_num⟩
  | 6 => ⟨((1181001383364133/18014398509481984), (7086988417095/140737488355328)), (19652879/1125899906842624), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1043154683/16777216)), (1/8388608), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-265666977/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((155222562936943/2251799813685248), (-345745166371417/9007199254740992)), (271662797/18014398509481984), by norm_num⟩
  | 1 => ⟨((-871741037/4294967296), (60679051/536870912)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((40106067/134217728), (-178665763/1073741824)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((-39363289/134217728), (701427249/4294967296)), (283/4294967296), by norm_num⟩
  | 4 => ⟨((231805605/1073741824), (-516327433/4294967296)), (105/2147483648), by norm_num⟩
  | 5 => ⟨((-546029967/4294967296), (76014731/1073741824)), (249/8589934592), by norm_num⟩
  | 6 => ⟨((267958653/4294967296), (-298427649/8589934592)), (247/17179869184), by norm_num⟩
  | 7 => ⟨((-225425115/8589934592), (251057715/17179869184)), (105/17179869184), by norm_num⟩
  | 8 => ⟨((1327500991/137438953472), (-369612061/68719476736)), (311/137438953472), by norm_num⟩
  | 9 => ⟨((-868610147/274877906944), (944705/536870912)), (205/274877906944), by norm_num⟩
  | 10 => ⟨((511513915/549755813888), (-569677051/1099511627776)), (243/1099511627776), by norm_num⟩
  | 11 => ⟨((-547680549/2199023255552), (304978057/2199023255552)), (131/2199023255552), by norm_num⟩
  | 12 => ⟨((537537319/8796093022208), (-598659519/17592186044416)), (259/17592186044416), by norm_num⟩
  | 13 => ⟨((-973997437/70368744177664), (135593571/17592186044416)), (59/17592186044416), by norm_num⟩
  | 14 => ⟨((204848287/70368744177664), (-456282281/281474976710656)), (25/35184372088832), by norm_num⟩
  | 15 => ⟨((-1286748333/2251799813685248), (716530845/2251799813685248)), (79/562949953421312), by norm_num⟩
  | 16 => ⟨((947187987/9007199254740992), (-527445337/9007199254740992)), (117/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-330922041089/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778052263264395/633825300114114700748351602688), (-782657025167/633825300114114700748351602688)), (184555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944467987192229/19807040628566084398385987584), (-440148013175/19807040628566084398385987584)), (103817/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944330463993449/1237940039285380274899124224), (-935072348433/2475880078570760549798248448)), (220623/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770327455806313/154742504910672534362390528), (-233700006755/38685626227668133590597632)), (55159/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548744441352959/9671406556917033397649408), (-876085794613/9671406556917033397649408)), (206859/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081118055911/604462909807314587353088), (-23946436383/18889465931478580854784)), (22627/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943321402311065/37778931862957161709568), (-1244672882933/75557863725914323419136)), (294177/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296678006874785/4722366482869645213696), (-933030844015/4722366482869645213696)), (220655/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620264410992861/590295810358705651712), (-641073975959/295147905179352825856)), (151719/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227749520620543/9223372036854775808), (-25023931551/1152921504606846976)), (379353/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910497617712291/4611686018427387904), (-1800138663921/9223372036854775808)), (426849/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796122868136121/576460752303423488), (-1798160264327/1152921504606846976)), (6671/18014398509481984), by norm_num⟩
  | 5 => ⟨((149132549382809/18014398509481984), (-392791857433/36028797018963968)), (373685/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489361325156375/36028797018963968), (-1176156388157/18014398509481984)), (560743/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486420401725253/9007199254740992), (-733160019091/2251799813685248)), (350655/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222296911240609/4503599627370496), (-2921046166683/2251799813685248)), (1403767/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207685235366217/2251799813685248), (-4352697673131/1125899906842624)), (2108541/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082063865114945/1125899906842624), (-17181171459049/2251799813685248)), (2114379/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1082063865114945/1125899906842624), (-17181171459049/2251799813685248)), (8065715794089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079737999637241/2251799813685248), (-129001842515/8796093022208)), (8192761/2251799813685248), by norm_num⟩
  | 2 => ⟨((960169617459953/1125899906842624), (-61002091093011/2251799813685248)), (15373799/2251799813685248), by norm_num⟩
  | 3 => ⟨((818008221615829/1125899906842624), (-26011350615211/562949953421312)), (1690911/140737488355328), by norm_num⟩
  | 4 => ⟨((591909711633837/1125899906842624), (-75592860534977/1125899906842624)), (41812453/2251799813685248), by norm_num⟩
  | 5 => ⟨((612208641404151/2251799813685248), (-158963147643601/2251799813685248)), (99155957/4503599627370496), by norm_num⟩
  | 6 => ⟨((155222562936943/2251799813685248), (-345745166371417/9007199254740992)), (271662797/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-265666977/4194304)), (1/8388608), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1081180005/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-3458149613303/1125899906842624), (-679346874965281/9007199254740992)), (223111895/18014398509481984), by norm_num⟩
  | 1 => ⟨((79038165/8589934592), (485215511/2147483648)), (321/8589934592), by norm_num⟩
  | 2 => ⟨((-59194295/4294967296), (-726787883/2147483648)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((59110087/4294967296), (1451507945/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((-44269499/4294967296), (-1087082299/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((53047827/8589934592), (1302643011/8589934592)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-26486181/8589934592), (-1300789903/17179869184)), (7/536870912), by norm_num⟩
  | 7 => ⟨((22670145/17179869184), (1113376655/34359738368)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((-67913685/137438953472), (-1667689189/137438953472)), (73/34359738368), by norm_num⟩
  | 9 => ⟨((22605691/137438953472), (69388199/17179869184)), (49/68719476736), by norm_num⟩
  | 10 => ⟨((-27088239/549755813888), (-665179095/549755813888)), (237/1099511627776), by norm_num⟩
  | 11 => ⟨((922149/68719476736), (362308815/1099511627776)), (65/1099511627776), by norm_num⟩
  | 12 => ⟨((-58933579/17592186044416), (-723586807/8796093022208)), (131/8796093022208), by norm_num⟩
  | 13 => ⟨((27161419/35184372088832), (166744027/8796093022208)), (243/70368744177664), by norm_num⟩
  | 14 => ⟨((-23248097/140737488355328), (-1141761059/281474976710656)), (105/140737488355328), by norm_num⟩
  | 15 => ⟨((74288079/2251799813685248), (1824218909/2251799813685248)), (169/1125899906842624), by norm_num⟩
  | 16 => ⟨((-55636799/9007199254740992), (-1366217865/9007199254740992)), (255/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-2099154851073/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444495285764015/158456325028528675187087900672), (-2482152955219/633825300114114700748351602688)), (92445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888855817708351/39614081257132168796771975168), (-697948720349/9903520314283042199192993792)), (6501/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472143891173141/618970019642690137449562112), (-2965500109919/2475880078570760549798248448)), (110535/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442560467836731/38685626227668133590597632), (-2964620764413/154742504910672534362390528)), (27639/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387165992782751/2417851639229258349412352), (-2778397983763/9671406556917033397649408)), (25917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258010472041793/604462909807314587353088), (-303770576855/75557863725914323419136)), (90731/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886527565500671/75557863725914323419136), (-3947267728631/75557863725914323419136)), (147479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324147798393351/1180591620717411303424), (-1479460257889/2361183241434822606848)), (55323/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810072209823887/295147905179352825856), (-1016507610821/147573952589676412928)), (152195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821845242737393/73786976294838206464), (-5078812674253/73786976294838206464)), (190331/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227603020934697/1152921504606846976), (-1427136488021/2305843009213693952)), (214243/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592073071511639/1152921504606846976), (-5702154200815/1152921504606846976)), (214393/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192907522113179/144115188075855872), (-4982202629491/144115188075855872)), (187763/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489128445967011/36028797018963968), (-7458960389905/36028797018963968)), (2203/281474976710656), by norm_num⟩
  | 3 => ⟨((185765385547555/1125899906842624), (-9298646543199/9007199254740992)), (353073/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221683736036173/4503599627370496), (-9261160029217/2251799813685248)), (707933/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206719520588005/2251799813685248), (-27596706989469/2251799813685248)), (1066381/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162014875579203/2251799813685248), (-54450267674853/2251799813685248)), (2150773/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162014875579203/2251799813685248), (-54450267674853/2251799813685248)), (8204547890670012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037246619834041/1125899906842624), (-52279198167105/1125899906842624)), (66157/35184372088832), by norm_num⟩
  | 2 => ⟨((1906292787261329/2251799813685248), (-24081368715329/281474976710656)), (8194521/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597316857598023/2251799813685248), (-163091369704959/1125899906842624)), (7638263/1125899906842624), by norm_num⟩
  | 4 => ⟨((542904824225113/1125899906842624), (-462756222955965/2251799813685248)), (3262323/281474976710656), by norm_num⟩
  | 5 => ⟨((53559338674299/281474976710656), (-111569680553363/562949953421312)), (17948033/1125899906842624), by norm_num⟩
  | 6 => ⟨((-3458149613303/1125899906842624), (-679346874965281/9007199254740992)), (223111895/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1081180005/16777216)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1098788705/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-72257953944029/1125899906842624), (-301339596714709/9007199254740992)), (471520965/18014398509481984), by norm_num⟩
  | 1 => ⟨((419599461/2147483648), (54683397/536870912)), (43/536870912), by norm_num⟩
  | 2 => ⟨((-638739987/2147483648), (-665939317/4294967296)), (263/2147483648), by norm_num⟩
  | 3 => ⟨((1296438815/4294967296), (337911199/2147483648)), (67/536870912), by norm_num⟩
  | 4 => ⟨((-493379633/2147483648), (-257194557/2147483648)), (205/2147483648), by norm_num⟩
  | 5 => ⟨((1201684291/8589934592), (19575865/268435456)), (251/4294967296), by norm_num⟩
  | 6 => ⟨((-1219518263/17179869184), (-79465547/2147483648)), (1/33554432), by norm_num⟩
  | 7 => ⟨((530407245/17179869184), (552993465/34359738368)), (447/34359738368), by norm_num⟩
  | 8 => ⟨((-807418379/68719476736), (-420900253/68719476736)), (171/34359738368), by norm_num⟩
  | 9 => ⟨((68283427/17179869184), (284764503/137438953472)), (465/274877906944), by norm_num⟩
  | 10 => ⟨((-332624681/274877906944), (-693577535/1099511627776)), (71/137438953472), by norm_num⟩
  | 11 => ⟨((736496949/2199023255552), (383929521/2199023255552)), (79/549755813888), by norm_num⟩
  | 12 => ⟨((-373713581/4398046511104), (-389627347/8796093022208)), (161/4398046511104), by norm_num⟩
  | 13 => ⟨((87521491/4398046511104), (5703025/549755813888)), (303/35184372088832), by norm_num⟩
  | 14 => ⟨((-1218108083/281474976710656), (-158747315/70368744177664)), (529/281474976710656), by norm_num⟩
  | 15 => ⟨((494474319/562949953421312), (515530413/1125899906842624)), (27/70368744177664), by norm_num⟩
  | 16 => ⟨((-94089885/562949953421312), (-392385977/4503599627370496)), (331/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-1733162168427/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777910623659521/633825300114114700748351602688), (-1024620592559/158456325028528675187087900672)), (185207/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944388093759909/19807040628566084398385987584), (-4609726529391/39614081257132168796771975168)), (104205/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888490560172551/2475880078570760549798248448), (-4896520620951/2475880078570760549798248448)), (27687/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885078210100893/77371252455336267181195264), (-4895042922179/154742504910672534362390528)), (55391/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387145846634995/2417851639229258349412352), (-2293766551251/4835703278458516698824704)), (51947/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314484871707139/151115727451828646838272), (-4012522297187/604462909807314587353088)), (181887/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235801415912115/9444732965739290427392), (-6517407541651/75557863725914323419136)), (73925/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324125809884909/1180591620717411303424), (-4885483111677/4722366482869645213696)), (110947/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810011112315985/295147905179352825856), (-6713360764563/590295810358705651712)), (305295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910845307370703/36893488147419103232), (-8385436458885/73786976294838206464)), (381907/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820647625207765/9223372036854775808), (-4712503826881/4611686018427387904)), (215021/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795946652284835/576460752303423488), (-9414255181809/1152921504606846976)), (215269/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192746608642977/144115188075855872), (-4112693863753/72057594037927936)), (5895/2251799813685248), by norm_num⟩
  | 4 => ⟨((93054991676541/2251799813685248), (-1539242239353/4503599627370496)), (567039/36028797018963968), by norm_num⟩
  | 3 => ⟨((371449950715233/2251799813685248), (-15350232694357/9007199254740992)), (88845/1125899906842624), by norm_num⟩
  | 2 => ⟨((2220999731789919/4503599627370496), (-30574143238067/4503599627370496)), (1427413/4503599627370496), by norm_num⟩
  | 1 => ⟨((17231255616209/17592186044416), (-45546273825819/2251799813685248)), (2155901/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159410914363747/2251799813685248), (-89837969777583/2251799813685248)), (4371185/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159410914363747/2251799813685248), (-89837969777583/2251799813685248)), (16674747475630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033614224490335/1125899906842624), (-5384500969041/70368744177664)), (8732467/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884601266676431/2251799813685248), (-316361865394741/2251799813685248)), (8684895/1125899906842624), by norm_num⟩
  | 3 => ⟨((1532834794418733/2251799813685248), (-529546160033909/2251799813685248)), (33955299/2251799813685248), by norm_num⟩
  | 4 => ⟨((459446563322099/1125899906842624), (-720940444543677/2251799813685248)), (62198037/2251799813685248), by norm_num⟩
  | 5 => ⟨((144155555765797/2251799813685248), (-73548635982745/281474976710656)), (90589253/2251799813685248), by norm_num⟩
  | 6 => ⟨((-72257953944029/1125899906842624), (-301339596714709/9007199254740992)), (471520965/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1098788705/16777216)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile019Terms2
