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
namespace Reinmann.XiBand97.Tile006Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10993/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10993/640))
  have he : value ((69/80), (10993/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-1266369943/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((676314578382249/4503599627370496), (-14093572995577/2251799813685248)), (43308309/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1417174353/4294967296), (59064379/4294967296)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((194615645/536870912), (-64888853/4294967296)), (105/4294967296), by norm_num⟩
  | 3 => ⟨((-570152371/2147483648), (5940641/536870912)), (79/4294967296), by norm_num⟩
  | 4 => ⟨((1252752803/8589934592), (-26105845/4294967296)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((-275257925/4294967296), (45888323/17179869184)), (81/17179869184), by norm_num⟩
  | 6 => ⟨((1612809275/68719476736), (-67217967/68719476736)), (121/68719476736), by norm_num⟩
  | 7 => ⟨((-253121727/34359738368), (42197991/137438953472)), (155/274877906944), by norm_num⟩
  | 8 => ⟨((17380165/8589934592), (-46359231/549755813888)), (11/68719476736), by norm_num⟩
  | 9 => ⟨((-271560005/549755813888), (45271841/2199023255552)), (11/274877906944), by norm_num⟩
  | 10 => ⟨((238671327/2199023255552), (-79577921/17592186044416)), (79/8796093022208), by norm_num⟩
  | 11 => ⟨((-1525569471/70368744177664), (63582023/70368744177664)), (129/70368744177664), by norm_num⟩
  | 12 => ⟨((1117339579/281474976710656), (-46567995/281474976710656)), (3/8796093022208), by norm_num⟩
  | 13 => ⟨((-1510797529/2251799813685248), (62966365/2251799813685248)), (33/562949953421312), by norm_num⟩
  | 14 => ⟨((1896892265/18014398509481984), (-39528927/9007199254740992)), (169/18014398509481984), by norm_num⟩
  | 15 => ⟨((-277859887/18014398509481984), (2895131/4503599627370496)), (101/72057594037927936), by norm_num⟩
  | 16 => ⟨((610520573/288230376151711744), (-6361253/72057594037927936)), (113/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-13564570667/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045856825643/633825300114114700748351602688), (-64230880185/633825300114114700748351602688)), (92207/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236256696220043/4951760157141521099596496896), (-72247745725/39614081257132168796771975168)), (103733/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944924064304703/1237940039285380274899124224), (-19187098187/618970019642690137449562112)), (110217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885757190750879/77371252455336267181195264), (-76731706675/154742504910672534362390528)), (110217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549856892169633/9671406556917033397649408), (-8989781399/1208925819614629174706176)), (103329/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629527110297903/302231454903657293676544), (-62910751757/604462909807314587353088)), (45207/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888223549099061/75557863725914323419136), (-102196762563/75557863725914323419136)), (36731/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648931543342101/2361183241434822606848), (-76618526283/4722366482869645213696)), (55097/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621893118480259/590295810358705651712), (-52651648737/295147905179352825856)), (151517/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228003860516325/9223372036854775808), (-131558397819/73786976294838206464)), (23675/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823282693455157/9223372036854775808), (-147906017335/9223372036854775808)), (106539/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398632798668901/288230376151711744), (-36946159995/288230376151711744)), (106541/576460752303423488), by norm_num⟩
  | 5 => ⟨((597528961934103/72057594037927936), (-129175144963/144115188075855872)), (46613/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492353129473073/36028797018963968), (-96745111651/18014398509481984)), (34961/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490152314374447/9007199254740992), (-241386669159/9007199254740992)), (349627/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229737259473169/4503599627370496), (-481348022571/4503599627370496)), (349655/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218787243790013/2251799813685248), (-22452164743/70368744177664)), (1049109/2251799813685248), by norm_num⟩
  | 0 => ⟨((2186098760858079/2251799813685248), (-1422790481175/2251799813685248)), (2098825/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2186098760858079/2251799813685248), (-1422790481175/2251799813685248)), (8006381997115325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1061156888558229/1125899906842624), (-1381277540283/1125899906842624)), (1019457/562949953421312), by norm_num⟩
  | 2 => ⟨((500067558121015/562949953421312), (-5207397808541/2251799813685248)), (7696685/2251799813685248), by norm_num⟩
  | 3 => ⟨((1776824858787895/2251799813685248), (-4625723282249/1125899906842624)), (13709505/2251799813685248), by norm_num⟩
  | 4 => ⟨((350499739181563/562949953421312), (-14600054707923/2251799813685248)), (21748135/2251799813685248), by norm_num⟩
  | 5 => ⟨((1745615130722933/4503599627370496), (-9090178151829/1125899906842624)), (27363345/2251799813685248), by norm_num⟩
  | 6 => ⟨((676314578382249/4503599627370496), (-14093572995577/2251799813685248)), (43308309/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1266369943/33554432)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-66638419/33554432), (-663547227/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-171165439912223/4503599627370496), (-593929131420595/4503599627370496)), (212833645/9007199254740992), by norm_num⟩
  | 1 => ⟨((375864973/4294967296), (81513665/268435456)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((-216365271/2147483648), (-1501537199/4294967296)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((332132965/4294967296), (576236195/2147483648)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-382382207/8589934592), (-1326832873/8589934592)), (247/8589934592), by norm_num⟩
  | 5 => ⟨((88046757/4294967296), (611029119/8589934592)), (229/17179869184), by norm_num⟩
  | 6 => ⟨((-135156767/17179869184), (-937964361/34359738368)), (89/17179869184), by norm_num⟩
  | 7 => ⟨((177834261/68719476736), (617069359/68719476736)), (237/137438953472), by norm_num⟩
  | 8 => ⟨((-204739259/274877906944), (-355213677/137438953472)), (69/137438953472), by norm_num⟩
  | 9 => ⟨((419048503/2199023255552), (181757715/274877906944)), (285/2199023255552), by norm_num⟩
  | 10 => ⟨((-385957935/8796093022208), (-83702521/549755813888)), (265/8796093022208), by norm_num⟩
  | 11 => ⟨((80790999/8796093022208), (1121350849/35184372088832)), (7/1099511627776), by norm_num⟩
  | 12 => ⟨((-248037533/140737488355328), (-860668583/140737488355328)), (87/70368744177664), by norm_num⟩
  | 13 => ⟨((351463093/1125899906842624), (609773123/562949953421312)), (249/1125899906842624), by norm_num⟩
  | 14 => ⟨((-231221051/4503599627370496), (-802316859/4503599627370496)), (165/4503599627370496), by norm_num⟩
  | 15 => ⟨((35493743/4503599627370496), (492640757/18014398509481984)), (205/36028797018963968), by norm_num⟩
  | 16 => ⟨((-163454727/144115188075855872), (-1134347263/288230376151711744)), (119/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-2411635558623/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889450689871157/316912650057057350374175801344), (-1427231406747/316912650057057350374175801344)), (92481/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889890812787497/39614081257132168796771975168), (-3210705344547/39614081257132168796771975168)), (104059/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472418728026697/618970019642690137449562112), (-426335320355/309485009821345068724781056)), (13823/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110708802633871/9671406556917033397649408), (-3409904373437/154742504910672534362390528)), (6913/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774846928102697/4835703278458516698824704), (-3195958703055/9671406556917033397649408)), (12965/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157363902695223/75557863725914323419136), (-1397818709809/302231454903657293676544)), (22695/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943995266943929/37778931862957161709568), (-4541361649593/75557863725914323419136)), (147563/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324421941061557/1180591620717411303424), (-3404666152659/4722366482869645213696)), (55357/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810825569722845/295147905179352825856), (-2339607375063/295147905179352825856)), (76149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823727046046251/73786976294838206464), (-2922859013681/36893488147419103232)), (23809/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455734750630647/2305843009213693952), (-6571896998431/9223372036854775808)), (214419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594185166598029/1152921504606846976), (-6566230692675/1152921504606846976)), (214591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597376262900077/72057594037927936), (-5739081966753/144115188075855872)), (93981/72057594037927936), by norm_num⟩
  | 4 => ⟨((745944899909633/18014398509481984), (-4297947465231/18014398509481984)), (141165/18014398509481984), by norm_num⟩
  | 3 => ⟨((744782013896303/4503599627370496), (-10722621079261/9007199254740992)), (44199/1125899906842624), by norm_num⟩
  | 2 => ⟨((278566680284703/562949953421312), (-21378605173455/4503599627370496)), (709227/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216913859897097/2251799813685248), (-15950842658315/1125899906842624)), (33405/70368744177664), by norm_num⟩
  | 0 => ⟨((1091042031041055/1125899906842624), (-15785174914143/562949953421312)), (2158467/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091042031041055/1125899906842624), (-15785174914143/562949953421312)), (8233898171431731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((528189059827393/562949953421312), (-30592931385813/562949953421312)), (2152165/1125899906842624), by norm_num⟩
  | 2 => ⟨((1975648128440129/2251799813685248), (-229631093390545/2251799813685248)), (8544925/2251799813685248), by norm_num⟩
  | 3 => ⟨((1709945557751723/2251799813685248), (-201470058364657/1125899906842624)), (8368393/1125899906842624), by norm_num⟩
  | 4 => ⟨((1226375922060993/2251799813685248), (-76494995076143/281474976710656)), (31408579/2251799813685248), by norm_num⟩
  | 5 => ⟨((501600054302201/2251799813685248), (-333285826029183/1125899906842624)), (51282995/2251799813685248), by norm_num⟩
  | 6 => ⟨((-171165439912223/4503599627370496), (-593929131420595/4503599627370496)), (212833645/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-663547227/16777216)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-1382026457/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1070820349395461/9007199254740992), (193557240100717/4503599627370496)), (100137369/4503599627370496), by norm_num⟩
  | 1 => ⟨((1224381949/4294967296), (-110657213/1073741824)), (231/4294967296), by norm_num⟩
  | 2 => ⟨((-366992461/1073741824), (33168051/268435456)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((1173345983/4294967296), (-212089367/2147483648)), (225/4294967296), by norm_num⟩
  | 4 => ⟨((-1406780393/8589934592), (508568091/8589934592)), (17/536870912), by norm_num⟩
  | 5 => ⟨((674662411/8589934592), (-487797209/17179869184)), (33/2147483648), by norm_num⟩
  | 6 => ⟨((-269628301/8589934592), (389895541/34359738368)), (213/34359738368), by norm_num⟩
  | 7 => ⟨((1477806693/137438953472), (-534244957/137438953472)), (147/68719476736), by norm_num⟩
  | 8 => ⟨((-885906421/274877906944), (40033233/34359738368)), (89/137438953472), by norm_num⟩
  | 9 => ⟨((472069071/549755813888), (-170658667/549755813888)), (191/1099511627776), by norm_num⟩
  | 10 => ⟨((-905577755/4398046511104), (327377289/4398046511104)), (185/4398046511104), by norm_num⟩
  | 11 => ⟨((197407329/4398046511104), (-285460529/17592186044416)), (163/17592186044416), by norm_num⟩
  | 12 => ⟨((-157787367/17592186044416), (228168151/70368744177664)), (263/140737488355328), by norm_num⟩
  | 13 => ⟨((931341739/562949953421312), (-21043205/35184372088832)), (49/140737488355328), by norm_num⟩
  | 14 => ⟨((-1276148545/4503599627370496), (230671551/2251799813685248)), (271/4503599627370496), by norm_num⟩
  | 15 => ⟨((816018817/18014398509481984), (-73750163/4503599627370496)), (175/18014398509481984), by norm_num⟩
  | 16 => ⟨((-122295479/18014398509481984), (176845167/72057594037927936)), (53/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1820203823575/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778769069561893/633825300114114700748351602688), (1077069733479/158456325028528675187087900672)), (92625/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889741675454809/39614081257132168796771975168), (2422956081767/19807040628566084398385987584)), (104229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889516075488171/2475880078570760549798248448), (2573846277267/1237940039285380274899124224)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221397697548013/19342813113834066795298816), (2573233669059/77371252455336267181195264)), (110811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549544096906651/9671406556917033397649408), (2411755750801/4835703278458516698824704)), (103923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314694932780679/151115727451828646838272), (527408890089/75557863725914323419136)), (45485/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887776016940071/75557863725914323419136), (3426937878995/37778931862957161709568)), (73949/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297526137913249/4722366482869645213696), (5138272375165/4722366482869645213696)), (110985/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621427704362051/590295810358705651712), (55169193621/4611686018427387904)), (152705/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823445956300711/73786976294838206464), (8821870673997/73786976294838206464)), (191033/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822620311143067/9223372036854775808), (9917456192807/9223372036854775808)), (215119/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593863399345769/1152921504606846976), (4954261980209/576460752303423488)), (53845/288230376151711744), by norm_num⟩
  | 5 => ⟨((74654220449917/9007199254740992), (2164978515021/36028797018963968)), (94375/72057594037927936), by norm_num⟩
  | 4 => ⟨((745727708818167/18014398509481984), (6484896597735/18014398509481984)), (283711/36028797018963968), by norm_num⟩
  | 3 => ⟨((2908220796937/17592186044416), (4044282452361/2251799813685248)), (355667/9007199254740992), by norm_num⟩
  | 2 => ⟨((556846914548501/1125899906842624), (16124511717899/2251799813685248)), (357211/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107553128190241/1125899906842624), (24055396154085/1125899906842624)), (539685/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089058469345113/1125899906842624), (11896588916399/281474976710656)), (273725/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089058469345113/1125899906842624), (11896588916399/281474976710656)), (1044178010106944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((525705651635805/562949953421312), (23014622946465/281474976710656)), (2210699/1125899906842624), by norm_num⟩
  | 2 => ⟨((974323699709439/1125899906842624), (171935956717899/1125899906842624)), (1122599/281474976710656), by norm_num⟩
  | 3 => ⟨((1633794785865543/2251799813685248), (595155133931035/2251799813685248)), (9143193/1125899906842624), by norm_num⟩
  | 4 => ⟨((1028100168943599/2251799813685248), (13494224551625/35184372088832)), (36201655/2251799813685248), by norm_num⟩
  | 5 => ⟨((138170603466735/2251799813685248), (1577224627600177/4503599627370496)), (121651627/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1070820349395461/9007199254740992), (193557240100717/4503599627370496)), (100137369/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1382026457/33554432)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-716087723/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((35302413601507/1125899906842624), (1017867155509609/9007199254740992)), (38729325/2251799813685248), by norm_num⟩
  | 1 => ⟨((-83659365/1073741824), (-1206066543/4294967296)), (185/4294967296), by norm_num⟩
  | 2 => ⟨((415771425/4294967296), (749240693/2147483648)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-344384393/4294967296), (-1241195453/4294967296)), (97/2147483648), by norm_num⟩
  | 4 => ⟨((213940767/4294967296), (1542127417/8589934592)), (243/8589934592), by norm_num⟩
  | 5 => ⟨((-106324567/4294967296), (-1532817069/17179869184)), (61/4294967296), by norm_num⟩
  | 6 => ⟨((176137749/17179869184), (19838059/536870912)), (51/8589934592), by norm_num⟩
  | 7 => ⟨((-7815819/2147483648), (-450703769/34359738368)), (147/68719476736), by norm_num⟩
  | 8 => ⟨((155372645/137438953472), (139994599/34359738368)), (185/274877906944), by norm_num⟩
  | 9 => ⟨((-343188017/1099511627776), (-1236883591/1099511627776)), (207/1099511627776), by norm_num⟩
  | 10 => ⟨((170558037/2199023255552), (153677013/549755813888)), (13/274877906944), by norm_num⟩
  | 11 => ⟨((-308233309/17592186044416), (-277725841/4398046511104)), (95/8796093022208), by norm_num⟩
  | 12 => ⟨((255310333/70368744177664), (920163719/70368744177664)), (159/70368744177664), by norm_num⟩
  | 13 => ⟨((-195206875/281474976710656), (-351772453/140737488355328)), (123/281474976710656), by norm_num⟩
  | 14 => ⟨((138591675/1125899906842624), (998996237/2251799813685248)), (177/2251799813685248), by norm_num⟩
  | 15 => ⟨((-367346533/18014398509481984), (-330988319/4503599627370496)), (237/18014398509481984), by norm_num⟩
  | 16 => ⟨((456410921/144115188075855872), (1644950149/144115188075855872)), (297/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (846790574675/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889330584838233/316912650057057350374175801344), (1002019142101/316912650057057350374175801344)), (46199/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889620751842261/39614081257132168796771975168), (1127059756677/19807040628566084398385987584)), (12995/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889388195917285/2475880078570760549798248448), (1197239111637/1237940039285380274899124224)), (13809/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771054377315107/154742504910672534362390528), (598472295763/38685626227668133590597632)), (110489/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387356390592679/2417851639229258349412352), (2243645434075/9671406556917033397649408)), (103601/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314669182812005/151115727451828646838272), (981282141245/302231454903657293676544)), (22667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887609987045935/75557863725914323419136), (796998657265/18889465931478580854784)), (147369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297402791226863/4722366482869645213696), (2389970613529/4722366482869645213696)), (110555/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621260011258775/590295810358705651712), (1642272096615/295147905179352825856)), (38015/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823239199348575/73786976294838206464), (512897944031/9223372036854775808)), (95073/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911195817833587/4611686018427387904), (1153162710149/2305843009213693952)), (107005/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796819811535139/576460752303423488), (576045744625/144115188075855872)), (53533/288230376151711744), by norm_num⟩
  | 5 => ⟨((149284652874129/18014398509481984), (4027504439379/144115188075855872)), (93751/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491180932518007/36028797018963968), (753954613165/4503599627370496)), (281525/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488685076322783/9007199254740992), (7522738066619/9007199254740992)), (352385/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113398429853393/2251799813685248), (7497578905875/2251799813685248)), (353103/2251799813685248), by norm_num⟩
  | 1 => ⟨((553590503994059/562949953421312), (22367310830811/2251799813685248)), (1062915/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177190873005243/2251799813685248), (44235132495581/2251799813685248)), (2140305/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177190873005243/2251799813685248), (44235132495581/2251799813685248)), (8164615639693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526046245513715/562949953421312), (42769488721975/1125899906842624)), (4222871/2251799813685248), by norm_num⟩
  | 2 => ⟨((1962997552082093/2251799813685248), (79931542148643/1125899906842624)), (8212917/2251799813685248), by norm_num⟩
  | 3 => ⟨((1699886091337199/2251799813685248), (278720018748283/2251799813685248)), (3871321/562949953421312), by norm_num⟩
  | 4 => ⟨((78046676751115/140737488355328), (210406040700417/1125899906842624)), (13606573/1125899906842624), by norm_num⟩
  | 5 => ⟨((306929111600177/1125899906842624), (933453762003603/4503599627370496)), (40353455/2251799813685248), by norm_num⟩
  | 6 => ⟨((35302413601507/1125899906842624), (1017867155509609/9007199254740992)), (38729325/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-716087723/16777216)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-579933/262144), (-1478308045/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((983105853547633/9007199254740992), (-147181050076031/18014398509481984)), (130882031/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1202400555/4294967296), (22501465/1073741824)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((771024133/2147483648), (-28857559/1073741824)), (27/1073741824), by norm_num⟩
  | 3 => ⟨((-1318425237/4294967296), (98690903/4294967296)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((1690846983/8589934592), (-15821073/1073741824)), (31/2147483648), by norm_num⟩
  | 5 => ⟨((-1734774753/17179869184), (129856803/17179869184)), (65/8589934592), by norm_num⟩
  | 6 => ⟨((741601565/17179869184), (-55512687/17179869184)), (57/17179869184), by norm_num⟩
  | 7 => ⟨((-1086954547/68719476736), (20341033/17179869184)), (85/68719476736), by norm_num⟩
  | 8 => ⟨((348497921/68719476736), (-104347439/274877906944)), (111/274877906944), by norm_num⟩
  | 9 => ⟨((-198639893/137438953472), (29738433/274877906944)), (129/1099511627776), by norm_num⟩
  | 10 => ⟨((1630404051/4398046511104), (-122044119/4398046511104)), (135/4398046511104), by norm_num⟩
  | 11 => ⟨((-380173075/4398046511104), (113831631/17592186044416)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((650083123/35184372088832), (-97324123/70368744177664)), (111/70368744177664), by norm_num⟩
  | 13 => ⟨((-1026110947/281474976710656), (19202419/70368744177664)), (89/281474976710656), by norm_num⟩
  | 14 => ⟨((375988945/562949953421312), (-112578817/2251799813685248)), (133/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1028685443/9007199254740992), (77002391/9007199254740992)), (93/9007199254740992), by norm_num⟩
  | 16 => ⟨((1319263033/72057594037927936), (-98753617/72057594037927936)), (121/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-97325665253/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778556905637481/633825300114114700748351602688), (-57576849549/316912650057057350374175801344)), (23053/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236187949747269/4951760157141521099596496896), (-129522990719/39614081257132168796771975168)), (103739/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263905612139/2475880078570760549798248448), (-137587132909/2475880078570760549798248448)), (6889/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885465147863623/77371252455336267181195264), (-137552221917/154742504910672534362390528)), (110225/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774654728754757/4835703278458516698824704), (-128918127655/9671406556917033397649408)), (103337/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258575360970273/604462909807314587353088), (-14095786927/75557863725914323419136)), (90421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887445675289743/75557863725914323419136), (-45793940185/18889465931478580854784)), (146935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324319980041239/1180591620717411303424), (-137321064861/4722366482869645213696)), (27551/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621091652423063/590295810358705651712), (-188717792313/590295810358705651712)), (37883/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823029633061489/73786976294838206464), (-58937332687/18446744073709551616)), (47355/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822157084987219/9223372036854775808), (-265014780727/9223372036854775808)), (213103/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796703292033975/576460752303423488), (-264760999153/1152921504606846976)), (213111/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194075010983233/144115188075855872), (-231380698107/144115188075855872)), (186481/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490880999952307/36028797018963968), (-346501514125/36028797018963968)), (139869/18014398509481984), by norm_num⟩
  | 3 => ⟨((744158032712281/4503599627370496), (-432132050375/9007199254740992)), (43713/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226076473631787/4503599627370496), (-861286921931/4503599627370496)), (349751/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213325251606399/2251799813685248), (-642256545297/1125899906842624)), (524749/1125899906842624), by norm_num⟩
  | 0 => ⟨((2175290963111037/2251799813685248), (-2539510435039/2251799813685248)), (525005/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175290963111037/2251799813685248), (-2539510435039/2251799813685248)), (2002735140086936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((262672346378295/281474976710656), (-4906452222345/2251799813685248)), (2031037/1125899906842624), by norm_num⟩
  | 2 => ⟨((30640550277897/35184372088832), (-9157398875717/2251799813685248)), (7599155/2251799813685248), by norm_num⟩
  | 3 => ⟨((853854406340353/1125899906842624), (-15949566469895/2251799813685248)), (831085/140737488355328), by norm_num⟩
  | 4 => ⟨((1294970797366077/2251799813685248), (-24191506770311/2251799813685248)), (20357145/2251799813685248), by norm_num⟩
  | 5 => ⟨((372227612517565/1125899906842624), (-27824227199457/2251799813685248)), (2981435/281474976710656), by norm_num⟩
  | 6 => ⟨((983105853547633/9007199254740992), (-147181050076031/18014398509481984)), (130882031/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1478308045/33554432)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-1521020159/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((409346108309865/18014398509481984), (-1803762357732873/18014398509481984)), (276854979/18014398509481984), by norm_num⟩
  | 1 => ⟨((-128780347/2147483648), (567463907/2147483648)), (11/268435456), by norm_num⟩
  | 2 => ⟨((339858719/4294967296), (-1497569783/4294967296)), (235/4294967296), by norm_num⟩
  | 3 => ⟨((-298968881/4294967296), (1317390837/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((49312251/1073741824), (-434583743/2147483648)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((-52055143/2147483648), (458756565/4294967296)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((366337351/34359738368), (-403561625/8589934592)), (33/4294967296), by norm_num⟩
  | 7 => ⟨((-276224363/68719476736), (608584151/34359738368)), (201/68719476736), by norm_num⟩
  | 8 => ⟨((364485965/274877906944), (-100380529/17179869184)), (267/274877906944), by norm_num⟩
  | 9 => ⟨((-213755413/549755813888), (470951059/274877906944)), (79/274877906944), by norm_num⟩
  | 10 => ⟨((56411279/549755813888), (-994293475/2199023255552)), (21/274877906944), by norm_num⟩
  | 11 => ⟨((-216541963/8796093022208), (954180903/8796093022208)), (163/8796093022208), by norm_num⟩
  | 12 => ⟨((190488885/35184372088832), (-1678758737/70368744177664)), (289/70368744177664), by norm_num⟩
  | 13 => ⟨((-154680335/140737488355328), (1363181707/281474976710656)), (237/281474976710656), by norm_num⟩
  | 14 => ⟨((58315753/281474976710656), (-128482667/140737488355328)), (181/1125899906842624), by norm_num⟩
  | 15 => ⟨((-164158523/4503599627370496), (361677999/2251799813685248)), (257/9007199254740992), by norm_num⟩
  | 16 => ⟨((216611877/36028797018963968), (-477244487/18014398509481984)), (171/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-438861584171/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778456095614919/633825300114114700748351602688), (-1038394188157/316912650057057350374175801344)), (92405/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889390079725197/39614081257132168796771975168), (-36498783511/618970019642690137449562112)), (103969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889143150326599/2475880078570760549798248448), (-2481340887093/2475880078570760549798248448)), (55241/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885404690350009/77371252455336267181195264), (-620173168261/38685626227668133590597632)), (110499/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549195930075725/9671406556917033397649408), (-145310054095/604462909807314587353088)), (103611/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258475855016053/604462909807314587353088), (-1016826240165/302231454903657293676544)), (45339/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887283660706301/75557863725914323419136), (-25807775529/590295810358705651712)), (147385/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81072383237847/295147905179352825856), (-1238209097959/2361183241434822606848)), (110569/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620923743199233/590295810358705651712), (-3403242554233/590295810358705651712)), (152081/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911409536101325/36893488147419103232), (-531413269373/9223372036854775808)), (95087/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821919278466775/9223372036854775808), (-4778944943197/9223372036854775808)), (107023/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796583811536857/576460752303423488), (-4774230882769/1152921504606846976)), (53543/288230376151711744), by norm_num⟩
  | 5 => ⟨((596932312359931/72057594037927936), (-4172154256433/144115188075855872)), (93771/72057594037927936), by norm_num⟩
  | 4 => ⟨((745281419114265/18014398509481984), (-48809763433/281474976710656)), (281595/36028797018963968), by norm_num⟩
  | 3 => ⟨((185989232897711/1125899906842624), (-3895537699487/4503599627370496)), (176245/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112629322306123/2251799813685248), (-3881703755191/1125899906842624)), (88309/562949953421312), by norm_num⟩
  | 1 => ⟨((1106032605411133/1125899906842624), (-23152317929755/2251799813685248)), (1063449/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172639269202907/2251799813685248), (-45755619979575/2251799813685248)), (535481/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172639269202907/2251799813685248), (-45755619979575/2251799813685248)), (2042697908641624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1047665913427937/1125899906842624), (-44147111190873/1125899906842624)), (4220299/2251799813685248), by norm_num⟩
  | 2 => ⟨((486568518246375/562949953421312), (-82159032592327/1125899906842624)), (4092529/1125899906842624), by norm_num⟩
  | 3 => ⟨((1670211675910211/2251799813685248), (-142023277579299/1125899906842624)), (15343567/2251799813685248), by norm_num⟩
  | 4 => ⟨((601502091879109/1125899906842624), (-210683858327327/1125899906842624)), (13316145/1125899906842624), by norm_num⟩
  | 5 => ⟨((1127691996228659/4503599627370496), (-450223970137561/2251799813685248)), (76846519/4503599627370496), by norm_num⟩
  | 6 => ⟨((409346108309865/18014398509481984), (-1803762357732873/18014398509481984)), (276854979/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1521020159/33554432)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-1560784187/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-714781125367601/9007199254740992), (-124600156554405/2251799813685248)), (158557353/9007199254740992), by norm_num⟩
  | 1 => ⟨((922996125/4294967296), (643584211/4294967296)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-1249759921/4294967296), (-108928647/536870912)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((1128137535/4294967296), (196656163/1073741824)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-381881635/2147483648), (-266277381/2147483648)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((827323711/8589934592), (144218503/2147483648)), (97/4294967296), by norm_num⟩
  | 6 => ⟨((-746811381/17179869184), (-520734595/17179869184)), (177/17179869184), by norm_num⟩
  | 7 => ⟨((288914673/17179869184), (3147713/268435456)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((-391197719/68719476736), (-545546549/137438953472)), (189/137438953472), by norm_num⟩
  | 9 => ⟨((117709229/68719476736), (82075969/68719476736)), (115/274877906944), by norm_num⟩
  | 10 => ⟨((-255010001/549755813888), (-355625351/1099511627776)), (251/2199023255552), by norm_num⟩
  | 11 => ⟨((125559979/1099511627776), (175100237/2199023255552)), (249/8796093022208), by norm_num⟩
  | 12 => ⟨((-453363635/17592186044416), (-632240309/35184372088832)), (227/35184372088832), by norm_num⟩
  | 13 => ⟨((377763533/70368744177664), (526811845/140737488355328)), (191/140737488355328), by norm_num⟩
  | 14 => ⟨((-584572921/562949953421312), (-815218813/1125899906842624)), (149/562949953421312), by norm_num⟩
  | 15 => ⟨((844294835/4503599627370496), (73588449/562949953421312)), (217/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1143196399/36028797018963968), (-99640607/4503599627370496)), (37/4503599627370496), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1649559898387/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889179273828299/316912650057057350374175801344), (-3902654500847/633825300114114700748351602688)), (92585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944640016871951/19807040628566084398385987584), (-1097394245917/9903520314283042199192993792)), (52091/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118064113937689/154742504910672534362390528), (-4662812475273/2475880078570760549798248448)), (55361/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885345799954747/77371252455336267181195264), (-582695061249/19342813113834066795298816)), (55377/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549085029136773/9671406556917033397649408), (-2184441508265/4835703278458516698824704)), (103867/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314594583913125/151115727451828646838272), (-1910721512083/302231454903657293676544)), (45459/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471781072662207/18889465931478580854784), (-6207352581699/75557863725914323419136)), (147805/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648518908334337/2361183241434822606848), (-4653334341491/4722366482869645213696)), (55455/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405189257915063/147573952589676412928), (-6394793371143/590295810358705651712)), (152593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455652192065673/18446744073709551616), (-15601917923/144115188075855872)), (190877/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455420014664177/2305843009213693952), (-4489703774563/4611686018427387904)), (107463/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592925125282519/1152921504606846976), (-4485145826931/576460752303423488)), (215161/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596824380426171/72057594037927936), (-3919378739959/72057594037927936)), (47133/36028797018963968), by norm_num⟩
  | 4 => ⟨((745115854681013/18014398509481984), (-5868829977251/18014398509481984)), (283329/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487487172089377/9007199254740992), (-3659071156803/2251799813685248)), (177547/4503599627370496), by norm_num⟩
  | 2 => ⟨((556091783330951/1125899906842624), (-14582685495143/2251799813685248)), (178247/1125899906842624), by norm_num⟩
  | 1 => ⟨((552658339283183/562949953421312), (-1358770800489/70368744177664)), (538251/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084700806495739/1125899906842624), (-42947699812341/1125899906842624)), (545299/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084700806495739/1125899906842624), (-42947699812341/1125899906842624)), (2080150606395530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((521685510210073/562949953421312), (-41376151059665/562949953421312)), (273073/140737488355328), by norm_num⟩
  | 2 => ⟨((1921618673510977/2251799813685248), (-76686527265545/562949953421312)), (8740071/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598066190915981/2251799813685248), (-261767963394597/1125899906842624)), (17298223/2251799813685248), by norm_num⟩
  | 4 => ⟨((1012401577642349/2251799813685248), (-743090091088017/2251799813685248)), (32596101/2251799813685248), by norm_num⟩
  | 5 => ⟨((209953863601129/2251799813685248), (-1336363163325247/4503599627370496)), (25411755/1125899906842624), by norm_num⟩
  | 6 => ⟨((-714781125367601/9007199254740992), (-124600156554405/2251799813685248)), (158557353/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1560784187/33554432)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile006Terms1
