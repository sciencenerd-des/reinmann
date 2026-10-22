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
namespace Reinmann.XiBand97.Tile005Terms1
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-4900516451/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((506396528766971/9007199254740992), (156940785617675/1125899906842624)), (23591663/4503599627370496), by norm_num⟩
  | 1 => ⟨((-265280461/2147483648), (-5261751577/17179869184)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((2331522995/17179869184), (5780624943/17179869184)), (223/17179869184), by norm_num⟩
  | 3 => ⟨((-853813271/8589934592), (-2116888533/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((117251219/2147483648), (581409939/4294967296)), (185/34359738368), by norm_num⟩
  | 5 => ⟨((-1648814465/68719476736), (-510995283/8589934592)), (165/68719476736), by norm_num⟩
  | 6 => ⟨((603802611/68719476736), (5988114105/274877906944)), (61/68719476736), by norm_num⟩
  | 7 => ⟨((-1516217071/549755813888), (-3759208995/549755813888)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((1665734707/2199023255552), (2064956599/1099511627776)), (87/1099511627776), by norm_num⟩
  | 9 => ⟨((-1626663661/8796093022208), (-2016521507/4398046511104)), (43/2199023255552), by norm_num⟩
  | 10 => ⟨((714829075/17592186044416), (3544600493/35184372088832)), (153/35184372088832), by norm_num⟩
  | 11 => ⟨((-2284567291/281474976710656), (-5664206051/281474976710656)), (247/281474976710656), by norm_num⟩
  | 12 => ⟨((209154475/140737488355328), (1037127729/281474976710656)), (183/1125899906842624), by norm_num⟩
  | 13 => ⟨((-2262446045/9007199254740992), (-5609360089/9007199254740992)), (125/4503599627370496), by norm_num⟩
  | 14 => ⟨((1420314873/36028797018963968), (1760717693/18014398509481984)), (159/36028797018963968), by norm_num⟩
  | 15 => ⟨((-832200199/144115188075855872), (-2063302501/144115188075855872)), (189/288230376151711744), by norm_num⟩
  | 16 => ⟨((1828530731/2305843009213693952), (2266769483/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1546745899529/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779044065443305/633825300114114700748351602688), (1831035662451/633825300114114700748351602688)), (2887/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((118128215777481/2475880078570760549798248448), (257446389395/4951760157141521099596496896)), (25985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472461436802723/618970019642690137449562112), (1093935551713/1237940039285380274899124224)), (27613/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771511851999799/154742504910672534362390528), (2187395126461/154742504910672534362390528)), (27617/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774927181746513/4835703278458516698824704), (1025088666553/4835703278458516698824704)), (25895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259051850838107/604462909807314587353088), (224174964003/75557863725914323419136)), (11331/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888219403775615/75557863725914323419136), (2913327109825/75557863725914323419136)), (36833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324464930062785/1180591620717411303424), (546041660677/1180591620717411303424)), (1727/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621888071703065/590295810358705651712), (750470771071/147573952589676412928)), (9501/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824023949476773/73786976294838206464), (468791972563/9223372036854775808)), (47521/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455818508032533/2305843009213693952), (4216354523283/9223372036854775808)), (26741/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797260730145625/576460752303423488), (2106445209731/576460752303423488)), (26755/576460752303423488), by norm_num⟩
  | 5 => ⟨((597524100739825/72057594037927936), (57537271001/2251799813685248)), (46853/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492336142250467/36028797018963968), (5515798823445/36028797018963968)), (70341/36028797018963968), by norm_num⟩
  | 3 => ⟨((372531721843107/2251799813685248), (3440576859855/4503599627370496)), (44017/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114836940003729/2251799813685248), (53599992321/17592186044416)), (44099/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218661047490107/2251799813685248), (20480885731007/2251799813685248)), (265415/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185722974734209/2251799813685248), (40557296224279/2251799813685248)), (534125/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185722974734209/2251799813685248), (40557296224279/2251799813685248)), (2037525185591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((132553413467849/140737488355328), (19683591234833/562949953421312)), (1056145/2251799813685248), by norm_num⟩
  | 2 => ⟨((498692775941401/562949953421312), (37077927679021/562949953421312)), (2063315/2251799813685248), by norm_num⟩
  | 3 => ⟨((1757312248110805/2251799813685248), (131382866757729/1125899906842624)), (3927397/2251799813685248), by norm_num⟩
  | 4 => ⟨((1340749958456271/2251799813685248), (205063273868393/1125899906842624)), (220203/70368744177664), by norm_num⟩
  | 5 => ⟨((723601918802607/2251799813685248), (488389019750377/2251799813685248)), (10957941/2251799813685248), by norm_num⟩
  | 6 => ⟨((506396528766971/9007199254740992), (156940785617675/1125899906842624)), (23591663/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-4900516451/134217728)), (1/67108864), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-266553675/134217728), (-5135504237/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1045156179013961/9007199254740992), (-330093270198859/4503599627370496)), (30439911/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4590150905/17179869184), (2899428723/17179869184)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((1321151631/4294967296), (-1669045339/8589934592)), (5/536870912), by norm_num⟩
  | 3 => ⟨((-4056085401/17179869184), (1281039639/8589934592)), (125/17179869184), by norm_num⟩
  | 4 => ⟨((2334870445/17179869184), (-368712847/4294967296)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-134405947/2147483648), (169798541/4294967296)), (137/68719476736), by norm_num⟩
  | 6 => ⟨((3301132053/137438953472), (-2085203143/137438953472)), (107/137438953472), by norm_num⟩
  | 7 => ⟨((-4343507117/549755813888), (685908239/137438953472)), (143/549755813888), by norm_num⟩
  | 8 => ⟨((5000647369/2199023255552), (-789681043/549755813888)), (167/2199023255552), by norm_num⟩
  | 9 => ⟨((-5117518261/8796093022208), (808136799/2199023255552)), (87/4398046511104), by norm_num⟩
  | 10 => ⟨((589176063/4398046511104), (-1488642997/17592186044416)), (163/35184372088832), by norm_num⟩
  | 11 => ⟨((-3946554239/140737488355328), (1246446245/70368744177664)), (139/140737488355328), by norm_num⟩
  | 12 => ⟨((94659135/17592186044416), (-1913365695/562949953421312)), (109/562949953421312), by norm_num⟩
  | 13 => ⟨((-1073037357/1125899906842624), (2711192201/4503599627370496)), (157/4503599627370496), by norm_num⟩
  | 14 => ⟨((2823725511/18014398509481984), (-891821535/9007199254740992)), (105/18014398509481984), by norm_num⟩
  | 15 => ⟨((-866915769/36028797018963968), (2190394637/144115188075855872)), (131/144115188075855872), by norm_num⟩
  | 16 => ⟨((3992294653/1152921504606846976), (-2521785019/1152921504606846976)), (153/1152921504606846976), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790694403444907/5070602400912917605986812821504), (-366930318473/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27795395878507/9903520314283042199192993792), (-434306479473/316912650057057350374175801344)), (721/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944947744044689/19807040628566084398385987584), (-977019728501/39614081257132168796771975168)), (12979/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889680170457009/2475880078570760549798248448), (-1037873182013/2475880078570760549798248448)), (27581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771346427438917/154742504910672534362390528), (-1037636699017/154742504910672534362390528)), (27583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193712429948821/1208925819614629174706176), (-972533216413/9671406556917033397649408)), (25861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258916453954891/604462909807314587353088), (-850715459011/604462909807314587353088)), (11315/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887999686516571/75557863725914323419136), (-345485493967/18889465931478580854784)), (18389/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297695196953367/4722366482869645213696), (-129505605617/590295810358705651712)), (13793/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621662281853543/590295810358705651712), (-711946542119/295147905179352825856)), (2371/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1823742356052799/73786976294838206464), (-1778864070561/73786976294838206464)), (11857/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911479061917927/4611686018427387904), (-1999844882337/9223372036854775808)), (53367/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594206655825823/1152921504606846976), (-1998124801671/1152921504606846976)), (13345/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194773987243193/144115188075855872), (-1746426055491/144115188075855872)), (23361/72057594037927936), by norm_num⟩
  | 4 => ⟨((745963647451617/18014398509481984), (-1307888824029/18014398509481984)), (70113/36028797018963968), by norm_num⟩
  | 3 => ⟨((1454707173555/8796093022208), (-1631487731005/4503599627370496)), (87693/9007199254740992), by norm_num⟩
  | 2 => ⟨((278584162684737/562949953421312), (-6505754712793/4503599627370496)), (87771/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108596137361191/1125899906842624), (-9708293762385/2251799813685248)), (263707/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182912811548781/2251799813685248), (-2402018134651/281474976710656)), (132249/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182912811548781/2251799813685248), (-2402018134651/281474976710656)), (504489900829124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2115969214330071/2251799813685248), (-2328535657493/140737488355328)), (32333/70368744177664), by norm_num⟩
  | 2 => ⟨((1987715620519787/2251799813685248), (-70018441046571/2251799813685248)), (247341/281474976710656), by norm_num⟩
  | 3 => ⟨((1752425229804797/2251799813685248), (-123613784979349/2251799813685248)), (3616393/2251799813685248), by norm_num⟩
  | 4 => ⟨((339252383765251/562949953421312), (-192400686981987/2251799813685248)), (6025843/2251799813685248), by norm_num⟩
  | 5 => ⟨((6260467331679/17592186044416), (-463788237657859/4503599627370496)), (8292481/2251799813685248), by norm_num⟩
  | 6 => ⟨((1045156179013961/9007199254740992), (-330093270198859/4503599627370496)), (30439911/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-266553675/134217728), (-5135504237/134217728)), (1/67108864), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-5348076547/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-155135230621737/2251799813685248), (-954695137193097/9007199254740992)), (25609819/4503599627370496), by norm_num⟩
  | 1 => ⟨((2838119783/17179869184), (4366414941/17179869184)), (237/17179869184), by norm_num⟩
  | 2 => ⟨((-1701378503/8589934592), (-2617551437/8589934592)), (9/536870912), by norm_num⟩
  | 3 => ⟨((2719818313/17179869184), (2092204739/8589934592)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((-1630459869/17179869184), (-5016887853/34359738368)), (281/34359738368), by norm_num⟩
  | 5 => ⟨((1563868805/34359738368), (4811988667/68719476736)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((-2499995743/137438953472), (-3846214959/137438953472)), (55/34359738368), by norm_num⟩
  | 7 => ⟨((1712779421/274877906944), (658772905/68719476736)), (153/274877906944), by norm_num⟩
  | 8 => ⟨((-2053532839/1099511627776), (-1579668435/549755813888)), (93/549755813888), by norm_num⟩
  | 9 => ⟨((2188514083/4398046511104), (420875497/549755813888)), (25/549755813888), by norm_num⟩
  | 10 => ⟨((-1049565515/8796093022208), (-3229489167/17592186044416)), (97/8796093022208), by norm_num⟩
  | 11 => ⟨((915181159/35184372088832), (1407995783/35184372088832)), (171/70368744177664), by norm_num⟩
  | 12 => ⟨((-2926011433/562949953421312), (-4501635243/562949953421312)), (69/140737488355328), by norm_num⟩
  | 13 => ⟨((2158851995/2251799813685248), (3321369191/2251799813685248)), (103/1125899906842624), by norm_num⟩
  | 14 => ⟨((-2958114853/18014398509481984), (-2275512995/9007199254740992)), (285/18014398509481984), by norm_num⟩
  | 15 => ⟨((1891533233/72057594037927936), (1455051161/36028797018963968)), (23/9007199254740992), by norm_num⟩
  | 16 => ⟨((-2267849299/576460752303423488), (-3489060301/576460752303423488)), (223/576460752303423488), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-2796920202347/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889386570132065/316912650057057350374175801344), (-1655022397979/316912650057057350374175801344)), (5783/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889746484748781/39614081257132168796771975168), (-1861558102249/19807040628566084398385987584)), (26029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889521484453745/2475880078570760549798248448), (-3954975196469/2475880078570760549798248448)), (13831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442796831396501/38685626227668133590597632), (-1977017559349/77371252455336267181195264)), (27669/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96846865003549/604462909807314587353088), (-1852954647475/4835703278458516698824704)), (12973/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258785113146445/604462909807314587353088), (-1620836116665/302231454903657293676544)), (22711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887785431123637/75557863725914323419136), (-5265845866443/75557863725914323419136)), (18459/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297533782852959/4722366482869645213696), (-3947747313045/4722366482869645213696)), (27701/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810719582313075/295147905179352825856), (-339093325143/36893488147419103232)), (38107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911730851278391/36893488147419103232), (-1694469767695/18446744073709551616)), (47663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822639976560113/9223372036854775808), (-7619633831887/9223372036854775808)), (13415/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398471374755763/288230376151711744), (-7612787573351/1152921504606846976)), (26855/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194489596998289/144115188075855872), (-6653492441847/144115188075855872)), (47053/144115188075855872), by norm_num⟩
  | 4 => ⟨((745746986305851/18014398509481984), (-4982429342377/18014398509481984)), (17673/9007199254740992), by norm_num⟩
  | 3 => ⟨((744533373136999/4503599627370496), (-6214594264989/4503599627370496)), (88561/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113765717299871/2251799813685248), (-12388921572801/2251799813685248)), (44429/1125899906842624), by norm_num⟩
  | 1 => ⟨((276924050486001/281474976710656), (-18482925999129/1125899906842624)), (134029/1125899906842624), by norm_num⟩
  | 0 => ⟨((136185523175027/140737488355328), (-36565293116303/1125899906842624)), (135519/562949953421312), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((136185523175027/140737488355328), (-36565293116303/1125899906842624)), (516963960887718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1053058768697649/1125899906842624), (-70765275567793/1125899906842624)), (1084297/2251799813685248), by norm_num⟩
  | 2 => ⟨((1960964805833539/2251799813685248), (-264748201871505/2251799813685248)), (541149/562949953421312), by norm_num⟩
  | 3 => ⟨((1676566156715775/2251799813685248), (-461108401486263/2251799813685248)), (16715/8796093022208), by norm_num⟩
  | 4 => ⟨((576928087508641/1125899906842624), (-686631854049205/2251799813685248)), (4062171/1125899906842624), by norm_num⟩
  | 5 => ⟨((763763070237701/4503599627370496), (-1407362057574063/4503599627370496)), (6640357/1125899906842624), by norm_num⟩
  | 6 => ⟨((-155135230621737/2251799813685248), (-954695137193097/9007199254740992)), (25609819/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-5348076547/134217728)), (1/67108864), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-2771069931/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-950491621487427/9007199254740992), (115211731644769/2251799813685248)), (11806947/2251799813685248), by norm_num⟩
  | 1 => ⟨((4504934217/17179869184), (-1092111199/8589934592)), (113/8589934592), by norm_num⟩
  | 2 => ⟨((-87455789/268435456), (2713794381/17179869184)), (283/17179869184), by norm_num⟩
  | 3 => ⟨((579518591/2147483648), (-2247841901/17179869184)), (237/17179869184), by norm_num⟩
  | 4 => ⟨((-2880099201/17179869184), (698209661/8589934592)), (297/34359738368), by norm_num⟩
  | 5 => ⟨((5725422125/68719476736), (-2775977327/68719476736)), (149/34359738368), by norm_num⟩
  | 6 => ⟨((-4742379837/137438953472), (2299348173/137438953472)), (249/137438953472), by norm_num⟩
  | 7 => ⟨((1683481599/137438953472), (-408118969/68719476736)), (179/274877906944), by norm_num⟩
  | 8 => ⟨((-1045823655/274877906944), (253534385/137438953472)), (7/34359738368), by norm_num⟩
  | 9 => ⟨((2310021471/2199023255552), (-2240032993/4398046511104)), (125/2199023255552), by norm_num⟩
  | 10 => ⟨((-4592150171/17592186044416), (69578411/549755813888)), (251/17592186044416), by norm_num⟩
  | 11 => ⟨((4149477999/70368744177664), (-1005939527/35184372088832)), (229/70368744177664), by norm_num⟩
  | 12 => ⟨((-26851733/2199023255552), (208305485/35184372088832)), (191/281474976710656), by norm_num⟩
  | 13 => ⟨((5255802083/2251799813685248), (-2548281525/2251799813685248)), (295/2251799813685248), by norm_num⟩
  | 14 => ⟨((-3731479299/9007199254740992), (452302979/2251799813685248)), (211/9007199254740992), by norm_num⟩
  | 15 => ⟨((4945268119/72057594037927936), (-9366089/281474976710656)), (141/36028797018963968), by norm_num⟩
  | 16 => ⟨((-384016551/36028797018963968), (744763419/144115188075855872)), (177/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (3504204356679/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778654114115945/633825300114114700748351602688), (2073287037101/316912650057057350374175801344)), (1447/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944806208833003/19807040628566084398385987584), (4664000913511/39614081257132168796771975168)), (26053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944689411306243/1237940039285380274899124224), (4954415092891/2475880078570760549798248448)), (27689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885522210725567/77371252455336267181195264), (4953193581411/154742504910672534362390528)), (13849/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549415610187169/9671406556917033397649408), (1160580332921/2417851639229258349412352)), (3247/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629333702492617/302231454903657293676544), (4060733744597/604462909807314587353088)), (11369/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887593673902021/75557863725914323419136), (3298130080429/37778931862957161709568)), (18483/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297389544122119/4722366482869645213696), (2472533729069/2361183241434822606848)), (27739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405310038353575/147573952589676412928), (6796011222421/590295810358705651712)), (19083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823211915622541/73786976294838206464), (8489830838785/73786976294838206464)), (373/576460752303423488), by norm_num⟩
  | 7 => ⟨((1822357562206573/9223372036854775808), (9543935426157/9223372036854775808)), (53761/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593601333293261/1152921504606846976), (9535034022305/1152921504606846976)), (841/18014398509481984), by norm_num⟩
  | 5 => ⟨((1194238986754263/144115188075855872), (8333146100931/144115188075855872)), (23583/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491114139438993/36028797018963968), (3119928839997/9007199254740992)), (70891/36028797018963968), by norm_num⟩
  | 3 => ⟨((46518285221137/281474976710656), (1945583511845/1125899906842624)), (22215/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113273913259213/2251799813685248), (7756132562619/1125899906842624)), (5577/140737488355328), by norm_num⟩
  | 1 => ⟨((553466615971027/562949953421312), (23137604999749/1125899906842624)), (67389/562949953421312), by norm_num⟩
  | 0 => ⟨((271964593708883/281474976710656), (45753332242081/1125899906842624)), (273295/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((271964593708883/281474976710656), (45753332242081/1125899906842624)), (1042537693503951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524621446857299/562949953421312), (88414867704821/1125899906842624)), (550335/1125899906842624), by norm_num⟩
  | 2 => ⟨((970862022934791/1125899906842624), (164790264346237/1125899906842624)), (1112165/1125899906842624), by norm_num⟩
  | 3 => ⟨((1626107668701827/2251799813685248), (568393721078829/2251799813685248)), (4487195/2251799813685248), by norm_num⟩
  | 4 => ⟨((1030799769119041/2251799813685248), (205229031255583/562949953421312)), (546627/140737488355328), by norm_num⟩
  | 5 => ⟨((10787062345979/140737488355328), (751576713876927/2251799813685248)), (7192099/1125899906842624), by norm_num⟩
  | 6 => ⟨((-950491621487427/9007199254740992), (115211731644769/2251799813685248)), (11806947/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-2771069931/67108864)), (1/67108864), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-2860330403/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((206228412135487/9007199254740992), (241011221362941/2251799813685248)), (37025765/9007199254740992), by norm_num⟩
  | 1 => ⟨((-126115187/2147483648), (-2358175573/8589934592)), (183/17179869184), by norm_num⟩
  | 2 => ⟨((1293916271/17179869184), (6048600921/17179869184)), (237/17179869184), by norm_num⟩
  | 3 => ⟨((-1106276569/17179869184), (-2585725841/8589934592)), (205/17179869184), by norm_num⟩
  | 4 => ⟨((1418771687/34359738368), (3316127917/17179869184)), (133/17179869184), by norm_num⟩
  | 5 => ⟨((-1455631011/68719476736), (-850570017/8589934592)), (275/68719476736), by norm_num⟩
  | 6 => ⟨((622269971/68719476736), (5817784049/137438953472)), (237/137438953472), by norm_num⟩
  | 7 => ⟨((-456025989/137438953472), (-4263520417/274877906944)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((1169683567/1099511627776), (5467856977/1099511627776)), (57/274877906944), by norm_num⟩
  | 9 => ⟨((-1333412939/4398046511104), (-1558308471/1099511627776)), (131/2199023255552), by norm_num⟩
  | 10 => ⟨((171006833/2199023255552), (3197585849/8796093022208)), (271/17592186044416), by norm_num⟩
  | 11 => ⟨((-637998351/35184372088832), (-2982416643/35184372088832)), (255/70368744177664), by norm_num⟩
  | 12 => ⟨((136369455/35184372088832), (637478971/35184372088832)), (55/70368744177664), by norm_num⟩
  | 13 => ⟨((-860998759/1125899906842624), (-2012432341/562949953421312)), (175/1125899906842624), by norm_num⟩
  | 14 => ⟨((1261953265/9007199254740992), (1474796297/2251799813685248)), (259/9007199254740992), by norm_num⟩
  | 15 => ⟨((-863158991/36028797018963968), (-2017481501/18014398509481984)), (179/36028797018963968), by norm_num⟩
  | 16 => ⟨((553489775/144115188075855872), (646842235/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (1771620554285/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889277279862745/316912650057057350374175801344), (2096144523611/633825300114114700748351602688)), (11551/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889500827411473/39614081257132168796771975168), (2357705840177/39614081257132168796771975168)), (25993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889260789612553/2475880078570760549798248448), (2504496984947/2475880078570760549798248448)), (27621/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770926986097785/154742504910672534362390528), (625965260509/38685626227668133590597632)), (13813/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774653074569805/4835703278458516698824704), (2346694237627/9671406556917033397649408)), (1619/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629286130355655/302231454903657293676544), (2052682193697/604462909807314587353088)), (22671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887440252511129/75557863725914323419136), (1667171461209/37778931862957161709568)), (2303/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648637758331783/2361183241434822606848), (312456279085/590295810358705651712)), (6911/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810542525777235/295147905179352825856), (1717610578531/295147905179352825856)), (19011/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823020563985709/73786976294838206464), (4291331143791/73786976294838206464)), (23773/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455536439828007/2305843009213693952), (4824044040405/9223372036854775808)), (26757/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593393857340319/1152921504606846976), (4819418484483/1152921504606846976)), (26773/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194062302556069/144115188075855872), (2105896332283/72057594037927936)), (46889/144115188075855872), by norm_num⟩
  | 4 => ⟨((745429400661625/18014398509481984), (3153652534513/18014398509481984)), (17601/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488282849572963/9007199254740992), (3932994442395/4503599627370496)), (44065/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225993720669107/4503599627370496), (3919416985629/1125899906842624)), (176635/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213160603049857/2251799813685248), (23381137966439/2251799813685248)), (265895/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174801285858615/2251799813685248), (46223278066765/2251799813685248)), (267789/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174801285858615/2251799813685248), (46223278066765/2251799813685248)), (1021533970359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2099486825074347/2251799813685248), (44642709340881/1125899906842624)), (1056517/2251799813685248), by norm_num⟩
  | 2 => ⟨((1953936142960615/2251799813685248), (10405762928745/140737488355328)), (513473/562949953421312), by norm_num⟩
  | 3 => ⟨((841581647886329/1125899906842624), (144468943699071/1125899906842624)), (1934067/1125899906842624), by norm_num⟩
  | 4 => ⟨((610523537827795/1125899906842624), (215973748585905/1125899906842624)), (3387669/1125899906842624), by norm_num⟩
  | 5 => ⟨((579259893675611/2251799813685248), (936900740559547/4503599627370496)), (19894481/4503599627370496), by norm_num⟩
  | 6 => ⟨((206228412135487/9007199254740992), (241011221362941/2251799813685248)), (37025765/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-2860330403/67108864)), (1/67108864), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-5885945383/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1834357457790505/18014398509481984), (237182622910605/18014398509481984)), (32313059/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4616713041/17179869184), (-596941509/17179869184)), (83/17179869184), by norm_num⟩
  | 2 => ⟨((3045942597/8589934592), (98460179/2147483648)), (7/1073741824), by norm_num⟩
  | 3 => ⟨((-5358944757/17179869184), (-86614019/2147483648)), (25/4294967296), by norm_num⟩
  | 4 => ⟨((7071281219/34359738368), (914317447/34359738368)), (135/34359738368), by norm_num⟩
  | 5 => ⟨((-1866151653/17179869184), (-15080851/1073741824)), (145/68719476736), by norm_num⟩
  | 6 => ⟨((6566508263/137438953472), (106131281/17179869184)), (65/68719476736), by norm_num⟩
  | 7 => ⟨((-4951254789/274877906944), (-320098897/137438953472)), (25/68719476736), by norm_num⟩
  | 8 => ⟨((1633330655/274877906944), (211189835/274877906944)), (67/549755813888), by norm_num⟩
  | 9 => ⟨((-957878497/549755813888), (-30963449/137438953472)), (5/137438953472), by norm_num⟩
  | 10 => ⟨((4044634029/8796093022208), (522971629/8796093022208)), (43/4398046511104), by norm_num⟩
  | 11 => ⟨((-3881462211/35184372088832), (-501873495/35184372088832)), (85/35184372088832), by norm_num⟩
  | 12 => ⟨((3414467099/140737488355328), (441490975/140737488355328)), (19/35184372088832), by norm_num⟩
  | 13 => ⟨((-2772607515/562949953421312), (-716996919/1125899906842624)), (125/1125899906842624), by norm_num⟩
  | 14 => ⟨((2090591481/2251799813685248), (540627421/4503599627370496)), (3/140737488355328), by norm_num⟩
  | 15 => ⟨((-5885003489/36028797018963968), (-190232901/9007199254740992)), (137/36028797018963968), by norm_num⟩
  | 16 => ⟨((1941357699/72057594037927936), (125508883/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (20937314269/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889229192419069/316912650057057350374175801344), (198159841159/633825300114114700748351602688)), (1441/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889392782912047/39614081257132168796771975168), (222885761225/39614081257132168796771975168)), (12969/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889146190521563/2475880078570760549798248448), (118380578707/1237940039285380274899124224)), (3445/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770812609781941/154742504910672534362390528), (236699349315/154742504910672534362390528)), (27559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774599578946231/4835703278458516698824704), (110919995849/4835703278458516698824704)), (12919/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629239439875285/302231454903657293676544), (97022185067/302231454903657293676544)), (22609/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887288951305681/75557863725914323419136), (39399889205/9444732965739290427392)), (9185/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324290606975201/1180591620717411303424), (236291775403/4722366482869645213696)), (27555/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405232545735153/147573952589676412928), (324726508627/590295810358705651712)), (18945/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822827919699869/73786976294838206464), (202823145315/36893488147419103232)), (11841/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455482581781681/2305843009213693952), (455992329991/9223372036854775808)), (53287/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593180038102669/1152921504606846976), (455543081063/1152921504606846976)), (53289/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596938510689661/72057594037927936), (398095388071/144115188075855872)), (46633/144115188075855872), by norm_num⟩
  | 4 => ⟨((93161530694541/2251799813685248), (596134957423/36028797018963968)), (69955/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487946260121385/9007199254740992), (92925978517/1125899906842624)), (2733/281474976710656), by norm_num⟩
  | 2 => ⟨((2225339349297725/4503599627370496), (740773211093/2251799813685248)), (87475/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106112879975907/1125899906842624), (276149153887/281474976710656)), (65631/562949953421312), by norm_num⟩
  | 0 => ⟨((543279158645043/562949953421312), (4366160006729/2251799813685248)), (262727/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543279158645043/562949953421312), (4366160006729/2251799813685248)), (1002223972800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2097174364894915/2251799813685248), (2106798055981/562949953421312)), (508113/1125899906842624), by norm_num⟩
  | 2 => ⟨((976567559974575/1125899906842624), (15697036115419/2251799813685248)), (118781/140737488355328), by norm_num⟩
  | 3 => ⟨((846987013821903/1125899906842624), (3403769767833/281474976710656)), (3323349/2251799813685248), by norm_num⟩
  | 4 => ⟨((1274006022819709/2251799813685248), (40969166425869/2251799813685248)), (2540263/1125899906842624), by norm_num⟩
  | 5 => ⟨((1440103923740621/4503599627370496), (11589610332865/562949953421312)), (370857/140737488355328), by norm_num⟩
  | 6 => ⟨((1834357457790505/18014398509481984), (237182622910605/18014398509481984)), (32313059/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-5885945383/134217728)), (1/67108864), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-1509955411/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((457626782151541/9007199254740992), (-741547685353747/9007199254740992)), (28250443/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2363731955/17179869184), (1915119513/8589934592)), (37/4294967296), by norm_num⟩
  | 2 => ⟨((1600276199/8589934592), (-2593119891/8589934592)), (203/17179869184), by norm_num⟩
  | 3 => ⟨((-1444542761/8589934592), (2340766281/8589934592)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((1955947157/17179869184), (-3169456299/17179869184)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-2118721237/34359738368), (3433218707/34359738368)), (141/34359738368), by norm_num⟩
  | 6 => ⟨((1912534491/68719476736), (-3099109537/68719476736)), (129/68719476736), by norm_num⟩
  | 7 => ⟨((-2959565379/274877906944), (2397869773/137438953472)), (101/137438953472), by norm_num⟩
  | 8 => ⟨((2003662905/549755813888), (-3246775861/549755813888)), (139/549755813888), by norm_num⟩
  | 9 => ⟨((-1205782163/1099511627776), (1953873783/1099511627776)), (169/2199023255552), by norm_num⟩
  | 10 => ⟨((2612254903/8796093022208), (-4232950633/8796093022208)), (185/8796093022208), by norm_num⟩
  | 11 => ⟨((-2572406333/35184372088832), (4168379205/35184372088832)), (23/4398046511104), by norm_num⟩
  | 12 => ⟨((145129281/8796093022208), (-3762726715/140737488355328)), (21/17592186044416), by norm_num⟩
  | 13 => ⟨((-1934854787/562949953421312), (783819449/140737488355328)), (71/281474976710656), by norm_num⟩
  | 14 => ⟨((2994105083/4503599627370496), (-4851708381/4503599627370496)), (111/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1081091583/9007199254740992), (3503645295/18014398509481984)), (81/9007199254740992), by norm_num⟩
  | 16 => ⟨((2927650279/144115188075855872), (-4744023673/144115188075855872)), (221/144115188075855872), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1325903388213/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889182694754631/316912650057057350374175801344), (-784230816771/316912650057057350374175801344)), (23089/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644055813079/19807040628566084398385987584), (-882080341303/19807040628566084398385987584)), (12989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889034907859415/2475880078570760549798248448), (-936987087447/1237940039285380274899124224)), (27605/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770701249115015/154742504910672534362390528), (-1873472005079/154742504910672534362390528)), (3451/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549094674457629/9671406556917033397649408), (-877923313943/4835703278458516698824704)), (12943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157298421751859/75557863725914323419136), (-191979077929/75557863725914323419136)), (22653/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887140099534547/75557863725914323419136), (-1247364367443/37778931862957161709568)), (18409/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648525326829529/2361183241434822606848), (-1870172609299/4722366482869645213696)), (6905/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620776273626901/590295810358705651712), (-1285033990809/295147905179352825856)), (18993/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822635204012229/73786976294838206464), (-3210457340819/73786976294838206464)), (47495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821713070435603/9223372036854775808), (-3608841278891/9223372036854775808)), (53451/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398240554581007/288230376151711744), (-450648830575/144115188075855872)), (53475/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193685797439823/144115188075855872), (-3150439524579/144115188075855872)), (23409/72057594037927936), by norm_num⟩
  | 4 => ⟨((372574099132099/9007199254740992), (-589683297487/4503599627370496)), (70279/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487583949514801/9007199254740992), (-2941260806329/4503599627370496)), (87943/9007199254740992), by norm_num⟩
  | 2 => ⟨((556152048012075/1125899906842624), (-5861106927363/2251799813685248)), (22021/562949953421312), by norm_num⟩
  | 1 => ⟨((2211112827238445/2251799813685248), (-17476613035445/2251799813685248)), (1035/8796093022208), by norm_num⟩
  | 0 => ⟨((271353354592561/281474976710656), (-8632145641427/562949953421312)), (532769/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((271353354592561/281474976710656), (-8632145641427/562949953421312)), (2032352456099700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092236131944743/2251799813685248), (-66573922968381/2251799813685248)), (521781/1125899906842624), by norm_num⟩
  | 2 => ⟨((1942010971854069/2251799813685248), (-61856460877753/1125899906842624)), (2000935/2251799813685248), by norm_num⟩
  | 3 => ⟨((834022124205869/1125899906842624), (-53346627428689/562949953421312)), (3671179/2251799813685248), by norm_num⟩
  | 4 => ⟨((607700070738567/1125899906842624), (-316136574890139/2251799813685248)), (6134711/2251799813685248), by norm_num⟩
  | 5 => ⟨((1223248320342813/4503599627370496), (-682533918889965/4503599627370496)), (521557/140737488355328), by norm_num⟩
  | 6 => ⟨((457626782151541/9007199254740992), (-741547685353747/9007199254740992)), (28250443/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1509955411/33554432)), (1/67108864), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile005Terms1
