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
namespace Reinmann.XiBand97.Tile062Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨62,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80309/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80309/2560))
  have he : value ((69/80), (80309/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-74011391749/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1330312737734991/9007199254740992), (15693812166145/562949953421312)), (96761/281474976710656), by norm_num⟩
  | 1 => ⟨((-89202753995/274877906944), (-2104664905/34359738368)), (105/137438953472), by norm_num⟩
  | 2 => ⟨((48999620861/137438953472), (18497685825/274877906944)), (233/274877906944), by norm_num⟩
  | 3 => ⟨((-71775447491/274877906944), (-52921315/1073741824)), (173/274877906944), by norm_num⟩
  | 4 => ⟨((39426694319/274877906944), (7441920895/274877906944)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((-69303441409/1099511627776), (-6540628597/549755813888)), (171/1099511627776), by norm_num⟩
  | 6 => ⟨((101516816505/4398046511104), (19161639873/4398046511104)), (253/4398046511104), by norm_num⟩
  | 7 => ⟨((-31865034891/4398046511104), (-751829037/549755813888)), (161/8796093022208), by norm_num⟩
  | 8 => ⟨((17503659455/8796093022208), (825968619/2199023255552)), (179/35184372088832), by norm_num⟩
  | 9 => ⟨((-68372392441/140737488355328), (-806594911/8796093022208)), (177/140737488355328), by norm_num⟩
  | 10 => ⟨((60091800433/562949953421312), (11342529039/562949953421312)), (157/562949953421312), by norm_num⟩
  | 11 => ⟨((-48012793021/2251799813685248), (-9062575845/2251799813685248)), (253/4503599627370496), by norm_num⟩
  | 12 => ⟨((35164962951/9007199254740992), (13275009587/18014398509481984)), (187/18014398509481984), by norm_num⟩
  | 13 => ⟨((-23773944879/36028797018963968), (-17949647587/144115188075855872)), (255/144115188075855872), by norm_num⟩
  | 14 => ⟨((29849540565/288230376151711744), (352137561/18014398509481984)), (81/288230376151711744), by norm_num⟩
  | 15 => ⟨((-34979276881/2305843009213693952), (-13204911849/4611686018427387904)), (3/72057594037927936), by norm_num⟩
  | 16 => ⟨((19214331715/9223372036854775808), (3626769607/9223372036854775808)), (213/36893488147419103232), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (121506614635/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889522907378119/316912650057057350374175801344), (35959840703/79228162514264337593543950336)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945026760018331/19807040628566084398385987584), (323584837501/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236231009085525/309485009821345068724781056), (21483902267/154742504910672534362390528)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771514322098671/154742504910672534362390528), (343667701181/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549856832786135/9671406556917033397649408), (322109086759/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259054164944555/604462909807314587353088), (281766093625/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888223451750859/75557863725914323419136), (228860581021/37778931862957161709568)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324465751906905/1180591620717411303424), (343160778743/4722366482869645213696)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50684156248851/18446744073709551616), (117908693171/147573952589676412928)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824030721279759/73786976294838206464), (294613349169/36893488147419103232)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227910311257055/1152921504606846976), (662444771977/9223372036854775808)), (6663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594530966078307/1152921504606846976), (82737641201/144115188075855872)), (833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195057695553225/144115188075855872), (578552491351/144115188075855872)), (729/18014398509481984), by norm_num⟩
  | 4 => ⟨((746176365277909/18014398509481984), (866608242835/36028797018963968)), (2187/9007199254740992), by norm_num⟩
  | 3 => ⟨((745075858631843/4503599627370496), (1081127809125/9007199254740992)), (10937/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229735771112691/4503599627370496), (2155871594659/4503599627370496)), (21879/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218784280275673/2251799813685248), (3217894342999/2251799813685248)), (32835/2251799813685248), by norm_num⟩
  | 0 => ⟨((546522484016651/562949953421312), (1593104440223/562949953421312)), (65737/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546522484016651/562949953421312), (1593104440223/562949953421312)), (250766762740325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2122279508071565/2251799813685248), (12372927869373/2251799813685248)), (128011/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000141039920155/2251799813685248), (23322509498785/2251799813685248)), (15169/140737488355328), by norm_num⟩
  | 3 => ⟨((1776365827820729/2251799813685248), (20716010419285/1125899906842624)), (109047/562949953421312), by norm_num⟩
  | 4 => ⟨((1400550316565255/2251799813685248), (32684266846413/1125899906842624)), (704239/2251799813685248), by norm_num⟩
  | 5 => ⟨((869201663548707/2251799813685248), (162628880241467/4503599627370496)), (458459/1125899906842624), by norm_num⟩
  | 6 => ⟨((1330312737734991/9007199254740992), (15693812166145/562949953421312)), (96761/281474976710656), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-74011391749/1073741824)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-38780179575/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-38621197186343/281474976710656), (-28328399717483/9007199254740992)), (6254905/9007199254740992), by norm_num⟩
  | 1 => ⟨((43422164509/137438953472), (995308699/137438953472)), (441/274877906944), by norm_num⟩
  | 2 => ⟨((-3124475897/8589934592), (-2291782973/274877906944)), (255/137438953472), by norm_num⟩
  | 3 => ⟨((76739963987/274877906944), (1759008437/274877906944)), (197/137438953472), by norm_num⟩
  | 4 => ⟨((-22087537139/137438953472), (-2025133303/549755813888)), (57/68719476736), by norm_num⟩
  | 5 => ⟨((81373494011/1099511627776), (932608351/549755813888)), (211/549755813888), by norm_num⟩
  | 6 => ⟨((-31228232379/1099511627776), (-2863213449/4398046511104)), (325/2199023255552), by norm_num⟩
  | 7 => ⟨((20544474959/2199023255552), (941827515/4398046511104)), (215/4398046511104), by norm_num⟩
  | 8 => ⟨((-5913175223/2199023255552), (-542159499/8796093022208)), (497/35184372088832), by norm_num⟩
  | 9 => ⟨((12102745885/17592186044416), (2219321565/140737488355328)), (511/140737488355328), by norm_num⟩
  | 10 => ⟨((-89176327229/562949953421312), (-2044070701/562949953421312)), (473/562949953421312), by norm_num⟩
  | 11 => ⟨((37333833041/1125899906842624), (427876975/562949953421312)), (199/1125899906842624), by norm_num⟩
  | 12 => ⟨((-55966359/8796093022208), (-1313630859/9007199254740992)), (613/18014398509481984), by norm_num⟩
  | 13 => ⟨((81206227223/72057594037927936), (1861382667/72057594037927936)), (109/18014398509481984), by norm_num⟩
  | 14 => ⟨((-13356017733/72057594037927936), (-2449138275/576460752303423488)), (9/9007199254740992), by norm_num⟩
  | 15 => ⟨((65607183645/2305843009213693952), (3007652951/4611686018427387904)), (355/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-75533061527/18446744073709551616), (-432836053/4611686018427387904)), (411/18446744073709551616), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-4062422379869/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444723341882963/158456325028528675187087900672), (-2404184491029/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889881344904689/39614081257132168796771975168), (-1352109603783/9903520314283042199192993792)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889664263571501/2475880078570760549798248448), (-2872648750459/1237940039285380274899124224)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110708095720139/9671406556917033397649408), (-2871991523207/77371252455336267181195264)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549682549465637/9671406556917033397649408), (-5383587578513/9671406556917033397649408)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258900625615011/604462909807314587353088), (-147163834177/18889465931478580854784)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943985999611453/37778931862957161709568), (-3824950624299/37778931862957161709568)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297672712556019/4722366482869645213696), (-716891908295/590295810358705651712)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621628575425771/590295810358705651712), (-985261126825/73786976294838206464)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823696042474811/73786976294838206464), (-9847028940057/73786976294838206464)), (5977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822900280980625/9223372036854775808), (-11070232896373/9223372036854775808)), (6731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594141650112573/1152921504606846976), (-5530320569643/576460752303423488)), (1685/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194709065847643/144115188075855872), (-9667272443155/144115188075855872)), (1477/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491813872022347/36028797018963968), (-14479337034933/36028797018963968)), (4441/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489450390138275/9007199254740992), (-18061433390051/9007199254740992)), (5569/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114125118193013/2251799813685248), (-18004851740493/2251799813685248)), (1399/281474976710656), by norm_num⟩
  | 1 => ⟨((138521881826965/140737488355328), (-13432956546191/562949953421312)), (8461/562949953421312), by norm_num⟩
  | 0 => ⟨((1090203045118355/1125899906842624), (-53166916779431/1125899906842624)), (34385/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090203045118355/1125899906842624), (-53166916779431/1125899906842624)), (131168369773482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263281831568541/281474976710656), (-12870312498523/140737488355328)), (34919/562949953421312), by norm_num⟩
  | 2 => ⟨((975642579118799/1125899906842624), (-96307515135283/562949953421312)), (71711/562949953421312), by norm_num⟩
  | 3 => ⟨((406242991381345/562949953421312), (-166909530561395/562949953421312)), (297637/1125899906842624), by norm_num⟩
  | 4 => ⟨((121835498715795/281474976710656), (-963578756132465/2251799813685248)), (606063/1125899906842624), by norm_num⟩
  | 5 => ⟨((19117916635653/4503599627370496), (-834163659429125/2251799813685248)), (4173407/4503599627370496), by norm_num⟩
  | 6 => ⟨((-38621197186343/281474976710656), (-28328399717483/9007199254740992)), (6254905/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-38780179575/536870912)), (1/536870912), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-40385395339/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1121341094008445/9007199254740992), (197757413929297/9007199254740992)), (2583723/9007199254740992), by norm_num⟩
  | 1 => ⟨((-82057449601/274877906944), (-14471483399/274877906944)), (191/274877906944), by norm_num⟩
  | 2 => ⟨((3074455789/8589934592), (542204713/8589934592)), (231/274877906944), by norm_num⟩
  | 3 => ⟨((-19659261341/68719476736), (-13868267927/274877906944)), (187/274877906944), by norm_num⟩
  | 4 => ⟨((11785212459/68719476736), (4156831763/137438953472)), (113/274877906944), by norm_num⟩
  | 5 => ⟨((-45215528391/549755813888), (-15948235575/1099511627776)), (219/1099511627776), by norm_num⟩
  | 6 => ⟨((36140700595/1099511627776), (12747399565/2199023255552)), (177/2199023255552), by norm_num⟩
  | 7 => ⟨((-49520922921/4398046511104), (-17466816661/8796093022208)), (245/8796093022208), by norm_num⟩
  | 8 => ⟨((3710812093/1099511627776), (2617724819/4398046511104)), (149/17592186044416), by norm_num⟩
  | 9 => ⟨((-31637826759/35184372088832), (-11159164389/70368744177664)), (161/70368744177664), by norm_num⟩
  | 10 => ⟨((60691356181/281474976710656), (10703403015/281474976710656)), (157/281474976710656), by norm_num⟩
  | 11 => ⟨((-6615068913/140737488355328), (-18665919631/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 12 => ⟨((84598626537/9007199254740992), (3729910037/2251799813685248)), (223/9007199254740992), by norm_num⟩
  | 13 => ⟨((-62418045125/36028797018963968), (-11007918333/36028797018963968)), (167/36028797018963968), by norm_num⟩
  | 14 => ⟨((21381705049/72057594037927936), (15083334477/288230376151711744)), (231/288230376151711744), by norm_num⟩
  | 15 => ⟨((-13672290523/288230376151711744), (-301402137/36028797018963968)), (149/1152921504606846976), by norm_num⟩
  | 16 => ⟨((65569441627/9223372036854775808), (1445461519/1152921504606846976)), (181/9223372036854775808), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (227387743101/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778966194783/633825300114114700748351602688), (134552214805/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889753367741251/39614081257132168796771975168), (302687852199/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889529225730725/2475880078570760549798248448), (321538011475/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442798887021785/38685626227668133590597632), (321461729733/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774779029813845/4835703278458516698824704), (1176911515/37778931862957161709568)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258792815881893/604462909807314587353088), (32943398043/75557863725914323419136)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798904688567/75557863725914323419136), (53514046251/9444732965739290427392)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648772362146921/2361183241434822606848), (160475754801/2361183241434822606848)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101340972911817/36893488147419103232), (441092692317/590295810358705651712)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911742119346553/36893488147419103232), (551042615499/73786976294838206464)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822668121903445/9223372036854775808), (309739399445/4611686018427387904)), (6663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593917128424601/1152921504606846976), (309462053325/576460752303423488)), (833/144115188075855872), by norm_num⟩
  | 5 => ⟨((597260591901973/72057594037927936), (540935233789/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((745774576897039/18014398509481984), (50634862673/2251799813685248)), (8747/36028797018963968), by norm_num⟩
  | 3 => ⟨((186143665859401/1125899906842624), (1010522174317/9007199254740992)), (1367/1125899906842624), by norm_num⟩
  | 2 => ⟨((2227737218269815/4503599627370496), (251816762907/562949953421312)), (21877/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107900986401193/1125899906842624), (3005577893287/2251799813685248)), (32831/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180187120860255/2251799813685248), (2973287945379/1125899906842624)), (65727/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180187120860255/2251799813685248), (2973287945379/1125899906842624)), (250728615767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055418090745187/1125899906842624), (2878730180955/562949953421312)), (63811/1125899906842624), by norm_num⟩
  | 2 => ⟨((989319024855459/1125899906842624), (21588163515347/2251799813685248)), (60143/562949953421312), by norm_num⟩
  | 3 => ⟨((869203039091073/1125899906842624), (37938684864655/2251799813685248)), (427391/2251799813685248), by norm_num⟩
  | 4 => ⟨((670711563810793/1125899906842624), (58577889531855/2251799813685248)), (168575/562949953421312), by norm_num⟩
  | 5 => ⟨((398788699435231/1125899906842624), (69791049193395/2251799813685248)), (1676919/4503599627370496), by norm_num⟩
  | 6 => ⟨((1121341094008445/9007199254740992), (197757413929297/9007199254740992)), (2583723/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-40385395339/536870912)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-83701685033/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-879763917578959/9007199254740992), (-73082751450871/1125899906842624)), (5980347/9007199254740992), by norm_num⟩
  | 1 => ⟨((16678857491/68719476736), (44336868913/274877906944)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((-20722701945/68719476736), (-13771622549/68719476736)), (285/137438953472), by norm_num⟩
  | 3 => ⟨((17164659955/68719476736), (22814130967/137438953472)), (237/137438953472), by norm_num⟩
  | 4 => ⟨((-333223263/2147483648), (-28345492875/274877906944)), (37/34359738368), by norm_num⟩
  | 5 => ⟨((42395069547/549755813888), (28174361495/549755813888)), (37/68719476736), by norm_num⟩
  | 6 => ⟨((-70231860157/2199023255552), (-46673772155/2199023255552)), (493/2199023255552), by norm_num⟩
  | 7 => ⟨((49862747523/4398046511104), (33137133371/4398046511104)), (11/137438953472), by norm_num⟩
  | 8 => ⟨((-61952136449/17592186044416), (-20585670767/8796093022208)), (55/2199023255552), by norm_num⟩
  | 9 => ⟨((2138128831/2199023255552), (45469751271/70368744177664)), (61/8796093022208), by norm_num⟩
  | 10 => ⟨((-17001761761/70368744177664), (-45195234919/281474976710656)), (61/35184372088832), by norm_num⟩
  | 11 => ⟨((61451332157/1125899906842624), (5104815445/140737488355328)), (443/1125899906842624), by norm_num⟩
  | 12 => ⟨((-50900274639/4503599627370496), (-33826639587/4503599627370496)), (369/4503599627370496), by norm_num⟩
  | 13 => ⟨((77835342109/36028797018963968), (25863397431/18014398509481984)), (567/36028797018963968), by norm_num⟩
  | 14 => ⟨((-55261016913/144115188075855872), (-18362322361/72057594037927936)), (405/144115188075855872), by norm_num⟩
  | 15 => ⟨((73236516481/1152921504606846976), (48670567403/1152921504606846976)), (539/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-45496476703/4611686018427387904), (-30235454147/4611686018427387904)), (337/4611686018427387904), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-832057884757/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778655015496767/633825300114114700748351602688), (-1969171487735/316912650057057350374175801344)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889613482395719/39614081257132168796771975168), (-553723514659/4951760157141521099596496896)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944690010045617/1237940039285380274899124224), (-4705618789393/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885522846676723/77371252455336267181195264), (-4704458949705/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549416881618359/9671406556917033397649408), (-2204599075405/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157333574556445/75557863725914323419136), (-241051031817/37778931862957161709568)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887595757967587/75557863725914323419136), (-6265017579267/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297391236487749/4722366482869645213696), (-4696743106353/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621242690322511/590295810358705651712), (-1613685027067/147573952589676412928)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823215401207111/73786976294838206464), (-8063504328607/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911180957596461/4611686018427387904), (-4532339502261/4611686018427387904)), (3359/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593606224913771/1152921504606846976), (-9056228916901/1152921504606846976)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597121935758967/72057594037927936), (-989337452683/18014398509481984)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491122672359895/36028797018963968), (-11853062252961/36028797018963968)), (1107/4503599627370496), by norm_num⟩
  | 3 => ⟨((744298947828587/4503599627370496), (-7391566099325/4503599627370496)), (11099/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113289820152107/2251799813685248), (-3683350688319/562949953421312)), (11143/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106964884498211/1125899906842624), (-21976004846477/1125899906842624)), (16825/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087952528236213/1125899906842624), (-21728480843127/562949953421312)), (34093/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087952528236213/1125899906842624), (-21728480843127/562949953421312)), (130054478171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131200849759657/140737488355328), (-83984572782513/1125899906842624)), (68521/1125899906842624), by norm_num⟩
  | 2 => ⟨((121527346197917/140737488355328), (-156587238333365/1125899906842624)), (137979/1125899906842624), by norm_num⟩
  | 3 => ⟨((1635473574739283/2251799813685248), (-540854657717619/2251799813685248)), (276671/1125899906842624), by norm_num⟩
  | 4 => ⟨((1057931543655697/2251799813685248), (-24551291568415/70368744177664)), (1069593/2251799813685248), by norm_num⟩
  | 5 => ⟨((445853888351295/4503599627370496), (-1476427416248179/4503599627370496)), (1751375/2251799813685248), by norm_num⟩
  | 6 => ⟨((-879763917578959/9007199254740992), (-73082751450871/1125899906842624)), (5980347/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-83701685033/1073741824)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-86397846479/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((42678490686293/1125899906842624), (924845756136283/9007199254740992)), (2186097/4503599627370496), by norm_num⟩
  | 1 => ⟨((-26725626773/274877906944), (-9049158203/34359738368)), (43/34359738368), by norm_num⟩
  | 2 => ⟨((17137469805/137438953472), (46421265037/137438953472)), (443/274877906944), by norm_num⟩
  | 3 => ⟨((-29304494777/274877906944), (-79378795953/274877906944)), (381/274877906944), by norm_num⟩
  | 4 => ⟨((9395568131/137438953472), (50900647919/274877906944)), (123/137438953472), by norm_num⟩
  | 5 => ⟨((-19279325153/549755813888), (-26111516835/274877906944)), (127/274877906944), by norm_num⟩
  | 6 => ⟨((32966995109/2199023255552), (44649812219/1099511627776)), (437/2199023255552), by norm_num⟩
  | 7 => ⟨((-24159620835/4398046511104), (-65442575521/4398046511104)), (161/2199023255552), by norm_num⟩
  | 8 => ⟨((30984101969/17592186044416), (83928446017/17592186044416)), (415/17592186044416), by norm_num⟩
  | 9 => ⟨((-35321178861/70368744177664), (-11959567427/8796093022208)), (475/70368744177664), by norm_num⟩
  | 10 => ⟨((18119407005/140737488355328), (12270273915/35184372088832)), (245/140737488355328), by norm_num⟩
  | 11 => ⟨((-8450065701/281474976710656), (-91556745293/1125899906842624)), (115/281474976710656), by norm_num⟩
  | 12 => ⟨((28898654121/4503599627370496), (78279471671/4503599627370496)), (99/1125899906842624), by norm_num⟩
  | 13 => ⟨((-11403628357/9007199254740992), (-30889673933/9007199254740992)), (315/18014398509481984), by norm_num⟩
  | 14 => ⟨((16714130987/72057594037927936), (45274542461/72057594037927936)), (29/9007199254740992), by norm_num⟩
  | 15 => ⟨((-2858059969/72057594037927936), (-61934351251/576460752303423488)), (319/576460752303423488), by norm_num⟩
  | 16 => ⟨((7330779081/1152921504606846976), (79429237223/4611686018427387904)), (103/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (1585466175339/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444638757059781/158456325028528675187087900672), (1875890541445/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236187672591847/4951760157141521099596496896), (2109968660359/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889261411923015/2475880078570760549798248448), (2241335713405/2475880078570760549798248448)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770927647078597/154742504910672534362390528), (70023958577/4835703278458516698824704)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96831675616781/604462909807314587353088), (525028584377/2417851639229258349412352)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258572879877089/604462909807314587353088), (1836995832605/604462909807314587353088)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887441335516405/75557863725914323419136), (2983985769045/75557863725914323419136)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648638198052111/2361183241434822606848), (2236998864943/4722366482869645213696)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810543184919511/295147905179352825856), (3074264762931/590295810358705651712)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823022375203779/73786976294838206464), (3840419380597/73786976294838206464)), (5941/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113884251325099/576460752303423488), (4317158231231/9223372036854775808)), (6687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796698199517983/576460752303423488), (4313019775429/1152921504606846976)), (6691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194064840593275/144115188075855872), (942310340461/36028797018963968)), (2929/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490863234668291/36028797018963968), (5644572200493/36028797018963968)), (8795/36028797018963968), by norm_num⟩
  | 3 => ⟨((186036185397345/1125899906842624), (1759871271663/2251799813685248)), (11007/9007199254740992), by norm_num⟩
  | 2 => ⟨((278251280921171/562949953421312), (7015193879993/2251799813685248)), (2757/562949953421312), by norm_num⟩
  | 1 => ⟨((276649185626617/281474976710656), (20924503155895/2251799813685248)), (33189/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087449539040549/1125899906842624), (41366951872577/2251799813685248)), (66801/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087449539040549/1125899906842624), (41366951872577/2251799813685248)), (254825600630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099864626683781/2251799813685248), (39954237914005/1125899906842624)), (131495/2251799813685248), by norm_num⟩
  | 2 => ⟨((977672628607853/1125899906842624), (149033658093115/2251799813685248)), (254579/2251799813685248), by norm_num⟩
  | 3 => ⟨((844027968332237/1125899906842624), (129413038737649/1125899906842624)), (475825/2251799813685248), by norm_num⟩
  | 4 => ⟨((1235696836821865/2251799813685248), (48507075761179/281474976710656)), (822787/2251799813685248), by norm_num⟩
  | 5 => ⟨((1222452133299891/4503599627370496), (212949800305635/1125899906842624)), (2373219/4503599627370496), by norm_num⟩
  | 6 => ⟨((42678490686293/1125899906842624), (924845756136283/9007199254740992)), (2186097/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-86397846479/1073741824)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-1388970345/16777216)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((103288483542031/2251799813685248), (-827396241349749/9007199254740992)), (244397/562949953421312), by norm_num⟩
  | 1 => ⟨((-33274442085/274877906944), (66636539161/274877906944)), (317/274877906944), by norm_num⟩
  | 2 => ⟨((43906580137/274877906944), (-87928823547/274877906944)), (421/274877906944), by norm_num⟩
  | 3 => ⟨((-38623994043/274877906944), (38674867711/137438953472)), (93/68719476736), by norm_num⟩
  | 4 => ⟨((25482733645/274877906944), (-6379074569/34359738368)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-13450079001/274877906944), (6733897399/68719476736)), (263/549755813888), by norm_num⟩
  | 6 => ⟨((23663686381/1099511627776), (-47389710101/1099511627776)), (233/1099511627776), by norm_num⟩
  | 7 => ⟨((-4460701785/549755813888), (71465235309/4398046511104)), (353/4398046511104), by norm_num⟩
  | 8 => ⟨((11772047741/4398046511104), (-2946888329/549755813888)), (117/4398046511104), by norm_num⟩
  | 9 => ⟨((-27615207889/35184372088832), (27651581313/17592186044416)), (277/35184372088832), by norm_num⟩
  | 10 => ⟨((29151246715/140737488355328), (-3648705417/8796093022208)), (147/70368744177664), by norm_num⟩
  | 11 => ⟨((-27975204113/562949953421312), (56024103415/562949953421312)), (71/140737488355328), by norm_num⟩
  | 12 => ⟨((12304694577/1125899906842624), (-24641803459/1125899906842624)), (63/562949953421312), by norm_num⟩
  | 13 => ⟨((-4995814525/2251799813685248), (80038316349/18014398509481984)), (411/18014398509481984), by norm_num⟩
  | 14 => ⟨((15067703931/36028797018963968), (-30175100773/36028797018963968)), (39/9007199254740992), by norm_num⟩
  | 15 => ⟨((-21207751733/288230376151711744), (42471371129/288230376151711744)), (221/288230376151711744), by norm_num⟩
  | 16 => ⟨((3498029541/288230376151711744), (-56042191639/2305843009213693952)), (147/1152921504606846976), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-360717597811/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778456845092733/633825300114114700748351602688), (-426748513245/158456325028528675187087900672)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944695482366259/19807040628566084398385987584), (-1919987100475/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889144145667913/2475880078570760549798248448), (-1019756314707/1237940039285380274899124224)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442702609470525/38685626227668133590597632), (-1019489977909/77371252455336267181195264)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549196986843895/9671406556917033397649408), (-119436120277/604462909807314587353088)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258476845296559/604462909807314587353088), (-835770051995/302231454903657293676544)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887285392818195/75557863725914323419136), (-339399080073/9444732965739290427392)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297159538322765/4722366482869645213696), (-1017733694643/2361183241434822606848)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620925851534313/590295810358705651712), (-1398630974967/295147905179352825856)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822821968823619/73786976294838206464), (-3494320293495/73786976294838206464)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910961447867965/4611686018427387904), (-1964004532929/4611686018427387904)), (6685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593171687683633/1152921504606846976), (-490516993211/144115188075855872)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193868683314043/144115188075855872), (-3429266445863/144115188075855872)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((372642481812853/9007199254740992), (-320950407923/2251799813685248)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487924469728899/9007199254740992), (-6403821835119/9007199254740992)), (1375/1125899906842624), by norm_num⟩
  | 2 => ⟨((2225285066737629/4503599627370496), (-6381095613127/2251799813685248)), (22037/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106058886599485/1125899906842624), (-19030027785119/2251799813685248)), (259/17592186044416), by norm_num⟩
  | 0 => ⟨((543198888239371/562949953421312), (-18804622707419/1125899906842624)), (66689/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543198888239371/562949953421312), (-18804622707419/1125899906842624)), (254398354537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047967503800239/1125899906842624), (-9072431826623/281474976710656)), (130927/2251799813685248), by norm_num⟩
  | 2 => ⟨((1948519469709219/2251799813685248), (-135111317472705/2251799813685248)), (126085/1125899906842624), by norm_num⟩
  | 3 => ⟨((209747389219677/281474976710656), (-233828097039205/2251799813685248)), (116669/562949953421312), by norm_num⟩
  | 4 => ⟨((1226102920189275/2251799813685248), (-174242248647895/1125899906842624)), (792429/2251799813685248), by norm_num⟩
  | 5 => ⟨((1227362146175509/4503599627370496), (-47437371783483/281474976710656)), (4329/8796093022208), by norm_num⟩
  | 6 => ⟨((103288483542031/2251799813685248), (-827396241349749/9007199254740992)), (244397/562949953421312), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-1388970345/16777216)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-45609030223/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1727969266311129/18014398509481984), (226678596089475/18014398509481984)), (2291363/4503599627370496), by norm_num⟩
  | 1 => ⟨((71402397447/274877906944), (-2341678687/68719476736)), (381/274877906944), by norm_num⟩
  | 2 => ⟨((-48340319191/137438953472), (6341383439/137438953472)), (259/137438953472), by norm_num⟩
  | 3 => ⟨((21818001851/68719476736), (-11448523131/274877906944)), (235/137438953472), by norm_num⟩
  | 4 => ⟨((-14771061075/68719476736), (3875396921/137438953472)), (639/549755813888), by norm_num⟩
  | 5 => ⟨((64001239863/549755813888), (-8395815529/549755813888)), (87/137438953472), by norm_num⟩
  | 6 => ⟨((-57772856827/1099511627776), (15157526621/2199023255552)), (315/1099511627776), by norm_num⟩
  | 7 => ⟨((89401026599/4398046511104), (-5863906145/2199023255552)), (489/4398046511104), by norm_num⟩
  | 8 => ⟨((-60525617015/8796093022208), (15879752215/17592186044416)), (665/17592186044416), by norm_num⟩
  | 9 => ⟨((72847293035/35184372088832), (-9556259151/35184372088832)), (201/17592186044416), by norm_num⟩
  | 10 => ⟨((-78909650621/140737488355328), (5175765903/70368744177664)), (437/140737488355328), by norm_num⟩
  | 11 => ⟨((77705925539/562949953421312), (-5096812325/281474976710656)), (27/35184372088832), by norm_num⟩
  | 12 => ⟨((-35071924547/1125899906842624), (9201615761/2251799813685248)), (391/2251799813685248), by norm_num⟩
  | 13 => ⟨((116894193627/18014398509481984), (-15334423023/18014398509481984)), (327/9007199254740992), by norm_num⟩
  | 14 => ⟨((-2826387005/2251799813685248), (2966170525/18014398509481984)), (127/18014398509481984), by norm_num⟩
  | 15 => ⟨((32657057695/144115188075855872), (-4284020633/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 16 => ⟨((-44218475829/1152921504606846976), (11601342937/2305843009213693952)), (125/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (1961183049301/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778355173453825/633825300114114700748351602688), (1159979074091/158456325028528675187087900672)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889276049967197/39614081257132168796771975168), (1304703699343/9903520314283042199192993792)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889021342641691/2475880078570760549798248448), (5543666229333/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770686841232013/154742504910672534362390528), (5542176271667/154742504910672534362390528)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549080272378771/9671406556917033397649408), (5194207431635/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314593469557703/151115727451828646838272), (1135837241997/151115727451828646838272)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887116494237611/75557863725914323419136), (7379975433619/75557863725914323419136)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((10133058483635/36893488147419103232), (2766193189715/2361183241434822606848)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810373771099487/295147905179352825856), (7602815230169/590295810358705651712)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227824466388753/9223372036854775808), (2374299248171/18446744073709551616)), (5975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821663778492669/9223372036854775808), (10675657086677/9223372036854775808)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592906832465389/1152921504606846976), (10664800103287/1152921504606846976)), (6737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596815247987329/72057594037927936), (582468298267/9007199254740992)), (5905/144115188075855872), by norm_num⟩
  | 4 => ⟨((186274976079399/4503599627370496), (1744355190525/4503599627370496)), (8877/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487439446480417/9007199254740992), (17400894386105/9007199254740992)), (5565/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112124128934135/2251799813685248), (17336985003409/2251799813685248)), (5591/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105198459722731/1125899906842624), (1615373384041/70368744177664)), (2113/140737488355328), by norm_num⟩
  | 0 => ⟨((1084349424331159/1125899906842624), (51055563053005/1125899906842624)), (34331/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084349424331159/1125899906842624), (51055563053005/1125899906842624)), (130962376121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042017142375201/1125899906842624), (49171396204021/562949953421312)), (69243/1125899906842624), by norm_num⟩
  | 2 => ⟨((955794039634455/1125899906842624), (182031945993489/1125899906842624)), (70133/562949953421312), by norm_num⟩
  | 3 => ⟨((390979078818609/562949953421312), (618119063501999/2251799813685248)), (17719/70368744177664), by norm_num⟩
  | 4 => ⟨((458247454319545/1125899906842624), (429295038714331/1125899906842624)), (1098883/2251799813685248), by norm_num⟩
  | 5 => ⟨((22823075985205/1125899906842624), (1397803534380079/4503599627370496)), (1732491/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1727969266311129/18014398509481984), (226678596089475/18014398509481984)), (2291363/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-45609030223/536870912)), (1/536870912), by norm_num⟩, -14, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile062Terms1
