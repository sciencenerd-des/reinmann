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
namespace Reinmann.XiBand97.Tile034Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32547/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32547/1280))
  have he : value ((69/80), (32547/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22364231/8388608), (-1318638829/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1250459954174205/18014398509481984), (17895663087513/4503599627370496)), (51824137/2251799813685248), by norm_num⟩
  | 1 => ⟨((460770703/2147483648), (-52753691/4294967296)), (613/8589934592), by norm_num⟩
  | 2 => ⟨((-356065451/1073741824), (81531949/4294967296)), (119/1073741824), by norm_num⟩
  | 3 => ⟨((1467484567/4294967296), (-84006239/4294967296)), (123/1073741824), by norm_num⟩
  | 4 => ⟨((-567007137/2147483648), (64916713/4294967296)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((1402114505/8589934592), (-40132063/4294967296)), (475/8589934592), by norm_num⟩
  | 6 => ⟨((-1444665153/17179869184), (20674985/4294967296)), (491/17179869184), by norm_num⟩
  | 7 => ⟨((637931617/17179869184), (-1141201/536870912)), (435/34359738368), by norm_num⟩
  | 8 => ⟨((-1971873711/137438953472), (14110003/17179869184)), (675/137438953472), by norm_num⟩
  | 9 => ⟨((1354476745/274877906944), (-77537099/274877906944)), (465/274877906944), by norm_num⟩
  | 10 => ⟨((-26167157/17179869184), (47934093/549755813888)), (577/1099511627776), by norm_num⟩
  | 11 => ⟨((1882386459/4398046511104), (-107757321/4398046511104)), (651/4398046511104), by norm_num⟩
  | 12 => ⟨((-1939512153/17592186044416), (111027485/17592186044416)), (673/17592186044416), by norm_num⟩
  | 13 => ⟨((922325293/35184372088832), (-105597129/70368744177664)), (321/35184372088832), by norm_num⟩
  | 14 => ⟨((-407278091/70368744177664), (93258631/281474976710656)), (569/281474976710656), by norm_num⟩
  | 15 => ⟨((1342841461/1125899906842624), (-76871037/1125899906842624)), (471/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1037694991/4503599627370496), (29701455/2251799813685248)), (365/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (2008894203027/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444461433642563/158456325028528675187087900672), (1187550698343/158456325028528675187087900672)), (23167/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944351517485025/19807040628566084398385987584), (5342715833753/39614081257132168796771975168)), (208563/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472103157232151/618970019642690137449562112), (5675088599675/2475880078570760549798248448)), (55417/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885039128366673/77371252455336267181195264), (5673348516569/154742504910672534362390528)), (221747/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774254930886089/4835703278458516698824704), (5316915819027/9671406556917033397649408)), (207971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628937453195301/302231454903657293676544), (4650453401277/604462909807314587353088)), (91029/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235788240358405/9444732965739290427392), (7553522898337/75557863725914323419136)), (4625/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324105945795569/1180591620717411303424), (5662112289675/4722366482869645213696)), (111069/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809956159101421/295147905179352825856), (1945120682711/147573952589676412928)), (305661/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910776126268469/36893488147419103232), (9718224228679/73786976294838206464)), (382411/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455122656048555/2305843009213693952), (10922861269899/9223372036854775808)), (26917/576460752303423488), by norm_num⟩
  | 6 => ⟨((99483414273029/72057594037927936), (5455096564197/576460752303423488)), (431247/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596302944094259/72057594037927936), (9532178463603/144115188075855872)), (377989/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488665043082989/36028797018963968), (14269814510389/36028797018963968)), (568281/36028797018963968), by norm_num⟩
  | 3 => ⟨((742762377692485/4503599627370496), (17787537819897/9007199254740992)), (712625/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110215106678377/2251799813685248), (17713068015711/2251799813685248)), (716043/2251799813685248), by norm_num⟩
  | 1 => ⟨((68896822994849/70368744177664), (13191934044291/562949953421312)), (541317/562949953421312), by norm_num⟩
  | 0 => ⟨((1078708217738363/1125899906842624), (52027449582373/1125899906842624)), (2199705/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078708217738363/1125899906842624), (52027449582373/1125899906842624)), (8391208652976607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515545190318813/562949953421312), (99693475541461/1125899906842624)), (2209153/562949953421312), by norm_num⟩
  | 2 => ⟨((1870874271464211/2251799813685248), (182597019536837/1125899906842624)), (138671/17592186044416), by norm_num⟩
  | 3 => ⟨((1495161262999555/2251799813685248), (151708008776515/562949953421312)), (35251769/2251799813685248), by norm_num⟩
  | 4 => ⟨((414615471631899/1125899906842624), (25182959940633/70368744177664)), (65813119/2251799813685248), by norm_num⟩
  | 5 => ⟨((2121754471103/281474976710656), (296758026163183/1125899906842624)), (191153919/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1250459954174205/18014398509481984), (17895663087513/4503599627370496)), (51824137/2251799813685248), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1318638829/16777216)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45371695/16777216), (-1337601953/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-112705894016485/4503599627370496), (279478981427823/4503599627370496)), (427611219/18014398509481984), by norm_num⟩
  | 1 => ⟨((337017707/4294967296), (-417854657/2147483648)), (321/4294967296), by norm_num⟩
  | 2 => ⟨((-528358535/4294967296), (327545215/1073741824)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((276110855/2147483648), (-342338709/1073741824)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-216435997/2147483648), (536700521/2147483648)), (417/4294967296), by norm_num⟩
  | 5 => ⟨((542907053/8589934592), (-1346257103/8589934592)), (525/8589934592), by norm_num⟩
  | 6 => ⟨((-141856827/4294967296), (1407060453/17179869184)), (275/8589934592), by norm_num⟩
  | 7 => ⟨((508332869/34359738368), (-78782677/2147483648)), (495/34359738368), by norm_num⟩
  | 8 => ⟨((-398468693/68719476736), (61755657/4294967296)), (195/34359738368), by norm_num⟩
  | 9 => ⟨((138821809/68719476736), (-688478241/137438953472)), (273/137438953472), by norm_num⟩
  | 10 => ⟨((-348219983/549755813888), (863487817/549755813888)), (43/68719476736), by norm_num⟩
  | 11 => ⟨((397033361/2199023255552), (-984531293/2199023255552)), (197/1099511627776), by norm_num⟩
  | 12 => ⟨((-414965269/8796093022208), (1028997391/8796093022208)), (207/4398046511104), by norm_num⟩
  | 13 => ⟨((400344985/35184372088832), (-496371595/17592186044416)), (401/35184372088832), by norm_num⟩
  | 14 => ⟨((-358651253/140737488355328), (889354437/140737488355328)), (361/140737488355328), by norm_num⟩
  | 15 => ⟨((599759429/1125899906842624), (-371808759/281474976710656)), (303/562949953421312), by norm_num⟩
  | 16 => ⟨((-470135555/4503599627370496), (1165804213/4503599627370496)), (477/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (318182391501/1267650600228229401496703205376)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777793935220527/633825300114114700748351602688), (3009287704733/633825300114114700748351602688)), (184993/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944322586392293/19807040628566084398385987584), (3384652346681/39614081257132168796771975168)), (208155/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888351700540989/2475880078570760549798248448), (3595200655583/2475880078570760549798248448)), (221209/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770017946669441/154742504910672534362390528), (3594084562693/154742504910672534362390528)), (221259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548453977531501/9671406556917033397649408), (3368268834855/9671406556917033397649408)), (207483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257826663534195/604462909807314587353088), (1473025122241/302231454903657293676544)), (181601/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471557189174753/18889465931478580854784), (1196277692145/18889465931478580854784)), (9225/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296366982217979/4722366482869645213696), (224180673581/295147905179352825856)), (221487/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619835959230929/590295810358705651712), (4928820400173/590295810358705651712)), (304685/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821459413249911/73786976294838206464), (192384282857/2305843009213693952)), (95267/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910194880649141/4611686018427387904), (6919337729041/9223372036854775808)), (428993/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198954779014861/144115188075855872), (1727806225451/288230376151711744)), (214679/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192526552741033/144115188075855872), (6038205493027/144115188075855872)), (376099/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488556028241119/36028797018963968), (9039102210083/36028797018963968)), (282485/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485405889577389/9007199254740992), (11267076911457/9007199254740992)), (353827/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110122191690477/2251799813685248), (5609747435855/1125899906842624)), (1419641/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102274137589405/1125899906842624), (33421407600777/2251799813685248)), (1070165/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078812329482953/1125899906842624), (32949747228351/1125899906842624)), (4324337/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078812329482953/1125899906842624), (32949747228351/1125899906842624)), (16496036538130950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065459548109813/2251799813685248), (126286869187069/2251799813685248)), (4270037/1125899906842624), by norm_num⟩
  | 2 => ⟨((1887456756021831/2251799813685248), (231672831819309/2251799813685248)), (16624637/2251799813685248), by norm_num⟩
  | 3 => ⟨((1558229414322055/2251799813685248), (388375955044097/2251799813685248)), (15645157/1125899906842624), by norm_num⟩
  | 4 => ⟨((252824763924635/562949953421312), (537506783051651/2251799813685248)), (27049427/1125899906842624), by norm_num⟩
  | 5 => ⟨((162939048526983/1125899906842624), (482796116091761/2251799813685248)), (74419247/2251799813685248), by norm_num⟩
  | 6 => ⟨((-112705894016485/4503599627370496), (279478981427823/4503599627370496)), (427611219/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1337601953/16777216)), (1/8388608), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45987547/16777216), (-677878943/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((186882626052423/4503599627370496), (889565524742085/18014398509481984)), (280769331/18014398509481984), by norm_num⟩
  | 1 => ⟨((-283204577/2147483648), (-674030095/4294967296)), (215/4294967296), by norm_num⟩
  | 2 => ⟨((900039391/4294967296), (535525981/2147483648)), (43/536870912), by norm_num⟩
  | 3 => ⟨((-476728939/2147483648), (-1134620263/4294967296)), (367/4294967296), by norm_num⟩
  | 4 => ⟨((757535115/4294967296), (225367767/1073741824)), (293/4294967296), by norm_num⟩
  | 5 => ⟨((-962994949/8589934592), (-143246179/1073741824)), (375/8589934592), by norm_num⟩
  | 6 => ⟨((127518741/2147483648), (303496045/4294967296)), (25/1073741824), by norm_num⟩
  | 7 => ⟨((-57894489/2147483648), (-551158153/17179869184)), (183/17179869184), by norm_num⟩
  | 8 => ⟨((367983605/34359738368), (875805139/68719476736)), (293/68719476736), by norm_num⟩
  | 9 => ⟨((-259882601/68719476736), (-77315441/17179869184)), (13/8589934592), by norm_num⟩
  | 10 => ⟨((165184179/137438953472), (786280427/549755813888)), (133/274877906944), by norm_num⟩
  | 11 => ⟨((-763584309/2199023255552), (-227167411/549755813888)), (155/1099511627776), by norm_num⟩
  | 12 => ⟨((808904013/8796093022208), (962600347/8796093022208)), (331/8796093022208), by norm_num⟩
  | 13 => ⟨((-197749269/8796093022208), (-941290991/35184372088832)), (163/17592186044416), by norm_num⟩
  | 14 => ⟨((718237511/140737488355328), (854706697/140737488355328)), (149/70368744177664), by norm_num⟩
  | 15 => ⟨((-608692659/562949953421312), (-90543463/70368744177664)), (255/562949953421312), by norm_num⟩
  | 16 => ⟨((483614509/2251799813685248), (1151007997/4503599627370496)), (407/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (1135801543231/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777741298643549/633825300114114700748351602688), (1311214495/618970019642690137449562112)), (23083/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888586183944637/39614081257132168796771975168), (377540661761/9903520314283042199192993792)), (207765/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888289328693451/2475880078570760549798248448), (200512422745/309485009821345068724781056)), (110385/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769955916203717/154742504910672534362390528), (801797577797/77371252455336267181195264)), (27599/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548396186397541/9671406556917033397649408), (375708733675/2417851639229258349412352)), (207017/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257776458392535/604462909807314587353088), (1314445288253/604462909807314587353088)), (181163/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943073925793889/37778931862957161709568), (1067485231251/37778931862957161709568)), (294435/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324076724038505/1180591620717411303424), (800175312693/2361183241434822606848)), (220865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25308660981927/9223372036854775808), (2199057595691/590295810358705651712)), (303753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455339695854573/18446744073709551616), (1373343460371/36893488147419103232)), (379785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820278529946957/9223372036854775808), (1543544907605/4611686018427387904)), (427389/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795764733377195/576460752303423488), (3083427731631/1152921504606846976)), (13361/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192434149698711/144115188075855872), (2693885092647/144115188075855872)), (374293/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488422938060713/36028797018963968), (4032613452137/36028797018963968)), (35113/2251799813685248), by norm_num⟩
  | 3 => ⟨((1485249134558343/9007199254740992), (5026423787899/9007199254740992)), (702909/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219959527137613/4503599627370496), (5004972705789/2251799813685248)), (1407769/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204192035048513/2251799813685248), (931756603495/140737488355328)), (2116559/2251799813685248), by norm_num⟩
  | 0 => ⟨((539298208286609/562949953421312), (29391609087503/2251799813685248)), (1063221/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539298208286609/562949953421312), (29391609087503/2251799813685248)), (4055866243602561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1033088515332813/1125899906842624), (56313503618635/2251799813685248)), (4129715/1125899906842624), by norm_num⟩
  | 2 => ⟨((1894447403998541/2251799813685248), (103342816697997/2251799813685248)), (3892567/562949953421312), by norm_num⟩
  | 3 => ⟨((794531380411131/1125899906842624), (86942688966215/1125899906842624)), (27627793/2251799813685248), by norm_num⟩
  | 4 => ⟨((276987803046565/562949953421312), (122708411753405/1125899906842624)), (43259945/2251799813685248), by norm_num⟩
  | 5 => ⟨((1036794180575411/4503599627370496), (483008952115099/4503599627370496)), (12999963/562949953421312), by norm_num⟩
  | 6 => ⟨((186882626052423/4503599627370496), (889565524742085/18014398509481984)), (280769331/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-677878943/8388608)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/1048576), (-1373172551/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1106321229510721/18014398509481984), (-46353857608263/4503599627370496)), (20435847/2251799813685248), by norm_num⟩
  | 1 => ⟨((-13266171/67108864), (142295181/4294967296)), (253/8589934592), by norm_num⟩
  | 2 => ⟨((341617257/1073741824), (-229015259/4294967296)), (205/4294967296), by norm_num⟩
  | 3 => ⟨((-1466164707/4294967296), (122861947/2147483648)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((1179850533/4294967296), (-49434669/1073741824)), (181/4294967296), by norm_num⟩
  | 5 => ⟨((-1519116943/8589934592), (127299249/4294967296)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((1629949601/17179869184), (-136586825/8589934592)), (127/8589934592), by norm_num⟩
  | 7 => ⟨((-1499030105/34359738368), (251232017/34359738368)), (59/8589934592), by norm_num⟩
  | 8 => ⟨((603148971/34359738368), (-202171167/68719476736)), (3/1073741824), by norm_num⟩
  | 9 => ⟨((-862871841/137438953472), (36153549/34359738368)), (277/274877906944), by norm_num⟩
  | 10 => ⟨((277747731/137438953472), (-23274757/68719476736)), (45/137438953472), by norm_num⟩
  | 11 => ⟨((-650207605/1099511627776), (13621555/137438953472)), (213/2199023255552), by norm_num⟩
  | 12 => ⟨((697645847/4398046511104), (-233845835/8796093022208)), (115/4398046511104), by norm_num⟩
  | 13 => ⟨((-1381929447/35184372088832), (231606371/35184372088832)), (115/17592186044416), by norm_num⟩
  | 14 => ⟨((635465613/70368744177664), (-213003471/140737488355328)), (213/140737488355328), by norm_num⟩
  | 15 => ⟨((-34091415/17592186044416), (91417563/281474976710656)), (185/562949953421312), by norm_num⟩
  | 16 => ⟨((877888253/2251799813685248), (-36782723/562949953421312)), (75/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-216302734377/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55552750460481/19807040628566084398385987584), (-998775829/2475880078570760549798248448)), (92225/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888526304766821/39614081257132168796771975168), (-287578897669/39614081257132168796771975168)), (207511/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888225793567265/2475880078570760549798248448), (-4772907923/38685626227668133590597632)), (55121/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884946239141819/77371252455336267181195264), (-152684439897/77371252455336267181195264)), (27561/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774168408275719/4835703278458516698824704), (-143090032287/4835703278458516698824704)), (206713/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724612893845/604462909807314587353088), (-250304345517/604462909807314587353088)), (90439/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943031897905361/37778931862957161709568), (-50818893183/9444732965739290427392)), (18371/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296244023149513/4722366482869645213696), (-304744224625/4722366482869645213696)), (55115/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25307314475955/9223372036854775808), (-418748661189/590295810358705651712)), (37893/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821251473332513/73786976294838206464), (-523024197435/73786976294838206464)), (378949/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227519796175647/1152921504606846976), (-587836788127/9223372036854775808)), (53293/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795705004434715/576460752303423488), (-587130828659/1152921504606846976)), (426377/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192330412515161/144115188075855872), (-128236603643/36028797018963968)), (373117/144115188075855872), by norm_num⟩
  | 4 => ⟨((744134452085151/18014398509481984), (-767836356101/36028797018963968)), (559751/36028797018963968), by norm_num⟩
  | 3 => ⟨((742529665834785/4503599627370496), (-239257785511/2251799813685248)), (699821/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219588094638205/4503599627370496), (-1905794961291/4503599627370496)), (87503/281474976710656), by norm_num⟩
  | 1 => ⟨((2203655162174401/2251799813685248), (-2838113411353/2251799813685248)), (2101111/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078099626220623/1125899906842624), (-5594444156177/2251799813685248)), (262907/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078099626220623/1125899906842624), (-5594444156177/2251799813685248)), (1002910614550542787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1032321765497895/1125899906842624), (-5356931035371/1125899906842624)), (4038375/1125899906842624), by norm_num⟩
  | 2 => ⟨((59155987375857/70368744177664), (-19646778440875/2251799813685248)), (14887775/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591185488581881/2251799813685248), (-16516204616219/1125899906842624)), (25290819/2251799813685248), by norm_num⟩
  | 4 => ⟨((1123892143357113/2251799813685248), (-2917704423819/140737488355328)), (18242209/1125899906842624), by norm_num⟩
  | 5 => ⟨((1119952328324757/4503599627370496), (-93200045471589/4503599627370496)), (75864229/4503599627370496), by norm_num⟩
  | 6 => ⟨((1106321229510721/18014398509481984), (-46353857608263/4503599627370496)), (20435847/2251799813685248), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1373172551/16777216)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47145793/16777216), (-347476027/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((429744725958115/18014398509481984), (-248913657270537/4503599627370496)), (303533743/18014398509481984), by norm_num⟩
  | 1 => ⟨((-333821727/4294967296), (773415303/4294967296)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((543811707/4294967296), (-1259930861/4294967296)), (97/1073741824), by norm_num⟩
  | 3 => ⟨((-590597013/4294967296), (1368325459/4294967296)), (423/4294967296), by norm_num⟩
  | 4 => ⟨((481055521/4294967296), (-557267055/2147483648)), (173/2147483648), by norm_num⟩
  | 5 => ⟨((-626930131/8589934592), (726251945/4294967296)), (453/8589934592), by norm_num⟩
  | 6 => ⟨((85108287/2147483648), (-788732983/8589934592)), (31/1073741824), by norm_num⟩
  | 7 => ⟨((-633808035/34359738368), (367109743/8589934592)), (29/2147483648), by norm_num⟩
  | 8 => ⟨((516251941/68719476736), (-1196078983/68719476736)), (95/17179869184), by norm_num⟩
  | 9 => ⟨((-46722185/17179869184), (865986843/137438953472)), (277/137438953472), by norm_num⟩
  | 10 => ⟨((243560623/274877906944), (-564293747/274877906944)), (363/549755813888), by norm_num⟩
  | 11 => ⟨((-288561463/1099511627776), (1337108003/2199023255552)), (27/137438953472), by norm_num⟩
  | 12 => ⟨((626774069/8796093022208), (-1452142319/8796093022208)), (471/8796093022208), by norm_num⟩
  | 13 => ⟨((-628335515/35184372088832), (727879979/17592186044416)), (237/17592186044416), by norm_num⟩
  | 14 => ⟨((584907933/140737488355328), (-1355144709/140737488355328)), (111/35184372088832), by norm_num⟩
  | 15 => ⟨((-254091535/281474976710656), (1177384609/562949953421312)), (97/140737488355328), by norm_num⟩
  | 16 => ⟨((413927375/2251799813685248), (-239752045/562949953421312)), (159/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-757684671181/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817121001217/316912650057057350374175801344), (-895592000267/316912650057057350374175801344)), (184753/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944232866482891/19807040628566084398385987584), (-2014594462681/39614081257132168796771975168)), (207871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944080665122073/1237940039285380274899124224), (-2139893263565/2475880078570760549798248448)), (27611/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442456974030025/38685626227668133590597632), (-2139203591193/154742504910672534362390528)), (110459/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96767259038937/604462909807314587353088), (-2004770886659/9671406556917033397649408)), (103571/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257671398939063/604462909807314587353088), (-876721189889/302231454903657293676544)), (181281/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942988543566707/37778931862957161709568), (-2847971802767/75557863725914323419136)), (294641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162022348177799/590295810358705651712), (-1067389502407/2361183241434822606848)), (27629/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809789045003779/295147905179352825856), (-2933372708463/590295810358705651712)), (304003/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910569213409539/36893488147419103232), (-1831897787131/36893488147419103232)), (190065/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455007626192929/2305843009213693952), (-4117758365337/9223372036854775808)), (427821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591281287343243/1152921504606846976), (-4112749448639/1152921504606846976)), (428039/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298054205062185/36028797018963968), (-3593028499977/144115188075855872)), (93695/36028797018963968), by norm_num⟩
  | 4 => ⟨((186012075196701/4503599627370496), (-5378307596841/36028797018963968)), (140665/9007199254740992), by norm_num⟩
  | 3 => ⟨((371210155193685/2251799813685248), (-6703266512929/9007199254740992)), (176047/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219140743434579/4503599627370496), (-13347852842711/4503599627370496)), (1410969/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101479775287411/1125899906842624), (-19875685312095/2251799813685248)), (265371/281474976710656), by norm_num⟩
  | 0 => ⟨((2154711113549309/2251799813685248), (-39170620477313/2251799813685248)), (4272159/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154711113549309/2251799813685248), (-39170620477313/2251799813685248)), (16296993264205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2061127111361005/2251799813685248), (-37481738276263/1125899906842624)), (8324553/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884104182168453/2251799813685248), (-137231784943991/2251799813685248)), (15793589/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568086108279295/2251799813685248), (-114823253100933/1125899906842624)), (14177171/1125899906842624), by norm_num⟩
  | 4 => ⟨((267137037509333/562949953421312), (-159918965265691/1125899906842624)), (45273587/2251799813685248), by norm_num⟩
  | 5 => ⟨((923260443334335/4503599627370496), (-607091672899211/4503599627370496)), (27914213/1125899906842624), by norm_num⟩
  | 6 => ⟨((429744725958115/18014398509481984), (-248913657270537/4503599627370496)), (303533743/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-347476027/4194304)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47691909/16777216), (-703002067/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-275305545730955/9007199254740992), (-893708217687399/18014398509481984)), (381525015/18014398509481984), by norm_num⟩
  | 1 => ⟨((432663997/4294967296), (702265857/4294967296)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-22281093/134217728), (-1157276851/4294967296)), (125/1073741824), by norm_num⟩
  | 3 => ⟨((391652521/2147483648), (635699285/2147483648)), (551/4294967296), by norm_num⟩
  | 4 => ⟨((-645411409/4294967296), (-523790285/2147483648)), (57/536870912), by norm_num⟩
  | 5 => ⟨((425434143/4294967296), (690530933/4294967296)), (151/2147483648), by norm_num⟩
  | 6 => ⟨((-233693589/4294967296), (-758625769/8589934592)), (167/4294967296), by norm_num⟩
  | 7 => ⟨((220061699/8589934592), (714373365/17179869184)), (79/4294967296), by norm_num⟩
  | 8 => ⟨((-181321865/17179869184), (-294307259/17179869184)), (523/68719476736), by norm_num⟩
  | 9 => ⟨((265603239/68719476736), (431106095/68719476736)), (385/137438953472), by norm_num⟩
  | 10 => ⟨((-700307957/549755813888), (-1136684289/549755813888)), (255/274877906944), by norm_num⟩
  | 11 => ⟨((13114209/34359738368), (681150179/1099511627776)), (307/1099511627776), by norm_num⟩
  | 12 => ⟨((-461037797/4398046511104), (-748319957/4398046511104)), (339/4398046511104), by norm_num⟩
  | 13 => ⟨((467540113/17592186044416), (758874001/17592186044416)), (173/8796093022208), by norm_num⟩
  | 14 => ⟨((-110066853/17592186044416), (-714607117/70368744177664)), (327/70368744177664), by norm_num⟩
  | 15 => ⟨((773893103/562949953421312), (2453363/1099511627776)), (577/562949953421312), by norm_num⟩
  | 16 => ⟨((-637656355/2251799813685248), (-258748295/562949953421312)), (477/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-2765402806927/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888790056365457/316912650057057350374175801344), (-3268562126209/633825300114114700748351602688)), (46261/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236050579254753/4951760157141521099596496896), (-3676224832663/39614081257132168796771975168)), (26027/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472024034044069/618970019642690137449562112), (-3904855753027/2475880078570760549798248448)), (110639/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769762391444471/154742504910672534362390528), (-975895371145/38685626227668133590597632)), (55333/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387053601066777/2417851639229258349412352), (-3658254212015/9671406556917033397649408)), (51889/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257617046741017/604462909807314587353088), (-1599809773019/302231454903657293676544)), (181669/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942944073962359/37778931862957161709568), (-2598423121163/37778931862957161709568)), (36915/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648055770976163/2361183241434822606848), (-1947708624565/2361183241434822606848)), (13849/295147905179352825856), by norm_num⟩
  | 9 => ⟨((25304449306133/9223372036854775808), (-1338149385001/147573952589676412928)), (304831/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821020449167537/73786976294838206464), (-3342674460113/36893488147419103232)), (381269/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819895982954601/9223372036854775808), (-7513601387923/9223372036854775808)), (107311/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591144524997361/1152921504606846976), (-3752170180949/576460752303423488)), (429641/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192094640383613/144115188075855872), (-6555891745523/144115188075855872)), (188191/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487908325564763/36028797018963968), (-9813056905959/36028797018963968)), (565467/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484596558459495/9007199254740992), (-12230025526523/9007199254740992)), (44275/562949953421312), by norm_num⟩
  | 2 => ⟨((2218626640575359/4503599627370496), (-24351446414055/4503599627370496)), (1421511/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202124056015213/2251799813685248), (-36256643921905/2251799813685248)), (536021/562949953421312), by norm_num⟩
  | 0 => ⟨((134549148404817/140737488355328), (-8929635826697/281474976710656)), (4335665/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((134549148404817/140737488355328), (-8929635826697/281474976710656)), (16539249428755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((513965083469603/562949953421312), (-34147970383379/562949953421312)), (8565139/2251799813685248), by norm_num⟩
  | 2 => ⟨((467171231734319/562949953421312), (-62353196200643/562949953421312)), (1042425/140737488355328), by norm_num⟩
  | 3 => ⟨((761563394333553/1125899906842624), (-413956790220397/2251799813685248)), (7844243/562949953421312), by norm_num⟩
  | 4 => ⟨((238537521977755/562949953421312), (-140001049983093/562949953421312)), (13495831/562949953421312), by norm_num⟩
  | 5 => ⟨((132515706478811/1125899906842624), (-237289324454443/1125899906842624)), (36299445/1125899906842624), by norm_num⟩
  | 6 => ⟨((-275305545730955/9007199254740992), (-893708217687399/18014398509481984)), (381525015/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-703002067/8388608)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile034Terms3
