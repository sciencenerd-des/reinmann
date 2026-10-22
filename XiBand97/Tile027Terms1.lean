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
namespace Reinmann.XiBand97.Tile027Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30399/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30399/1280))
  have he : value ((69/80), (30399/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-875474845/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-459238153243751/9007199254740992), (-1273532102120411/9007199254740992)), (235599793/9007199254740992), by norm_num⟩
  | 1 => ⟨((120288057/1073741824), (1334302919/4294967296)), (249/4294967296), by norm_num⟩
  | 2 => ⟨((-528599751/4294967296), (-91617599/268435456)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((96787697/1073741824), (536811841/2147483648)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-425328613/8589934592), (-1179496171/8589934592)), (57/2147483648), by norm_num⟩
  | 5 => ⟨((373816993/17179869184), (1036647191/17179869184)), (203/17179869184), by norm_num⟩
  | 6 => ⟨((-68446657/8589934592), (-1518497791/68719476736)), (75/17179869184), by norm_num⟩
  | 7 => ⟨((171877345/68719476736), (953280191/137438953472)), (95/68719476736), by norm_num⟩
  | 8 => ⟨((-377653127/549755813888), (-1047285333/549755813888)), (211/549755813888), by norm_num⟩
  | 9 => ⟨((23049687/137438953472), (1022720477/2199023255552)), (13/137438953472), by norm_num⟩
  | 10 => ⟨((-40516271/1099511627776), (-898858627/8796093022208)), (185/8796093022208), by norm_num⟩
  | 11 => ⟨((16186063/2199023255552), (1436359467/70368744177664)), (149/35184372088832), by norm_num⟩
  | 12 => ⟨((-379353765/281474976710656), (-1052001441/281474976710656)), (55/70368744177664), by norm_num⟩
  | 13 => ⟨((256469359/1125899906842624), (1422451337/2251799813685248)), (75/562949953421312), by norm_num⟩
  | 14 => ⟨((-161005937/4503599627370496), (-892984297/9007199254740992)), (95/4503599627370496), by norm_num⟩
  | 15 => ⟨((377350615/72057594037927936), (130805803/9007199254740992)), (225/72057594037927936), by norm_num⟩
  | 16 => ⟨((-414562023/576460752303423488), (-1149638901/576460752303423488)), (249/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-2496956328161/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444760296209021/158456325028528675187087900672), (-1477946728625/316912650057057350374175801344)), (92491/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890048047711951/39614081257132168796771975168), (-3324819409723/39614081257132168796771975168)), (104071/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889841917846533/2475880078570760549798248448), (-1765968397203/1237940039285380274899124224)), (110597/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442876946120393/38685626227668133590597632), (-3531167618017/154742504910672534362390528)), (110621/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387462574325869/2417851639229258349412352), (-1654826274481/4835703278458516698824704)), (51867/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39345251256147/18889465931478580854784), (-2895129063903/604462909807314587353088)), (90793/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888212737974821/75557863725914323419136), (-4703053385565/75557863725914323419136)), (73793/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297854306932301/4722366482869645213696), (-3525950488857/4722366482869645213696)), (27683/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621879956350345/590295810358705651712), (-2423002928071/295147905179352825856)), (76163/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912006399189767/36893488147419103232), (-3027122225893/36893488147419103232)), (190511/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823260104521155/9223372036854775808), (-3403270282041/4611686018427387904)), (214467/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594505807206535/1152921504606846976), (-3400469004349/576460752303423488)), (107323/576460752303423488), by norm_num⟩
  | 5 => ⟨((298758141930799/36028797018963968), (-1486130501915/36028797018963968)), (11751/9007199254740992), by norm_num⟩
  | 4 => ⟨((746154413310681/18014398509481984), (-8904195823945/36028797018963968)), (282425/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490086000708459/9007199254740992), (-5554120202541/4503599627370496)), (353735/9007199254740992), by norm_num⟩
  | 2 => ⟨((17418530988931/35184372088832), (-22150560501565/4503599627370496)), (44349/281474976710656), by norm_num⟩
  | 1 => ⟨((2218458128376903/2251799813685248), (-33061364846615/2251799813685248)), (1069673/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092559371142571/1125899906842624), (-65466775330559/2251799813685248)), (540151/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092559371142571/1125899906842624), (-65466775330559/2251799813685248)), (2060512544872093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2118508932375471/2251799813685248), (-63528150638603/1125899906842624)), (4318879/2251799813685248), by norm_num⟩
  | 2 => ⟨((496484719210201/562949953421312), (-59767726139437/562949953421312)), (2153461/562949953421312), by norm_num⟩
  | 3 => ⟨((107880324816169/140737488355328), (-210844765505915/1125899906842624)), (2127841/281474976710656), by norm_num⟩
  | 4 => ⟨((1244137258522663/2251799813685248), (-80810031692263/281474976710656)), (32472679/2251799813685248), by norm_num⟩
  | 5 => ⟨((501794516973673/2251799813685248), (-357185468014413/1125899906842624)), (13632077/562949953421312), by norm_num⟩
  | 6 => ⟨((-459238153243751/9007199254740992), (-1273532102120411/9007199254740992)), (235599793/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-875474845/16777216)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-917455297/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-357371834019453/9007199254740992), (591710033743533/4503599627370496)), (13335119/562949953421312), by norm_num⟩
  | 1 => ⟨((392379311/4294967296), (-1299345687/4294967296)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((-28233961/268435456), (1495927005/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((346725855/4294967296), (-1148166407/4294967296)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((-399182893/8589934592), (1321875427/8589934592)), (249/8589934592), by norm_num⟩
  | 5 => ⟨((45957629/2147483648), (-1217492261/17179869184)), (29/2147483648), by norm_num⟩
  | 6 => ⟨((-282190271/34359738368), (233614961/8589934592)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((92823873/34359738368), (-307381901/34359738368)), (239/137438953472), by norm_num⟩
  | 8 => ⟨((-427469733/549755813888), (707772983/274877906944)), (139/274877906944), by norm_num⟩
  | 9 => ⟨((437460193/2199023255552), (-1448628907/2199023255552)), (287/2199023255552), by norm_num⟩
  | 10 => ⟨((-25182233/549755813888), (1334236531/8796093022208)), (267/8796093022208), by norm_num⟩
  | 11 => ⟨((168681409/17592186044416), (-139645143/4398046511104)), (113/17592186044416), by norm_num⟩
  | 12 => ⟨((-64733883/35184372088832), (428726433/70368744177664)), (175/140737488355328), by norm_num⟩
  | 13 => ⟨((183452645/562949953421312), (-607494827/562949953421312)), (125/562949953421312), by norm_num⟩
  | 14 => ⟨((-120690093/2251799813685248), (1598638323/9007199254740992)), (83/2251799813685248), by norm_num⟩
  | 15 => ⟨((296425823/36028797018963968), (-490800103/18014398509481984)), (103/18014398509481984), by norm_num⟩
  | 16 => ⟨((-341272841/288230376151711744), (1130109001/288230376151711744)), (239/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1214080098909/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778901319784733/633825300114114700748351602688), (718505431417/158456325028528675187087900672)), (92483/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889890741936721/39614081257132168796771975168), (1616352568997/19807040628566084398385987584)), (52031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889674832420509/2475880078570760549798248448), (3434052589885/2475880078570760549798248448)), (110587/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442835189375259/38685626227668133590597632), (1716634526123/77371252455336267181195264)), (55305/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193711721449185/1208925819614629174706176), (3217857407175/9671406556917033397649408)), (51861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258911142268903/604462909807314587353088), (1407396551863/302231454903657293676544)), (90783/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887990395186873/75557863725914323419136), (2286239491543/37778931862957161709568)), (9223/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297687651609365/4722366482869645213696), (3427994831815/4722366482869645213696)), (55359/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405412742647827/147573952589676412928), (2355638269235/295147905179352825856)), (152303/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823726814035377/73786976294838206464), (2942886273219/36893488147419103232)), (11905/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911469356377355/4611686018427387904), (1654231775125/2305843009213693952)), (53607/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594184840946795/1152921504606846976), (3305610879781/576460752303423488)), (107301/576460752303423488), by norm_num⟩
  | 5 => ⟨((597376100285309/72057594037927936), (5778405242207/144115188075855872)), (46993/36028797018963968), by norm_num⟩
  | 4 => ⟨((372972307903867/9007199254740992), (8654792043967/36028797018963968)), (70587/9007199254740992), by norm_num⟩
  | 3 => ⟨((744781588690177/4503599627370496), (10796088859323/9007199254740992)), (88405/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228531322863563/4503599627370496), (21525080051345/4503599627370496)), (709297/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216909640876761/2251799813685248), (16060123238297/1125899906842624)), (1069099/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182071503766683/2251799813685248), (63573220740265/2251799813685248)), (2158887/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182071503766683/2251799813685248), (63573220740265/2251799813685248)), (8235500344283293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1056353780705189/1125899906842624), (123209276896575/2251799813685248)), (4305973/2251799813685248), by norm_num⟩
  | 2 => ⟨((987732720975567/1125899906842624), (231197435361085/2251799813685248)), (8551203/2251799813685248), by norm_num⟩
  | 3 => ⟨((26707882143551/35184372088832), (202825553607313/1125899906842624)), (2094949/281474976710656), by norm_num⟩
  | 4 => ⟨((612214480572203/1125899906842624), (153961564747209/562949953421312)), (7870547/562949953421312), by norm_num⟩
  | 5 => ⟨((497362003217205/2251799813685248), (669739814823317/2251799813685248)), (51457409/2251799813685248), by norm_num⟩
  | 6 => ⟨((-357371834019453/9007199254740992), (591710033743533/4503599627370496)), (13335119/562949953421312), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-917455297/16777216)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-955431235/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((524498106473337/4503599627370496), (-221427633034283/4503599627370496)), (99629981/9007199254740992), by norm_num⟩
  | 1 => ⟨((-599714055/2147483648), (506363177/4294967296)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((719025749/2147483648), (-303551467/2147483648)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((-143679037/536870912), (485256419/4294967296)), (29/1073741824), by norm_num⟩
  | 4 => ⟨((1378109135/8589934592), (-581797037/8589934592)), (71/4294967296), by norm_num⟩
  | 5 => ⟨((-165228069/2147483648), (279017673/8589934592)), (69/8589934592), by norm_num⟩
  | 6 => ⟨((528266141/17179869184), (-446036773/34359738368)), (113/34359738368), by norm_num⟩
  | 7 => ⟨((-1447687865/137438953472), (611171125/137438953472)), (79/68719476736), by norm_num⟩
  | 8 => ⟨((216962743/68719476736), (-11449409/8589934592)), (3/8589934592), by norm_num⟩
  | 9 => ⟨((-462447943/549755813888), (48807971/137438953472)), (13/137438953472), by norm_num⟩
  | 10 => ⟨((887121389/4398046511104), (-374516489/4398046511104)), (51/2199023255552), by norm_num⟩
  | 11 => ⟨((-773536067/17592186044416), (81641029/4398046511104)), (91/17592186044416), by norm_num⟩
  | 12 => ⟨((1236572319/140737488355328), (-522044367/140737488355328)), (37/35184372088832), by norm_num⟩
  | 13 => ⟨((-912360283/562949953421312), (192585803/281474976710656)), (111/562949953421312), by norm_num⟩
  | 14 => ⟨((1250139663/4503599627370496), (-527772099/4503599627370496)), (77/2251799813685248), by norm_num⟩
  | 15 => ⟨((-399693865/9007199254740992), (168738963/9007199254740992)), (25/4503599627370496), by norm_num⟩
  | 16 => ⟨((958424029/144115188075855872), (-202309181/72057594037927936)), (61/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-260178183291/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444694700490203/158456325028528675187087900672), (-615821245741/633825300114114700748351602688)), (92261/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29527393339197/618970019642690137449562112), (-173168454753/9903520314283042199192993792)), (51899/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889529007502307/2475880078570760549798248448), (-735810698961/2475880078570760549798248448)), (110289/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442798829073231/38685626227668133590597632), (-183909031413/38685626227668133590597632)), (55147/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549557827916079/9671406556917033397649408), (-344736720791/4835703278458516698824704)), (51703/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157349074842497/75557863725914323419136), (-301551950173/302231454903657293676544)), (90487/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471949631216385/18889465931478580854784), (-489848212281/37778931862957161709568)), (73525/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297544415851893/4722366482869645213696), (-91808558749/590295810358705651712)), (110297/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810727552106697/295147905179352825856), (-504700325937/295147905179352825856)), (18959/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455870900848235/18446744073709551616), (-630505513427/36893488147419103232)), (189611/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227833416059647/1152921504606846976), (-354405233313/2305843009213693952)), (213343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593916236780063/1152921504606846976), (-44260982725/36028797018963968)), (213381/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194520293357927/144115188075855872), (-1237880860901/144115188075855872)), (93375/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491547598206167/36028797018963968), (-1853971767245/36028797018963968)), (140105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489146998868643/9007199254740992), (-578121637503/2251799813685248)), (87603/2251799813685248), by norm_num⟩
  | 2 => ⟨((278466427127855/562949953421312), (-4610072595989/4503599627370496)), (87659/562949953421312), by norm_num⟩
  | 1 => ⟨((1107895213221151/1125899906842624), (-6877976272599/2251799813685248)), (1053035/2251799813685248), by norm_num⟩
  | 0 => ⟨((545038190309945/562949953421312), (-6804065879657/1125899906842624)), (65957/70368744177664), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((545038190309945/562949953421312), (-6804065879657/1125899906842624)), (251605987817263581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2110703114995375/2251799813685248), (-6587576269009/562949953421312)), (4112449/2251799813685248), by norm_num⟩
  | 2 => ⟨((1978139119650981/2251799813685248), (-24699207570341/1125899906842624)), (3902889/1125899906842624), by norm_num⟩
  | 3 => ⟨((1736652676454019/2251799813685248), (-86790075072101/2251799813685248)), (3514191/562949953421312), by norm_num⟩
  | 4 => ⟨((334002825564271/562949953421312), (-133869996122735/2251799813685248)), (2845691/281474976710656), by norm_num⟩
  | 5 => ⟨((784707864863407/2251799813685248), (-317704667646065/4503599627370496)), (29720781/2251799813685248), by norm_num⟩
  | 6 => ⟨((524498106473337/4503599627370496), (-221427633034283/4503599627370496)), (99629981/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-955431235/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-495050275/8388608)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-206058880647871/2251799813685248), (-330321818668367/4503599627370496)), (18017671/562949953421312), by norm_num⟩
  | 1 => ⟨((488316615/2147483648), (24462309/134217728)), (43/536870912), by norm_num⟩
  | 2 => ⟨((-303355301/1073741824), (-243146217/1073741824)), (27/268435456), by norm_num⟩
  | 3 => ⟨((1005079473/4294967296), (402797101/2147483648)), (45/536870912), by norm_num⟩
  | 4 => ⟨((-312191083/2147483648), (-500456597/4294967296)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((310306279/4294967296), (248717585/4294967296)), (227/8589934592), by norm_num⟩
  | 6 => ⟨((-1028109515/34359738368), (-206013327/8589934592)), (379/34359738368), by norm_num⟩
  | 7 => ⟨((364965167/34359738368), (292527935/34359738368)), (271/68719476736), by norm_num⟩
  | 8 => ⟨((-453452185/137438953472), (-726904611/274877906944)), (339/274877906944), by norm_num⟩
  | 9 => ⟨((500793933/549755813888), (802795601/1099511627776)), (377/1099511627776), by norm_num⟩
  | 10 => ⟨((-995540939/4398046511104), (-797948851/4398046511104)), (377/4398046511104), by norm_num⟩
  | 11 => ⟨((56223325/1099511627776), (721028511/17592186044416)), (343/17592186044416), by norm_num⟩
  | 12 => ⟨((-745118475/70368744177664), (-298614757/35184372088832)), (143/35184372088832), by norm_num⟩
  | 13 => ⟨((569707647/281474976710656), (57079215/35184372088832)), (55/70368744177664), by norm_num⟩
  | 14 => ⟨((-808954469/2251799813685248), (-162098881/562949953421312)), (157/1125899906842624), by norm_num⟩
  | 15 => ⟨((1072094047/18014398509481984), (859307919/18014398509481984)), (419/18014398509481984), by norm_num⟩
  | 16 => ⟨((-333006703/36028797018963968), (-266912495/36028797018963968)), (263/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-3212141084417/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889327792358811/316912650057057350374175801344), (-1900485757621/316912650057057350374175801344)), (138861/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944807077385795/19807040628566084398385987584), (-534409520569/4951760157141521099596496896)), (156255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472345194074781/618970019642690137449562112), (-4435044887/2417851639229258349412352)), (166063/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771046496560415/154742504910672534362390528), (-2270183390889/77371252455336267181195264)), (83055/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549417684528431/9671406556917033397649408), (-2127702473269/4835703278458516698824704)), (77889/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629334674432167/302231454903657293676544), (-3722290664055/604462909807314587353088)), (34089/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((29493704282175/1180591620717411303424), (-6046494109235/75557863725914323419136)), (221671/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297392305220979/4722366482869645213696), (-4532921415155/4722366482869645213696)), (2599/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1621244292388003/590295810358705651712), (-778700066955/73786976294838206464)), (57211/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823217602366855/73786976294838206464), (-3891126390011/36893488147419103232)), (286255/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911182332061555/4611686018427387904), (-8748508834935/9223372036854775808)), (322313/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796804656998795/576460752303423488), (-8740356116949/1152921504606846976)), (322657/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194246956276045/144115188075855872), (-7638645586899/144115188075855872)), (282713/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491128060961119/36028797018963968), (-5719825419917/18014398509481984)), (424845/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488605959126997/9007199254740992), (-14267540483401/9007199254740992)), (532415/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113299865526813/2251799813685248), (-888723200499/140737488355328)), (534459/2251799813685248), by norm_num⟩
  | 1 => ⟨((138373109192055/140737488355328), (-10604831274465/562949953421312)), (806809/1125899906842624), by norm_num⟩
  | 0 => ⟨((272002997011335/281474976710656), (-5242740487877/140737488355328)), (1634175/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((272002997011335/281474976710656), (-5242740487877/140737488355328)), (6233882908347701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049836627542155/1125899906842624), (-20265263248905/281474976710656)), (3280119/1125899906842624), by norm_num⟩
  | 2 => ⟨((973075886726639/1125899906842624), (-151169499144177/1125899906842624)), (6589359/1125899906842624), by norm_num⟩
  | 3 => ⟨((410349294036531/562949953421312), (-130650507679901/562949953421312)), (26318705/2251799813685248), by norm_num⟩
  | 4 => ⟨((268792966478883/562949953421312), (-190469306431715/562949953421312)), (25292505/1125899906842624), by norm_num⟩
  | 5 => ⟨((511180106399527/4503599627370496), (-1455100854711761/4503599627370496)), (5158493/140737488355328), by norm_num⟩
  | 6 => ⟨((-206058880647871/2251799813685248), (-330321818668367/4503599627370496)), (18017671/562949953421312), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-495050275/8388608)), (3/33554432), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1021993229/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-333889572465227/9007199254740992), (57974618572685/562949953421312)), (258616383/9007199254740992), by norm_num⟩
  | 1 => ⟨((408368037/4294967296), (-567252963/2147483648)), (319/4294967296), by norm_num⟩
  | 2 => ⟨((-523721667/4294967296), (1454975123/4294967296)), (411/4294967296), by norm_num⟩
  | 3 => ⟨((874557/8388608), (-1243979169/4294967296)), (177/2147483648), by norm_num⟩
  | 4 => ⟨((-287128885/4294967296), (797685893/4294967296)), (229/4294967296), by norm_num⟩
  | 5 => ⟨((73647105/2147483648), (-25575299/268435456)), (237/8589934592), by norm_num⟩
  | 6 => ⟨((-125934063/8589934592), (1399452731/34359738368)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((184579711/34359738368), (-1025578681/68719476736)), (301/68719476736), by norm_num⟩
  | 8 => ⟨((-473437611/274877906944), (657639345/137438953472)), (97/68719476736), by norm_num⟩
  | 9 => ⟨((539708221/1099511627776), (-1499388103/1099511627776)), (445/1099511627776), by norm_num⟩
  | 10 => ⟨((-276864851/2199023255552), (1538341821/4398046511104)), (459/4398046511104), by norm_num⟩
  | 11 => ⟨((258234299/8796093022208), (-717412521/8796093022208)), (431/17592186044416), by norm_num⟩
  | 12 => ⟨((-441571933/70368744177664), (613375595/35184372088832)), (185/35184372088832), by norm_num⟩
  | 13 => ⟨((87123819/70368744177664), (-484085335/140737488355328)), (147/140737488355328), by norm_num⟩
  | 14 => ⟨((-127696105/562949953421312), (1419033565/2251799813685248)), (433/2251799813685248), by norm_num⟩
  | 15 => ⟨((349369645/9007199254740992), (-970599795/9007199254740992)), (149/4503599627370496), by norm_num⟩
  | 16 => ⟨((-448057723/72057594037927936), (311192415/18014398509481984)), (385/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (312025916755/1267650600228229401496703205376)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889276120672965/316912650057057350374175801344), (2953460502773/633825300114114700748351602688)), (8671/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472374522340601/9903520314283042199192993792), (3321995169407/39614081257132168796771975168)), (78053/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889257710194565/2475880078570760549798248448), (441102827127/309485009821345068724781056)), (165895/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221365464415719/19342813113834066795298816), (440990742307/19342813113834066795298816)), (41483/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193662859951905/1208925819614629174706176), (1653239044497/4835703278458516698824704)), (9725/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314642299214315/151115727451828646838272), (1446108061207/302231454903657293676544)), (136189/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943717446707669/37778931862957161709568), (1174516598355/18889465931478580854784)), (221379/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297271164880145/4722366482869645213696), (880497167469/1180591620717411303424)), (166099/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50658704006877/18446744073709551616), (1210049669809/147573952589676412928)), (228489/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455752900362449/18446744073709551616), (6046446637383/73786976294838206464)), (142883/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28470852604801/144115188075855872), (3398514101007/4611686018427387904)), (321701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398345320043473/288230376151711744), (848812812757/144115188075855872)), (321969/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194049743512667/144115188075855872), (1483588660667/36028797018963968)), (35253/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490836863721443/36028797018963968), (8886877778463/36028797018963968)), (423639/36028797018963968), by norm_num⟩
  | 3 => ⟨((744125012244125/4503599627370496), (1385373521491/1125899906842624)), (265303/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112955970994479/2251799813685248), (11044646095093/2251799813685248)), (1064387/4503599627370496), by norm_num⟩
  | 1 => ⟨((553249473868779/562949953421312), (32942727974465/2251799813685248)), (1604543/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174317395989239/2251799813685248), (32561805863487/1125899906842624)), (3241051/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174317395989239/2251799813685248), (32561805863487/1125899906842624)), (12363628396041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1048808829495109/1125899906842624), (125765532981255/2251799813685248)), (6446527/2251799813685248), by norm_num⟩
  | 2 => ⟨((486742077090601/562949953421312), (234308575096695/2251799813685248)), (12730351/2251799813685248), by norm_num⟩
  | 3 => ⟨((829510923373293/1125899906842624), (405179330168097/2251799813685248)), (24663313/2251799813685248), by norm_num⟩
  | 4 => ⟨((287346057879721/562949953421312), (74629342772139/281474976710656)), (2826075/140737488355328), by norm_num⟩
  | 5 => ⟨((856766771571107/4503599627370496), (609487854254911/2251799813685248)), (70137831/2251799813685248), by norm_num⟩
  | 6 => ⟨((-333889572465227/9007199254740992), (57974618572685/562949953421312)), (258616383/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1021993229/16777216)), (3/33554432), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1051521237/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1827079868195965/18014398509481984), (35990891815575/2251799813685248)), (132554505/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1149599199/4294967296), (-181163839/4294967296)), (85/4294967296), by norm_num⟩
  | 2 => ⟨((189616137/536870912), (239050879/4294967296)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((-1334420949/4294967296), (-105144829/2147483648)), (103/4294967296), by norm_num⟩
  | 4 => ⟨((1760806693/8589934592), (8671351/268435456)), (139/8589934592), by norm_num⟩
  | 5 => ⟨((-464686981/4294967296), (-146458831/8589934592)), (75/8589934592), by norm_num⟩
  | 6 => ⟨((817557055/17179869184), (257675501/34359738368)), (67/17179869184), by norm_num⟩
  | 7 => ⟨((-616451411/34359738368), (-48572887/17179869184)), (103/68719476736), by norm_num⟩
  | 8 => ⟨((813425307/137438953472), (256373267/274877906944)), (69/137438953472), by norm_num⟩
  | 9 => ⟨((-477039115/274877906944), (-18793993/68719476736)), (83/549755813888), by norm_num⟩
  | 10 => ⟨((503573429/1099511627776), (9919685/137438953472)), (89/2199023255552), by norm_num⟩
  | 11 => ⟨((-30203617/274877906944), (-38077989/2199023255552)), (87/8796093022208), by norm_num⟩
  | 12 => ⟨((1700460305/70368744177664), (267973323/70368744177664)), (39/17592186044416), by norm_num⟩
  | 13 => ⟨((-1380803763/281474976710656), (-217599065/281474976710656)), (129/281474976710656), by norm_num⟩
  | 14 => ⟨((520574327/562949953421312), (164073259/1125899906842624)), (99/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1465413859/9007199254740992), (-57733165/2251799813685248)), (71/4503599627370496), by norm_num⟩
  | 16 => ⟨((241706949/9007199254740992), (38090283/9007199254740992)), (95/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (101801228069/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889229187396779/316912650057057350374175801344), (240872765781/633825300114114700748351602688)), (1441/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889392771051091/39614081257132168796771975168), (67732075709/9903520314283042199192993792)), (51877/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472286544295469/618970019642690137449562112), (287794510351/2475880078570760549798248448)), (3445/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885406297806729/77371252455336267181195264), (287719379425/154742504910672534362390528)), (55121/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549199143729529/9671406556917033397649408), (8426784979/302231454903657293676544)), (51677/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258478866478713/604462909807314587353088), (58967552933/151115727451828646838272)), (90437/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887288928091711/75557863725914323419136), (95784898985/18889465931478580854784)), (36741/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648581204525245/2361183241434822606848), (287223952337/4722366482869645213696)), (27557/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810465077342221/295147905179352825856), (197360299293/295147905179352825856)), (9473/36893488147419103232), by norm_num⟩
  | 8 => ⟨((14240842819367/576460752303423488), (61635307687/9223372036854775808)), (47367/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227741284830947/1152921504606846976), (277140238699/4611686018427387904)), (213163/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593179983628139/1152921504606846976), (276867195451/576460752303423488)), (213179/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74617310436583/9007199254740992), (241951985139/72057594037927936)), (186549/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490584396104085/36028797018963968), (362315261713/18014398509481984)), (139929/18014398509481984), by norm_num⟩
  | 3 => ⟨((185993264746207/1125899906842624), (112955964729/1125899906842624)), (349883/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225338995179147/4503599627370496), (450222593113/1125899906842624)), (349975/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106112527742061/1125899906842624), (2685379618417/2251799813685248)), (262599/562949953421312), by norm_num⟩
  | 0 => ⟨((1086557269967649/1125899906842624), (5307274635495/2251799813685248)), (32855/35184372088832), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086557269967649/1125899906842624), (5307274635495/2251799813685248)), (125331878796327103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((524291569771645/562949953421312), (1280455261579/281474976710656)), (4068401/2251799813685248), by norm_num⟩
  | 2 => ⟨((1953104997702639/2251799813685248), (19080400168025/2251799813685248)), (7615055/2251799813685248), by norm_num⟩
  | 3 => ⟨((1693869520371851/2251799813685248), (16549439563789/1125899906842624)), (3334733/562949953421312), by norm_num⟩
  | 4 => ⟨((1273691559442575/2251799813685248), (12448971301077/562949953421312)), (20460003/2251799813685248), by norm_num⟩
  | 5 => ⟨((179835097747991/562949953421312), (112664719650899/4503599627370496)), (48101181/4503599627370496), by norm_num⟩
  | 6 => ⟨((1827079868195965/18014398509481984), (35990891815575/2251799813685248)), (132554505/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1051521237/16777216)), (1/16777216), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1079011155/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((9635037914275/1125899906842624), (-433985560887935/4503599627370496)), (273796327/18014398509481984), by norm_num⟩
  | 1 => ⟨((-24883429/1073741824), (1120810209/4294967296)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((67385575/2147483648), (-379401289/1073741824)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((-950435/33554432), (684958491/2147483648)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((41181211/2147483648), (-1854901979/8589934592)), (303/8589934592), by norm_num⟩
  | 5 => ⟨((-89216629/8589934592), (1004633535/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((40267185/8589934592), (-1813732031/34359738368)), (151/17179869184), by norm_num⟩
  | 7 => ⟨((-124623495/68719476736), (1403336397/68719476736)), (59/17179869184), by norm_num⟩
  | 8 => ⟨((42185835/68719476736), (-950076353/137438953472)), (161/137438953472), by norm_num⟩
  | 9 => ⟨((-101547875/549755813888), (571745435/274877906944)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((109998697/2199023255552), (-77415767/137438953472)), (107/1099511627776), by norm_num⟩
  | 11 => ⟨((-108320725/8796093022208), (1219757285/8796093022208)), (53/2199023255552), by norm_num⟩
  | 12 => ⟨((12222415/4398046511104), (-1101054653/35184372088832)), (97/17592186044416), by norm_num⟩
  | 13 => ⟨((-162948497/281474976710656), (917449623/140737488355328)), (163/140737488355328), by norm_num⟩
  | 14 => ⟨((126077917/1125899906842624), (-709857039/562949953421312)), (127/562949953421312), by norm_num⟩
  | 15 => ⟨((-45523377/2251799813685248), (1025241865/4503599627370496)), (185/4503599627370496), by norm_num⟩
  | 16 => ⟨((61639795/18014398509481984), (-1388203219/36028797018963968)), (63/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-965380819903/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222295489092865/79228162514264337593543950336), (-570992875965/158456325028528675187087900672)), (92425/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472321592017855/9903520314283042199192993792), (-2568943535753/39614081257132168796771975168)), (103993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889032946950369/2475880078570760549798248448), (-2728851998743/2475880078570760549798248448)), (110509/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885349583197043/77371252455336267181195264), (-2728120432459/154742504910672534362390528)), (1727/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1549092592574309/9671406556917033397649408), (-639208964243/2417851639229258349412352)), (12955/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314596355784709/151115727451828646838272), (-1118227298589/302231454903657293676544)), (45353/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887136687279777/75557863725914323419136), (-14190557959/295147905179352825856)), (147433/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324261970717073/1180591620717411303424), (-680828451399/1180591620717411303424)), (6913/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810386060177419/295147905179352825856), (-233905525705/36893488147419103232)), (152139/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911314748997555/36893488147419103232), (-4675010292043/73786976294838206464)), (95127/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821705945006169/9223372036854775808), (-5255126834753/9223372036854775808)), (107073/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592954211957647/1152921504606846976), (-5249806744335/1152921504606846976)), (53571/288230376151711744), by norm_num⟩
  | 5 => ⟨((596838901618021/72057594037927936), (-1146900526267/36028797018963968)), (93827/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490282433997617/36028797018963968), (-3434730657203/18014398509481984)), (281793/36028797018963968), by norm_num⟩
  | 3 => ⟨((371890765067603/2251799813685248), (-4282981906719/4503599627370496)), (176393/4503599627370496), by norm_num⟩
  | 2 => ⟨((139034759963733/281474976710656), (-8534740261691/2251799813685248)), (707213/4503599627370496), by norm_num⟩
  | 1 => ⟨((138188083227297/140737488355328), (-25448596980347/2251799813685248)), (1064933/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085259592851215/1125899906842624), (-50277655318939/2251799813685248)), (2146393/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085259592851215/1125899906842624), (-50277655318939/2251799813685248)), (8187839516646575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2091049863429881/2251799813685248), (-96925681242769/2251799813685248)), (1058421/562949953421312), by norm_num⟩
  | 2 => ⟨((968801693016663/1125899906842624), (-180012833550993/2251799813685248)), (8227373/2251799813685248), by norm_num⟩
  | 3 => ⟨((1652856634370871/2251799813685248), (-309790838153619/2251799813685248)), (15474217/2251799813685248), by norm_num⟩
  | 4 => ⟨((585301738271733/1125899906842624), (-454782737788337/2251799813685248)), (6743591/562949953421312), by norm_num⟩
  | 5 => ⟨((1033382411379863/4503599627370496), (-236419885414111/1125899906842624)), (77882163/4503599627370496), by norm_num⟩
  | 6 => ⟨((9635037914275/1125899906842624), (-433985560887935/4503599627370496)), (273796327/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1079011155/16777216)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile027Terms1
