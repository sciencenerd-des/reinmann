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
namespace Reinmann.XiBand97.Tile050Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨50,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76013/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76013/2560))
  have he : value ((69/80), (76013/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-715655399/268435456), (-12318639915/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-488986021471189/9007199254740992), (195631153979257/4503599627370496)), (28721521/18014398509481984), by norm_num⟩
  | 1 => ⟨((1441456367/8589934592), (-4613526933/34359738368)), (341/68719476736), by norm_num⟩
  | 2 => ⟨((-4455602825/17179869184), (14260607609/68719476736)), (529/68719476736), by norm_num⟩
  | 3 => ⟨((9181638325/34359738368), (-1836672647/8589934592)), (137/17179869184), by norm_num⟩
  | 4 => ⟨((-14190416927/68719476736), (11354466249/68719476736)), (213/34359738368), by norm_num⟩
  | 5 => ⟨((17545272461/137438953472), (-3509713721/34359738368)), (529/137438953472), by norm_num⟩
  | 6 => ⟨((-1129857959/17179869184), (7232449407/137438953472)), (547/274877906944), by norm_num⟩
  | 7 => ⟨((15965435051/549755813888), (-12774747519/549755813888)), (485/549755813888), by norm_num⟩
  | 8 => ⟨((-6168729691/549755813888), (308494429/34359738368)), (47/137438953472), by norm_num⟩
  | 9 => ⟨((8474580159/2199023255552), (-13561875579/4398046511104)), (259/2199023255552), by norm_num⟩
  | 10 => ⟨((-5239057409/4398046511104), (1048008329/1099511627776)), (161/4398046511104), by norm_num⟩
  | 11 => ⟨((2944390703/8796093022208), (-2355955081/8796093022208)), (363/35184372088832), by norm_num⟩
  | 12 => ⟨((-1516872777/17592186044416), (9709809565/140737488355328)), (47/17592186044416), by norm_num⟩
  | 13 => ⟨((11541460061/562949953421312), (-577181415/35184372088832)), (45/70368744177664), by norm_num⟩
  | 14 => ⟨((-5096449003/1125899906842624), (4077925159/1125899906842624)), (319/2251799813685248), by norm_num⟩
  | 15 => ⟨((16803562911/18014398509481984), (-6722687887/9007199254740992)), (33/1125899906842624), by norm_num⟩
  | 16 => ⟨((-12985131581/72057594037927936), (5195028415/36028797018963968)), (205/36028797018963968), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (3213230414839/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777850096090881/633825300114114700748351602688), (474872446887/79228162514264337593543950336)), (11573/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888708180211835/39614081257132168796771975168), (2136426497991/19807040628566084398385987584)), (6511/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944209207655899/1237940039285380274899124224), (4538670318345/2475880078570760549798248448)), (13839/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885042201127135/77371252455336267181195264), (4537280224713/154742504910672534362390528)), (13843/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193564500558551/1208925819614629174706176), (1063055917243/2417851639229258349412352)), (12983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157235082770969/75557863725914323419136), (929804913771/151115727451828646838272)), (2841/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943157994738883/37778931862957161709568), (6040965369437/75557863725914323419136)), (9237/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296431956680693/4722366482869645213696), (4528304311681/4722366482869645213696)), (6931/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619924568614849/590295810358705651712), (6222488328415/590295810358705651712)), (19071/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821569080878437/73786976294838206464), (1943054662533/18446744073709551616)), (23855/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820511635672917/9223372036854775808), (4367825159137/4611686018427387904)), (26861/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795879116688667/576460752303423488), (8725538998593/1152921504606846976)), (26889/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192629452103655/144115188075855872), (3811741371245/72057594037927936)), (23561/144115188075855872), by norm_num⟩
  | 4 => ⟨((744353093788901/18014398509481984), (11412524725313/36028797018963968)), (35405/36028797018963968), by norm_num⟩
  | 3 => ⟨((371396571919707/2251799813685248), (222281184267/140737488355328)), (22185/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110291699865117/2251799813685248), (28333266381279/4503599627370496)), (89081/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205002780378569/2251799813685248), (1318874342181/70368744177664)), (67239/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158320162492523/2251799813685248), (41614812512425/1125899906842624)), (68099/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158320162492523/2251799813685248), (41614812512425/1125899906842624)), (259777071239280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((64551402464141/70368744177664), (79774488263163/1125899906842624)), (542313/2251799813685248), by norm_num⟩
  | 2 => ⟨((941787290291487/1125899906842624), (292718317396425/2251799813685248)), (267953/562949953421312), by norm_num⟩
  | 3 => ⟨((768755989372967/1125899906842624), (489703195255697/2251799813685248)), (1035873/1125899906842624), by norm_num⟩
  | 4 => ⟨((471652464938099/1125899906842624), (334365659043009/1125899906842624)), (3730239/2251799813685248), by norm_num⟩
  | 5 => ⟨((196563927330329/2251799813685248), (1120557067780845/4503599627370496)), (10681733/4503599627370496), by norm_num⟩
  | 6 => ⟨((-488986021471189/9007199254740992), (195631153979257/4503599627370496)), (28721521/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-12318639915/134217728)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-725947119/268435456), (-24991584415/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((495827291325009/18014398509481984), (549348073105445/9007199254740992)), (2612133/2251799813685248), by norm_num⟩
  | 1 => ⟨((-5930570999/68719476736), (-3285365497/17179869184)), (63/17179869184), by norm_num⟩
  | 2 => ⟨((2324408883/17179869184), (10301244513/34359738368)), (397/68719476736), by norm_num⟩
  | 3 => ⟨((-9717560811/68719476736), (-10766497529/34359738368)), (417/68719476736), by norm_num⟩
  | 4 => ⟨((7617338929/68719476736), (4219786341/17179869184)), (329/68719476736), by norm_num⟩
  | 5 => ⟨((-9553648861/137438953472), (-21169785063/137438953472)), (207/68719476736), by norm_num⟩
  | 6 => ⟨((9985136915/274877906944), (2765739109/34359738368)), (435/274877906944), by norm_num⟩
  | 7 => ⟨((-4472619863/274877906944), (-19821620523/549755813888)), (49/68719476736), by norm_num⟩
  | 8 => ⟨((7011936855/1099511627776), (15537644125/1099511627776)), (309/1099511627776), by norm_num⟩
  | 9 => ⟨((-4885752767/2199023255552), (-5413132587/1099511627776)), (433/4398046511104), by norm_num⟩
  | 10 => ⟨((765962477/1099511627776), (13578276733/8796093022208)), (273/8796093022208), by norm_num⟩
  | 11 => ⟨((-6986679029/35184372088832), (-7740837847/17592186044416)), (313/35184372088832), by norm_num⟩
  | 12 => ⟨((7302230561/140737488355328), (8090450765/70368744177664)), (329/140737488355328), by norm_num⟩
  | 13 => ⟨((-7044954365/562949953421312), (-15610807125/562949953421312)), (319/562949953421312), by norm_num⟩
  | 14 => ⟨((3155630523/1125899906842624), (6992513635/1125899906842624)), (9/70368744177664), by norm_num⟩
  | 15 => ⟨((-5277046001/9007199254740992), (-11693325897/9007199254740992)), (121/4503599627370496), by norm_num⟩
  | 16 => ⟨((8273073607/72057594037927936), (18332177857/72057594037927936)), (191/36028797018963968), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (1493929666897/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777797119586475/633825300114114700748351602688), (883075300999/316912650057057350374175801344)), (2887/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472162232247323/9903520314283042199192993792), (1986455632923/39614081257132168796771975168)), (12993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888355924811705/2475880078570760549798248448), (263753380229/309485009821345068724781056)), (6903/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770022433098471/154742504910672534362390528), (1054686264805/77371252455336267181195264)), (863/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548458461870933/9671406556917033397649408), (1976841597585/9671406556917033397649408)), (12947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257830865383349/604462909807314587353088), (1729041553159/604462909807314587353088)), (5665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943118052749721/37778931862957161709568), (1404195168061/37778931862957161709568)), (1151/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648186474481319/2361183241434822606848), (2105153983553/4722366482869645213696)), (13815/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619844902080771/590295810358705651712), (723184359639/147573952589676412928)), (2375/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821471697869231/73786976294838206464), (903287495261/18446744073709551616)), (11879/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910202549695423/4611686018427387904), (4060985915955/9223372036854775808)), (13369/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198956932898589/144115188075855872), (507028912373/144115188075855872)), (209/9007199254740992), by norm_num⟩
  | 5 => ⟨((1192543753497093/144115188075855872), (3543860514391/144115188075855872)), (23423/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488586061472279/36028797018963968), (5305124683135/36028797018963968)), (8791/9007199254740992), by norm_num⟩
  | 3 => ⟨((742725401762133/4503599627370496), (6612779860041/9007199254740992)), (5501/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110178096936187/2251799813685248), (13169840057263/4503599627370496)), (88175/4503599627370496), by norm_num⟩
  | 1 => ⟨((551192619527941/562949953421312), (19616013585691/2251799813685248)), (66331/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158284212925731/2251799813685248), (38680345466529/2251799813685248)), (266937/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158284212925731/2251799813685248), (38680345466529/2251799813685248)), (1018283852584075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2067987814164521/2251799813685248), (74147957969937/2251799813685248)), (260437/1125899906842624), by norm_num⟩
  | 2 => ⟨((118546163992479/140737488355328), (17023834955833/281474976710656)), (991015/2251799813685248), by norm_num⟩
  | 3 => ⟨((12417391788749/17592186044416), (229432581642763/2251799813685248)), (1789381/2251799813685248), by norm_num⟩
  | 4 => ⟨((549257566868221/1125899906842624), (323888600105685/2251799813685248)), (1445347/1125899906842624), by norm_num⟩
  | 5 => ⟨((978623114784203/4503599627370496), (632021597476761/4503599627370496)), (1825977/1125899906842624), by norm_num⟩
  | 6 => ⟨((495827291325009/18014398509481984), (549348073105445/9007199254740992)), (2612133/2251799813685248), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-24991584415/268435456)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-25330807557/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1154029211283003/18014398509481984), (-67722202091465/9007199254740992)), (5057215/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3497664409/17179869184), (1642034941/68719476736)), (247/137438953472), by norm_num⟩
  | 2 => ⟨((22231531545/68719476736), (-2609237717/68719476736)), (99/34359738368), by norm_num⟩
  | 3 => ⟨((-23551001327/68719476736), (2764099307/68719476736)), (53/17179869184), by norm_num⟩
  | 4 => ⟨((9355793747/34359738368), (-1098057049/34359738368)), (85/34359738368), by norm_num⟩
  | 5 => ⟨((-23786572923/137438953472), (348968441/17179869184)), (109/68719476736), by norm_num⟩
  | 6 => ⟨((25198336397/274877906944), (-739360327/68719476736)), (233/274877906944), by norm_num⟩
  | 7 => ⟨((-11440238501/274877906944), (2685402193/549755813888)), (107/274877906944), by norm_num⟩
  | 8 => ⟨((9089423447/549755813888), (-2133588181/1099511627776)), (43/274877906944), by norm_num⟩
  | 9 => ⟨((-1604815389/274877906944), (1506812909/2199023255552)), (245/4398046511104), by norm_num⟩
  | 10 => ⟨((16320607021/8796093022208), (-1915493015/8796093022208)), (157/8796093022208), by norm_num⟩
  | 11 => ⟨((-18861006421/35184372088832), (1106825439/17592186044416)), (183/35184372088832), by norm_num⟩
  | 12 => ⟨((9990215617/70368744177664), (-586258471/35184372088832)), (195/140737488355328), by norm_num⟩
  | 13 => ⟨((-9769059387/281474976710656), (2293121205/562949953421312)), (193/562949953421312), by norm_num⟩
  | 14 => ⟨((17740912345/2251799813685248), (-2082189323/2251799813685248)), (177/2251799813685248), by norm_num⟩
  | 15 => ⟨((-30070173031/18014398509481984), (3529231869/18014398509481984)), (151/9007199254740992), by norm_num⟩
  | 16 => ⟨((23891157145/72057594037927936), (-2804022215/72057594037927936)), (121/36028797018963968), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-152186772041/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222217781047659/79228162514264337593543950336), (-89953518153/316912650057057350374175801344)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888587304133529/39614081257132168796771975168), (-50586940771/9903520314283042199192993792)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888290588472225/2475880078570760549798248448), (-107467212585/1237940039285380274899124224)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884978627080221/77371252455336267181195264), (-214866879433/154742504910672534362390528)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774198761863183/4835703278458516698824704), (-100682981075/4835703278458516698824704)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628888855735577/302231454903657293676544), (-176123513363/604462909807314587353088)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943075021570589/37778931862957161709568), (-143033168453/37778931862957161709568)), (18369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324077168885155/1180591620717411303424), (-107216124325/2361183241434822606848)), (6889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619756969735543/590295810358705651712), (-294653532267/590295810358705651712)), (18945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455340611710471/18446744073709551616), (-2875241687/576460752303423488)), (11841/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455070775975081/2305843009213693952), (-206820981421/4611686018427387904)), (13321/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591534605135263/1152921504606846976), (-413151484489/1152921504606846976)), (6661/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192439278944837/144115188075855872), (-360956545925/144115188075855872)), (5829/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488431893720849/36028797018963968), (-270167386349/18014398509481984)), (1093/1125899906842624), by norm_num⟩
  | 3 => ⟨((1485262527093069/9007199254740992), (-673497786259/9007199254740992)), (21863/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109996432765081/2251799813685248), (-83828193551/281474976710656)), (43735/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102129142320687/1125899906842624), (-1997576739575/2251799813685248)), (131253/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157389457632839/2251799813685248), (-1969160031779/1125899906842624)), (16419/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157389457632839/2251799813685248), (-1969160031779/1125899906842624)), (62633514941167787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1033465260378373/1125899906842624), (-3773199613157/1125899906842624)), (126075/562949953421312), by norm_num⟩
  | 2 => ⟨((948606710847615/1125899906842624), (-13853702969409/2251799813685248)), (929177/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598377804501253/2251799813685248), (-11672188199859/1125899906842624)), (1577157/2251799813685248), by norm_num⟩
  | 4 => ⟨((567161128287087/1125899906842624), (-4142589948545/281474976710656)), (283963/281474976710656), by norm_num⟩
  | 5 => ⟨((1141832117270429/4503599627370496), (-66777260748481/4503599627370496)), (4711131/4503599627370496), by norm_num⟩
  | 6 => ⟨((1154029211283003/18014398509481984), (-67722202091465/9007199254740992)), (5057215/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-25330807557/268435456)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-25656180927/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((268662877503907/18014398509481984), (-1089103214730047/18014398509481984)), (5251329/4503599627370496), by norm_num⟩
  | 1 => ⟨((-6597842723/137438953472), (26746276921/137438953472)), (259/68719476736), by norm_num⟩
  | 2 => ⟨((5309409109/68719476736), (-10761618023/34359738368)), (419/68719476736), by norm_num⟩
  | 3 => ⟨((-356048513/4294967296), (23093541393/68719476736)), (113/17179869184), by norm_num⟩
  | 4 => ⟨((1146075951/17179869184), (-18583810525/68719476736)), (365/68719476736), by norm_num⟩
  | 5 => ⟨((-5902521875/137438953472), (23927591373/137438953472)), (59/17179869184), by norm_num⟩
  | 6 => ⟨((791645207/34359738368), (-25673315139/274877906944)), (127/68719476736), by norm_num⟩
  | 7 => ⟨((-5824474557/549755813888), (23611203841/549755813888)), (469/549755813888), by norm_num⟩
  | 8 => ⟨((2343532543/549755813888), (-9500191655/549755813888)), (379/1099511627776), by norm_num⟩
  | 9 => ⟨((-6705369109/4398046511104), (6795541611/1099511627776)), (17/137438953472), by norm_num⟩
  | 10 => ⟨((539593763/1099511627776), (-17499203687/8796093022208)), (11/274877906944), by norm_num⟩
  | 11 => ⟨((-5052757291/35184372088832), (5120705791/8796093022208)), (207/17592186044416), by norm_num⟩
  | 12 => ⟨((5421399431/140737488355328), (-5494305359/35184372088832)), (223/70368744177664), by norm_num⟩
  | 13 => ⟨((-2684740241/281474976710656), (10883376427/281474976710656)), (111/140737488355328), by norm_num⟩
  | 14 => ⟨((1234549351/562949953421312), (-20018421299/2251799813685248)), (205/1125899906842624), by norm_num⟩
  | 15 => ⟨((-4238785131/9007199254740992), (17183149965/9007199254740992)), (177/4503599627370496), by norm_num⟩
  | 16 => ⟨((1705515373/18014398509481984), (-1728450813/4503599627370496)), (143/18014398509481984), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-432773929183/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777685803209321/633825300114114700748351602688), (-2046289430987/633825300114114700748351602688)), (11551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944261848283521/19807040628566084398385987584), (-1150762098779/19807040628566084398385987584)), (12997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118013928773287/154742504910672534362390528), (-2444677089275/2475880078570760549798248448)), (13811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110618085192973/9671406556917033397649408), (-1221949273881/77371252455336267181195264)), (13813/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774166851421501/4835703278458516698824704), (-1145164006285/4835703278458516698824704)), (1619/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257721695371993/604462909807314587353088), (-2003210500087/604462909807314587353088)), (11335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886058693305259/75557863725914323419136), (-1626834065017/37778931862957161709568)), (18423/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648119940161137/2361183241434822606848), (-1219448278217/2361183241434822606848)), (13821/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619661917393585/590295810358705651712), (-3351283087959/590295810358705651712)), (9505/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821242944263823/73786976294838206464), (-261612930233/4611686018427387904)), (5943/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910073860327457/4611686018427387904), (-4704503525269/9223372036854775808)), (26755/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397849511577279/288230376151711744), (-2349424090471/576460752303423488)), (26771/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74519904470451/9007199254740992), (-513142297901/18014398509481984)), (11721/72057594037927936), by norm_num⟩
  | 4 => ⟨((186031006986279/4503599627370496), (-1536255303693/9007199254740992)), (17599/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485028155924429/9007199254740992), (-3829561494791/4503599627370496)), (22029/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109755246317807/2251799813685248), (-15251975414077/4503599627370496)), (22075/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101750483123065/1125899906842624), (-22712950062535/2251799813685248)), (132913/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155741677081151/2251799813685248), (-44769814274713/2251799813685248)), (66923/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155741677081151/2251799813685248), (-44769814274713/2251799813685248)), (255290987254905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2062891121050497/2251799813685248), (-85720012872043/2251799813685248)), (523191/2251799813685248), by norm_num⟩
  | 2 => ⟨((943283641575075/1125899906842624), (-157057525607193/2251799813685248)), (998433/2251799813685248), by norm_num⟩
  | 3 => ⟨((784809783272485/1125899906842624), (-263166901056031/2251799813685248)), (453065/562949953421312), by norm_num⟩
  | 4 => ⟨((1063348860461393/2251799813685248), (-366881562609711/2251799813685248)), (2950073/2251799813685248), by norm_num⟩
  | 5 => ⟨((884722267057469/4503599627370496), (-43312363864937/281474976710656)), (7494955/4503599627370496), by norm_num⟩
  | 6 => ⟨((268662877503907/18014398509481984), (-1089103214730047/18014398509481984)), (5251329/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-25656180927/268435456)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-754332693/268435456), (-6492197805/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-216139736745625/4503599627370496), (-654634595239469/18014398509481984)), (24900083/18014398509481984), by norm_num⟩
  | 1 => ⟨((5372651123/34359738368), (4068112771/34359738368)), (311/68719476736), by norm_num⟩
  | 2 => ⟨((-2188077003/8589934592), (-13254304135/68719476736)), (509/68719476736), by norm_num⟩
  | 3 => ⟨((19010576289/68719476736), (14394600805/68719476736)), (555/68719476736), by norm_num⟩
  | 4 => ⟨((-7742286599/34359738368), (-5862374881/34359738368)), (227/34359738368), by norm_num⟩
  | 5 => ⟨((5045023433/34359738368), (3820036661/34359738368)), (297/68719476736), by norm_num⟩
  | 6 => ⟨((-2739528897/34359738368), (-1037170685/17179869184)), (81/34359738368), by norm_num⟩
  | 7 => ⟨((10200742417/274877906944), (241371587/8589934592)), (303/274877906944), by norm_num⟩
  | 8 => ⟨((-16617501777/1099511627776), (-196602983/17179869184)), (495/1099511627776), by norm_num⟩
  | 9 => ⟨((3007856945/549755813888), (9110065753/2199023255552)), (45/274877906944), by norm_num⟩
  | 10 => ⟨((-15679821279/8796093022208), (-2968147369/2199023255552)), (471/8796093022208), by norm_num⟩
  | 11 => ⟨((18576862337/35184372088832), (7033098667/17592186044416)), (35/2199023255552), by norm_num⟩
  | 12 => ⟨((-10087535145/70368744177664), (-7638171473/70368744177664)), (153/35184372088832), by norm_num⟩
  | 13 => ⟨((10112665641/281474976710656), (3828600005/140737488355328)), (77/70368744177664), by norm_num⟩
  | 14 => ⟨((-18827451951/2251799813685248), (-14255941053/2251799813685248)), (9/35184372088832), by norm_num⟩
  | 15 => ⟨((16357774939/9007199254740992), (1548241073/1125899906842624)), (251/4503599627370496), by norm_num⟩
  | 16 => ⟨((-13323802475/36028797018963968), (-157634965/562949953421312)), (411/36028797018963968), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (-812017617611/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111101753391953/39614081257132168796771975168), (-1919628336291/316912650057057350374175801344)), (11573/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888458435978539/39614081257132168796771975168), (-4318103691461/39614081257132168796771975168)), (13023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888153124084465/2475880078570760549798248448), (-1146667195495/618970019642690137449562112)), (865/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769819180829725/154742504910672534362390528), (-4585188318955/154742504910672534362390528)), (3461/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387066858388365/2417851639229258349412352), (-134282548693/302231454903657293676544)), (12983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257663236793589/604462909807314587353088), (-3758339435831/604462909807314587353088)), (2841/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885962812337889/75557863725914323419136), (-1526088853945/18889465931478580854784)), (18475/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296167195544531/4722366482869645213696), (-2287844930923/2361183241434822606848)), (13863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619560719868349/590295810358705651712), (-6287388665551/590295810358705651712)), (19073/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455278641677075/18446744073709551616), (-7852962414475/73786976294838206464)), (11929/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820000715343855/9223372036854775808), (-8825963142371/9223372036854775808)), (26863/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99452988955135/72057594037927936), (-1101899779301/144115188075855872)), (6723/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192183417409753/144115188075855872), (-481325067039/9007199254740992)), (23563/144115188075855872), by norm_num⟩
  | 4 => ⟨((46501196378893/1125899906842624), (-11527639675639/36028797018963968)), (17705/18014398509481984), by norm_num⟩
  | 3 => ⟨((742376709533551/4503599627370496), (-14367340039033/9007199254740992)), (22189/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218923697234807/4503599627370496), (-28608346504185/4503599627370496)), (22275/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101264161094985/1125899906842624), (-42597717658731/2251799813685248)), (134517/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153431677453535/2251799813685248), (-163950019545/4398046511104)), (272515/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153431677453535/2251799813685248), (-163950019545/4398046511104)), (1039562233931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056231478980733/2251799813685248), (-160550901276715/2251799813685248)), (541539/2251799813685248), by norm_num⟩
  | 2 => ⟨((1866201106204513/2251799813685248), (-36651772415287/281474976710656)), (266559/562949953421312), by norm_num⟩
  | 3 => ⟨((1508452036100083/2251799813685248), (-243004117186859/1125899906842624)), (255623/281474976710656), by norm_num⟩
  | 4 => ⟨((28299911599353/70368744177664), (-651141461374075/2251799813685248)), (3622561/2251799813685248), by norm_num⟩
  | 5 => ⟨((351826153746139/4503599627370496), (-130933456401009/562949953421312)), (10017553/4503599627370496), by norm_num⟩
  | 6 => ⟨((-216139736745625/4503599627370496), (-654634595239469/18014398509481984)), (24900083/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-6492197805/67108864)), (1/134217728), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-763070545/268435456), (-13134801021/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-467342380402443/9007199254740992), (477756572024207/18014398509481984)), (5946825/4503599627370496), by norm_num⟩
  | 1 => ⟨((5875718103/34359738368), (-46926967/536870912)), (301/68719476736), by norm_num⟩
  | 2 => ⟨((-9682704169/34359738368), (4949236091/34359738368)), (249/34359738368), by norm_num⟩
  | 3 => ⟨((21275075575/68719476736), (-5437291589/34359738368)), (549/68719476736), by norm_num⟩
  | 4 => ⟨((-8764897301/34359738368), (8960213035/68719476736)), (227/34359738368), by norm_num⟩
  | 5 => ⟨((11555068661/68719476736), (-2953140045/34359738368)), (301/68719476736), by norm_num⟩
  | 6 => ⟨((-12694540427/137438953472), (6488711887/137438953472)), (333/137438953472), by norm_num⟩
  | 7 => ⟨((5977019191/137438953472), (-6110210243/274877906944)), (315/274877906944), by norm_num⟩
  | 8 => ⟨((-19699280199/1099511627776), (10069128089/1099511627776)), (521/1099511627776), by norm_num⟩
  | 9 => ⟨((14427914203/2199023255552), (-7374711903/2199023255552)), (383/2199023255552), by norm_num⟩
  | 10 => ⟨((-4755205153/2199023255552), (4861169473/4398046511104)), (507/8796093022208), by norm_num⟩
  | 11 => ⟨((1424761859/2199023255552), (-1456511051/4398046511104)), (305/17592186044416), by norm_num⟩
  | 12 => ⟨((-6261043547/35184372088832), (6400563757/70368744177664)), (337/70368744177664), by norm_num⟩
  | 13 => ⟨((12698694241/281474976710656), (-6490835075/281474976710656)), (343/281474976710656), by norm_num⟩
  | 14 => ⟨((-5978974947/562949953421312), (1528052395/281474976710656)), (325/1125899906842624), by norm_num⟩
  | 15 => ⟨((21019441121/9007199254740992), (-10743917689/9007199254740992)), (573/9007199254740992), by norm_num⟩
  | 16 => ⟨((-17319162237/36028797018963968), (8852550001/36028797018963968)), (237/18014398509481984), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (434595418741/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777576783752871/633825300114114700748351602688), (4109353248225/633825300114114700748351602688)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236050088575123/4951760157141521099596496896), (4621872711185/39614081257132168796771975168)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944045860837881/1237940039285380274899124224), (4909314153669/2475880078570760549798248448)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769757703081323/154742504910672534362390528), (1226927706821/38685626227668133590597632)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548209718201909/9671406556917033397649408), (2299637946277/4835703278458516698824704)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257612655995329/604462909807314587353088), (4022663989339/604462909807314587353088)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235735058624763/9444732965739290427392), (816704776003/9444732965739290427392)), (18483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296105307395225/4722366482869645213696), (4897437984609/4722366482869645213696)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202434426468801/73786976294838206464), (3364722371629/295147905179352825856)), (19083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227625951795533/9223372036854775808), (8405011322131/73786976294838206464)), (23871/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454969989725679/2305843009213693952), (295196932781/288230376151711744)), (26879/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795563262328955/576460752303423488), (1179330253827/144115188075855872)), (26911/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298019168350293/36028797018963968), (4121104142827/72057594037927936)), (11791/72057594037927936), by norm_num⟩
  | 4 => ⟨((371969239571161/9007199254740992), (12337139947309/36028797018963968)), (17721/18014398509481984), by norm_num⟩
  | 3 => ⟨((742274828566583/4503599627370496), (15375700691163/9007199254740992)), (22213/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218509909561347/4503599627370496), (30614538906495/4503599627370496)), (44611/2251799813685248), by norm_num⟩
  | 1 => ⟨((2201892155798517/2251799813685248), (2848796087775/140737488355328)), (16845/281474976710656), by norm_num⟩
  | 0 => ⟨((538024611828023/562949953421312), (22450924277657/562949953421312)), (273247/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538024611828023/562949953421312), (22450924277657/562949953421312)), (1042354592330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((513307510153591/562949953421312), (171655043170443/2251799813685248)), (544093/2251799813685248), by norm_num⟩
  | 2 => ⟨((929542697444367/1125899906842624), (313036078179349/2251799813685248)), (1075181/2251799813685248), by norm_num⟩
  | 3 => ⟨((1491343457281277/2251799813685248), (64610628071779/281474976710656)), (1037137/1125899906842624), by norm_num⟩
  | 4 => ⟨((217263449336543/562949953421312), (684655087792987/2251799813685248)), (3699811/2251799813685248), by norm_num⟩
  | 5 => ⟨((127232408360535/2251799813685248), (1056936056753827/4503599627370496)), (10211263/4503599627370496), by norm_num⟩
  | 6 => ⟨((-467342380402443/9007199254740992), (477756572024207/18014398509481984)), (5946825/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-13134801021/134217728)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile050Terms3
