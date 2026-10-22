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
namespace Reinmann.XiBand97.Tile026Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30041/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30041/1280))
  have he : value ((69/80), (30041/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1217108461/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-600338368092363/9007199254740992), (44572544151319/2251799813685248)), (110006131/4503599627370496), by norm_num⟩
  | 1 => ⟨((221213267/1073741824), (-32848269/536870912)), (163/2147483648), by norm_num⟩
  | 2 => ⟨((-1367559199/4294967296), (50767697/536870912)), (253/2147483648), by norm_num⟩
  | 3 => ⟨((1409061181/4294967296), (-418466951/4294967296)), (131/1073741824), by norm_num⟩
  | 4 => ⟨((-544433491/2147483648), (161687389/2147483648)), (407/4294967296), by norm_num⟩
  | 5 => ⟨((1346293627/8589934592), (-399826067/8589934592)), (505/8589934592), by norm_num⟩
  | 6 => ⟨((-346787563/4294967296), (205979891/8589934592)), (261/8589934592), by norm_num⟩
  | 7 => ⟨((612534331/17179869184), (-22739021/2147483648)), (463/34359738368), by norm_num⟩
  | 8 => ⟨((-946684811/68719476736), (281149117/68719476736)), (359/68719476736), by norm_num⟩
  | 9 => ⟨((650276209/137438953472), (-193120857/137438953472)), (495/274877906944), by norm_num⟩
  | 10 => ⟨((-1608025095/1099511627776), (238777907/549755813888)), (307/549755813888), by norm_num⟩
  | 11 => ⟨((903722515/2199023255552), (-134195027/1099511627776)), (347/2199023255552), by norm_num⟩
  | 12 => ⟨((-232787055/2199023255552), (276535017/8796093022208)), (359/8796093022208), by norm_num⟩
  | 13 => ⟨((885605747/35184372088832), (-263009685/35184372088832)), (343/35184372088832), by norm_num⟩
  | 14 => ⟨((-1564254263/281474976710656), (232278315/140737488355328)), (19/8796093022208), by norm_num⟩
  | 15 => ⟨((322345089/281474976710656), (-95730951/281474976710656)), (503/1125899906842624), by norm_num⟩
  | 16 => ⟨((-996382355/4503599627370496), (147954217/2251799813685248)), (391/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (1858114436919/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777847483060781/633825300114114700748351602688), (4393671092961/633825300114114700748351602688)), (185265/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944352548822881/19807040628566084398385987584), (2470858643067/19807040628566084398385987584)), (6515/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1888414948626907/2475880078570760549798248448), (328071519427/154742504910672534362390528)), (110787/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221260090050561/19342813113834066795298816), (5247535545409/154742504910672534362390528)), (221647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774256162154615/4835703278458516698824704), (4917855695653/9671406556917033397649408)), (207871/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257877213814507/604462909807314587353088), (1075353836053/151115727451828646838272)), (45491/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943154979225393/37778931862957161709568), (6986597742647/75557863725914323419136)), (295837/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296427059837067/4722366482869645213696), (5237147427969/4722366482869645213696)), (55501/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809958614618707/295147905179352825856), (7196528232947/590295810358705651712)), (152731/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821558998798089/73786976294838206464), (4494419739901/36893488147419103232)), (382135/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820499047409681/9223372036854775808), (10103071340447/9223372036854775808)), (53791/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591744091280683/1152921504606846976), (10091363311375/1152921504606846976)), (107715/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192615334609155/144115188075855872), (8816782799277/144115188075855872)), (377601/144115188075855872), by norm_num⟩
  | 4 => ⟨((744340768627003/18014398509481984), (13198882597789/36028797018963968)), (283801/18014398509481984), by norm_num⟩
  | 3 => ⟨((92846838913361/562949953421312), (16452657308695/9007199254740992)), (711605/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110245811396643/2251799813685248), (16383867187279/2251799813685248)), (357383/1125899906842624), by norm_num⟩
  | 1 => ⟨((551205095162463/562949953421312), (3050534561585/140737488355328)), (1080075/1125899906842624), by norm_num⟩
  | 0 => ⟨((67430584768199/70368744177664), (12031290994521/281474976710656)), (2191995/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((67430584768199/70368744177664), (12031290994521/281474976710656)), (8361797337058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063569247408893/2251799813685248), (184463030399665/2251799813685248)), (8776661/2251799813685248), by norm_num⟩
  | 2 => ⟨((937981121499893/1125899906842624), (169043551075543/1125899906842624)), (8761977/1125899906842624), by norm_num⟩
  | 3 => ⟨((756046658283409/1125899906842624), (281658535819251/1125899906842624)), (17230173/1125899906842624), by norm_num⟩
  | 4 => ⟨((437228048168295/1125899906842624), (378269850612765/1125899906842624)), (31760977/1125899906842624), by norm_num⟩
  | 5 => ⟨((170815490543153/4503599627370496), (1175167969793249/4503599627370496)), (92018875/2251799813685248), by norm_num⟩
  | 6 => ⟨((-600338368092363/9007199254740992), (44572544151319/2251799813685248)), (110006131/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1217108461/16777216)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1234611493/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-142588247915615/9007199254740992), (585587798694873/9007199254740992)), (104056125/9007199254740992), by norm_num⟩
  | 1 => ⟨((213186563/4294967296), (-437762059/2147483648)), (157/4294967296), by norm_num⟩
  | 2 => ⟨((-167111309/2147483648), (343150101/1073741824)), (31/536870912), by norm_num⟩
  | 3 => ⟨((349317695/4294967296), (-717296771/2147483648)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-273820903/4294967296), (562269969/2147483648)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((343425543/8589934592), (-352598847/2147483648)), (65/2147483648), by norm_num⟩
  | 6 => ⟨((-89734067/4294967296), (1474095527/17179869184)), (137/8589934592), by norm_num⟩
  | 7 => ⟨((160777513/17179869184), (-1320576571/34359738368)), (247/34359738368), by norm_num⟩
  | 8 => ⟨((-252058481/68719476736), (517582525/34359738368)), (195/68719476736), by norm_num⟩
  | 9 => ⟨((21953553/17179869184), (-1442557345/274877906944)), (137/137438953472), by norm_num⟩
  | 10 => ⟨((-220272763/549755813888), (452313021/274877906944)), (173/549755813888), by norm_num⟩
  | 11 => ⟨((31393817/274877906944), (-515718131/1099511627776)), (199/2199023255552), by norm_num⟩
  | 12 => ⟨((-65623421/2199023255552), (1078020811/8796093022208)), (105/4398046511104), by norm_num⟩
  | 13 => ⟨((126622681/17592186044416), (-520019695/17592186044416)), (51/8796093022208), by norm_num⟩
  | 14 => ⟨((-14179453/8796093022208), (931724997/140737488355328)), (185/140737488355328), by norm_num⟩
  | 15 => ⟨((189694263/562949953421312), (-1558089781/1125899906842624)), (39/140737488355328), by norm_num⟩
  | 16 => ⟨((-37174079/562949953421312), (610672687/2251799813685248)), (123/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (2357263631709/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777794626942635/633825300114114700748351602688), (2786799589323/633825300114114700748351602688)), (92475/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472161497181029/9903520314283042199192993792), (97950416073/1237940039285380274899124224)), (26013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888352618154699/2475880078570760549798248448), (832348800041/618970019642690137449562112)), (6911/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770018921230221/154742504910672534362390528), (832090450847/38685626227668133590597632)), (110599/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774227475819137/4835703278458516698824704), (194952599599/604462909807314587353088)), (103711/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628913788138567/302231454903657293676544), (682059808147/151115727451828646838272)), (22693/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886230353035339/75557863725914323419136), (4431332499251/75557863725914323419136)), (73775/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296368278338201/4722366482869645213696), (830425269185/1180591620717411303424)), (55351/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809918950916001/295147905179352825856), (4564418479013/590295810358705651712)), (152281/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821462081762089/73786976294838206464), (2850572688183/36893488147419103232)), (190449/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227549136636945/1152921504606846976), (800971762581/1152921504606846976)), (107195/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591641975112459/1152921504606846976), (1600065854133/288230376151711744)), (214559/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596265144572581/72057594037927936), (5591791102801/144115188075855872)), (187929/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488562552145499/36028797018963968), (8370833187887/36028797018963968)), (141137/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485415645886691/9007199254740992), (1304263098721/1125899906842624)), (176755/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110134335500651/2251799813685248), (5195031657295/1125899906842624)), (709027/4503599627370496), by norm_num⟩
  | 1 => ⟨((551149135502247/562949953421312), (30950775970937/2251799813685248)), (1068575/2251799813685248), by norm_num⟩
  | 0 => ⟨((269720990590507/281474976710656), (476786280671/17592186044416)), (269673/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269720990590507/281474976710656), (476786280671/17592186044416)), (1028720856786632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1033004331316373/1125899906842624), (116960352827433/2251799813685248)), (2125765/1125899906842624), by norm_num⟩
  | 2 => ⟨((236183965159899/281474976710656), (26827551527615/281474976710656)), (2060787/562949953421312), by norm_num⟩
  | 3 => ⟨((782494394651473/1125899906842624), (360173401948237/2251799813685248)), (1925609/281474976710656), by norm_num⟩
  | 4 => ⟨((1030049392968439/2251799813685248), (500637163950741/2251799813685248)), (26340599/2251799813685248), by norm_num⟩
  | 5 => ⟨((719747978573445/4503599627370496), (916033483422221/4503599627370496)), (35810645/2251799813685248), by norm_num⟩
  | 6 => ⟨((-142588247915615/9007199254740992), (585587798694873/9007199254740992)), (104056125/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1234611493/16777216)), (1/16777216), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-625684743/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((12507779206671/281474976710656), (210554600830869/4503599627370496)), (271139829/18014398509481984), by norm_num⟩
  | 1 => ⟨((-303271451/2147483648), (-319077423/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((240953249/1073741824), (507022613/2147483648)), (331/4294967296), by norm_num⟩
  | 3 => ⟨((-63813533/268435456), (-1074230105/4294967296)), (353/4294967296), by norm_num⟩
  | 4 => ⟨((202802843/1073741824), (853490275/4294967296)), (141/2147483648), by norm_num⟩
  | 5 => ⟨((-1031229363/8589934592), (-1084975215/8589934592)), (45/1073741824), by norm_num⟩
  | 6 => ⟨((546217071/8589934592), (143671235/2147483648)), (3/134217728), by norm_num⟩
  | 7 => ⟨((-991947003/34359738368), (-130455691/4294967296)), (351/34359738368), by norm_num⟩
  | 8 => ⟨((788115243/68719476736), (829190417/68719476736)), (281/68719476736), by norm_num⟩
  | 9 => ⟨((-278296963/68719476736), (-292801309/68719476736)), (25/17179869184), by norm_num⟩
  | 10 => ⟨((707554183/549755813888), (744430657/549755813888)), (1/2147483648), by norm_num⟩
  | 11 => ⟨((-817689193/2199023255552), (-860305709/2199023255552)), (149/1099511627776), by norm_num⟩
  | 12 => ⟨((433110045/4398046511104), (911365951/8796093022208)), (159/4398046511104), by norm_num⟩
  | 13 => ⟨((-847044331/35184372088832), (-891190785/35184372088832)), (313/35184372088832), by norm_num⟩
  | 14 => ⟨((12017645/2199023255552), (809214939/140737488355328)), (143/70368744177664), by norm_num⟩
  | 15 => ⟨((-162955617/140737488355328), (-685794303/562949953421312)), (61/140737488355328), by norm_num⟩
  | 16 => ⟨((1035763445/4503599627370496), (544872803/2251799813685248)), (195/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (1056144487619/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444435357385853/158456325028528675187087900672), (624258672871/316912650057057350374175801344)), (92323/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888586338337035/39614081257132168796771975168), (351062666341/9903520314283042199192993792)), (207743/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944144751162325/1237940039285380274899124224), (372899840751/618970019642690137449562112)), (220745/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769956100609507/154742504910672534362390528), (1491130514679/154742504910672534362390528)), (110383/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774198185358183/4835703278458516698824704), (1397436908733/9671406556917033397649408)), (103495/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628888315549541/302231454903657293676544), (1222259574357/604462909807314587353088)), (90569/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58942129801239/2361183241434822606848), (992619533047/37778931862957161709568)), (294391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307141398231/4722366482869645213696), (1488113634061/4722366482869645213696)), (220829/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404938667601813/147573952589676412928), (2044831697175/590295810358705651712)), (303699/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910679644163873/36893488147419103232), (1277027191327/36893488147419103232)), (379713/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113767447521759/576460752303423488), (358823006445/1152921504606846976)), (213649/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49735317967047/36028797018963968), (358397374761/144115188075855872)), (213725/576460752303423488), by norm_num⟩
  | 5 => ⟨((596217428314475/72057594037927936), (2504956236027/144115188075855872)), (374191/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488424172356883/36028797018963968), (1874898402361/18014398509481984)), (280815/18014398509481984), by norm_num⟩
  | 3 => ⟨((742625490176067/4503599627370496), (1168477499581/2251799813685248)), (702641/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219964121903975/4503599627370496), (2326982630875/1125899906842624)), (1407099/4503599627370496), by norm_num⟩
  | 1 => ⟨((551050291415071/562949953421312), (6931292917277/1125899906842624)), (1057609/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078609966002433/1125899906842624), (27330404754035/2251799813685248)), (4248857/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078609966002433/1125899906842624), (27330404754035/2251799813685248)), (16208103188521575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066280872632413/2251799813685248), (52364951384089/2251799813685248)), (8243933/2251799813685248), by norm_num⟩
  | 2 => ⟨((947414270696247/1125899906842624), (48050762231919/1125899906842624)), (7756451/1125899906842624), by norm_num⟩
  | 3 => ⟨((198793187371001/281474976710656), (80866829421837/1125899906842624)), (27431483/2251799813685248), by norm_num⟩
  | 4 => ⟨((277893378273757/562949953421312), (228450499738443/2251799813685248)), (10671937/562949953421312), by norm_num⟩
  | 5 => ⟨((262768927546659/1125899906842624), (112771802812695/1125899906842624)), (50806123/2251799813685248), by norm_num⟩
  | 6 => ⟨((12507779206671/281474976710656), (210554600830869/4503599627370496)), (271139829/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-625684743/8388608)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1267443285/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1109606398669113/18014398509481984), (-164618300141141/18014398509481984)), (80371191/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1703112227/8589934592), (252669271/8589934592)), (125/8589934592), by norm_num⟩
  | 2 => ⟨((685263347/2147483648), (-25415969/536870912)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-735259207/2147483648), (109081131/2147483648)), (7/268435456), by norm_num⟩
  | 4 => ⟨((1183354043/4294967296), (-43889827/1073741824)), (23/1073741824), by norm_num⟩
  | 5 => ⟨((-1523627889/8589934592), (226041445/8589934592)), (15/1073741824), by norm_num⟩
  | 6 => ⟨((408697415/4294967296), (-121266557/8589934592)), (131/17179869184), by norm_num⟩
  | 7 => ⟨((-1503481405/34359738368), (223052565/34359738368)), (61/17179869184), by norm_num⟩
  | 8 => ⟨((1209879987/68719476736), (-179494627/68719476736)), (25/17179869184), by norm_num⟩
  | 9 => ⟨((-432717049/68719476736), (128393537/137438953472)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((1114289959/549755813888), (-165313141/549755813888)), (95/549755813888), by norm_num⟩
  | 11 => ⟨((-1304276731/2199023255552), (193499081/2199023255552)), (113/2199023255552), by norm_num⟩
  | 12 => ⟨((699717473/4398046511104), (-207616505/8796093022208)), (123/8796093022208), by norm_num⟩
  | 13 => ⟨((-1386033021/35184372088832), (102814115/17592186044416)), (31/8796093022208), by norm_num⟩
  | 14 => ⟨((318676299/35184372088832), (-189111925/140737488355328)), (29/35184372088832), by norm_num⟩
  | 15 => ⟨((-1094164731/562949953421312), (81163707/281474976710656)), (101/562949953421312), by norm_num⟩
  | 16 => ⟨((1760990201/4503599627370496), (-130627947/2251799813685248)), (165/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-191852667957/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888844011108463/316912650057057350374175801344), (-14174046059/39614081257132168796771975168)), (92223/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888526313590291/39614081257132168796771975168), (-255072036687/39614081257132168796771975168)), (103753/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472056450872549/618970019642690137449562112), (-135468670923/1237940039285380274899124224)), (110239/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769892488822275/154742504910672534362390528), (-67712776235/38685626227668133590597632)), (110241/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774168413542521/4835703278458516698824704), (-126915661491/4835703278458516698824704)), (12919/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257724622763755/604462909807314587353088), (-222010863403/604462909807314587353088)), (22609/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886063813072385/75557863725914323419136), (-360596100439/75557863725914323419136)), (73481/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296244037164607/4722366482869645213696), (-270297059547/4722366482869645213696)), (110225/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619668147466267/590295810358705651712), (-371414854985/590295810358705651712)), (151565/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821251502186185/73786976294838206464), (-231951734857/36893488147419103232)), (23683/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455039601357427/2305843009213693952), (-130347471379/2305843009213693952)), (106579/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795705024669293/576460752303423488), (-520763727163/1152921504606846976)), (213173/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192330452911381/144115188075855872), (-227482423983/72057594037927936)), (186543/144115188075855872), by norm_num⟩
  | 4 => ⟨((372067243674973/9007199254740992), (-340521489237/18014398509481984)), (34981/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485059437137157/9007199254740992), (-848851898107/9007199254740992)), (174935/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219588357166907/4503599627370496), (-105648188815/281474976710656)), (349961/2251799813685248), by norm_num⟩
  | 1 => ⟨((550913920956273/562949953421312), (-629325949433/562949953421312)), (1050351/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156200800457977/2251799813685248), (-1240517482413/562949953421312)), (2102641/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156200800457977/2251799813685248), (-1240517482413/562949953421312)), (8020938881880950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064649460179539/2251799813685248), (-4751407780221/1125899906842624)), (252251/140737488355328), by norm_num⟩
  | 2 => ⟨((1893013341598897/2251799813685248), (-17426045510629/2251799813685248)), (1858805/562949953421312), by norm_num⟩
  | 3 => ⟨((1591258611281747/2251799813685248), (-14649497900501/1125899906842624)), (3154041/562949953421312), by norm_num⟩
  | 4 => ⟨((1124098830384387/2251799813685248), (-647014100217/35184372088832)), (18159005/2251799813685248), by norm_num⟩
  | 5 => ⟨((1120777678018591/4503599627370496), (-20671330767531/1125899906842624)), (9398909/1125899906842624), by norm_num⟩
  | 6 => ⟨((1109606398669113/18014398509481984), (-164618300141141/18014398509481984)), (80371191/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1267443285/16777216)), (1/16777216), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-641443287/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((16336907317279/562949953421312), (-950109814827511/18014398509481984)), (290402747/18014398509481984), by norm_num⟩
  | 1 => ⟨((-203045735/2147483648), (738036513/4294967296)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((330771303/2147483648), (-75143569/268435456)), (93/1073741824), by norm_num⟩
  | 3 => ⟨((-359228279/2147483648), (40804167/134217728)), (203/2147483648), by norm_num⟩
  | 4 => ⟨((292600103/2147483648), (-531775661/2147483648)), (83/1073741824), by norm_num⟩
  | 5 => ⟨((-381327753/4294967296), (43314411/268435456)), (109/2147483648), by norm_num⟩
  | 6 => ⟨((414134211/8589934592), (-752653507/8589934592)), (119/4294967296), by norm_num⟩
  | 7 => ⟨((-385511211/17179869184), (700633653/17179869184)), (223/17179869184), by norm_num⟩
  | 8 => ⟨((628016371/68719476736), (-142670755/8589934592)), (365/68719476736), by norm_num⟩
  | 9 => ⟨((-454697325/137438953472), (826373499/137438953472)), (133/68719476736), by norm_num⟩
  | 10 => ⟨((74072389/68719476736), (-1076961855/549755813888)), (349/549755813888), by norm_num⟩
  | 11 => ⟨((-351032719/1099511627776), (79746493/137438953472)), (415/2199023255552), by norm_num⟩
  | 12 => ⟨((381232829/4398046511104), (-692858061/4398046511104)), (227/4398046511104), by norm_num⟩
  | 13 => ⟨((-95545643/4398046511104), (694584139/17592186044416)), (115/8796093022208), by norm_num⟩
  | 14 => ⟨((711535837/140737488355328), (-1293155531/140737488355328)), (215/70368744177664), by norm_num⟩
  | 15 => ⟨((-618200653/562949953421312), (35110213/17592186044416)), (47/70368744177664), by norm_num⟩
  | 16 => ⟨((62942419/281474976710656), (-228784927/562949953421312)), (77/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-695447976147/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888817256603457/316912650057057350374175801344), (-1644055021117/633825300114114700748351602688)), (46181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944233026394173/19807040628566084398385987584), (-924557345153/19807040628566084398385987584)), (51959/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888161689916593/2475880078570760549798248448), (-982060709433/1237940039285380274899124224)), (110425/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884914139053883/77371252455336267181195264), (-122718027377/9671406556917033397649408)), (220877/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548276526425947/9671406556917033397649408), (-460024535871/2417851639229258349412352)), (207101/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78604484792699/37778931862957161709568), (-804706958921/302231454903657293676544)), (181243/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885977712793565/75557863725914323419136), (-2614038353065/75557863725914323419136)), (294573/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296179293403963/4722366482869645213696), (-1959427566189/4722366482869645213696)), (110489/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404894712834411/147573952589676412928), (-2692424686629/590295810358705651712)), (303921/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821139472605213/73786976294838206464), (-3362850685353/73786976294838206464)), (190009/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910015905220975/4611686018427387904), (-3779525277835/9223372036854775808)), (427679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795641377038307/576460752303423488), (-1887464167725/576460752303423488)), (53485/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192218284304109/144115188075855872), (-3297897925053/144115188075855872)), (93655/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488099157656129/36028797018963968), (-1234134026041/9007199254740992)), (562381/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484844442897539/9007199254740992), (-1538166645961/2251799813685248)), (703769/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219150256862831/4503599627370496), (-12251483473691/4503599627370496)), (704961/2251799813685248), by norm_num⟩
  | 1 => ⟨((550744613073123/562949953421312), (-18243162696369/2251799813685248)), (2120871/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077383598238943/1125899906842624), (-17976716498809/1125899906842624)), (33327/17592186044416), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077383598238943/1125899906842624), (-17976716498809/1125899906842624)), (127132415838593239/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1030670886786401/1125899906842624), (-68808317287535/2251799813685248)), (4150147/1125899906842624), by norm_num⟩
  | 2 => ⟨((942445082629711/1125899906842624), (-125976970005979/2251799813685248)), (7851885/1125899906842624), by norm_num⟩
  | 3 => ⟨((1570717217678121/2251799813685248), (-210900409859117/2251799813685248)), (876471/70368744177664), by norm_num⟩
  | 4 => ⟨((537941601271131/1125899906842624), (-294222339808215/2251799813685248)), (44381529/2251799813685248), by norm_num⟩
  | 5 => ⟨((14862526213499/70368744177664), (-562303755935183/4503599627370496)), (54007803/2251799813685248), by norm_num⟩
  | 6 => ⟨((16336907317279/562949953421312), (-950109814827511/18014398509481984)), (290402747/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-641443287/8388608)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-324436739/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-392014423359843/18014398509481984), (-486880797598533/9007199254740992)), (93290753/9007199254740992), by norm_num⟩
  | 1 => ⟨((308040521/4294967296), (1530341799/8589934592)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-507625653/4294967296), (-630469615/2147483648)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((139420945/1073741824), (1385283333/4294967296)), (273/4294967296), by norm_num⟩
  | 4 => ⟨((-229754345/2147483648), (-570708485/2147483648)), (227/4294967296), by norm_num⟩
  | 5 => ⟨((18930821/268435456), (376192413/2147483648)), (151/4294967296), by norm_num⟩
  | 6 => ⟨((-332762121/8589934592), (-51661201/536870912)), (21/1073741824), by norm_num⟩
  | 7 => ⟨((313351333/17179869184), (778362929/17179869184)), (5/536870912), by norm_num⟩
  | 8 => ⟨((-258188719/34359738368), (-641339309/34359738368)), (133/34359738368), by norm_num⟩
  | 9 => ⟨((189099533/68719476736), (117430541/17179869184)), (49/34359738368), by norm_num⟩
  | 10 => ⟨((-249296485/274877906944), (-309625525/137438953472)), (65/137438953472), by norm_num⟩
  | 11 => ⟨((597556761/2199023255552), (1484327593/2199023255552)), (157/1099511627776), by norm_num⟩
  | 12 => ⟨((-5128775/68719476736), (-815350267/4398046511104)), (87/2199023255552), by norm_num⟩
  | 13 => ⟨((332871005/17592186044416), (826849683/17592186044416)), (89/8796093022208), by norm_num⟩
  | 14 => ⟨((-156726933/35184372088832), (-778617619/70368744177664)), (169/70368744177664), by norm_num⟩
  | 15 => ⟨((550982831/562949953421312), (1368638215/562949953421312)), (299/562949953421312), by norm_num⟩
  | 16 => ⟨((-226993691/1125899906842624), (-1127702071/2251799813685248)), (31/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1272340671731/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888790495705775/316912650057057350374175801344), (-3007680849125/633825300114114700748351602688)), (92497/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888405670153537/39614081257132168796771975168), (-3382807509357/39614081257132168796771975168)), (52039/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944048650691261/1237940039285380274899124224), (-3593190479185/2475880078570760549798248448)), (110605/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884881814468555/77371252455336267181195264), (-449002270289/19342813113834066795298816)), (55315/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774107820576861/4835703278458516698824704), (-420783987201/1208925819614629174706176)), (51871/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257618205678627/604462909807314587353088), (-1472121647505/302231454903657293676544)), (90801/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885890174779049/75557863725914323419136), (-2391031396359/37778931862957161709568)), (9225/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324028296891533/1180591620717411303424), (-1792253597411/2361183241434822606848)), (13843/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619487221905359/590295810358705651712), (-4925384601915/590295810358705651712)), (152343/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821023836925201/73786976294838206464), (-1537941286167/18446744073709551616)), (190535/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909950106261391/4611686018427387904), (-6913913888979/9223372036854775808)), (214497/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795574638108605/576460752303423488), (-1726348806759/288230376151711744)), (214679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298024845702457/36028797018963968), (-1508162324289/36028797018963968)), (94025/72057594037927936), by norm_num⟩
  | 4 => ⟨((11624348477011/281474976710656), (-9029860782733/36028797018963968)), (141243/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484608938273017/9007199254740992), (-2813486277977/2251799813685248)), (88457/2251799813685248), by norm_num⟩
  | 2 => ⟨((2218657452484153/4503599627370496), (-22408015880681/4503599627370496)), (11091/70368744177664), by norm_num⟩
  | 1 => ⟨((2202185268411279/2251799813685248), (-8340818744467/562949953421312)), (1070175/2251799813685248), by norm_num⟩
  | 0 => ⟨((2152967964708299/2251799813685248), (-32868580809707/1125899906842624)), (2162217/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152967964708299/2251799813685248), (-32868580809707/1125899906842624)), (8248203286177825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028277392710035/1125899906842624), (-15712986806965/281474976710656)), (4260879/2251799813685248), by norm_num⟩
  | 2 => ⟨((1871221451722629/2251799813685248), (-114804586143813/1125899906842624)), (4129293/1125899906842624), by norm_num⟩
  | 3 => ⟨((1531552373540783/2251799813685248), (-381605510477175/2251799813685248)), (15409799/2251799813685248), by norm_num⟩
  | 4 => ⟨((977009543166867/2251799813685248), (-259547417037513/1125899906842624)), (26184725/2251799813685248), by norm_num⟩
  | 5 => ⟨((608480555431391/4503599627370496), (-900898212385787/4503599627370496)), (34794463/2251799813685248), by norm_num⟩
  | 6 => ⟨((-392014423359843/18014398509481984), (-486880797598533/9007199254740992)), (93290753/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-324436739/4194304)), (1/16777216), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile026Terms3
