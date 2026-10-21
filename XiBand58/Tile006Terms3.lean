/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile006Terms3
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
  | 0 => ⟨((15/16), (559/32)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (559/32))
  have he : value ((15/16), (559/32))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-1811826849/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-825643757513895/18014398509481984), (276151845431509/9007199254740992)), (91074039/9007199254740992), by norm_num⟩
  | 1 => ⟨((1216936067/8589934592), (-407026805/4294967296)), (271/8589934592), by norm_num⟩
  | 2 => ⟨((-470200131/2147483648), (629068567/4294967296)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((242234761/1073741824), (-40509951/268435456)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-374378965/2147483648), (500871913/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((231444255/2147483648), (-619286539/8589934592)), (215/8589934592), by norm_num⟩
  | 6 => ⟨((-119234003/2147483648), (79760041/2147483648)), (7/536870912), by norm_num⟩
  | 7 => ⟨((842416835/34359738368), (-35220239/2147483648)), (25/4294967296), by norm_num⟩
  | 8 => ⟨((-325493275/34359738368), (54433627/8589934592)), (39/17179869184), by norm_num⟩
  | 9 => ⟨((894323139/274877906944), (-299122937/137438953472)), (27/34359738368), by norm_num⟩
  | 10 => ⟨((-276439079/274877906944), (369840679/549755813888)), (269/1099511627776), by norm_num⟩
  | 11 => ⟨((1242887169/4398046511104), (-831413265/4398046511104)), (305/4398046511104), by norm_num⟩
  | 12 => ⟨((-320151417/4398046511104), (428322283/8796093022208)), (79/4398046511104), by norm_num⟩
  | 13 => ⟨((608985613/35184372088832), (-203686517/17592186044416)), (303/70368744177664), by norm_num⟩
  | 14 => ⟨((-537828681/140737488355328), (719547053/281474976710656)), (269/281474976710656), by norm_num⟩
  | 15 => ⟨((443320343/562949953421312), (-593106797/1125899906842624)), (7/35184372088832), by norm_num⟩
  | 16 => ⟨((-85645125/562949953421312), (114582393/1125899906842624)), (175/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (3324290854299/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777492588838297/633825300114114700748351602688), (1964390171397/316912650057057350374175801344)), (23147/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888306056271223/39614081257132168796771975168), (4418761165745/39614081257132168796771975168)), (52093/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((471997810087713/618970019642690137449562112), (2346772322143/1237940039285380274899124224)), (110727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769657319309419/154742504910672534362390528), (1172995609697/38685626227668133590597632)), (110759/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548115712002825/9671406556917033397649408), (549634280153/1208925819614629174706176)), (1623/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((78595656505463/37778931862957161709568), (3845781282109/604462909807314587353088)), (45461/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885747166090365/75557863725914323419136), (6246285869519/75557863725914323419136)), (36953/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296005499763905/4722366482869645213696), (585249448293/590295810358705651712)), (27729/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809669225746773/295147905179352825856), (6433328309117/590295810358705651712)), (76301/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820836826404797/73786976294838206464), (1004380155727/9223372036854775808)), (95445/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819688388645435/9223372036854775808), (2257581764129/2305843009213693952)), (107471/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590935660947833/1152921504606846976), (4509484790667/576460752303423488)), (53795/288230376151711744), by norm_num⟩
  | 5 => ⟨((1191910460873107/144115188075855872), (7878835595033/144115188075855872)), (188551/144115188075855872), by norm_num⟩
  | 4 => ⟨((743814610907647/18014398509481984), (11792763724009/36028797018963968)), (283363/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484242746368051/9007199254740992), (14696428478313/9007199254740992)), (355145/9007199254740992), by norm_num⟩
  | 2 => ⟨((2217904330586589/4503599627370496), (29259601141597/4503599627370496)), (22285/140737488355328), by norm_num⟩
  | 1 => ⟨((2201004264829825/2251799813685248), (43557390511885/2251799813685248)), (1076781/2251799813685248), by norm_num⟩
  | 0 => ⟨((2150403804278323/2251799813685248), (42896748434091/1125899906842624)), (272763/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2150403804278323/2251799813685248), (42896748434091/1125899906842624)), (1040508271337413699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1025152406819399/1125899906842624), (163860624666937/2251799813685248)), (2166985/1125899906842624), by norm_num⟩
  | 2 => ⟨((57966125295769/70368744177664), (149198088337457/1125899906842624)), (4261537/1125899906842624), by norm_num⟩
  | 3 => ⟨((1488441869274615/2251799813685248), (491606617882681/2251799813685248)), (16300597/2251799813685248), by norm_num⟩
  | 4 => ⟨((438267673588935/1125899906842624), (649904906130655/2251799813685248)), (28666823/2251799813685248), by norm_num⟩
  | 5 => ⟨((307254513245011/4503599627370496), (1011927648391681/4503599627370496)), (38865083/2251799813685248), by norm_num⟩
  | 6 => ⟨((-825643757513895/18014398509481984), (276151845431509/9007199254740992)), (91074039/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-1811826849/33554432)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-918941213/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-193684520351791/18014398509481984), (233225551643831/4503599627370496)), (81944143/9007199254740992), by norm_num⟩
  | 1 => ⟨((289581629/8589934592), (-174350111/1073741824)), (247/8589934592), by norm_num⟩
  | 2 => ⟨((-226995381/4294967296), (1093347529/4294967296)), (195/4294967296), by norm_num⟩
  | 3 => ⟨((14827973/268435456), (-285682071/1073741824)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-92986047/2147483648), (895754481/4294967296)), (81/2147483648), by norm_num⟩
  | 5 => ⟨((116622885/4294967296), (-1123453197/8589934592)), (205/8589934592), by norm_num⟩
  | 6 => ⟨((-121890127/8589934592), (1174193667/17179869184)), (27/2147483648), by norm_num⟩
  | 7 => ⟨((218391879/34359738368), (-1051907843/34359738368)), (195/34359738368), by norm_num⟩
  | 8 => ⟨((-342383237/137438953472), (824562739/68719476736)), (77/34359738368), by norm_num⟩
  | 9 => ⟨((238564591/274877906944), (-574535933/137438953472)), (27/34359738368), by norm_num⟩
  | 10 => ⟨((-149603579/549755813888), (360290819/274877906944)), (273/1099511627776), by norm_num⟩
  | 11 => ⟨((85287483/1099511627776), (-1643185133/4398046511104)), (313/4398046511104), by norm_num⟩
  | 12 => ⟨((-356557879/17592186044416), (214674895/2199023255552)), (165/8796093022208), by norm_num⟩
  | 13 => ⟨((85998859/17592186044416), (-828445405/35184372088832)), (5/1099511627776), by norm_num⟩
  | 14 => ⟨((-38521275/35184372088832), (1484334729/281474976710656)), (289/281474976710656), by norm_num⟩
  | 15 => ⟨((257670901/1125899906842624), (-1241099455/1125899906842624)), (243/1125899906842624), by norm_num⟩
  | 16 => ⟨((-201981405/4503599627370496), (60804065/281474976710656)), (3/70368744177664), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (2312791146517/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888716355129571/316912650057057350374175801344), (1366580574031/316912650057057350374175801344)), (46235/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236029867781763/4951760157141521099596496896), (3074026618111/39614081257132168796771975168)), (52023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1887920267462203/2475880078570760549798248448), (1632586959449/1237940039285380274899124224)), (110569/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884793361849545/77371252455336267181195264), (3264072658609/154742504910672534362390528)), (27/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((1548049929136133/9671406556917033397649408), (3058898490875/9671406556917033397649408)), (12963/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257473344214159/604462909807314587353088), (1337683536631/302231454903657293676544)), (90765/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942827515368299/37778931862957161709568), (2172640262509/37778931862957161709568)), (147537/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295937053196391/4722366482869645213696), (25445659379/36893488147419103232)), (110693/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809622700115745/295147905179352825856), (69926947371/9223372036854775808)), (76133/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910361051909501/36893488147419103232), (2794746140787/36893488147419103232)), (190429/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909780754859591/4611686018427387904), (6281772371861/9223372036854775808)), (214365/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795405752765667/576460752303423488), (6273773126301/1152921504606846976)), (214531/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191804879952177/144115188075855872), (171267638643/4503599627370496)), (93951/72057594037927936), by norm_num⟩
  | 4 => ⟨((371869234603615/9007199254740992), (128170355877/562949953421312)), (282227/36028797018963968), by norm_num⟩
  | 3 => ⟨((371015749087589/2251799813685248), (5111147287361/4503599627370496)), (353439/9007199254740992), by norm_num⟩
  | 2 => ⟨((2217576444916819/4503599627370496), (20350858529459/4503599627370496)), (708851/4503599627370496), by norm_num⟩
  | 1 => ⟨((2200590780746511/2251799813685248), (30292907715305/2251799813685248)), (267057/562949953421312), by norm_num⟩
  | 0 => ⟨((1074943043108497/1125899906842624), (14914488970129/562949953421312)), (539093/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1074943043108497/1125899906842624), (14914488970129/562949953421312)), (2056476595165061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2051004305063479/2251799813685248), (14239477295027/281474976710656)), (4231815/2251799813685248), by norm_num⟩
  | 2 => ⟨((931175546829143/1125899906842624), (103757817391973/1125899906842624)), (8137085/2251799813685248), by norm_num⟩
  | 3 => ⟨((760566911088929/1125899906842624), (171625811070031/1125899906842624)), (14959307/2251799813685248), by norm_num⟩
  | 4 => ⟨((975231641607459/2251799813685248), (115936516377127/562949953421312)), (24771221/2251799813685248), by norm_num⟩
  | 5 => ⟨((326856915541355/2251799813685248), (803374854205541/4503599627370496)), (31659329/2251799813685248), by norm_num⟩
  | 6 => ⟨((-193684520351791/18014398509481984), (233225551643831/4503599627370496)), (81944143/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-918941213/16777216)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-931414457/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((469729102042651/18014398509481984), (98230156126191/2251799813685248)), (15098803/2251799813685248), by norm_num⟩
  | 1 => ⟨((-711834131/8589934592), (-595437477/4294967296)), (185/8589934592), by norm_num⟩
  | 2 => ⟨((565561797/4294967296), (946166177/4294967296)), (149/4294967296), by norm_num⟩
  | 3 => ⟨((-149782153/1073741824), (-1002322347/4294967296)), (5/134217728), by norm_num⟩
  | 4 => ⟨((476015745/4294967296), (796358593/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((-605121465/8589934592), (-1012348191/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((160259049/4294967296), (1072432349/17179869184)), (89/8589934592), by norm_num⟩
  | 7 => ⟨((-582070725/34359738368), (-973785067/34359738368)), (163/34359738368), by norm_num⟩
  | 8 => ⟨((28903939/4294967296), (193421335/17179869184)), (131/68719476736), by norm_num⟩
  | 9 => ⟨((-653214393/274877906944), (-546403035/137438953472)), (187/274877906944), by norm_num⟩
  | 10 => ⟨((415190101/549755813888), (694599303/549755813888)), (121/549755813888), by norm_num⟩
  | 11 => ⟨((-239908453/1099511627776), (-802717809/2199023255552)), (71/1099511627776), by norm_num⟩
  | 12 => ⟨((127073663/2199023255552), (106295017/1099511627776)), (19/1099511627776), by norm_num⟩
  | 13 => ⟨((-497042389/35184372088832), (-831535473/35184372088832)), (75/17592186044416), by norm_num⟩
  | 14 => ⟨((225661067/70368744177664), (377523499/70368744177664)), (69/70368744177664), by norm_num⟩
  | 15 => ⟨((-382486943/562949953421312), (-639888001/562949953421312)), (59/281474976710656), by norm_num⟩
  | 16 => ⟨((607782047/4503599627370496), (127099907/562949953421312)), (189/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (1344347219055/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55542935846227/19807040628566084398385987584), (1588589310261/633825300114114700748351602688)), (92357/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472043248598477/9903520314283042199192993792), (1786706812929/39614081257132168796771975168)), (12989/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1887850414347331/2475880078570760549798248448), (118612459695/154742504910672534362390528)), (55209/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884758556913755/77371252455336267181195264), (948575504009/77371252455336267181195264)), (3451/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1547984928108065/9671406556917033397649408), (888945251137/4835703278458516698824704)), (12943/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628708363146981/302231454903657293676544), (194370745077/75557863725914323419136)), (90615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885563509802759/75557863725914323419136), (2525529976557/75557863725914323419136)), (73637/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40495901086245/147573952589676412928), (946509852949/2361183241434822606848)), (110479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809576142538911/295147905179352825856), (650267701597/147573952589676412928)), (75973/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910303367977551/36893488147419103232), (3248593930579/73786976294838206464)), (47497/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819433128943959/9223372036854775808), (1825449101787/4611686018427387904)), (106907/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590684880673567/1152921504606846976), (3646191475301/1152921504606846976)), (26739/144115188075855872), by norm_num⟩
  | 5 => ⟨((1191696052882873/144115188075855872), (796282585773/36028797018963968)), (187281/144115188075855872), by norm_num⟩
  | 4 => ⟨((185914702861313/4503599627370496), (2383570383661/18014398509481984)), (70285/9007199254740992), by norm_num⟩
  | 3 => ⟨((370967672197097/2251799813685248), (5940499276231/9007199254740992)), (351809/9007199254740992), by norm_num⟩
  | 2 => ⟨((8660985205373/17592186044416), (5912947292645/2251799813685248)), (352387/2251799813685248), by norm_num⟩
  | 1 => ⟨((2200094944061401/2251799813685248), (2200212046135/281474976710656)), (1060065/2251799813685248), by norm_num⟩
  | 0 => ⟨((1074546902590869/1125899906842624), (34658482187307/2251799813685248)), (532959/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1074546902590869/1125899906842624), (34658482187307/2251799813685248)), (2033077242137718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2050538837875757/2251799813685248), (66155373948489/2251799813685248)), (1033707/562949953421312), by norm_num⟩
  | 2 => ⟨((932661279792101/1125899906842624), (30121275166455/562949953421312)), (3886743/1125899906842624), by norm_num⟩
  | 3 => ⟨((769364925503903/1125899906842624), (99806197247133/1125899906842624)), (13710499/2251799813685248), by norm_num⟩
  | 4 => ⟨((516885300415997/1125899906842624), (8525112561427/70368744177664)), (5292109/562949953421312), by norm_num⟩
  | 5 => ⟨((220770035563667/1125899906842624), (250480830311141/2251799813685248)), (24565357/2251799813685248), by norm_num⟩
  | 6 => ⟨((469729102042651/18014398509481984), (98230156126191/2251799813685248)), (15098803/2251799813685248), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-931414457/16777216)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-1886756889/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((418358471713831/9007199254740992), (552573034083815/36028797018963968)), (18359619/4503599627370496), by norm_num⟩
  | 1 => ⟨((-160532471/1073741824), (-424066539/8589934592)), (115/8589934592), by norm_num⟩
  | 2 => ⟨((258367045/1073741824), (341254383/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-277217145/1073741824), (-91537957/1073741824)), (103/4294967296), by norm_num⟩
  | 4 => ⟨((446163783/2147483648), (294649317/4294967296)), (85/4294967296), by norm_num⟩
  | 5 => ⟨((-287229163/2147483648), (-379375825/8589934592)), (111/8589934592), by norm_num⟩
  | 6 => ⟨((308185003/4294967296), (407054557/17179869184)), (121/17179869184), by norm_num⟩
  | 7 => ⟨((-17714451/536870912), (-374359449/34359738368)), (113/34359738368), by norm_num⟩
  | 8 => ⟨((912329889/68719476736), (301254145/68719476736)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((-1305189611/274877906944), (-215488819/137438953472)), (135/274877906944), by norm_num⟩
  | 10 => ⟨((840248657/549755813888), (69363175/137438953472)), (11/68719476736), by norm_num⟩
  | 11 => ⟨((-983511305/2199023255552), (-324758469/2199023255552)), (105/2199023255552), by norm_num⟩
  | 12 => ⟨((1055266921/8796093022208), (348452395/8796093022208)), (57/4398046511104), by norm_num⟩
  | 13 => ⟨((-1045160979/35184372088832), (-172557691/17592186044416)), (115/35184372088832), by norm_num⟩
  | 14 => ⟨((961212403/140737488355328), (317395303/140737488355328)), (27/35184372088832), by norm_num⟩
  | 15 => ⟨((-412536449/281474976710656), (-136220809/281474976710656)), (47/281474976710656), by norm_num⟩
  | 16 => ⟨((1327903603/4503599627370496), (438477869/4503599627370496)), (153/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (103860708597/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777316265586059/633825300114114700748351602688), (490889771669/633825300114114700748351602688)), (92249/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236013523198851/4951760157141521099596496896), (138027184897/9903520314283042199192993792)), (12973/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1887781666188865/2475880078570760549798248448), (146608777527/618970019642690137449562112)), (110273/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769448490607835/154742504910672534362390528), (293116127509/77371252455336267181195264)), (55139/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547920726477865/9671406556917033397649408), (274688652239/4835703278458516698824704)), (51695/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257360682382715/604462909807314587353088), (480489818203/604462909807314587353088)), (90471/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885472686651655/75557863725914323419136), (195098115025/18889465931478580854784)), (73511/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295800934314565/4722366482869645213696), (36558845237/295147905179352825856)), (110275/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809529636984251/295147905179352825856), (200930425877/147573952589676412928)), (151639/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820490999218345/73786976294838206464), (31368548943/2305843009213693952)), (94783/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909651824279823/4611686018427387904), (1128088494563/9223372036854775808)), (106643/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590556302518597/1152921504606846976), (70413518351/72057594037927936)), (213317/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191584559156027/144115188075855872), (984135616699/144115188075855872)), (186687/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487152399511669/36028797018963968), (11507051549/281474976710656)), (280101/36028797018963968), by norm_num⟩
  | 3 => ⟨((741833836871513/4503599627370496), (917683145785/4503599627370496)), (350249/9007199254740992), by norm_num⟩
  | 2 => ⟨((69275520671423/140737488355328), (3653504526373/4503599627370496)), (87609/562949953421312), by norm_num⟩
  | 1 => ⟨((137470474600487/140737488355328), (339836769693/140737488355328)), (526129/1125899906842624), by norm_num⟩
  | 0 => ⟨((268507711177847/281474976710656), (10704507356841/2251799813685248)), (1054197/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((268507711177847/281474976710656), (10704507356841/2251799813685248)), (4021442417625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1024525894141721/1125899906842624), (20422723208013/2251799813685248)), (1010643/562949953421312), by norm_num⟩
  | 2 => ⟨((1864373608137777/2251799813685248), (37167795517765/2251799813685248)), (3715251/1125899906842624), by norm_num⟩
  | 3 => ⟨((1542991292823103/2251799813685248), (61546018979881/2251799813685248)), (12549435/2251799813685248), by norm_num⟩
  | 4 => ⟨((1055615247336501/2251799813685248), (42172919109743/1125899906842624)), (17884395/2251799813685248), by norm_num⟩
  | 5 => ⟨((491699716491369/2251799813685248), (39540261231371/1125899906842624)), (18107751/2251799813685248), by norm_num⟩
  | 6 => ⟨((418358471713831/9007199254740992), (552573034083815/36028797018963968)), (18359619/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1886756889/33554432)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-954873133/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1586047332043847/36028797018963968), (-608256996766553/36028797018963968)), (73555973/18014398509481984), by norm_num⟩
  | 1 => ⟨((-308006723/2147483648), (472488407/8589934592)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((501757819/2147483648), (-384853211/4294967296)), (3/134217728), by norm_num⟩
  | 3 => ⟨((-1089850275/4294967296), (104490743/1073741824)), (107/4294967296), by norm_num⟩
  | 4 => ⟨((110963669/536870912), (-10638779/134217728)), (89/4294967296), by norm_num⟩
  | 5 => ⟨((-1156897107/8589934592), (110918941/2147483648)), (59/4294967296), by norm_num⟩
  | 6 => ⟨((1256427487/17179869184), (-481846157/17179869184)), (65/8589934592), by norm_num⟩
  | 7 => ⟨((-292397289/8589934592), (448543227/34359738368)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((952658595/68719476736), (-91337321/17179869184)), (51/34359738368), by norm_num⟩
  | 9 => ⟨((-172436315/34359738368), (529041439/274877906944)), (75/137438953472), by norm_num⟩
  | 10 => ⟨((449451329/274877906944), (-21545851/34359738368)), (25/137438953472), by norm_num⟩
  | 11 => ⟨((-532493025/1099511627776), (408427419/2199023255552)), (121/2199023255552), by norm_num⟩
  | 12 => ⟨((1156609121/8796093022208), (-55445665/1099511627776)), (133/8796093022208), by norm_num⟩
  | 13 => ⟨((-1159490515/35184372088832), (444670349/35184372088832)), (135/35184372088832), by norm_num⟩
  | 14 => ⟨((539676005/70368744177664), (-103484209/35184372088832)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((-937768813/562949953421312), (359638979/562949953421312)), (113/562949953421312), by norm_num⟩
  | 16 => ⟨((763835331/2251799813685248), (-73233657/562949953421312)), (93/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (-238512187949/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444314907893593/158456325028528675187087900672), (-70452579601/79228162514264337593543950336)), (2883/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888044486623069/39614081257132168796771975168), (-316954012675/19807040628566084398385987584)), (6487/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1887714003949613/2475880078570760549798248448), (-673317598597/2475880078570760549798248448)), (27571/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884690424256221/77371252455336267181195264), (-168270464111/38685626227668133590597632)), (6893/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1547857333408181/9671406556917033397649408), (-630763880623/9671406556917033397649408)), (12925/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314326308708093/151115727451828646838272), (-275834083315/302231454903657293676544)), (5655/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885382624461043/75557863725914323419136), (-223997967375/18889465931478580854784)), (147039/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647866711360555/2361183241434822606848), (-335791945631/2361183241434822606848)), (6893/295147905179352825856), by norm_num⟩
  | 9 => ⟨((809483251223339/295147905179352825856), (-922762103205/590295810358705651712)), (151659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113773445008213/4611686018427387904), (-36014216185/2305843009213693952)), (94797/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819173401792459/9223372036854775808), (-1295141406865/9223372036854775808)), (106661/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590426202104103/1152921504606846976), (-161678831233/144115188075855872)), (213357/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595735442864077/72057594037927936), (-1129830255179/144115188075855872)), (186727/144115188075855872), by norm_num⟩
  | 4 => ⟨((1486982217710245/36028797018963968), (-422727459569/9007199254740992)), (140085/18014398509481984), by norm_num⟩
  | 3 => ⟨((741727759949025/4503599627370496), (-2106942119659/9007199254740992)), (350353/9007199254740992), by norm_num⟩
  | 2 => ⟨((2216394069270017/4503599627370496), (-4193866625093/4503599627370496)), (701133/4503599627370496), by norm_num⟩
  | 1 => ⟨((2198897977402335/2251799813685248), (-6240992822645/2251799813685248)), (263195/562949953421312), by norm_num⟩
  | 0 => ⟨((1073409723207125/1125899906842624), (-3071043081235/562949953421312)), (2109965/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1073409723207125/1125899906842624), (-3071043081235/562949953421312)), (8048877724654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2046666318472691/2251799813685248), (-5855738123347/562949953421312)), (505777/281474976710656), by norm_num⟩
  | 2 => ⟨((1859976343817427/2251799813685248), (-42578356793579/2251799813685248)), (7439409/2251799813685248), by norm_num⟩
  | 3 => ⟨((767763426855073/1125899906842624), (-35169527909795/1125899906842624)), (6285587/1125899906842624), by norm_num⟩
  | 4 => ⟨((1044895341669245/2251799813685248), (-95929938726511/2251799813685248)), (17930209/2251799813685248), by norm_num⟩
  | 5 => ⟨((480772631438427/2251799813685248), (-178056229497421/4503599627370496)), (36335799/4503599627370496), by norm_num⟩
  | 6 => ⟨((1586047332043847/36028797018963968), (-608256996766553/36028797018963968)), (73555973/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-954873133/16777216)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-965933955/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((212613641858243/9007199254740992), (-700913377296575/18014398509481984)), (27000123/4503599627370496), by norm_num⟩
  | 1 => ⟨((-668277625/8589934592), (1101539683/8589934592)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((137658377/1073741824), (-453811887/2147483648)), (143/4294967296), by norm_num⟩
  | 3 => ⟨((-302466369/2147483648), (124640829/536870912)), (159/4294967296), by norm_num⟩
  | 4 => ⟨((498439905/4294967296), (-410795839/2147483648)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((-328555323/4294967296), (135391607/1073741824)), (89/4294967296), by norm_num⟩
  | 6 => ⟨((721909831/17179869184), (-594971533/8589934592)), (99/8589934592), by norm_num⟩
  | 7 => ⟨((-679799153/34359738368), (1120530921/34359738368)), (189/34359738368), by norm_num⟩
  | 8 => ⟨((560126777/68719476736), (-230817945/17179869184)), (79/34359738368), by norm_num⟩
  | 9 => ⟨((-12820045/4294967296), (84526477/17179869184)), (59/68719476736), by norm_num⟩
  | 10 => ⟨((540835545/549755813888), (-891473533/549755813888)), (157/549755813888), by norm_num⟩
  | 11 => ⟨((-648183901/2199023255552), (1068418667/2199023255552)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((712102799/8796093022208), (-1173777877/8796093022208)), (105/4398046511104), by norm_num⟩
  | 13 => ⟨((-2820883/137438953472), (1190332431/35184372088832)), (215/35184372088832), by norm_num⟩
  | 14 => ⟨((680021591/140737488355328), (-560448787/70368744177664)), (51/35184372088832), by norm_num⟩
  | 15 => ⟨((-597664061/562949953421312), (985145479/562949953421312)), (181/562949953421312), by norm_num⟩
  | 16 => ⟨((492450811/2251799813685248), (-811719697/2251799813685248)), (151/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (-667902725753/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777204010968153/633825300114114700748351602688), (-1578207578069/633825300114114700748351602688)), (23089/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1887981867117067/39614081257132168796771975168), (-1775014835457/39614081257132168796771975168)), (103911/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887647405734921/2475880078570760549798248448), (-942679609381/1237940039285380274899124224)), (110417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884657088655899/77371252455336267181195264), (-1884691316845/154742504910672534362390528)), (55215/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1547794751695057/9671406556917033397649408), (-110386799151/604462909807314587353088)), (51771/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257250398466743/604462909807314587353088), (-772353114103/302231454903657293676544)), (90613/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885293370507969/75557863725914323419136), (-627204773099/18889465931478580854784)), (147273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295666355708057/4722366482869645213696), (-1880452627797/4722366482869645213696)), (55239/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809437040021785/295147905179352825856), (-2583736058867/590295810358705651712)), (151943/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455064821225659/18446744073709551616), (-3226843142493/73786976294838206464)), (189985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((3552817706651/18014398509481984), (-906578901219/2305843009213693952)), (106905/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795147470519783/576460752303423488), (-3621468084553/1152921504606846976)), (106953/576460752303423488), by norm_num⟩
  | 5 => ⟨((74459715237609/9007199254740992), (-3163339548449/144115188075855872)), (187277/144115188075855872), by norm_num⟩
  | 4 => ⟨((1486807883358605/36028797018963968), (-1183535081133/9007199254740992)), (281133/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483235564296625/9007199254740992), (-2949350967123/4503599627370496)), (351797/9007199254740992), by norm_num⟩
  | 2 => ⟨((1107974047231871/2251799813685248), (-11740672087673/4503599627370496)), (88093/562949953421312), by norm_num⟩
  | 1 => ⟨((2198214028105189/2251799813685248), (-17469836796005/2251799813685248)), (132501/281474976710656), by norm_num⟩
  | 0 => ⟨((1072696311845529/1125899906842624), (-34378920194863/2251799813685248)), (1065839/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1072696311845529/1125899906842624), (-34378920194863/2251799813685248)), (4065853123191451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((255436094478103/281474976710656), (-65508737808993/2251799813685248)), (2063493/1125899906842624), by norm_num⟩
  | 2 => ⟨((115783907474275/140737488355328), (-59448610088421/1125899906842624)), (7730531/2251799813685248), by norm_num⟩
  | 3 => ⟨((94862374564385/140737488355328), (-195632093492349/2251799813685248)), (13536085/2251799813685248), by norm_num⟩
  | 4 => ⟨((503028470353813/1125899906842624), (-8241463036323/70368744177664)), (20599643/2251799813685248), by norm_num⟩
  | 5 => ⟨((418597926923519/2251799813685248), (-235655224096209/2251799813685248)), (46464331/4503599627370496), by norm_num⟩
  | 6 => ⟨((212613641858243/9007199254740992), (-700913377296575/18014398509481984)), (27000123/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-965933955/16777216)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile006Terms3
