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
namespace Reinmann.XiBand97.Tile045Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨45,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (7297/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (7297/256))
  have he : value ((69/80), (7297/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1050748371/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1326176414387049/9007199254740992), (272102580747613/9007199254740992)), (6279313/281474976710656), by norm_num⟩
  | 1 => ⟨((-694729665/2147483648), (-71271715/1073741824)), (213/4294967296), by norm_num⟩
  | 2 => ⟨((1526477095/4294967296), (39149991/536870912)), (59/1073741824), by norm_num⟩
  | 3 => ⟨((-559002165/2147483648), (-229390193/4294967296)), (175/4294967296), by norm_num⟩
  | 4 => ⟨((76765831/536870912), (252010885/8589934592)), (97/4294967296), by norm_num⟩
  | 5 => ⟨((-269874833/4294967296), (-55372451/4294967296)), (43/4294967296), by norm_num⟩
  | 6 => ⟨((1581268309/68719476736), (162220947/34359738368)), (255/68719476736), by norm_num⟩
  | 7 => ⟨((-992686169/137438953472), (-101838815/68719476736)), (81/68719476736), by norm_num⟩
  | 8 => ⟨((136322153/68719476736), (223762747/549755813888)), (45/137438953472), by norm_num⟩
  | 9 => ⟨((-1064996925/2199023255552), (-218514225/2199023255552)), (89/1099511627776), by norm_num⟩
  | 10 => ⟨((117001871/1099511627776), (96024965/4398046511104)), (159/8796093022208), by norm_num⟩
  | 11 => ⟨((-1495734613/70368744177664), (-306892237/70368744177664)), (257/70368744177664), by norm_num⟩
  | 12 => ⟨((1095488285/281474976710656), (224770389/281474976710656)), (191/281474976710656), by norm_num⟩
  | 13 => ⟨((-185156445/281474976710656), (-151960315/1125899906842624)), (261/2251799813685248), by norm_num⟩
  | 14 => ⟨((464948905/4503599627370496), (95397411/4503599627370496)), (83/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1089703639/72057594037927936), (-223583505/72057594037927936)), (49/18014398509481984), by norm_num⟩
  | 16 => ⟨((1197161809/576460752303423488), (122815793/288230376151711744)), (217/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (263609089893/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889522903468271/316912650057057350374175801344), (156030038511/316912650057057350374175801344)), (184461/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890053510794025/39614081257132168796771975168), (87752325663/9903520314283042199192993792)), (207523/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889848062288585/2475880078570760549798248448), (186437649119/1237940039285380274899124224)), (110249/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771514311056319/154742504910672534362390528), (372794228971/154742504910672534362390528)), (220503/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774928410873585/4835703278458516698824704), (349408478429/9671406556917033397649408)), (206727/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259054154599149/604462909807314587353088), (152823167687/302231454903657293676544)), (45223/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((29503491150839/1180591620717411303424), (496513948321/75557863725914323419136)), (36745/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324465748232639/1180591620717411303424), (186122171159/2361183241434822606848)), (220479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810946488964871/295147905179352825856), (127901690943/147573952589676412928)), (303173/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824030691003477/73786976294838206464), (319582419535/36893488147419103232)), (378989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823282452240863/9223372036854775808), (718588288669/9223372036854775808)), (53299/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199316365447109/144115188075855872), (358999284273/576460752303423488)), (426431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597528826551651/72057594037927936), (627585963487/144115188075855872)), (373171/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492352656384619/36028797018963968), (470027501691/18014398509481984)), (279921/18014398509481984), by norm_num⟩
  | 3 => ⟨((745075803119781/4503599627370496), (1172755510019/9007199254740992)), (699957/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229735494367195/4503599627370496), (1169292939849/2251799813685248)), (1400375/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218783729227679/2251799813685248), (3490616934661/2251799813685248)), (1050865/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093044147555625/1125899906842624), (6912491271071/2251799813685248)), (2104095/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093044147555625/1125899906842624), (6912491271071/2251799813685248)), (8026485447410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2122273135668191/2251799813685248), (13421544993395/2251799813685248)), (8196613/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000117016235985/2251799813685248), (25299037867871/2251799813685248)), (15547975/2251799813685248), by norm_num⟩
  | 3 => ⟨((222035059078679/281474976710656), (44942748308621/2251799813685248)), (27969733/2251799813685248), by norm_num⟩
  | 4 => ⟨((1400280987526473/2251799813685248), (17726026470411/562949953421312)), (45243035/2251799813685248), by norm_num⟩
  | 5 => ⟨((1737063339210855/4503599627370496), (44091695363071/1125899906842624)), (118235875/4503599627370496), by norm_num⟩
  | 6 => ⟨((1326176414387049/9007199254740992), (272102580747613/9007199254740992)), (6279313/281474976710656), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1050748371/16777216)), (1/8388608), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-1101133475/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1165115811190111/9007199254740992), (-413162100735333/9007199254740992)), (216922115/4503599627370496), by norm_num⟩
  | 1 => ⟨((319812095/1073741824), (453634689/4294967296)), (479/4294967296), by norm_num⟩
  | 2 => ⟨((-1472789125/4294967296), (-130566559/1073741824)), (277/2147483648), by norm_num⟩
  | 3 => ⟨((282601857/1073741824), (200427075/2147483648)), (427/4294967296), by norm_num⟩
  | 4 => ⟨((-1301429647/8589934592), (-461500395/8589934592)), (247/4294967296), by norm_num⟩
  | 5 => ⟨((599330501/8589934592), (106264393/4294967296)), (457/17179869184), by norm_num⟩
  | 6 => ⟨((-460003159/17179869184), (-326243743/34359738368)), (353/34359738368), by norm_num⟩
  | 7 => ⟨((1210510191/137438953472), (429259417/137438953472)), (467/137438953472), by norm_num⟩
  | 8 => ⟨((-1393651361/549755813888), (-494203167/549755813888)), (541/549755813888), by norm_num⟩
  | 9 => ⟨((178277825/274877906944), (505753265/2199023255552)), (139/549755813888), by norm_num⟩
  | 10 => ⟨((-1313599559/8796093022208), (-116453993/2199023255552)), (515/8796093022208), by norm_num⟩
  | 11 => ⟨((274970433/8796093022208), (390029423/35184372088832)), (433/35184372088832), by norm_num⟩
  | 12 => ⟨((-844190427/140737488355328), (-299358645/140737488355328)), (167/70368744177664), by norm_num⟩
  | 13 => ⟨((1196197103/1125899906842624), (53022981/140737488355328)), (119/281474976710656), by norm_num⟩
  | 14 => ⟨((-786955891/4503599627370496), (-279062687/4503599627370496)), (629/9007199254740992), by norm_num⟩
  | 15 => ⟨((966417549/36028797018963968), (85675411/9007199254740992)), (389/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1112629321/288230376151711744), (-49318731/36028797018963968)), (225/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (-3648376276815/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778895761070503/633825300114114700748351602688), (-4318295264421/633825300114114700748351602688)), (185249/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889884173303223/39614081257132168796771975168), (-2428605787305/19807040628566084398385987584)), (52115/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944833722330273/1237940039285380274899124224), (-5159738826255/2475880078570760549798248448)), (221553/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771332910394697/154742504910672534362390528), (-5158559304647/154742504910672534362390528)), (27703/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549685927174425/9671406556917033397649408), (-4834896238049/9671406556917033397649408)), (25981/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258903790981097/604462909807314587353088), (-2114640622975/302231454903657293676544)), (181943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943988768071381/37778931862957161709568), (-1717558258633/18889465931478580854784)), (147899/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648838604493985/2361183241434822606848), (-160956866381/147573952589676412928)), (221973/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621635316023341/590295810358705651712), (-3539381626293/295147905179352825856)), (152707/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113981581513585/4611686018427387904), (-2210861699791/18446744073709551616)), (382071/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822911848294349/9223372036854775808), (-155343661621/144115188075855872)), (215123/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594154649782939/1152921504606846976), (-9933392747031/1152921504606846976)), (26923/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194722048579191/144115188075855872), (-4341022675987/72057594037927936)), (377509/144115188075855872), by norm_num⟩
  | 4 => ⟨((745918276855255/18014398509481984), (-13003730188377/36028797018963968)), (567439/36028797018963968), by norm_num⟩
  | 3 => ⟨((186185542066627/1125899906842624), (-4055210327335/2251799813685248)), (711357/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114167418043595/2251799813685248), (-16170148942447/2251799813685248)), (714451/2251799813685248), by norm_num⟩
  | 1 => ⟨((138532406907447/140737488355328), (-12064316266681/562949953421312)), (269857/281474976710656), by norm_num⟩
  | 0 => ⟨((545226827137169/562949953421312), (-47751748405299/1125899906842624)), (547493/281474976710656), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545226827137169/562949953421312), (-47751748405299/1125899906842624)), (2088520051122569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((263524522790991/281474976710656), (-46248399373769/562949953421312)), (4427815/1125899906842624), by norm_num⟩
  | 2 => ⟨((489638164687709/562949953421312), (-21649504189049/140737488355328)), (9018405/1125899906842624), by norm_num⟩
  | 3 => ⟨((825104663038593/1125899906842624), (-301282156485877/1125899906842624)), (18462499/1125899906842624), by norm_num⟩
  | 4 => ⟨((1048098083258341/2251799813685248), (-441583324940389/1125899906842624)), (73881935/2251799813685248), by norm_num⟩
  | 5 => ⟨((282908150833247/4503599627370496), (-1644276311441455/4503599627370496)), (31682563/562949953421312), by norm_num⟩
  | 6 => ⟨((-1165115811190111/9007199254740992), (-413162100735333/9007199254740992)), (216922115/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-1101133475/16777216)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-573356173/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((820881126111007/9007199254740992), (394546580981215/4503599627370496)), (127974355/4503599627370496), by norm_num⟩
  | 1 => ⟨((-469300025/2147483648), (-902253515/4294967296)), (295/4294967296), by norm_num⟩
  | 2 => ⟨((140666539/536870912), (33804835/134217728)), (179/2147483648), by norm_num⟩
  | 3 => ⟨((-112434543/536870912), (-864644843/4294967296)), (9/134217728), by norm_num⟩
  | 4 => ⟨((1078425037/8589934592), (1036663891/8589934592)), (87/2147483648), by norm_num⟩
  | 5 => ⟨((-1034380119/17179869184), (-994324577/17179869184)), (337/17179869184), by norm_num⟩
  | 6 => ⟨((826778399/34359738368), (198690517/8589934592)), (17/2147483648), by norm_num⟩
  | 7 => ⟨((-17701143/2147483648), (-544501773/68719476736)), (47/17179869184), by norm_num⟩
  | 8 => ⟨((339563897/137438953472), (326414557/137438953472)), (227/274877906944), by norm_num⟩
  | 9 => ⟨((-723767701/1099511627776), (-86967547/137438953472)), (61/274877906944), by norm_num⟩
  | 10 => ⟨((173551915/1099511627776), (667325023/4398046511104)), (237/4398046511104), by norm_num⟩
  | 11 => ⟨((-302661321/8796093022208), (-581882007/17592186044416)), (209/17592186044416), by norm_num⟩
  | 12 => ⟨((241916717/35184372088832), (930194743/140737488355328)), (337/140737488355328), by norm_num⟩
  | 13 => ⟨((-713958095/562949953421312), (-686310639/562949953421312)), (125/281474976710656), by norm_num⟩
  | 14 => ⟨((244570963/1125899906842624), (940400593/4503599627370496)), (345/4503599627370496), by norm_num⟩
  | 15 => ⟨((-625552593/18014398509481984), (-300664285/9007199254740992)), (111/9007199254740992), by norm_num⟩
  | 16 => ⟨((750004803/144115188075855872), (180240367/36028797018963968)), (67/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (249338215933/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222347282403067/79228162514264337593543950336), (1180327795395/633825300114114700748351602688)), (184633/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889752532497793/39614081257132168796771975168), (663814310947/19807040628566084398385987584)), (103863/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944764143166387/1237940039285380274899124224), (1410307831037/2475880078570760549798248448)), (110363/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771194550292793/154742504910672534362390528), (176246646437/19342813113834066795298816)), (110373/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549557062188619/9671406556917033397649408), (330373594965/2417851639229258349412352)), (103485/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314697970290019/151115727451828646838272), (577976117371/302231454903657293676544)), (181119/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943898634839819/37778931862957161709568), (1877756361199/75557863725914323419136)), (147179/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297543396555803/4722366482869645213696), (703867379813/2361183241434822606848)), (220803/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621453576217989/590295810358705651712), (1934689194279/590295810358705651712)), (303659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455870375984971/18446744073709551616), (2416943183141/73786976294838206464)), (47457/9223372036854775808), by norm_num⟩
  | 7 => ⟨((113916544154371/576460752303423488), (2717112270287/9223372036854775808)), (427227/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593913290193889/1152921504606846976), (2714678302975/1152921504606846976)), (213685/576460752303423488), by norm_num⟩
  | 5 => ⟨((597258675366099/72057594037927936), (593152028201/36028797018963968)), (187055/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491542457509733/36028797018963968), (3553448384463/36028797018963968)), (561487/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489139305590191/9007199254740992), (138508269733/281474976710656)), (702425/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227712245869213/4503599627370496), (8835954709889/4503599627370496)), (1406549/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215752269706955/2251799813685248), (3295678925639/562949953421312)), (2114089/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180039215014633/2251799813685248), (26081882405209/2251799813685248)), (4245325/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180039215014633/2251799813685248), (26081882405209/2251799813685248)), (16194629677779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055131696328497/1125899906842624), (50501404342601/2251799813685248)), (8318415/2251799813685248), by norm_num⟩
  | 2 => ⟨((988245306598497/1125899906842624), (94654297610539/2251799813685248)), (15964243/2251799813685248), by norm_num⟩
  | 3 => ⟨((1730862434712181/2251799813685248), (166163377036441/2251799813685248)), (7341741/562949953421312), by norm_num⟩
  | 4 => ⟨((659089338668123/1125899906842624), (127722697901197/1125899906842624)), (24740161/1125899906842624), by norm_num⟩
  | 5 => ⟨((1485338674409403/4503599627370496), (74767453111065/562949953421312)), (8644577/281474976710656), by norm_num⟩
  | 6 => ⟨((820881126111007/9007199254740992), (394546580981215/4503599627370496)), (127974355/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-573356173/8388608)), (1/8388608), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1188322595/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-75641715580039/4503599627370496), (-261357936519961/2251799813685248)), (353723913/9007199254740992), by norm_num⟩
  | 1 => ⟨((89627553/2147483648), (1238727711/4294967296)), (421/4294967296), by norm_num⟩
  | 2 => ⟨((-111358051/2147483648), (-1539061363/4294967296)), (525/4294967296), by norm_num⟩
  | 3 => ⟨((184476241/4294967296), (637403969/2147483648)), (437/4294967296), by norm_num⟩
  | 4 => ⟨((-229203119/8589934592), (-1583889361/8589934592)), (545/8589934592), by norm_num⟩
  | 5 => ⟨((113909671/8589934592), (787163441/8589934592)), (17/536870912), by norm_num⟩
  | 6 => ⟨((-94351633/17179869184), (-652009223/17179869184)), (453/34359738368), by norm_num⟩
  | 7 => ⟨((66987143/34359738368), (1851636633/137438953472)), (323/68719476736), by norm_num⟩
  | 8 => ⟨((-166456797/274877906944), (-1150286045/274877906944)), (403/274877906944), by norm_num⟩
  | 9 => ⟨((183835379/1099511627776), (1270379307/1099511627776)), (7/17179869184), by norm_num⟩
  | 10 => ⟨((-91362751/2199023255552), (-1262709595/4398046511104)), (447/4398046511104), by norm_num⟩
  | 11 => ⟨((165111205/17592186044416), (1140987443/17592186044416)), (203/8796093022208), by norm_num⟩
  | 12 => ⟨((-136761977/70368744177664), (-236270607/17592186044416)), (169/35184372088832), by norm_num⟩
  | 13 => ⟨((209132767/562949953421312), (1445194837/562949953421312)), (519/562949953421312), by norm_num⟩
  | 14 => ⟨((-148478687/2251799813685248), (-1026049789/2251799813685248)), (371/2251799813685248), by norm_num⟩
  | 15 => ⟨((196776361/18014398509481984), (1359806903/18014398509481984)), (247/9007199254740992), by norm_num⟩
  | 16 => ⟨((-61121361/36028797018963968), (-1689496607/144115188075855872)), (77/18014398509481984), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-2233337802165/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55583111894867/19807040628566084398385987584), (-660684972021/158456325028528675187087900672)), (23115/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889618874833989/39614081257132168796771975168), (-1486260583325/19807040628566084398385987584)), (208069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889386084871829/2475880078570760549798248448), (-1578806371791/1237940039285380274899124224)), (221111/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771052135065563/154742504910672534362390528), (-3156835581093/154742504910672534362390528)), (221155/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549423320949117/9671406556917033397649408), (-739676958921/2417851639229258349412352)), (207379/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258674630794641/604462909807314587353088), (-647011018699/151115727451828646838272)), (709/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((943803156505271/37778931862957161709568), (-4204024729109/75557863725914323419136)), (295029/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324349951930121/1180591620717411303424), (-49244773845/73786976294838206464)), (55337/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810627769440293/295147905179352825856), (-2165671197941/295147905179352825856)), (304477/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56976032953373/2305843009213693952), (-2705441557033/36893488147419103232)), (190391/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227797995203801/1152921504606846976), (-6082715759831/9223372036854775808)), (214317/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593630999415057/1152921504606846976), (-1519265038807/288230376151711744)), (428953/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149283576421345/18014398509481984), (-5311070680811/144115188075855872)), (187847/72057594037927936), by norm_num⟩
  | 4 => ⟨((372791472304893/9007199254740992), (-3976953051849/18014398509481984)), (564261/36028797018963968), by norm_num⟩
  | 3 => ⟨((744331282686151/4503599627370496), (-9920189235351/9007199254740992)), (353293/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226740770943501/4503599627370496), (-4943481006145/1125899906842624)), (5535/17592186044416), by norm_num⟩
  | 1 => ⟨((1107125201390907/1125899906842624), (-29495189509669/2251799813685248)), (266867/281474976710656), by norm_num⟩
  | 0 => ⟨((544214711138863/562949953421312), (-58330226511971/2251799813685248)), (4307991/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544214711138863/562949953421312), (-58330226511971/2251799813685248)), (16433681496627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051450485299723/1125899906842624), (-112777937644199/2251799813685248)), (8552425/2251799813685248), by norm_num⟩
  | 2 => ⟨((1958199659725685/2251799813685248), (-52660283807835/562949953421312)), (8415237/1125899906842624), by norm_num⟩
  | 3 => ⟨((1683176362509471/2251799813685248), (-366353524702705/2251799813685248)), (32420839/2251799813685248), by norm_num⟩
  | 4 => ⟨((1198538052026751/2251799813685248), (-34230262685543/140737488355328)), (29508609/1125899906842624), by norm_num⟩
  | 5 => ⟨((504723141492139/2251799813685248), (-1166036792014173/4503599627370496)), (91533165/2251799813685248), by norm_num⟩
  | 6 => ⟨((-75641715580039/4503599627370496), (-261357936519961/2251799813685248)), (353723913/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1188322595/16777216)), (1/8388608), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1226600315/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-647349911327487/9007199254740992), (371769679021599/4503599627370496)), (179420015/4503599627370496), by norm_num⟩
  | 1 => ⟨((395874915/2147483648), (-909395599/4294967296)), (441/4294967296), by norm_num⟩
  | 2 => ⟨((-507699555/2147483648), (291569207/1073741824)), (285/2147483648), by norm_num⟩
  | 3 => ⟨((434074549/2147483648), (-124643375/536870912)), (245/2147483648), by norm_num⟩
  | 4 => ⟨((-278344809/2147483648), (639407889/4294967296)), (79/1073741824), by norm_num⟩
  | 5 => ⟨((571152271/8589934592), (-328009771/4294967296)), (163/4294967296), by norm_num⟩
  | 6 => ⟨((-976651101/34359738368), (1121771269/34359738368)), (35/2147483648), by norm_num⟩
  | 7 => ⟨((178932901/17179869184), (-12845029/1073741824)), (103/17179869184), by norm_num⟩
  | 8 => ⟨((-917907659/274877906944), (263574791/68719476736)), (531/274877906944), by norm_num⟩
  | 9 => ⟨((130799259/137438953472), (-600938659/549755813888)), (305/549755813888), by norm_num⟩
  | 10 => ⟨((-536789561/2199023255552), (616550891/2199023255552)), (315/2199023255552), by norm_num⟩
  | 11 => ⟨((250334189/4398046511104), (-575062477/8796093022208)), (295/8796093022208), by norm_num⟩
  | 12 => ⟨((-856126023/70368744177664), (983337421/70368744177664)), (507/70368744177664), by norm_num⟩
  | 13 => ⟨((675667659/281474976710656), (-776064827/281474976710656)), (201/140737488355328), by norm_num⟩
  | 14 => ⟨((-990316187/2251799813685248), (568733423/1125899906842624)), (37/140737488355328), by norm_num⟩
  | 15 => ⟨((338681449/4503599627370496), (-389005981/4503599627370496)), (407/9007199254740992), by norm_num⟩
  | 16 => ⟨((-868700765/72057594037927936), (997780641/72057594037927936)), (131/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (1489632574195/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((13894923893931/4951760157141521099596496896), (1762502221483/316912650057057350374175801344)), (92547/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118093484218341/2475880078570760549798248448), (3964852294443/39614081257132168796771975168)), (52069/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((29519610568071/38685626227668133590597632), (4211703515737/2475880078570760549798248448)), (6917/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770920917821883/154742504910672534362390528), (4210632664485/154742504910672534362390528)), (110701/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549300083178709/9671406556917033397649408), (493291324133/1208925819614629174706176)), (103813/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258566576331699/604462909807314587353088), (431487752441/75557863725914323419136)), (181735/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887430309762175/75557863725914323419136), (2803604517583/37778931862957161709568)), (295435/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81079215174125/295147905179352825856), (4203542094219/4722366482869645213696)), (110839/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101317059299639/36893488147419103232), (1444210347195/147573952589676412928)), (76243/147573952589676412928), by norm_num⟩
  | 8 => ⟨((56968872992923/2305843009213693952), (7216510205967/73786976294838206464)), (190731/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822124993657725/9223372036854775808), (8112332556909/9223372036854775808)), (107371/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593370522921979/1152921504606846976), (8104535544721/1152921504606846976)), (429911/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194039001783079/144115188075855872), (3541351760325/72057594037927936)), (376651/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490818100582223/36028797018963968), (2651635378781/9007199254740992)), (565937/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488221949460389/9007199254740992), (13227564699729/9007199254740992)), (709103/9007199254740992), by norm_num⟩
  | 2 => ⟨((69557562433723/140737488355328), (13181720212325/2251799813685248)), (711631/2251799813685248), by norm_num⟩
  | 1 => ⟨((553214683985333/562949953421312), (4914556866145/281474976710656)), (1073781/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086951774483655/1125899906842624), (38860594093263/1125899906842624)), (4345985/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086951774483655/1125899906842624), (38860594093263/1125899906842624)), (16578617104537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096019383443855/2251799813685248), (37516293811245/562949953421312)), (8691295/2251799813685248), by norm_num⟩
  | 2 => ⟨((1941015214757447/2251799813685248), (139683605168529/1125899906842624)), (17338473/2251799813685248), by norm_num⟩
  | 3 => ⟨((1638464486623365/2251799813685248), (240810041138217/1125899906842624)), (17096565/1125899906842624), by norm_num⟩
  | 4 => ⟨((544588367795475/1125899906842624), (350438523024437/1125899906842624)), (32193061/1125899906842624), by norm_num⟩
  | 5 => ⟨((308676341231601/2251799813685248), (678016729930189/2251799813685248)), (204733339/4503599627370496), by norm_num⟩
  | 6 => ⟨((-647349911327487/9007199254740992), (371769679021599/4503599627370496)), (179420015/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1226600315/16777216)), (1/8388608), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-631019973/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1821448028116261/18014398509481984), (321636379213913/18014398509481984)), (134769115/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1146055643/4294967296), (-101186853/2147483648)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((189031659/536870912), (133518953/2147483648)), (227/4294967296), by norm_num⟩
  | 3 => ⟨((-665153847/2147483648), (-29363681/536870912)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((1755379135/8589934592), (154984875/4294967296)), (269/8589934592), by norm_num⟩
  | 5 => ⟨((-463254617/4294967296), (-40901397/2147483648)), (9/536870912), by norm_num⟩
  | 6 => ⟨((815036995/17179869184), (287843017/34359738368)), (1/134217728), by norm_num⟩
  | 7 => ⟨((-1229102489/68719476736), (-108519175/34359738368)), (195/68719476736), by norm_num⟩
  | 8 => ⟨((810917983/137438953472), (71597081/68719476736)), (259/274877906944), by norm_num⟩
  | 9 => ⟨((-475568677/274877906944), (-83977245/274877906944)), (153/549755813888), by norm_num⟩
  | 10 => ⟨((502021201/1099511627776), (177296611/2199023255552)), (163/2199023255552), by norm_num⟩
  | 11 => ⟨((-963536531/8796093022208), (-170143971/8796093022208)), (79/4398046511104), by norm_num⟩
  | 12 => ⟨((1695218763/70368744177664), (149673231/35184372088832)), (281/70368744177664), by norm_num⟩
  | 13 => ⟨((-1376547539/281474976710656), (-15192163/17592186044416)), (231/281474976710656), by norm_num⟩
  | 14 => ⟨((16217803/17592186044416), (45820559/281474976710656)), (11/70368744177664), by norm_num⟩
  | 15 => ⟨((-22826513/140737488355328), (-128984621/4503599627370496)), (125/4503599627370496), by norm_num⟩
  | 16 => ⟨((963847623/36028797018963968), (170198905/36028797018963968)), (167/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (113835891573/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778458367011355/633825300114114700748351602688), (134674043567/316912650057057350374175801344)), (184453/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472348190465405/9903520314283042199192993792), (302956706471/39614081257132168796771975168)), (103757/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889146166846735/2475880078570760549798248448), (321816790797/2475880078570760549798248448)), (27561/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770812584636195/154742504910672534362390528), (160866388951/77371252455336267181195264)), (220491/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387299783189141/2417851639229258349412352), (301535246575/9671406556917033397649408)), (51679/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258478856196125/604462909807314587353088), (131877071461/302231454903657293676544)), (90441/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887288910106307/75557863725914323419136), (428433310399/75557863725914323419136)), (293941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324290598611475/1180591620717411303424), (321178781473/4722366482869645213696)), (13779/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620930132792513/590295810358705651712), (441383386119/590295810358705651712)), (151575/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822827850801855/73786976294838206464), (275686658843/36893488147419103232)), (378957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455482560271891/2305843009213693952), (309902996659/4611686018427387904)), (213177/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593179941423107/1152921504606846976), (19349854607/36028797018963968)), (426387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193876924842693/144115188075855872), (541109763373/144115188075855872)), (373127/144115188075855872), by norm_num⟩
  | 4 => ⟨((745292161247323/18014398509481984), (810294338721/36028797018963968)), (559767/36028797018963968), by norm_num⟩
  | 3 => ⟨((185993250979411/1125899906842624), (1010474436197/9007199254740992)), (699845/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225338720820019/4503599627370496), (1006893285293/2251799813685248)), (1400101/4503599627370496), by norm_num⟩
  | 1 => ⟨((553056127421587/562949953421312), (1501418750077/1125899906842624)), (1050597/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173112917075387/2251799813685248), (5934684689189/2251799813685248)), (4206651/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173112917075387/2251799813685248), (5934684689189/2251799813685248)), (16047100075728606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2097160014481475/2251799813685248), (11454606114155/2251799813685248)), (4070741/1125899906842624), by norm_num⟩
  | 2 => ⟨((1953081660105975/2251799813685248), (5333987013021/562949953421312)), (3811895/562949953421312), by norm_num⟩
  | 3 => ⟨((1693788553131195/2251799813685248), (37011148671605/2251799813685248)), (26738693/2251799813685248), by norm_num⟩
  | 4 => ⟨((1273447941582029/2251799813685248), (27839535103081/1125899906842624)), (5138037/281474976710656), by norm_num⟩
  | 5 => ⟨((1437578501626721/4503599627370496), (62975755582107/2251799813685248)), (24261851/1125899906842624), by norm_num⟩
  | 6 => ⟨((1821448028116261/18014398509481984), (321636379213913/18014398509481984)), (134769115/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-631019973/8388608)), (1/8388608), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1295033455/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-95501711801155/4503599627370496), (-850195820719009/9007199254740992)), (595980363/18014398509481984), by norm_num⟩
  | 1 => ⟨((246642523/4294967296), (1097856981/4294967296)), (387/4294967296), by norm_num⟩
  | 2 => ⟨((-333960167/4294967296), (-1486525909/4294967296)), (263/2147483648), by norm_num⟩
  | 3 => ⟨((301460299/4294967296), (670931131/2147483648)), (477/4294967296), by norm_num⟩
  | 4 => ⟨((-102046203/2147483648), (-113557199/536870912)), (81/1073741824), by norm_num⟩
  | 5 => ⟨((431791/16777216), (492029753/4294967296)), (353/8589934592), by norm_num⟩
  | 6 => ⟨((-199562531/17179869184), (-888294181/17179869184)), (5/268435456), by norm_num⟩
  | 7 => ⟨((308814487/68719476736), (1374597277/68719476736)), (497/68719476736), by norm_num⟩
  | 8 => ⟨((-209071283/137438953472), (-116327451/17179869184)), (169/68719476736), by norm_num⟩
  | 9 => ⟨((251633569/549755813888), (1120073163/549755813888)), (409/549755813888), by norm_num⟩
  | 10 => ⟨((-272574535/2199023255552), (-606642871/1099511627776)), (445/2199023255552), by norm_num⟩
  | 11 => ⟨((134208277/4398046511104), (298694427/2199023255552)), (55/1099511627776), by norm_num⟩
  | 12 => ⟨((-1892931/274877906944), (-269626501/8796093022208)), (399/35184372088832), by norm_num⟩
  | 13 => ⟨((50472883/35184372088832), (449330523/70368744177664)), (167/70368744177664), by norm_num⟩
  | 14 => ⟨((-78104629/281474976710656), (-695319779/562949953421312)), (519/1125899906842624), by norm_num⟩
  | 15 => ⟨((225612007/4503599627370496), (251061449/1125899906842624)), (377/4503599627370496), by norm_num⟩
  | 16 => ⟨((-9546385/1125899906842624), (-1359774015/36028797018963968)), (513/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-2334000500081/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444590655869417/158456325028528675187087900672), (-2760978114687/633825300114114700748351602688)), (184943/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118080302868199/2475880078570760549798248448), (-1552732097485/19807040628566084398385987584)), (208097/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472257808753849/618970019642690137449562112), (-1649384539697/1237940039285380274899124224)), (221143/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770697348113831/154742504910672534362390528), (-412235549331/19342813113834066795298816)), (221189/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549090775025705/9671406556917033397649408), (-3090826913071/9671406556917033397649408)), (207413/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258383719964089/604462909807314587353088), (-2703534146385/604462909807314587353088)), (181535/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887133708277411/75557863725914323419136), (-1097870563675/18889465931478580854784)), (73771/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20266335373195/73786976294838206464), (-823017923981/1180591620717411303424)), (221393/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620768494424959/590295810358705651712), (-2262048650765/295147905179352825856)), (9517/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1822624516475741/73786976294838206464), (-5651371826031/73786976294838206464)), (190437/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821699724303427/9223372036854775808), (-1588160192777/2305843009213693952)), (214375/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796473611089665/576460752303423488), (-6346205266689/1152921504606846976)), (107271/288230376151711744), by norm_num⟩
  | 5 => ⟨((149208853010781/18014398509481984), (-173303023739/4503599627370496)), (375825/144115188075855872), by norm_num⟩
  | 4 => ⟨((745135122183603/18014398509481984), (-8304097164301/36028797018963968)), (564489/36028797018963968), by norm_num⟩
  | 3 => ⟨((185943102938401/1125899906842624), (-2588719335091/2251799813685248)), (706931/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224510734035915/4503599627370496), (-20634181534287/4503599627370496)), (44307/140737488355328), by norm_num⟩
  | 1 => ⟨((2210918978986981/2251799813685248), (-30762895876079/2251799813685248)), (1068337/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170250608179519/2251799813685248), (-60775618656981/2251799813685248)), (4313257/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170250608179519/2251799813685248), (-60775618656981/2251799813685248)), (16453769692427825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090014395541765/2251799813685248), (-58574622198293/1125899906842624)), (8546933/2251799813685248), by norm_num⟩
  | 2 => ⟨((1933758143883465/2251799813685248), (-217464808130523/2251799813685248)), (16755025/2251799813685248), by norm_num⟩
  | 3 => ⟨((819817461974543/1125899906842624), (-373500647059947/2251799813685248)), (32013321/2251799813685248), by norm_num⟩
  | 4 => ⟨((282984741248807/562949953421312), (-543924643136747/2251799813685248)), (28620287/1125899906842624), by norm_num⟩
  | 5 => ⟨((875239261566767/4503599627370496), (-273421062496663/1125899906842624)), (21300161/562949953421312), by norm_num⟩
  | 6 => ⟨((-95501711801155/4503599627370496), (-850195820719009/9007199254740992)), (595980363/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1295033455/16777216)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile045Terms1
