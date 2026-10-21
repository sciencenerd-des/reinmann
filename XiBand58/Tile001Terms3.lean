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
namespace Reinmann.XiBand58.Tile001Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4659/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4659/320))
  have he : value ((15/16), (4659/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-1510071787/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((518738650312859/18014398509481984), (-423567348226401/9007199254740992)), (130193875/18014398509481984), by norm_num⟩
  | 1 => ⟨((-382290647/4294967296), (1248612075/8589934592)), (97/4294967296), by norm_num⟩
  | 2 => ⟨((295419155/2147483648), (-964878233/4294967296)), (19/536870912), by norm_num⟩
  | 3 => ⟨((-304384383/2147483648), (248539965/1073741824)), (159/4294967296), by norm_num⟩
  | 4 => ⟨((470432525/4294967296), (-768247583/4294967296)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((-290825381/4294967296), (474937179/4294967296)), (39/2147483648), by norm_num⟩
  | 6 => ⟨((599302399/17179869184), (-978700655/17179869184)), (163/17179869184), by norm_num⟩
  | 7 => ⟨((-264638451/17179869184), (216086091/8589934592)), (73/17179869184), by norm_num⟩
  | 8 => ⟨((409004343/68719476736), (-667931281/68719476736)), (115/68719476736), by norm_num⟩
  | 9 => ⟨((-561888795/274877906944), (458800877/137438953472)), (5/8589934592), by norm_num⟩
  | 10 => ⟨((43420553/68719476736), (-1134538391/1099511627776)), (25/137438953472), by norm_num⟩
  | 11 => ⟨((-390442975/2199023255552), (637619333/2199023255552)), (227/4398046511104), by norm_num⟩
  | 12 => ⟨((402291937/8796093022208), (-164242369/2199023255552)), (59/4398046511104), by norm_num⟩
  | 13 => ⟨((-765231665/70368744177664), (1249674179/70368744177664)), (113/35184372088832), by norm_num⟩
  | 14 => ⟨((675818161/281474976710656), (-1103655983/281474976710656)), (201/281474976710656), by norm_num⟩
  | 15 => ⟨((-278531017/562949953421312), (909719333/1125899906842624)), (21/140737488355328), by norm_num⟩
  | 16 => ⟨((430475599/4503599627370496), (-351497635/2251799813685248)), (131/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (-1330421203727/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777499546681997/633825300114114700748351602688), (-1572345171325/633825300114114700748351602688)), (23089/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888314259639903/39614081257132168796771975168), (-1768448332831/39614081257132168796771975168)), (51955/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888000465732893/2475880078570760549798248448), (-469605302573/618970019642690137449562112)), (6901/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442416779232085/38685626227668133590597632), (-234724626595/19342813113834066795298816)), (110429/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387031376182899/2417851639229258349412352), (-1759771771111/9671406556917033397649408)), (103541/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257539679577461/604462909807314587353088), (-769568844121/302231454903657293676544)), (90613/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885763212817503/75557863725914323419136), (-156241063741/4722366482869645213696)), (147271/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296018528004277/4722366482869645213696), (-58556466543/147573952589676412928)), (27619/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619357976847099/590295810358705651712), (-2574721305397/590295810358705651712)), (151941/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820863646152951/73786976294838206464), (-200984937603/4611686018427387904)), (94991/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819721871952091/9223372036854775808), (-3614098838141/9223372036854775808)), (106903/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198871659104849/144115188075855872), (-902391662643/288230376151711744)), (106951/576460752303423488), by norm_num⟩
  | 5 => ⟨((595974000913689/72057594037927936), (-3153279470137/144115188075855872)), (23409/18014398509481984), by norm_num⟩
  | 4 => ⟨((185961844893913/4503599627370496), (-4719754884081/36028797018963968)), (70281/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484340734387181/9007199254740992), (-5881947315681/9007199254740992)), (351785/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218148190755983/4503599627370496), (-11710820474319/4503599627370496)), (88089/562949953421312), by norm_num⟩
  | 1 => ⟨((2201488667782751/2251799813685248), (-17434120106431/2251799813685248)), (1059937/2251799813685248), by norm_num⟩
  | 0 => ⟨((1075920255863637/1125899906842624), (-17171616470637/1125899906842624)), (1065721/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1075920255863637/1125899906842624), (-17171616470637/1125899906842624)), (4065402988914107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2055794703475761/2251799813685248), (-16409353863871/562949953421312)), (4138667/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874937357607161/2251799813685248), (-29962044188641/562949953421312)), (7798119/2251799813685248), by norm_num⟩
  | 3 => ⟨((1554768096258887/2251799813685248), (-199580639870901/2251799813685248)), (13816127/2251799813685248), by norm_num⟩
  | 4 => ⟨((65988087253699/140737488355328), (-68900798733609/562949953421312)), (5381985/562949953421312), by norm_num⟩
  | 5 => ⟨((922618745623529/4503599627370496), (-129223051279807/1125899906842624)), (25457477/2251799813685248), by norm_num⟩
  | 6 => ⟨((518738650312859/18014398509481984), (-423567348226401/9007199254740992)), (130193875/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-1510071787/33554432)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-1531787875/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-185961092601415/36028797018963968), (-948248300007225/18014398509481984)), (319351545/36028797018963968), by norm_num⟩
  | 1 => ⟨((1086071/67108864), (708872571/4294967296)), (241/8589934592), by norm_num⟩
  | 2 => ⟨((-108971819/4294967296), (-1111332923/4294967296)), (95/2147483648), by norm_num⟩
  | 3 => ⟨((113893503/4294967296), (36297687/134217728)), (25/536870912), by norm_num⟩
  | 4 => ⟨((-89278105/4294967296), (-910489501/4294967296)), (315/8589934592), by norm_num⟩
  | 5 => ⟨((111972393/8589934592), (1141933825/8589934592)), (199/8589934592), by norm_num⟩
  | 6 => ⟨((-117029597/17179869184), (-149188621/2147483648)), (105/8589934592), by norm_num⟩
  | 7 => ⟨((104841607/34359738368), (1069211561/34359738368)), (95/17179869184), by norm_num⟩
  | 8 => ⟨((-82182563/68719476736), (-419063333/34359738368)), (75/34359738368), by norm_num⟩
  | 9 => ⟨((28631439/68719476736), (1167973917/274877906944)), (105/137438953472), by norm_num⟩
  | 10 => ⟨((-71818969/549755813888), (-183108773/137438953472)), (265/1099511627776), by norm_num⟩
  | 11 => ⟨((163773063/4398046511104), (417553817/1099511627776)), (19/274877906944), by norm_num⟩
  | 12 => ⟨((-171169831/17592186044416), (-218206263/2199023255552)), (5/274877906944), by norm_num⟩
  | 13 => ⟨((82569541/35184372088832), (1684146401/70368744177664)), (311/70368744177664), by norm_num⟩
  | 14 => ⟨((-147940753/281474976710656), (-1508751799/281474976710656)), (281/281474976710656), by norm_num⟩
  | 15 => ⟨((123697967/1125899906842624), (78844709/70368744177664)), (237/1125899906842624), by norm_num⟩
  | 16 => ⟨((-96963565/4503599627370496), (-247217129/1125899906842624)), (187/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-2173458249737/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777433178880593/633825300114114700748351602688), (-1284251639855/316912650057057350374175801344)), (46227/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236029936838295/4951760157141521099596496896), (-361104281353/4951760157141521099596496896)), (104027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((471980222184819/618970019642690137449562112), (-767116529135/618970019642690137449562112)), (110547/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769587383508945/154742504910672534362390528), (-3067431312863/154742504910672534362390528)), (110569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774025294306027/4835703278458516698824704), (-718654454589/2417851639229258349412352)), (405/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1257473962118217/604462909807314587353088), (-628548012577/151115727451828646838272)), (90743/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885656111359891/75557863725914323419136), (-2041751686421/37778931862957161709568)), (147499/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647968965269379/2361183241434822606848), (-3060827213799/4722366482869645213696)), (55331/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809623357541919/295147905179352825856), (-4205713881711/590295810358705651712)), (38055/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820723909855713/73786976294838206464), (-5252760501885/73786976294838206464)), (95183/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909781882220061/4611686018427387904), (-5903336131627/9223372036854775808)), (107143/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590814038212875/1152921504606846976), (-184244382797/36028797018963968)), (107221/576460752303423488), by norm_num⟩
  | 5 => ⟨((595903703895749/72057594037927936), (-2575199450611/72057594037927936)), (187813/144115188075855872), by norm_num⟩
  | 4 => ⟨((743740675628993/18014398509481984), (-481796222293/2251799813685248)), (141035/18014398509481984), by norm_num⟩
  | 3 => ⟨((742034796957135/4503599627370496), (-9606486341383/9007199254740992)), (353205/9007199254740992), by norm_num⟩
  | 2 => ⟨((1108796431546375/2251799813685248), (-4781229253489/1125899906842624)), (88533/562949953421312), by norm_num⟩
  | 1 => ⟨((2200623390778555/2251799813685248), (-28468139342597/2251799813685248)), (266763/562949953421312), by norm_num⟩
  | 0 => ⟨((2149982790867343/2251799813685248), (-56064733866613/2251799813685248)), (2152833/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2149982790867343/2251799813685248), (-56064733866613/2251799813685248)), (8212406167037200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2051373625030359/2251799813685248), (-3345607485155/70368744177664)), (527273/281474976710656), by norm_num⟩
  | 2 => ⟨((1863696763972377/2251799813685248), (-97530388455185/1125899906842624)), (8086571/2251799813685248), by norm_num⟩
  | 3 => ⟨((1525587177187863/2251799813685248), (-322883176822759/2251799813685248)), (3696663/562949953421312), by norm_num⟩
  | 4 => ⟨((123410320258803/281474976710656), (-27344040048365/140737488355328)), (1517269/140737488355328), by norm_num⟩
  | 5 => ⟨((1358837602629/8796093022208), (-767280821387035/4503599627370496)), (61441639/4503599627370496), by norm_num⟩
  | 6 => ⟨((-185961092601415/36028797018963968), (-948248300007225/18014398509481984)), (319351545/36028797018963968), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-1531787875/33554432)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-776289795/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-300941304760229/9007199254740992), (-86234529618677/2251799813685248)), (42166141/4503599627370496), by norm_num⟩
  | 1 => ⟨((912101427/8589934592), (130681027/1073741824)), (129/4294967296), by norm_num⟩
  | 2 => ⟨((-362338429/2147483648), (-830622677/4294967296)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((767687355/4294967296), (879921193/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-609937935/4294967296), (-699109229/4294967296)), (89/2147483648), by norm_num⟩
  | 5 => ⟨((193841559/2147483648), (888722705/8589934592)), (57/2147483648), by norm_num⟩
  | 6 => ⟨((-205346303/4294967296), (-235367383/4294967296)), (243/17179869184), by norm_num⟩
  | 7 => ⟨((745830405/34359738368), (854868815/34359738368)), (223/34359738368), by norm_num⟩
  | 8 => ⟨((-296286147/34359738368), (-339602389/34359738368)), (179/68719476736), by norm_num⟩
  | 9 => ⟨((418494811/137438953472), (959355265/274877906944)), (255/274877906944), by norm_num⟩
  | 10 => ⟨((-531999615/549755813888), (-609776535/549755813888)), (41/137438953472), by norm_num⟩
  | 11 => ⟨((307404257/1099511627776), (352345937/1099511627776)), (191/2199023255552), by norm_num⟩
  | 12 => ⟨((-81412273/1099511627776), (-186629059/2199023255552)), (51/2199023255552), by norm_num⟩
  | 13 => ⟨((159220053/8796093022208), (729990395/35184372088832)), (201/35184372088832), by norm_num⟩
  | 14 => ⟨((-144574257/35184372088832), (-331421253/70368744177664)), (23/17592186044416), by norm_num⟩
  | 15 => ⟨((122523939/140737488355328), (140436611/140737488355328)), (157/562949953421312), by norm_num⟩
  | 16 => ⟨((-778775347/4503599627370496), (-892630219/4503599627370496)), (251/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (-2980610347991/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444342160413869/158456325028528675187087900672), (-880532512315/158456325028528675187087900672)), (23137/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944083370256533/19807040628566084398385987584), (-1980686537823/19807040628566084398385987584)), (104139/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887843381388147/2475880078570760549798248448), (-1051919767405/618970019642690137449562112)), (110673/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221188705589573/19342813113834066795298816), (-262889991025/9671406556917033397649408)), (55351/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((773988731414361/4835703278458516698824704), (-3941821262819/9671406556917033397649408)), (51907/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628704865831725/302231454903657293676544), (-3447565633793/604462909807314587353088)), (90869/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885551277332199/75557863725914323419136), (-5599430550231/75557863725914323419136)), (147719/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295858903496825/4722366482869645213696), (-4197068599373/4722366482869645213696)), (13855/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619137401506673/590295810358705651712), (-2883451164007/295147905179352825856)), (19061/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455146573168929/18446744073709551616), (-7202531811551/73786976294838206464)), (95367/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819407607256977/9223372036854775808), (-8094473291873/9223372036854775808)), (107373/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795328106643547/576460752303423488), (-8084015249025/1152921504606846976)), (13435/72057594037927936), by norm_num⟩
  | 5 => ⟨((148958430131565/18014398509481984), (-7061762749629/144115188075855872)), (188331/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487267676960411/36028797018963968), (-2642294917009/9007199254740992)), (282977/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483796018869573/9007199254740992), (-13170494340513/9007199254740992)), (177283/4503599627370496), by norm_num⟩
  | 2 => ⟨((138564150414793/281474976710656), (-6554594430221/1125899906842624)), (88959/562949953421312), by norm_num⟩
  | 1 => ⟨((1099862964273631/1125899906842624), (-19511095696073/1125899906842624)), (1073881/2251799813685248), by norm_num⟩
  | 0 => ⟨((1073999834598259/1125899906842624), (-76829779315705/2251799813685248)), (2173385/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1073999834598259/1125899906842624), (-76829779315705/2251799813685248)), (8290805825240325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2046362974130145/2251799813685248), (-146576387076337/2251799813685248)), (4294709/2251799813685248), by norm_num⟩
  | 2 => ⟨((231265938879367/281474976710656), (-33300972134807/281474976710656)), (8364897/2251799813685248), by norm_num⟩
  | 3 => ⟨((1488586455611537/2251799813685248), (-437772802476489/2251799813685248)), (3931211/562949953421312), by norm_num⟩
  | 4 => ⟨((112368148632691/281474976710656), (-18087272357681/70368744177664)), (13452217/1125899906842624), by norm_num⟩
  | 5 => ⟨((105049623551901/1125899906842624), (-924243662961027/4503599627370496)), (17655967/1125899906842624), by norm_num⟩
  | 6 => ⟨((-300941304760229/9007199254740992), (-86234529618677/2251799813685248)), (42166141/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-776289795/16777216)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-1572522423/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1703494409587837/36028797018963968), (-225734760380037/18014398509481984)), (309400151/36028797018963968), by norm_num⟩
  | 1 => ⟨((653664705/4294967296), (346475679/8589934592)), (239/8589934592), by norm_num⟩
  | 2 => ⟨((-526016379/2147483648), (-278815547/4294967296)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((282196901/1073741824), (299157541/4294967296)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((-908356783/4294967296), (-15046109/268435456)), (171/4294967296), by norm_num⟩
  | 5 => ⟨((292388769/2147483648), (154980981/4294967296)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-1254884187/17179869184), (-332576355/17179869184)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((144261299/4294967296), (305863425/34359738368)), (223/34359738368), by norm_num⟩
  | 8 => ⟨((-58044901/4294967296), (-15383381/4294967296)), (181/68719476736), by norm_num⟩
  | 9 => ⟨((664317613/137438953472), (352122263/274877906944)), (261/274877906944), by norm_num⟩
  | 10 => ⟨((-427671181/274877906944), (-14167973/34359738368)), (169/549755813888), by norm_num⟩
  | 11 => ⟨((1001178491/2199023255552), (132668933/1099511627776)), (25/274877906944), by norm_num⟩
  | 12 => ⟨((-1074223081/8796093022208), (-284696547/8796093022208)), (217/8796093022208), by norm_num⟩
  | 13 => ⟨((531967801/17592186044416), (140985051/17592186044416)), (217/35184372088832), by norm_num⟩
  | 14 => ⟨((-978479025/140737488355328), (-259321927/140737488355328)), (201/140737488355328), by norm_num⟩
  | 15 => ⟨((1679787989/1125899906842624), (222593355/562949953421312)), (347/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1351757237/4503599627370496), (-358250185/4503599627370496)), (281/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (-58668876929/158456325028528675187087900672)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888652912664349/316912650057057350374175801344), (-2218352020797/316912650057057350374175801344)), (92637/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944047940043265/19807040628566084398385987584), (-4989976958103/39614081257132168796771975168)), (52123/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((943883913902555/1237940039285380274899124224), (-82815882621/38685626227668133590597632)), (55397/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27647403033117/2417851639229258349412352), (-2649189383091/77371252455336267181195264)), (110831/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547906037628265/9671406556917033397649408), (-4965278145657/9671406556917033397649408)), (103943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314336729924537/151115727451828646838272), (-4342667139317/604462909807314587353088)), (90989/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885448618168003/75557863725914323419136), (-7053177037471/75557863725914323419136)), (147929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295781393862423/4722366482869645213696), (-5286684354611/4722366482869645213696)), (27753/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619029989854005/590295810358705651712), (-7263996375551/590295810358705651712)), (152745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820450776689053/73786976294838206464), (-4536104248247/36893488147419103232)), (191087/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819253435023967/9223372036854775808), (-2548883876349/2305843009213693952)), (53797/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1590499901044009/1152921504606846976), (-1272771717355/144115188075855872)), (215457/1152921504606846976), by norm_num⟩
  | 5 => ⟨((148941033557687/18014398509481984), (-8894386599327/144115188075855872)), (47207/36028797018963968), by norm_num⟩
  | 4 => ⟨((1487054139608417/36028797018963968), (-1663948807183/4503599627370496)), (35481/4503599627370496), by norm_num⟩
  | 3 => ⟨((1483520780406641/9007199254740992), (-8293549838461/4503599627370496)), (177937/4503599627370496), by norm_num⟩
  | 2 => ⟨((2216451160991301/4503599627370496), (-33017406535679/4503599627370496)), (714947/4503599627370496), by norm_num⟩
  | 1 => ⟨((1099400885664647/1125899906842624), (-12283857595123/562949953421312)), (1080447/2251799813685248), by norm_num⟩
  | 0 => ⟨((2145909977701445/2251799813685248), (-24178988353745/562949953421312)), (2193163/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2145909977701445/2251799813685248), (-24178988353745/562949953421312)), (8366252907759856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1020422781106955/1125899906842624), (-92167930814619/1125899906842624)), (4368457/2251799813685248), by norm_num⟩
  | 2 => ⟨((1834564011338465/2251799813685248), (-167066816009379/1125899906842624)), (2158409/562949953421312), by norm_num⟩
  | 3 => ⟨((1445057330530123/2251799813685248), (-544444077625371/2251799813685248)), (4157507/562949953421312), by norm_num⟩
  | 4 => ⟨((795706316328861/2251799813685248), (-349388476122427/1125899906842624)), (7346449/562949953421312), by norm_num⟩
  | 5 => ⟨((257321831144421/9007199254740992), (-1975384245889207/9007199254740992)), (156023039/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1703494409587837/36028797018963968), (-225734760380037/18014398509481984)), (309400151/36028797018963968), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1572522423/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-1591682979/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-808347001226529/18014398509481984), (521366680975299/36028797018963968)), (75396077/9007199254740992), by norm_num⟩
  | 1 => ⟨((627916471/4294967296), (-202496407/4294967296)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((-7991455/33554432), (329876421/4294967296)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((1110909093/4294967296), (-44782051/536870912)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-226215567/1073741824), (291808491/4294967296)), (175/4294967296), by norm_num⟩
  | 5 => ⟨((1179251449/8589934592), (-190148047/4294967296)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-1280705021/17179869184), (103253449/4294967296)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((596094371/17179869184), (-192234117/17179869184)), (59/8589934592), by norm_num⟩
  | 8 => ⟨((-971066503/68719476736), (305819/67108864)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((1406145961/274877906944), (-226733585/137438953472)), (283/274877906944), by norm_num⟩
  | 10 => ⟨((-458135929/274877906944), (295487963/549755813888)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((1085564425/2199023255552), (-175041511/1099511627776)), (111/1099511627776), by norm_num⟩
  | 12 => ⟨((-589478949/4398046511104), (380201427/8796093022208)), (243/8796093022208), by norm_num⟩
  | 13 => ⟨((147736871/4398046511104), (-381148601/35184372088832)), (245/35184372088832), by norm_num⟩
  | 14 => ⟨((-1100207973/140737488355328), (354805411/140737488355328)), (115/70368744177664), by norm_num⟩
  | 15 => ⟨((477944505/281474976710656), (-308264075/562949953421312)), (201/562949953421312), by norm_num⟩
  | 16 => ⟨((-1557189337/4503599627370496), (251088529/2251799813685248)), (165/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (921478286221/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777249616835237/633825300114114700748351602688), (4355032612389/633825300114114700748351602688)), (46315/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888032683738535/39614081257132168796771975168), (2449053801265/19807040628566084398385987584)), (104237/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887700730848761/2475880078570760549798248448), (5202616037957/2475880078570760549798248448)), (110783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442341688109631/38685626227668133590597632), (5200790436959/154742504910672534362390528)), (110819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547843244749491/9671406556917033397649408), (304612624039/604462909807314587353088)), (103931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257292034589329/604462909807314587353088), (4262638418045/604462909807314587353088)), (45489/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471339884943805/18889465931478580854784), (6923154636431/75557863725914323419136)), (147911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295714681159623/4722366482869645213696), (2594594418805/2361183241434822606848)), (110997/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202367301986179/73786976294838206464), (7129974713071/590295810358705651712)), (76361/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820336542978193/73786976294838206464), (2226183395207/18446744073709551616)), (191055/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454781310769921/2305843009213693952), (10007198195507/9223372036854775808)), (53787/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1590372109697497/1152921504606846976), (9993926760907/1152921504606846976)), (215413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((148927112605395/18014398509481984), (8729772622797/144115188075855872)), (11799/9007199254740992), by norm_num⟩
  | 4 => ⟨((1486887985645737/36028797018963968), (6532437504801/18014398509481984)), (283771/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483314653672843/9007199254740992), (16279067838067/9007199254740992)), (355759/9007199254740992), by norm_num⟩
  | 2 => ⟨((2216043585330067/4503599627370496), (16201220729393/2251799813685248)), (357329/2251799813685248), by norm_num⟩
  | 1 => ⟨((2198202034725583/2251799813685248), (12053942019361/562949953421312)), (269967/562949953421312), by norm_num⟩
  | 0 => ⟨((2144756607128005/2251799813685248), (2965250004753/70368744177664)), (1095711/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2144756607128005/2251799813685248), (2965250004753/70368744177664)), (4179805759910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2038803424418475/2251799813685248), (90377334622081/1125899906842624)), (2179593/1125899906842624), by norm_num⟩
  | 2 => ⟨((915722420772743/1125899906842624), (327314387713275/2251799813685248)), (4296771/1125899906842624), by norm_num⟩
  | 3 => ⟨((360495577746917/562949953421312), (532425878444351/2251799813685248)), (16476943/2251799813685248), by norm_num⟩
  | 4 => ⟨((398755621669821/1125899906842624), (681897825874977/2251799813685248)), (28894409/2251799813685248), by norm_num⟩
  | 5 => ⟨((303827253702809/9007199254740992), (1932040955467157/9007199254740992)), (151866613/9007199254740992), by norm_num⟩
  | 6 => ⟨((-808347001226529/18014398509481984), (521366680975299/36028797018963968)), (75396077/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-1591682979/33554432)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-12579065/262144)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-533986350912715/18014398509481984), (622058182430781/18014398509481984)), (151248145/18014398509481984), by norm_num⟩
  | 1 => ⟨((419600463/4294967296), (-488806317/4294967296)), (15/536870912), by norm_num⟩
  | 2 => ⟨((-691467337/4294967296), (201378235/1073741824)), (25/536870912), by norm_num⟩
  | 3 => ⟨((379827257/2147483648), (-884946415/4294967296)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((-312962169/2147483648), (729159755/4294967296)), (185/4294967296), by norm_num⟩
  | 5 => ⟨((825177803/8589934592), (-961276641/8589934592)), (123/4294967296), by norm_num⟩
  | 6 => ⟨((-906550475/17179869184), (1056070331/17179869184)), (273/17179869184), by norm_num⟩
  | 7 => ⟨((853669279/34359738368), (-497233647/17179869184)), (259/34359738368), by norm_num⟩
  | 8 => ⟨((-351694335/34359738368), (204850123/17179869184)), (215/68719476736), by norm_num⟩
  | 9 => ⟨((64395953/17179869184), (-600135633/137438953472)), (159/137438953472), by norm_num⟩
  | 10 => ⟨((-679163379/549755813888), (395589829/274877906944)), (53/137438953472), by norm_num⟩
  | 11 => ⟨((203491973/549755813888), (-948217849/2199023255552)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-894235129/8796093022208), (1041723781/8796093022208)), (283/8796093022208), by norm_num⟩
  | 13 => ⟨((906847109/35184372088832), (-528207945/17592186044416)), (289/35184372088832), by norm_num⟩
  | 14 => ⟨((-426974305/70368744177664), (124349087/17592186044416)), (137/70368744177664), by norm_num⟩
  | 15 => ⟨((750526749/562949953421312), (-27322287/17592186044416)), (243/562949953421312), by norm_num⟩
  | 16 => ⟨((-77300429/281474976710656), (360199203/1125899906842624)), (101/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (742539963019/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111074920937741/39614081257132168796771975168), (438642541597/79228162514264337593543950336)), (46273/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((471993912417251/9903520314283042199192993792), (1973364497811/19807040628566084398385987584)), (104137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((943820206917025/1237940039285380274899124224), (4192077376085/2475880078570760549798248448)), (110671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884653375965327/77371252455336267181195264), (4190590579691/154742504910672534362390528)), (27675/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((773893665131857/4835703278458516698824704), (3927099559873/9671406556917033397649408)), (103813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257243445069165/604462909807314587353088), (107332302975/18889465931478580854784)), (90867/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885281210445515/75557863725914323419136), (697290210147/9444732965739290427392)), (36929/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1295656483511029/4722366482869645213696), (261322150585/295147905179352825856)), (55419/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1618859285480769/590295810358705651712), (718110802585/73786976294838206464)), (38121/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820238964673393/73786976294838206464), (7174811482775/73786976294838206464)), (190729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819017298923783/9223372036854775808), (1007876619871/1152921504606846976)), (214741/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795133224584935/576460752303423488), (4026106091633/576460752303423488)), (214953/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595663504591179/72057594037927936), (7033550825203/144115188075855872)), (47081/36028797018963968), by norm_num⟩
  | 4 => ⟨((1486758251341491/36028797018963968), (5263048310835/18014398509481984)), (141483/18014398509481984), by norm_num⟩
  | 3 => ⟨((1483161372789627/9007199254740992), (13115308961855/9007199254740992)), (177275/4503599627370496), by norm_num⟩
  | 2 => ⟨((1107881755374983/2251799813685248), (815751312047/140737488355328)), (355817/2251799813685248), by norm_num⟩
  | 1 => ⟨((1098923767410165/1125899906842624), (1213777467449/70368744177664)), (1073807/2251799813685248), by norm_num⟩
  | 0 => ⟨((2144306437672951/2251799813685248), (76428537184113/2251799813685248)), (2173179/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2144306437672951/2251799813685248), (76428537184113/2251799813685248)), (8290019997603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2039350367399687/2251799813685248), (145560189950995/2251799813685248)), (2143199/1125899906842624), by norm_num⟩
  | 2 => ⟨((918767762340049/1125899906842624), (263654189019151/2251799813685248)), (129971/35184372088832), by norm_num⟩
  | 3 => ⟨((183576669036901/281474976710656), (53787412141283/281474976710656)), (7761791/1125899906842624), by norm_num⟩
  | 4 => ⟨((875596348061767/2251799813685248), (561278395537767/2251799813685248)), (26181659/2251799813685248), by norm_num⟩
  | 5 => ⟨((50141616130445/562949953421312), (872996454466411/4503599627370496)), (4176633/281474976710656), by norm_num⟩
  | 6 => ⟨((-533986350912715/18014398509481984), (622058182430781/18014398509481984)), (151248145/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-12579065/262144)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile001Terms3
