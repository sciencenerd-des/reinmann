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
namespace Reinmann.XiBand97.Tile062Terms3
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
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2862621597/1073741824), (-104118785257/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-571519094600509/9007199254740992), (-1000178867363/35184372088832)), (1757573/4503599627370496), by norm_num⟩
  | 1 => ⟨((26956020879/137438953472), (12076544297/137438953472)), (333/274877906944), by norm_num⟩
  | 2 => ⟨((-83322204911/274877906944), (-4666138889/34359738368)), (517/274877906944), by norm_num⟩
  | 3 => ⟨((85850824229/274877906944), (38461955731/274877906944)), (535/274877906944), by norm_num⟩
  | 4 => ⟨((-66342135587/274877906944), (-29721884501/274877906944)), (415/274877906944), by norm_num⟩
  | 5 => ⟨((82026543019/549755813888), (36748642715/549755813888)), (129/137438953472), by norm_num⟩
  | 6 => ⟨((-42257921129/549755813888), (-37863871579/1099511627776)), (267/549755813888), by norm_num⟩
  | 7 => ⟨((74640587543/2199023255552), (4179958375/274877906944)), (237/1099511627776), by norm_num⟩
  | 8 => ⟨((-28839653105/2199023255552), (-25840857581/4398046511104)), (23/274877906944), by norm_num⟩
  | 9 => ⟨((79239637411/17592186044416), (35500083473/17592186044416)), (127/4398046511104), by norm_num⟩
  | 10 => ⟨((-48986616645/35184372088832), (-21946453023/35184372088832)), (79/8796093022208), by norm_num⟩
  | 11 => ⟨((860339271/2199023255552), (12334075999/70368744177664)), (357/140737488355328), by norm_num⟩
  | 12 => ⟨((-28366348917/281474976710656), (-25416768357/562949953421312)), (185/281474976710656), by norm_num⟩
  | 13 => ⟨((53957900769/2251799813685248), (6043408463/562949953421312)), (353/2251799813685248), by norm_num⟩
  | 14 => ⟨((-47653189135/9007199254740992), (-10674532641/4503599627370496)), (157/4503599627370496), by norm_num⟩
  | 15 => ⟨((39279474841/36028797018963968), (17597564567/36028797018963968)), (65/9007199254740992), by norm_num⟩
  | 16 => ⟨((-15176815535/72057594037927936), (-3399676197/36028797018963968)), (101/72057594037927936), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (-3543618929399/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777848422479447/633825300114114700748351602688), (-4189595577249/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888706205870275/39614081257132168796771975168), (-2356094415541/19807040628566084398385987584)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1844156440379/2417851639229258349412352), (-1251334261897/618970019642690137449562112)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442520511020581/38685626227668133590597632), (-2501901685593/77371252455336267181195264)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12097762870165/75557863725914323419136), (-586179570829/1208925819614629174706176)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628939226775211/302231454903657293676544), (-2050814196633/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886312126700449/75557863725914323419136), (-3331046776693/37778931862957161709568)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648214410166071/2361183241434822606848), (-4993900196691/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202489983483307/73786976294838206464), (-6862276029665/590295810358705651712)), (1193/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910781311739467/36893488147419103232), (-4285671676071/36893488147419103232)), (2985/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910251786555501/4611686018427387904), (-2408456755559/2305843009213693952)), (3361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795874587808429/576460752303423488), (-4811333781637/576460752303423488)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192620410103685/144115188075855872), (-8407291211407/144115188075855872)), (2949/72057594037927936), by norm_num⟩
  | 4 => ⟨((372172599873363/9007199254740992), (-1573234964767/4503599627370496)), (277/1125899906842624), by norm_num⟩
  | 3 => ⟨((1485562676269817/9007199254740992), (-15688564335431/9007199254740992)), (11111/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110262309104055/2251799813685248), (-15623015599755/2251799813685248)), (22315/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102442978147099/1125899906842624), (-23271103919249/1125899906842624)), (33707/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157973370763119/2251799813685248), (-45891244385529/1125899906842624)), (68363/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2157973370763119/2251799813685248), (-45891244385529/1125899906842624)), (260784157759856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064315404694085/2251799813685248), (-175916318552457/2251799813685248)), (136603/2251799813685248), by norm_num⟩
  | 2 => ⟨((939348940614927/1125899906842624), (-80634780258417/562949953421312)), (67951/562949953421312), by norm_num⟩
  | 3 => ⟨((190152018816357/281474976710656), (-134548719565795/562949953421312)), (265701/1125899906842624), by norm_num⟩
  | 4 => ⟨((224758528416213/562949953421312), (-727161212085769/2251799813685248)), (486001/1125899906842624), by norm_num⟩
  | 5 => ⟨((124122449727749/2251799813685248), (-1161280379944765/4503599627370496)), (1403913/2251799813685248), by norm_num⟩
  | 6 => ⟨((-571519094600509/9007199254740992), (-1000178867363/35184372088832)), (1757573/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-104118785257/1073741824)), (1/536870912), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1451894239/536870912), (-105616100027/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-678138495309383/18014398509481984), (124568386105795/2251799813685248)), (1714797/4503599627370496), by norm_num⟩
  | 1 => ⟨((32444752955/274877906944), (-23839322151/137438953472)), (165/137438953472), by norm_num⟩
  | 2 => ⟨((-25432583807/137438953472), (18687014179/68719476736)), (519/274877906944), by norm_num⟩
  | 3 => ⟨((53162479615/274877906944), (-39062016581/137438953472)), (545/274877906944), by norm_num⟩
  | 4 => ⟨((-20836330917/137438953472), (30619681763/137438953472)), (429/274877906944), by norm_num⟩
  | 5 => ⟨((52265756057/549755813888), (-76806268049/549755813888)), (135/137438953472), by norm_num⟩
  | 6 => ⟨((-54626325269/1099511627776), (78393753/1073741824)), (567/1099511627776), by norm_num⟩
  | 7 => ⟨((48937293405/2199023255552), (-17978745351/549755813888)), (255/1099511627776), by norm_num⟩
  | 8 => ⟨((-4795081263/549755813888), (28186126029/2199023255552)), (201/2199023255552), by norm_num⟩
  | 9 => ⟨((26728799227/8796093022208), (-78557720119/17592186044416)), (563/17592186044416), by norm_num⟩
  | 10 => ⟨((-16761599075/17592186044416), (24631727705/17592186044416)), (177/17592186044416), by norm_num⟩
  | 11 => ⟨((38222470509/140737488355328), (-1755287267/4398046511104)), (203/70368744177664), by norm_num⟩
  | 12 => ⟨((-1248399325/17592186044416), (58706059445/562949953421312)), (213/281474976710656), by norm_num⟩
  | 13 => ⟨((19270640555/1125899906842624), (-14159423833/562949953421312)), (413/2251799813685248), by norm_num⟩
  | 14 => ⟨((-8631854571/2251799813685248), (50739190319/9007199254740992)), (93/2251799813685248), by norm_num⟩
  | 15 => ⟨((14434736043/18014398509481984), (-42424650071/36028797018963968)), (313/36028797018963968), by norm_num⟩
  | 16 => ⟨((-45260031371/288230376151711744), (66511122455/288230376151711744)), (493/288230376151711744), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (2824461591441/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777792812013319/633825300114114700748351602688), (3339129445357/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888643847874973/39614081257132168796771975168), (938908660851/9903520314283042199192993792)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888350210535789/2475880078570760549798248448), (997315072977/618970019642690137449562112)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885008182097267/77371252455336267181195264), (3988021517931/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548452395793815/9671406556917033397649408), (934363601221/2417851639229258349412352)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257825181438089/604462909807314587353088), (3268957318671/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((235778270574505/9444732965739290427392), (5309590507549/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81022804850057/295147905179352825856), (1990018456101/2361183241434822606848)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619832804870277/590295810358705651712), (5469049226635/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821455080169035/73786976294838206464), (6831062602515/73786976294838206464)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910192175594699/4611686018427387904), (3838866803393/4611686018427387904)), (6709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795816077160367/576460752303423488), (7668727014559/1152921504606846976)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596260242823849/72057594037927936), (6700014967937/144115188075855872)), (1471/36028797018963968), by norm_num⟩
  | 4 => ⟨((744272717438727/18014398509481984), (10029808208471/36028797018963968)), (4419/18014398509481984), by norm_num⟩
  | 3 => ⟨((742695023770295/4503599627370496), (3125487123999/2251799813685248)), (11073/9007199254740992), by norm_num⟩
  | 2 => ⟨((555051236477729/1125899906842624), (24898214068839/4503599627370496)), (5555/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204469901469927/2251799813685248), (1158874870415/70368744177664)), (16759/1125899906842624), by norm_num⟩
  | 0 => ⟨((67418501017467/70368744177664), (36559986562539/1125899906842624)), (67791/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((67418501017467/70368744177664), (36559986562539/1125899906842624)), (258602150923918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032284003094963/1125899906842624), (140108766758267/2251799813685248)), (134301/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884186400529463/2251799813685248), (256918110995347/2251799813685248)), (131491/1125899906842624), by norm_num⟩
  | 3 => ⟨((773637038027965/1125899906842624), (53743855009353/281474976710656)), (250055/1125899906842624), by norm_num⟩
  | 4 => ⟨((981081589991855/2251799813685248), (590862282502375/2251799813685248)), (439129/1125899906842624), by norm_num⟩
  | 5 => ⟨((544811173363717/4503599627370496), (1029725829197841/4503599627370496)), (1226195/2251799813685248), by norm_num⟩
  | 6 => ⟨((-678138495309383/18014398509481984), (124568386105795/2251799813685248)), (1714797/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-105616100027/1073741824)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-107049679611/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((781440053397785/18014398509481984), (429965129418815/9007199254740992)), (268249/1125899906842624), by norm_num⟩
  | 1 => ⟨((-18947285117/137438953472), (-41700815627/274877906944)), (105/137438953472), by norm_num⟩
  | 2 => ⟨((60215492041/274877906944), (4141482401/17179869184)), (21/17179869184), by norm_num⟩
  | 3 => ⟨((-7973669797/34359738368), (-17549138677/68719476736)), (179/137438953472), by norm_num⟩
  | 4 => ⟨((791898495/4294967296), (435719589/2147483648)), (287/274877906944), by norm_num⟩
  | 5 => ⟨((-64427418759/549755813888), (-70898703809/549755813888)), (367/549755813888), by norm_num⟩
  | 6 => ⟨((34125634161/549755813888), (37553316201/549755813888)), (49/137438953472), by norm_num⟩
  | 7 => ⟨((-15493300337/549755813888), (-8524747171/274877906944)), (179/1099511627776), by norm_num⟩
  | 8 => ⟨((49238542481/4398046511104), (54184210799/4398046511104)), (143/2199023255552), by norm_num⟩
  | 9 => ⟨((-4346742737/1099511627776), (-4783342741/1099511627776)), (51/2199023255552), by norm_num⟩
  | 10 => ⟨((44205383695/35184372088832), (190021509/137438953472)), (131/17592186044416), by norm_num⟩
  | 11 => ⟨((-12771553543/35184372088832), (-7027183529/17592186044416)), (305/140737488355328), by norm_num⟩
  | 12 => ⟨((54118246209/562949953421312), (59554046749/562949953421312)), (325/562949953421312), by norm_num⟩
  | 13 => ⟨((-52920215279/2251799813685248), (-14558920491/562949953421312)), (5/35184372088832), by norm_num⟩
  | 14 => ⟨((48052369391/9007199254740992), (26439447447/4503599627370496)), (293/9007199254740992), by norm_num⟩
  | 15 => ⟨((-40723471093/36028797018963968), (-44813859857/36028797018963968)), (125/18014398509481984), by norm_num⟩
  | 16 => ⟨((32355345823/144115188075855872), (71210429485/288230376151711744)), (25/18014398509481984), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (1085312173571/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777741382676255/633825300114114700748351602688), (1282997819025/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944293141530425/19807040628566084398385987584), (360758002201/9903520314283042199192993792)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((3688065312819/4835703278458516698824704), (1532793020563/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769956034593789/154742504910672534362390528), (1532311218403/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548396304734771/9671406556917033397649408), (1436030060277/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628888284638599/302231454903657293676544), (157001853709/75557863725914323419136)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886148045522327/75557863725914323419136), (1020032791499/37778931862957161709568)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307053618787/4722366482869645213696), (764605491463/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809877269426143/295147905179352825856), (2101303949805/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910679553811787/36893488147419103232), (328073729559/9223372036854775808)), (2967/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820278934741437/9223372036854775808), (2949861068665/9223372036854775808)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397882480377747/288230376151711744), (2946361904707/1152921504606846976)), (835/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192434603657129/144115188075855872), (643533885617/36028797018963968)), (731/18014398509481984), by norm_num⟩
  | 4 => ⟨((186052966336195/4503599627370496), (3853354633867/36028797018963968)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485250319903015/9007199254740992), (4802988577331/9007199254740992)), (10981/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109981238955583/2251799813685248), (1195623079659/562949953421312)), (21991/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204197898904559/2251799813685248), (14245420141235/2251799813685248)), (33059/2251799813685248), by norm_num⟩
  | 0 => ⟨((269651279624769/281474976710656), (7021287544915/562949953421312)), (66413/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269651279624769/281474976710656), (7021287544915/562949953421312)), (253345498091887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066243723208409/2251799813685248), (53810798905823/2251799813685248)), (16113/281474976710656), by norm_num⟩
  | 2 => ⟨((1894692190526855/2251799813685248), (24688301509809/562949953421312)), (121363/1125899906842624), by norm_num⟩
  | 3 => ⟨((1589886578452681/2251799813685248), (41546083966899/562949953421312)), (107439/562949953421312), by norm_num⟩
  | 4 => ⟨((555138623704869/1125899906842624), (234669390715115/2251799813685248)), (670293/2251799813685248), by norm_num⟩
  | 5 => ⟨((1045959623959495/4503599627370496), (462826373092359/4503599627370496)), (1601401/4503599627370496), by norm_num⟩
  | 6 => ⟨((781440053397785/18014398509481984), (429965129418815/9007199254740992)), (268249/1125899906842624), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-107049679611/1073741824)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-13553091143/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1011326714289937/18014398509481984), (-121332145124329/4503599627370496)), (804201/4503599627370496), by norm_num⟩
  | 1 => ⟨((-49672471797/274877906944), (23837470015/274877906944)), (159/274877906944), by norm_num⟩
  | 2 => ⟨((79944759315/274877906944), (-38364927979/274877906944)), (129/137438953472), by norm_num⟩
  | 3 => ⟨((-85777417695/274877906944), (10290994933/68719476736)), (279/274877906944), by norm_num⟩
  | 4 => ⟨((69026714035/274877906944), (-8281358701/68719476736)), (113/137438953472), by norm_num⟩
  | 5 => ⟨((-88875368431/549755813888), (666416633/8589934592)), (293/549755813888), by norm_num⟩
  | 6 => ⟨((11919948953/137438953472), (-22881198819/549755813888)), (159/549755813888), by norm_num⟩
  | 7 => ⟨((-87700195471/2199023255552), (21043353635/1099511627776)), (147/1099511627776), by norm_num⟩
  | 8 => ⟨((2205437805/137438953472), (-33867971145/4398046511104)), (119/2199023255552), by norm_num⟩
  | 9 => ⟨((-12620498549/2199023255552), (6056488531/2199023255552)), (43/2199023255552), by norm_num⟩
  | 10 => ⟨((16249527071/8796093022208), (-15596067613/17592186044416)), (223/35184372088832), by norm_num⟩
  | 11 => ⟨((-76080305243/140737488355328), (18255201819/70368744177664)), (263/140737488355328), by norm_num⟩
  | 12 => ⟨((1275484663/8796093022208), (-9793537969/140737488355328)), (71/140737488355328), by norm_num⟩
  | 13 => ⟨((-80849265167/2251799813685248), (9699748495/562949953421312)), (71/562949953421312), by norm_num⟩
  | 14 => ⟨((2323604867/281474976710656), (-35682612501/9007199254740992)), (33/1125899906842624), by norm_num⟩
  | 15 => ⟨((-63824175215/36028797018963968), (30628772999/36028797018963968)), (229/36028797018963968), by norm_num⟩
  | 16 => ⟨((51360523661/144115188075855872), (-12323777119/72057594037927936)), (93/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-145707854291/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777687795151035/633825300114114700748351602688), (-344475974801/316912650057057350374175801344)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888526045796103/39614081257132168796771975168), (-774886162233/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944112751163397/1237940039285380274899124224), (-411541768471/1237940039285380274899124224)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769892168971605/154742504910672534362390528), (-822821542325/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548336507386681/9671406556917033397649408), (-771116943673/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314431080802083/151115727451828646838272), (-674449205185/604462909807314587353088)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886063289173871/75557863725914323419136), (-1095458762203/75557863725914323419136)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648121805900097/2361183241434822606848), (-821138304551/4722366482869645213696)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809833754974915/295147905179352825856), (-564162535541/295147905179352825856)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910625313231015/36893488147419103232), (-176162138545/9223372036854775808)), (5927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820157312064799/9223372036854775808), (-1583935542119/9223372036854775808)), (6669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795704410537629/576460752303423488), (-1582033139417/1152921504606846976)), (6671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596164613430119/72057594037927936), (-691070926943/72057594037927936)), (5839/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488266834079105/36028797018963968), (-1034473066315/18014398509481984)), (1095/4503599627370496), by norm_num⟩
  | 3 => ⟨((742528118060533/4503599627370496), (-2578733184471/9007199254740992)), (10955/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219580389227047/4503599627370496), (-5135186375011/4503599627370496)), (21925/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101819925665707/1125899906842624), (-7647318424965/2251799813685248)), (32927/2251799813685248), by norm_num⟩
  | 0 => ⟨((539038454245089/562949953421312), (-15074219578049/2251799813685248)), (66017/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((539038454245089/562949953421312), (-15074219578049/2251799813685248)), (251834877974700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032234753313837/1125899906842624), (-7216968374293/562949953421312)), (127311/2251799813685248), by norm_num⟩
  | 2 => ⟨((236544172564649/281474976710656), (-13233157804237/562949953421312)), (236705/2251799813685248), by norm_num⟩
  | 3 => ⟨((1589039767905163/2251799813685248), (-2780199504589/70368744177664)), (408971/2251799813685248), by norm_num⟩
  | 4 => ⟨((558915661858157/1125899906842624), (-125562780098737/2251799813685248)), (304759/1125899906842624), by norm_num⟩
  | 5 => ⟨((1095817531413739/4503599627370496), (-249325908696235/4503599627370496)), (673125/2251799813685248), by norm_num⟩
  | 6 => ⟨((1011326714289937/18014398509481984), (-121332145124329/4503599627370496)), (804201/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-13553091143/134217728)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-3017330773/1073741824), (-109745841057/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-115833132602675/18014398509481984), (-269558818870385/4503599627370496)), (710197/2251799813685248), by norm_num⟩
  | 1 => ⟨((719824845/34359738368), (53604043857/274877906944)), (567/549755813888), by norm_num⟩
  | 2 => ⟨((-4690517671/137438953472), (-87323574857/274877906944)), (463/274877906944), by norm_num⟩
  | 3 => ⟨((10188106257/274877906944), (47418106155/137438953472)), (505/274877906944), by norm_num⟩
  | 4 => ⟨((-8298458431/274877906944), (-77246383751/274877906944)), (413/274877906944), by norm_num⟩
  | 5 => ⟨((5407435737/274877906944), (100670470189/549755813888)), (135/137438953472), by norm_num⟩
  | 6 => ⟨((-2936324609/274877906944), (-54665685067/549755813888)), (589/1099511627776), by norm_num⟩
  | 7 => ⟨((5466759453/1099511627776), (101774902437/2199023255552)), (275/1099511627776), by norm_num⟩
  | 8 => ⟨((-556600939/274877906944), (-41449057161/2199023255552)), (225/2199023255552), by norm_num⟩
  | 9 => ⟨((12895712657/17592186044416), (120040026347/17592186044416)), (653/17592186044416), by norm_num⟩
  | 10 => ⟨((-8403095353/35184372088832), (-78220398853/35184372088832)), (427/35184372088832), by norm_num⟩
  | 11 => ⟨((2488917807/35184372088832), (92672585711/140737488355328)), (127/35184372088832), by norm_num⟩
  | 12 => ⟨((-10812179321/562949953421312), (-100645410225/562949953421312)), (277/281474976710656), by norm_num⟩
  | 13 => ⟨((10839115081/2251799813685248), (100896142345/2251799813685248)), (557/2251799813685248), by norm_num⟩
  | 14 => ⟨((-10089966663/9007199254740992), (-93922677735/9007199254740992)), (65/1125899906842624), by norm_num⟩
  | 15 => ⟨((2191605697/9007199254740992), (10200305039/4503599627370496)), (227/18014398509481984), by norm_num⟩
  | 16 => ⟨((-3570231467/72057594037927936), (-66467157069/144115188075855872)), (371/144115188075855872), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-2185540495947/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888816191272259/316912650057057350374175801344), (-2583334015873/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888463540169581/39614081257132168796771975168), (-1452772284967/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888158864230681/2475880078570760549798248448), (-192891009383/154742504910672534362390528)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221228159638739/19342813113834066795298816), (-24103601753/1208925819614629174706176)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((387068381720479/2417851639229258349412352), (-1445687645015/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257668946154249/604462909807314587353088), (-632224227333/151115727451828646838272)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942986398726383/37778931862957161709568), (-4107477555183/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296175302579197/4722366482869645213696), (-1539438345747/2361183241434822606848)), (3459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404893217538183/147573952589676412928), (-2115321799017/295147905179352825856)), (2379/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910565628338731/36893488147419103232), (-660511231981/9223372036854775808)), (2975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910010776410141/4611686018427387904), (-185587845321/288230376151711744)), (3349/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591271231125741/1152921504606846976), (-5931581139189/1152921504606846976)), (3351/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192206782412093/144115188075855872), (-2591005167953/72057594037927936)), (2935/72057594037927936), by norm_num⟩
  | 4 => ⟨((744039538319235/18014398509481984), (-1939198843535/9007199254740992)), (551/2251799813685248), by norm_num⟩
  | 3 => ⟨((1484814415738761/9007199254740992), (-9667667838531/9007199254740992)), (11039/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219075518280617/4503599627370496), (-19250591510271/4503599627370496)), (2767/562949953421312), by norm_num⟩
  | 1 => ⟨((2202829959227137/2251799813685248), (-7166211838567/562949953421312)), (33349/2251799813685248), by norm_num⟩
  | 0 => ⟨((538581652779647/562949953421312), (-56490442990531/2251799813685248)), (67285/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538581652779647/562949953421312), (-56490442990531/2251799813685248)), (256671914107512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059655547103937/2251799813685248), (-108090305247169/2251799813685248)), (66061/1125899906842624), by norm_num⟩
  | 2 => ⟨((1878718273674625/2251799813685248), (-197734092913117/2251799813685248)), (254381/2251799813685248), by norm_num⟩
  | 3 => ⟨((1550086095187271/2251799813685248), (-329946429009053/2251799813685248)), (234573/1125899906842624), by norm_num⟩
  | 4 => ⟨((1018697240552189/2251799813685248), (-454254742055961/2251799813685248)), (783383/2251799813685248), by norm_num⟩
  | 5 => ⟨((369214302344075/2251799813685248), (-411002833757971/2251799813685248)), (2049713/4503599627370496), by norm_num⟩
  | 6 => ⟨((-115833132602675/18014398509481984), (-269558818870385/4503599627370496)), (710197/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-109745841057/1073741824)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-3052282179/1073741824), (-13877135953/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1008874679830341/18014398509481984), (-144964501381229/9007199254740992)), (1442057/4503599627370496), by norm_num⟩
  | 1 => ⟨((101473582855/549755813888), (29161337153/549755813888)), (291/274877906944), by norm_num⟩
  | 2 => ⟨((-83610093825/274877906944), (-24027752513/274877906944)), (481/274877906944), by norm_num⟩
  | 3 => ⟨((91855076533/274877906944), (6599296045/68719476736)), (265/137438953472), by norm_num⟩
  | 4 => ⟨((-18921209223/68719476736), (-21750203195/274877906944)), (219/137438953472), by norm_num⟩
  | 5 => ⟨((99777950251/549755813888), (28674048613/549755813888)), (145/137438953472), by norm_num⟩
  | 6 => ⟨((-27404320571/274877906944), (-7875415543/274877906944)), (5/8589934592), by norm_num⟩
  | 7 => ⟨((51611525729/1099511627776), (1854006063/137438953472)), (605/2199023255552), by norm_num⟩
  | 8 => ⟨((-85051584605/4398046511104), (-24442006129/4398046511104)), (125/1099511627776), by norm_num⟩
  | 9 => ⟨((62292477345/8796093022208), (17901525529/8796093022208)), (23/549755813888), by norm_num⟩
  | 10 => ⟨((-20530584331/8796093022208), (-23600203119/35184372088832)), (487/35184372088832), by norm_num⟩
  | 11 => ⟨((24605620625/35184372088832), (1767782261/8796093022208)), (293/70368744177664), by norm_num⟩
  | 12 => ⟨((-27032037189/140737488355328), (-15536858525/281474976710656)), (323/281474976710656), by norm_num⟩
  | 13 => ⟨((54826575219/1125899906842624), (15755984957/1125899906842624)), (329/1125899906842624), by norm_num⟩
  | 14 => ⟨((-25814206835/2251799813685248), (-29673803475/9007199254740992)), (311/4503599627370496), by norm_num⟩
  | 15 => ⟨((22687843881/9007199254740992), (26080004119/36028797018963968)), (549/36028797018963968), by norm_num⟩
  | 16 => ⟨((-74775432273/144115188075855872), (-1343053735/9007199254740992)), (455/144115188075855872), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (-931938837161/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444393857024237/158456325028528675187087900672), (-4406012721827/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888399110049541/39614081257132168796771975168), (-1238881958135/9903520314283042199192993792)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888089923968031/2475880078570760549798248448), (-657964921571/309485009821345068724781056)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769755793849339/154742504910672534362390528), (-5261999745275/154742504910672534362390528)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548207809906131/9671406556917033397649408), (-4931298187477/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257610867962371/604462909807314587353088), (-2156529968007/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942938670964113/37778931862957161709568), (-7005299953071/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296102768513583/4722366482869645213696), (-5250981593077/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619471606685689/590295810358705651712), (-7215237834915/590295810358705651712)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910501193845301/36893488147419103232), (-9011758663913/73786976294838206464)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113742089593123/576460752303423488), (-1266026672583/1152921504606846976)), (6725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591119194461361/1152921504606846976), (-10115704609841/1152921504606846976)), (6733/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192069356805529/144115188075855872), (-2209295771895/36028797018963968)), (5901/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487864184802749/36028797018963968), (-13227692542043/36028797018963968)), (8871/36028797018963968), by norm_num⟩
  | 3 => ⟨((742265278963629/4503599627370496), (-8242775163365/4503599627370496)), (695/562949953421312), by norm_num⟩
  | 2 => ⟨((2218462374637291/4503599627370496), (-32824217817847/4503599627370496)), (22339/4503599627370496), by norm_num⟩
  | 1 => ⟨((275224715418413/281474976710656), (-48870215863389/2251799813685248)), (33757/2251799813685248), by norm_num⟩
  | 0 => ⟨((1075909161906819/1125899906842624), (-6017660328653/140737488355328)), (68513/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1075909161906819/1125899906842624), (-6017660328653/140737488355328)), (261356362349700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1026079613792283/1125899906842624), (-11500943985327/140737488355328)), (68401/1125899906842624), by norm_num⟩
  | 2 => ⟨((1855180869790531/2251799813685248), (-335401300694429/2251799813685248)), (135853/1125899906842624), by norm_num⟩
  | 3 => ⟨((1478462697659049/2251799813685248), (-276325663129369/1125899906842624)), (2065/8796093022208), by norm_num⟩
  | 4 => ⟨((417538994480211/1125899906842624), (-45356738958299/140737488355328)), (953663/2251799813685248), by norm_num⟩
  | 5 => ⟨((75807539268069/2251799813685248), (-1076512443066211/4503599627370496)), (661011/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1008874679830341/18014398509481984), (-144964501381229/9007199254740992)), (1442057/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-13877135953/134217728)), (1/536870912), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile062Terms3
