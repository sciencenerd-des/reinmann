/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RectangleModel
import XiRectangle.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile043
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

private theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((215/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88064000/1504020649), (-45841920/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-2826893233356800/2262078112618381201), (4037022842880000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((43296345988743/4611686018427387904), (-328780094711229/4611686018427387904)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((119775604343495/147573952589676412928), (658256449557731/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-68179352691747/1180591620717411303424), (-499857058856853/9444732965739290427392)), (1/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((754751120996017/302231454903657293676544), (404582372505873/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1611463388280765/19342813113834066795298816), (178557862152661/9671406556917033397649408)), (11/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((166940582158471/77371252455336267181195264), (-560213664320347/309485009821345068724781056)), (9/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-176192005066729/4951760157141521099596496896), (53154963953527/618970019642690137449562112)), (7/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-84629308454923/316912650057057350374175801344), (-1937219776167509/633825300114114700748351602688)), (41/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((551649154072419/10141204801825835211973625643008), (13533738923481/158456325028528675187087900672)), (15/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-234802191294181/81129638414606681695789005144064), (-271213273336489/162259276829213363391578010288128)), (11/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((572206798498453/5192296858534827628530496329220096), (1566839635085/324518553658426726783156020576256)), (1/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

private theorem V_shiftInv : F_shift c=value ((215/16), (17907/2560)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (17907/2560)))⁻¹=value ((88064000/1504020649), (-45841920/1504020649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using contains_exact ((88064000/1504020649), (-45841920/1504020649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((765032480559509/281474976710656), (67547514687059/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((44032000/1504020649), (-22920960/1504020649)), 0, by norm_num⟩
  | 2 => ⟨((-706723308339200/2262078112618381201), (1009255710720000/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((14432115329581/9223372036854775808), (-109593364903743/9223372036854775808)), (1/73786976294838206464), by norm_num⟩
  | 4 => ⟨((119775604343495/1180591620717411303424), (658256449557731/2361183241434822606848)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-436347857227181/75557863725914323419136), (-799771294170965/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((1006334827994689/4835703278458516698824704), (134860790835291/2417851639229258349412352)), (5/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-920836221874723/154742504910672534362390528), (408132256348939/309485009821345068724781056)), (7/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((166940582158471/1237940039285380274899124224), (-560213664320347/4951760157141521099596496896)), (9/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-626460462459481/316912650057057350374175801344), (755981709561273/158456325028528675187087900672)), (13/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-135406893527877/10141204801825835211973625643008), (-1549775820934007/10141204801825835211973625643008)), (17/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((401199384779941/162259276829213363391578010288128), (314967014946467/81129638414606681695789005144064)), (45/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-1252278353568965/10384593717069655257060992658440192), (-723235395563971/10384593717069655257060992658440192)), (15/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

private def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (381/40960)), 0, by norm_num⟩
  | 45 => ⟨((362084153177/16322553446400), (-1505331/120586240)), 0, by norm_num⟩
  | 44 => ⟨((-38283647570441/1838572420202496), (55464659959079/4741643894784000)), 0, by norm_num⟩
  | 43 => ⟨((773782829042049/36028797018963968), (-395474851388563/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 42 => ⟨((-808859926103399/36028797018963968), (200811085751525/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 41 => ⟨((416356443642883/18014398509481984), (-417941800336757/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 40 => ⟨((-851367208725181/36028797018963968), (430983590889535/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 39 => ⟨((435874276735501/18014398509481984), (-441227660226493/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 38 => ⟨((-447422576667331/18014398509481984), (451778681594019/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 37 => ⟨((919556528462773/36028797018963968), (-463565925586439/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 36 => ⟨((-472704838934117/18014398509481984), (238128555017455/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 35 => ⟨((972596139443695/36028797018963968), (-244796115031927/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 34 => ⟨((-1001396638521563/36028797018963968), (503613381304617/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 33 => ⟨((1031990642146213/36028797018963968), (-518450033871189/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 32 => ⟨((-1064522315435099/36028797018963968), (534201383083673/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 31 => ⟨((1099165601995957/36028797018963968), (-550946342175909/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 30 => ⟨((-1136133977774453/36028797018963968), (568773594717177/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 29 => ⟨((1175673339651099/36028797018963968), (-587790671908003/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 28 => ⟨((-1218062319677641/36028797018963968), (304061148692001/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 27 => ⟨((1263619685436717/36028797018963968), (-629910259504555/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 26 => ⟨((-656356868335055/18014398509481984), (326658313103823/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 25 => ⟨((1365772517649565/36028797018963968), (-339264183965745/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 24 => ⟨((-1423296072841727/36028797018963968), (352881281337663/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 23 => ⟨((1485872073009831/36028797018963968), (-735272587586107/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 22 => ⟨((-777097948388475/18014398509481984), (383677971019921/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 21 => ⟨((203637063555109/4503599627370496), (-200591069966835/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 20 => ⟨((-855785061409007/18014398509481984), (420358164704351/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 19 => ⟨((901412280980861/18014398509481984), (-220728670106343/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 18 => ⟨((-476084626224235/9007199254740992), (464783932307605/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 17 => ⟨((1008970901442277/18014398509481984), (-490709897449527/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1072963065529945/18014398509481984), (519694796371967/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 15 => ⟨((1145600110379291/18014398509481984), (-69039146358169/2251799813685248)), (3/18014398509481984), by norm_num⟩
  | 14 => ⟨((-153594506351147/2251799813685248), (589292860777311/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 13 => ⟨((662443664182859/9007199254740992), (-631569720911599/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 12 => ⟨((-718638779224613/9007199254740992), (170091886952057/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 11 => ⟨((785208355270615/9007199254740992), (-368658939853177/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 10 => ⟨((-108163083868541/1125899906842624), (6286288705165/140737488355328)), (1/4503599627370496), by norm_num⟩
  | 9 => ⟨((963495474894715/9007199254740992), (-110682654984425/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 8 => ⟨((-1086655597860323/9007199254740992), (246064774606091/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((155703368994027/1125899906842624), (-553884561370037/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1458546115154259/9007199254740992), (316637262587839/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((879089256444449/4503599627370496), (-369536940542233/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-276284104689085/1125899906842624), (443506192507515/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((46384411949291/140737488355328), (-554176720544899/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 2 => ⟨((-280905436981645/562949953421312), (368832770502991/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((283813447917325/281474976710656), (-275149384944103/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((-123054923689285/2251799813685248), (1080760234992943/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (17907/40960)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (17907/40960)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

private theorem logNorm : ‖value ((-41/256), (17907/40960))‖≤(1/2:ℝ) := by
  have h := Complex.sq_norm (value ((-41/256), (17907/40960)))
  norm_num [Complex.normSq_apply,value] at h
  nlinarith [norm_nonneg (value ((-41/256), (17907/40960)))]

set_option maxHeartbeats 5000000 in
private theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (17907/2560)))
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (J_shiftLog ⟨0,by omega⟩).radius_nonneg ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
private theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((207/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1119078567633233/35184372088832), (887391796984859/35184372088832)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((1038266941302007/562949953421312), (139384649125333/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-243740172647719/4611686018427387904), (370325671644095/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((171026043101547/1180591620717411303424), (-1918057950849321/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((492368898205979/37778931862957161709568), (288295432765935/9444732965739290427392)), (29/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-353794498234457/604462909807314587353088), (-141724015122367/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((690153000874161/38685626227668133590597632), (257236704151329/77371252455336267181195264)), (111/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-271944201008299/618970019642690137449562112), (172059772127279/1237940039285380274899124224)), (147/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((335937036074333/39614081257132168796771975168), (-686963129008401/79228162514264337593543950336)), (203/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-233658323292809/2535301200456458802993406410752), (1597014690531539/5070602400912917605986812821504)), (137/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-299077433137517/162259276829213363391578010288128), (-1442076702898471/162259276829213363391578010288128)), (721/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((848002101432163/5192296858534827628530496329220096), (510360444374119/2596148429267413814265248164610048)), (959/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((646288567689553/35184372088832), (641279863002549/35184372088832)), (7/35184372088832), by norm_num⟩
  | 1 => ⟨((756791964591351/562949953421312), (139384649125333/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-243740172647719/4611686018427387904), (370325671644095/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((171026043101547/1180591620717411303424), (-1918057950849321/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((492368898205979/37778931862957161709568), (288295432765935/9444732965739290427392)), (29/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-353794498234457/604462909807314587353088), (-141724015122367/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((690153000874161/38685626227668133590597632), (257236704151329/77371252455336267181195264)), (111/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-271944201008299/618970019642690137449562112), (172059772127279/1237940039285380274899124224)), (147/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((335937036074333/39614081257132168796771975168), (-686963129008401/79228162514264337593543950336)), (203/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-233658323292809/2535301200456458802993406410752), (1597014690531539/5070602400912917605986812821504)), (137/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-299077433137517/162259276829213363391578010288128), (-1442076702898471/162259276829213363391578010288128)), (721/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((848002101432163/5192296858534827628530496329220096), (510360444374119/2596148429267413814265248164610048)), (959/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2069265617858477/1125899906842624), 0), (9/1125899906842624), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2069265617858477/2251799813685248), 0), (9/2251799813685248), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42413802685537/2199023255552), (641279863002549/35184372088832)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((756791964591351/562949953421312), (139384649125333/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-243740172647719/4611686018427387904), (370325671644095/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((171026043101547/1180591620717411303424), (-1918057950849321/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((492368898205979/37778931862957161709568), (288295432765935/9444732965739290427392)), (29/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-353794498234457/604462909807314587353088), (-141724015122367/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((690153000874161/38685626227668133590597632), (257236704151329/77371252455336267181195264)), (111/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-271944201008299/618970019642690137449562112), (172059772127279/1237940039285380274899124224)), (147/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((335937036074333/39614081257132168796771975168), (-686963129008401/79228162514264337593543950336)), (203/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-233658323292809/2535301200456458802993406410752), (1597014690531539/5070602400912917605986812821504)), (137/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-299077433137517/162259276829213363391578010288128), (-1442076702898471/162259276829213363391578010288128)), (721/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((848002101432163/5192296858534827628530496329220096), (510360444374119/2596148429267413814265248164610048)), (959/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5653786466713600/2262078112618381201), (-8074045685760000/2262078112618381201)), 0, by norm_num⟩
  | 1 => ⟨((-43296345988743/1152921504606846976), (328780094711229/1152921504606846976)), (1/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-359326813030485/73786976294838206464), (-987384674336597/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 3 => ⟨((1090869643067953/2361183241434822606848), (499857058856853/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-471719450622511/18889465931478580854784), (-252863982816171/37778931862957161709568)), (1/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((604298770605287/604462909807314587353088), (-4184949894203/18889465931478580854784)), (3/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1168584075109297/38685626227668133590597632), (30636684767519/1208925819614629174706176)), (11/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((176192005066729/309485009821345068724781056), (-53154963953527/38685626227668133590597632)), (9/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((23801993002947/4951760157141521099596496896), (1089686124094223/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((-689561442590523/633825300114114700748351602688), (-67668694617405/39614081257132168796771975168)), (11/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((1291412052117995/20282409603651670423947251286016), (745836501675345/20282409603651670423947251286016)), (17/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-858310197747679/324518553658426726783156020576256), (-75208302484081/649037107316853453566312041152512)), (51/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((222743170754531/2596148429267413814265248164610048), (-415291462122831/10384593717069655257060992658440192)), (19/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43296345988743/1152921504606846976), (-328780094711229/1152921504606846976)), (1/4611686018427387904), by norm_num⟩
  | 1 => ⟨((359326813030485/36893488147419103232), (987384674336597/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-818152232300965/590295810358705651712), (-23430799633915/18446744073709551616)), (3/590295810358705651712), by norm_num⟩
  | 3 => ⟨((471719450622511/4722366482869645213696), (252863982816171/9444732965739290427392)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-755373463256609/151115727451828646838272), (20924749471015/18889465931478580854784)), (7/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((876438056331973/4835703278458516698824704), (-735280434420457/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((-616672017733551/154742504910672534362390528), (1488338990698757/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-95207972011789/2475880078570760549798248448), (-68105382755889/154742504910672534362390528)), (11/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((775756622914339/79228162514264337593543950336), (609018251556645/39614081257132168796771975168)), (19/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-807132532573747/1267650600228229401496703205376), (-466147813547091/1267650600228229401496703205376)), (1/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((1180176521903059/40564819207303340847894502572032), (25852853978903/20282409603651670423947251286016)), (3/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-668229512263593/649037107316853453566312041152512), (622937193184247/1298074214633706907132624082305024)), (37/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((553149350568433/20769187434139310514121985316880384), (-720618936718349/20769187434139310514121985316880384)), (29/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-119775604343495/18446744073709551616), (-658256449557731/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((1090869643067953/590295810358705651712), (999714117713707/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-471719450622511/2361183241434822606848), (-252863982816171/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((1007164617675479/75557863725914323419136), (-223197327690827/75557863725914323419136)), (5/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-730365046943311/1208925819614629174706176), (612733695350381/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((616672017733551/38685626227668133590597632), (-1488338990698757/38685626227668133590597632)), (3/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((111075967347087/618970019642690137449562112), (158912559763741/77371252455336267181195264)), (11/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-517171081942893/9903520314283042199192993792), (-203006083852215/2475880078570760549798248448)), (11/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((1210698798860621/316912650057057350374175801344), (174805430080159/79228162514264337593543950336)), (19/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-61467527182451/316912650057057350374175801344), (-21544044982419/2535301200456458802993406410752)), (33/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((1225087439149921/162259276829213363391578010288128), (-571025760418893/162259276829213363391578010288128)), (7/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-553149350568433/2596148429267413814265248164610048), (720618936718349/2596148429267413814265248164610048)), (11/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((208481030780461/83076749736557242056487941267521536), (-1181074400528057/83076749736557242056487941267521536)), (9/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-68179352691747/73786976294838206464), (-499857058856853/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((471719450622511/2361183241434822606848), (252863982816171/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-755373463256609/37778931862957161709568), (20924749471015/4722366482869645213696)), (1/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((730365046943311/604462909807314587353088), (-612733695350381/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((-192710005541735/4835703278458516698824704), (232552967296681/2417851639229258349412352)), (9/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-166613951020631/309485009821345068724781056), (-1906950717164893/309485009821345068724781056)), (9/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((452524696700031/2475880078570760549798248448), (710521293482753/2475880078570760549798248448)), (5/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-1210698798860621/79228162514264337593543950336), (-174805430080159/19807040628566084398385987584)), (9/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((553207744642059/633825300114114700748351602688), (48474101210443/1267650600228229401496703205376)), (9/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-1531359298937401/40564819207303340847894502572032), (713782200523617/40564819207303340847894502572032)), (31/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((760580357031595/649037107316853453566312041152512), (-495425518993865/324518553658426726783156020576256)), (7/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-312721546170691/20769187434139310514121985316880384), (885805800396043/10384593717069655257060992658440192)), (23/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-95166365467645/83076749736557242056487941267521536), (-1208146250578859/332306998946228968225951765070086144)), (19/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-754751120996017/9444732965739290427392), (-404582372505873/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((604298770605287/37778931862957161709568), (-4184949894203/1180591620717411303424)), (7/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-876438056331973/604462909807314587353088), (735280434420457/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((616672017733551/9671406556917033397649408), (-744169495349379/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((83306975510315/77371252455336267181195264), (953475358582447/77371252455336267181195264)), (21/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-271514818020019/618970019642690137449562112), (-106578194022413/154742504910672534362390528)), (13/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((847489159202435/19807040628566084398385987584), (489455204224445/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-885132391427295/316912650057057350374175801344), (-19389640484177/158456325028528675187087900672)), (29/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((689111684521831/5070602400912917605986812821504), (-642403980471255/10141204801825835211973625643008)), (29/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((-760580357031595/162259276829213363391578010288128), (495425518993865/81129638414606681695789005144064)), (7/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((21499606299235/324518553658426726783156020576256), (-15224787194307/40564819207303340847894502572032)), (25/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((456798554244697/83076749736557242056487941267521536), (1449775500694631/83076749736557242056487941267521536)), (11/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-803932227941435/1329227995784915872903807060280344576), (-804267600418787/1329227995784915872903807060280344576)), (19/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1611463388280765/302231454903657293676544), (178557862152661/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((1168584075109297/1208925819614629174706176), (-980373912560609/1208925819614629174706176)), (3/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-616672017733551/9671406556917033397649408), (1488338990698757/9671406556917033397649408)), (1/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((-111075967347087/77371252455336267181195264), (-1271300478109929/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((3535349192969/4835703278458516698824704), (710521293482753/618970019642690137449562112)), (3/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-847489159202435/9903520314283042199192993792), (-244727602112223/4951760157141521099596496896)), (1/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((2065308913330355/316912650057057350374175801344), (90484988926159/316912650057057350374175801344)), (39/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((-918815579362441/2535301200456458802993406410752), (428269320314171/2535301200456458802993406410752)), (21/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((570435267773697/40564819207303340847894502572032), (-371569139245399/20282409603651670423947251286016)), (11/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((-286661417323133/1298074214633706907132624082305024), (25374645323845/20282409603651670423947251286016)), (43/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((-418732008057639/20769187434139310514121985316880384), (-1328960875636745/20769187434139310514121985316880384)), (21/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((803932227941435/332306998946228968225951765070086144), (804267600418787/332306998946228968225951765070086144)), (19/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-859030695808681/5316911983139663491615228241121378304), (-33882405577831/664613997892457936451903530140172288)), (17/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-166940582158471/604462909807314587353088), (560213664320347/2417851639229258349412352)), (9/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((176192005066729/4835703278458516698824704), (-850479423256433/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((95207972011789/77371252455336267181195264), (68105382755889/4835703278458516698824704)), (15/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-517171081942893/618970019642690137449562112), (-812024335408861/618970019642690137449562112)), (15/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((605349399430311/4951760157141521099596496896), (174805430080159/2475880078570760549798248448)), (13/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((-1770264782854591/158456325028528675187087900672), (-77558561936709/158456325028528675187087900672)), (37/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((918815579362441/1267650600228229401496703205376), (-428269320314171/1267650600228229401496703205376)), (25/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((-162981505078199/5070602400912917605986812821504), (424650444851885/10141204801825835211973625643008)), (7/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((11517646231733/20282409603651670423947251286016), (-1043985407609623/324518553658426726783156020576256)), (31/324518553658426726783156020576256), by norm_num⟩
  | 9 => ⟨((149547145734871/2596148429267413814265248164610048), (949257768311961/5192296858534827628530496329220096)), (1/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-631661036239699/83076749736557242056487941267521536), (-315962271593095/41538374868278621028243970633760768)), (1/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((368156012489435/664613997892457936451903530140172288), (232336495390841/1329227995784915872903807060280344576)), (31/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((-1271590104654211/42535295865117307932921825928971026432), (223911855318671/42535295865117307932921825928971026432)), (57/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-176192005066729/19342813113834066795298816), (53154963953527/2417851639229258349412352)), (7/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-95207972011789/154742504910672534362390528), (-1089686124094225/154742504910672534362390528)), (19/154742504910672534362390528), by norm_num⟩
  | 2 => ⟨((193939155728585/309485009821345068724781056), (609018251556645/618970019642690137449562112)), (27/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((-1210698798860621/9903520314283042199192993792), (-174805430080159/2475880078570760549798248448)), (15/4951760157141521099596496896), by norm_num⟩
  | 4 => ⟨((1106415489284119/79228162514264337593543950336), (48474101210443/79228162514264337593543950336)), (27/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-1378223369043663/1267650600228229401496703205376), (80300497558907/158456325028528675187087900672)), (41/1267650600228229401496703205376), by norm_num⟩
  | 6 => ⟨((570435267773697/10141204801825835211973625643008), (-743138278490799/10141204801825835211973625643008)), (15/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-11517646231733/10141204801825835211973625643008), (1043985407609623/162259276829213363391578010288128)), (9/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((-84120269475865/649037107316853453566312041152512), (-266978747337739/649037107316853453566312041152512)), (21/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((98697036912453/5192296858534827628530496329220096), (394952839491369/20769187434139310514121985316880384)), (45/41538374868278621028243970633760768), by norm_num⟩
  | 10 => ⟨((-506214517172973/332306998946228968225951765070086144), (-159731340581203/332306998946228968225951765070086144)), (47/664613997892457936451903530140172288), by norm_num⟩
  | 11 => ⟨((1907385156981317/21267647932558653966460912964485513216), (-335867782978007/21267647932558653966460912964485513216)), (47/10633823966279326983230456482242756608), by norm_num⟩
  | 12 => ⟨((-84537371283207/21267647932558653966460912964485513216), (64835135017097/21267647932558653966460912964485513216)), (23/85070591730234615865843651857942052864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((84629308454923/618970019642690137449562112), (1937219776167509/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 1 => ⟨((-689561442590525/2475880078570760549798248448), (-1082699113878481/2475880078570760549798248448)), (31/2475880078570760549798248448), by norm_num⟩
  | 2 => ⟨((201783133143437/2475880078570760549798248448), (233073906773545/4951760157141521099596496896)), (3/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((-1966960869838433/158456325028528675187087900672), (-21544044982419/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 4 => ⟨((1531359298937403/1267650600228229401496703205376), (-356891100261809/633825300114114700748351602688)), (27/633825300114114700748351602688), by norm_num⟩
  | 5 => ⟨((-190145089257899/2535301200456458802993406410752), (990851037987731/10141204801825835211973625643008)), (11/2535301200456458802993406410752), by norm_num⟩
  | 6 => ⟨((286661417323133/162259276829213363391578010288128), (-811988650363041/81129638414606681695789005144064)), (33/81129638414606681695789005144064), by norm_num⟩
  | 7 => ⟨((299094291469743/1298074214633706907132624082305024), (949257768311961/1298074214633706907132624082305024)), (11/324518553658426726783156020576256), by norm_num⟩
  | 8 => ⟨((-98697036912453/2596148429267413814265248164610048), (-394952839491369/10384593717069655257060992658440192)), (53/20769187434139310514121985316880384), by norm_num⟩
  | 9 => ⟨((562460574636637/166153499473114484112975882535043072), (2773113551757/2596148429267413814265248164610048)), (15/83076749736557242056487941267521536), by norm_num⟩
  | 10 => ⟨((-582812131299847/2658455991569831745807614120560689152), (205252534042115/5316911983139663491615228241121378304)), (33/2658455991569831745807614120560689152), by norm_num⟩
  | 11 => ⟨((28179123761069/2658455991569831745807614120560689152), (-691574773515701/85070591730234615865843651857942052864)), (17/21267647932558653966460912964485513216), by norm_num⟩
  | 12 => ⟨((-111018773454937/340282366920938463463374607431768211456), (29740273063075/42535295865117307932921825928971026432)), (69/1361129467683753853853498429727072845824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((551649154072419/9903520314283042199192993792), (13533738923481/154742504910672534362390528)), (15/4951760157141521099596496896), by norm_num⟩
  | 1 => ⟨((-1291412052117997/39614081257132168796771975168), (-745836501675345/39614081257132168796771975168)), (49/39614081257132168796771975168), by norm_num⟩
  | 2 => ⟨((295044130475765/39614081257132168796771975168), (51705707957805/158456325028528675187087900672)), (21/79228162514264337593543950336), by norm_num⟩
  | 3 => ⟨((-612543719574961/633825300114114700748351602688), (285512880209447/633825300114114700748351602688)), (13/316912650057057350374175801344), by norm_num⟩
  | 4 => ⟨((190145089257899/2535301200456458802993406410752), (-990851037987731/10141204801825835211973625643008)), (53/10141204801825835211973625643008), by norm_num⟩
  | 5 => ⟨((-21499606299235/10141204801825835211973625643008), (974386380435649/81129638414606681695789005144064)), (23/40564819207303340847894502572032), by norm_num⟩
  | 6 => ⟨((-52341501007205/162259276829213363391578010288128), (-1328960875636747/1298074214633706907132624082305024)), (9/162259276829213363391578010288128), by norm_num⟩
  | 7 => ⟨((157915259059925/2596148429267413814265248164610048), (315962271593095/5192296858534827628530496329220096)), (51/10384593717069655257060992658440192), by norm_num⟩
  | 8 => ⟨((-1012429034345947/166153499473114484112975882535043072), (-159731340581203/83076749736557242056487941267521536)), (65/166153499473114484112975882535043072), by norm_num⟩
  | 9 => ⟨((582812131299847/1329227995784915872903807060280344576), (-205252534042115/2658455991569831745807614120560689152)), (77/2658455991569831745807614120560689152), by norm_num⟩
  | 10 => ⟨((-991905156389629/42535295865117307932921825928971026432), (760732250867271/42535295865117307932921825928971026432)), (11/5316911983139663491615228241121378304), by norm_num⟩
  | 11 => ⟨((266445056291849/340282366920938463463374607431768211456), (-17844163837845/10633823966279326983230456482242756608)), (95/680564733841876926926749214863536422912), by norm_num⟩
  | 12 => ⟨((52895347439853/10889035741470030830827987437816582766592), (1218956127719523/10889035741470030830827987437816582766592)), (99/10889035741470030830827987437816582766592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22016000/4512061947), (-3820160/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-706723308339200/6786234337855143603), (336418570240000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((14432115329581/18446744073709551616), (-109593364903743/18446744073709551616)), (1/147573952589676412928), by norm_num⟩
  | 3 => ⟨((319401611582653/4722366482869645213696), (877675266076975/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-22726450897249/4722366482869645213696), (-166619019618951/37778931862957161709568)), (3/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((1006334827994689/4835703278458516698824704), (134860790835291/2417851639229258349412352)), (5/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((-537154462760255/77371252455336267181195264), (238077149536881/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((890349771511845/4951760157141521099596496896), (-746951552427129/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-469845346844611/158456325028528675187087900672), (1133972564341909/158456325028528675187087900672)), (5/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-112839077939897/5070602400912917605986812821504), (-1291479850778339/5070602400912917605986812821504)), (7/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((183883051357473/40564819207303340847894502572032), (4511246307827/633825300114114700748351602688)), (5/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-1252278353568965/5192296858534827628530496329220096), (-723235395563971/5192296858534827628530496329220096)), (15/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((1525884795995875/166153499473114484112975882535043072), (66851824430293/166153499473114484112975882535043072)), (43/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((678792520384595/35184372088832), (641190495924399/35184372088832)), (9/35184372088832), by norm_num⟩
  | 1 => ⟨((1513466677159355/1125899906842624), (139468371618111/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1077411183307901/144115188075855872), (-145519240886389/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 3 => ⟨((-15214266063213/288230376151711744), (742365552792247/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((165344430377235/1180591620717411303424), (-1923264795212413/1180591620717411303424)), (5/295147905179352825856), by norm_num⟩
  | 5 => ⟨((62528861131211/4722366482869645213696), (1155288930920541/37778931862957161709568)), (15/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-715982034949543/1208925819614629174706176), (-565036082758711/1208925819614629174706176)), (43/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1394217716928195/77371252455336267181195264), (245565586144655/77371252455336267181195264)), (7/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-1095118137577643/2475880078570760549798248448), (22614866598275/154742504910672534362390528)), (37/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((670110961555855/79228162514264337593543950336), (-707142501676813/79228162514264337593543950336)), (51/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-222165632582967/2535301200456458802993406410752), (1633104660994155/5070602400912917605986812821504)), (275/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-338211131686547/162259276829213363391578010288128), (-1464677809009845/162259276829213363391578010288128)), (181/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((447843000653517/2596148429267413814265248164610048), (1022810008261685/5192296858534827628530496329220096)), (963/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-246308101624849/2361183241434822606848), (1870393427690547/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-511042578532245/18889465931478580854784), (-175535053215395/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((581797142969575/151115727451828646838272), (1066361725561287/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-1341779770659587/4835703278458516698824704), (-359628775560777/4835703278458516698824704)), (5/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((1074308925520511/77371252455336267181195264), (-119038574768441/38685626227668133590597632)), (3/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-155811210014573/309485009821345068724781056), (32679130418687/77371252455336267181195264)), (3/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((109630580930409/9903520314283042199192993792), (-1058374393385783/39614081257132168796771975168)), (5/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((67703446763939/633825300114114700748351602688), (1549775820934007/1267650600228229401496703205376)), (17/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((-551649154072419/20282409603651670423947251286016), (-13533738923481/316912650057057350374175801344)), (7/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((1147921824104885/649037107316853453566312041152512), (331482889633487/324518553658426726783156020576256)), (3/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((-839236637797731/10384593717069655257060992658440192), (-18384251718331/5192296858534827628530496329220096)), (35/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((950370861885999/332306998946228968225951765070086144), (-442977559597687/332306998946228968225951765070086144)), (27/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-98337662323277/1329227995784915872903807060280344576), (1024880265554985/10633823966279326983230456482242756608)), (21/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((339396258357159/17592186044416), (641190523795433/35184372088832)), (5/17592186044416), by norm_num⟩
  | 1 => ⟨((378366661674711/281474976710656), (139468329767293/562949953421312)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((538705869076447/72057594037927936), (-582076455064661/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((-486859073264627/9223372036854775808), (371182433427397/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 4 => ⟨((165360823030517/1180591620717411303424), (-961634213990709/590295810358705651712)), (21/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((500211869126591/37778931862957161709568), (1155304887527191/37778931862957161709568)), (31/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-715968652310269/1208925819614629174706176), (-565068381781947/1208925819614629174706176)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((1394225981509099/77371252455336267181195264), (122830088477019/38685626227668133590597632)), (113/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-1095185477562271/2475880078570760549798248448), (90433033309265/618970019642690137449562112)), (149/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((670251088731649/79228162514264337593543950336), (-707061573236961/79228162514264337593543950336)), (205/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-111185262170121/1267650600228229401496703205376), (204135838452917/633825300114114700748351602688)), (551/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-168873541707071/81129638414606681695789005144064), (-1464894106646367/162259276829213363391578010288128)), (725/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((55956366863349/324518553658426726783156020576256), (1023310438078851/5192296858534827628530496329220096)), (241/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-886548027382209/1208925819614629174706176), (-812466076618123/1208925819614629174706176)), (1/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((191682824379941/1208925819614629174706176), (205502157463301/4835703278458516698824704)), (7/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-613890814583149/38685626227668133590597632), (272088170899293/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((1187133028682461/1237940039285380274899124224), (-995935403236175/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-626460462459481/19807040628566084398385987584), (377990854780637/4951760157141521099596496896)), (1/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((-67703446763939/158456325028528675187087900672), (-193721977616751/39614081257132168796771975168)), (1/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((183883051357473/1267650600228229401496703205376), (1154879054803713/5070602400912917605986812821504)), (17/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-491966496044951/40564819207303340847894502572032), (-284128191114417/40564819207303340847894502572032)), (1/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((1798364223852281/2596148429267413814265248164610048), (39394825110709/1298074214633706907132624082305024)), (31/2596148429267413814265248164610048), by norm_num⟩
  | 9 => ⟨((-311133317879345/10384593717069655257060992658440192), (145022415344481/10384593717069655257060992658440192)), (13/20769187434139310514121985316880384), by norm_num⟩
  | 10 => ⟨((618122448889169/664613997892457936451903530140172288), (-805263065793203/664613997892457936451903530140172288)), (3/83076749736557242056487941267521536), by norm_num⟩
  | 11 => ⟨((-127074152094757/10633823966279326983230456482242756608), (719892967940911/10633823966279326983230456482242756608)), (19/10633823966279326983230456482242756608), by norm_num⟩
  | 12 => ⟨((-309366216631329/340282366920938463463374607431768211456), (-981858540152977/340282366920938463463374607431768211456)), (1/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((169698129172129/8796093022208), (641190523771787/35184372088832)), (11/35184372088832), by norm_num⟩
  | 1 => ⟨((1513466646877363/1125899906842624), (278936659582433/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((1077411735865973/144115188075855872), (-582076454557857/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-486859064419797/9223372036854775808), (742364859434497/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 4 => ⟨((41340196422641/295147905179352825856), (-1923268337861375/1180591620717411303424)), (11/590295810358705651712), by norm_num⟩
  | 5 => ⟨((500211852984831/37778931862957161709568), (288826175694879/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-357984238472863/604462909807314587353088), (-141267026609331/302231454903657293676544)), (45/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1394225043157475/77371252455336267181195264), (245659635022521/77371252455336267181195264)), (57/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-1095183762508499/2475880078570760549798248448), (180866104188363/1237940039285380274899124224)), (75/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((670248714972815/79228162514264337593543950336), (-353530233401869/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-444736332780453/5070602400912917605986812821504), (816540281976853/2535301200456458802993406410752)), (69/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-21109313900739/10141204801825835211973625643008), (-732441560975711/81129638414606681695789005144064)), (363/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((895297149259741/5192296858534827628530496329220096), (511647728053249/2596148429267413814265248164610048)), (965/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((491112651666519/154742504910672534362390528), (-108835268359717/154742504910672534362390528)), (1/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-178069954302369/309485009821345068724781056), (597561241941705/1237940039285380274899124224)), (9/1237940039285380274899124224), by norm_num⟩
  | 2 => ⟨((46984534684461/1237940039285380274899124224), (-113397256434191/1237940039285380274899124224)), (11/9903520314283042199192993792), by norm_num⟩
  | 3 => ⟨((135406893527877/158456325028528675187087900672), (1549775820934009/158456325028528675187087900672)), (5/39614081257132168796771975168), by norm_num⟩
  | 4 => ⟨((-137912288518105/316912650057057350374175801344), (-866159291102785/1267650600228229401496703205376)), (1/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((1033129641694397/20282409603651670423947251286016), (596669201340277/20282409603651670423947251286016)), (5/5070602400912917605986812821504), by norm_num⟩
  | 6 => ⟨((-1258854956696597/324518553658426726783156020576256), (-3447047197187/20282409603651670423947251286016)), (25/324518553658426726783156020576256), by norm_num⟩
  | 7 => ⟨((560039972182821/2596148429267413814265248164610048), (-130520173810033/1298074214633706907132624082305024)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 8 => ⟨((-173846938750079/20769187434139310514121985316880384), (452960474508677/41538374868278621028243970633760768)), (7/20769187434139310514121985316880384), by norm_num⟩
  | 9 => ⟨((174726959130291/1329227995784915872903807060280344576), (-494926415459377/664613997892457936451903530140172288)), (7/332306998946228968225951765070086144), by norm_num⟩
  | 10 => ⟨((510454257441693/42535295865117307932921825928971026432), (1620066591252413/42535295865117307932921825928971026432)), (13/10633823966279326983230456482242756608), by norm_num⟩
  | 11 => ⟨((-490015834173827/340282366920938463463374607431768211456), (-61277531460479/42535295865117307932921825928971026432)), (47/680564733841876926926749214863536422912), by norm_num⟩
  | 12 => ⟨((130899915551799/1361129467683753853853498429727072845824), (330434126778085/10889035741470030830827987437816582766592)), (21/5444517870735015415413993718908291383296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((169698129172157/8796093022208), (320595261885881/17592186044416)), (3/8796093022208), by norm_num⟩
  | 1 => ⟨((1513466646876715/1125899906842624), (34049885203/137438953472)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((1077411735871443/144115188075855872), (-291038227285529/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-486859064411915/9223372036854775808), (371182429762353/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 4 => ⟨((165360785176801/1180591620717411303424), (-1923268338668049/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((500211854909185/37778931862957161709568), (1155304703890899/37778931862957161709568)), (33/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-357984240817663/604462909807314587353088), (-17658378332587/37778931862957161709568)), (23/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1394225059847967/77371252455336267181195264), (7676863351341/2417851639229258349412352)), (115/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-1095183783232669/2475880078570760549798248448), (180866117687637/1237940039285380274899124224)), (151/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((670248725387353/79228162514264337593543950336), (-176765131450891/19807040628566084398385987584)), (207/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-111184067982391/1267650600228229401496703205376), (1633080757080693/5070602400912917605986812821504)), (553/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-168874628034791/81129638414606681695789005144064), (-732441677853327/81129638414606681695789005144064)), (727/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((895297648603291/5192296858534827628530496329220096), (127911951708721/649037107316853453566312041152512)), (483/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-607476812081921/79228162514264337593543950336), (733073172907901/39614081257132168796771975168)), (25/79228162514264337593543950336), by norm_num⟩
  | 1 => ⟨((-164129567912579/316912650057057350374175801344), (-1878516146586677/316912650057057350374175801344)), (17/158456325028528675187087900672), by norm_num⟩
  | 2 => ⟨((334332820649951/633825300114114700748351602688), (262472512455389/316912650057057350374175801344)), (25/1267650600228229401496703205376), by norm_num⟩
  | 3 => ⟨((-1043565294640805/10141204801825835211973625643008), (-75337020371247/1267650600228229401496703205376)), (27/10141204801825835211973625643008), by norm_num⟩
  | 4 => ⟨((1907355994994845/162259276829213363391578010288128), (20891195134467/40564819207303340847894502572032)), (47/162259276829213363391578010288128), by norm_num⟩
  | 5 => ⟨((-1187963577357501/1298074214633706907132624082305024), (276860974748555/649037107316853453566312041152512)), (37/1298074214633706907132624082305024), by norm_num⟩
  | 6 => ⟨((491688311616385/10384593717069655257060992658440192), (-640550165971867/10384593717069655257060992658440192)), (27/10384593717069655257060992658440192), by norm_num⟩
  | 7 => ⟨((-317685380236891/332306998946228968225951765070086144), (1799732419852279/332306998946228968225951765070086144)), (63/332306998946228968225951765070086144), by norm_num⟩
  | 8 => ⟨((-290030828091871/2658455991569831745807614120560689152), (-920492381393417/2658455991569831745807614120560689152)), (37/2658455991569831745807614120560689152), by norm_num⟩
  | 9 => ⟨((680577547463649/42535295865117307932921825928971026432), (340430730335995/21267647932558653966460912964485513216)), (5/5316911983139663491615228241121378304), by norm_num⟩
  | 10 => ⟨((-872666103678661/680564733841876926926749214863536422912), (-137680886157535/340282366920938463463374607431768211456)), (21/340282366920938463463374607431768211456), by norm_num⟩
  | 11 => ⟨((1644076094906455/21778071482940061661655974875633165533184), (-36187774596957/2722258935367507707706996859454145691648)), (41/10889035741470030830827987437816582766592), by norm_num⟩
  | 12 => ⟨((-1165875665912511/348449143727040986586495598010130648530944), (55884830183087/21778071482940061661655974875633165533184)), (81/348449143727040986586495598010130648530944), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((169698129172157/8796093022208), (641190523771763/35184372088832)), (13/35184372088832), by norm_num⟩
  | 1 => ⟨((756733323438357/562949953421312), (278936659582969/1125899906842624)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((1077411735871519/144115188075855872), (-582076454570939/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((-7607172881451/144115188075855872), (371182429762079/4611686018427387904)), (9/9223372036854775808), by norm_num⟩
  | 4 => ⟨((165360785190679/1180591620717411303424), (-1923268338667441/1180591620717411303424)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((500211854874611/37778931862957161709568), (577652351953507/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-357984240789043/604462909807314587353088), (-282534053358677/604462909807314587353088)), (47/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((87139066235875/4835703278458516698824704), (245659627661945/77371252455336267181195264)), (29/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-1095183783502781/2475880078570760549798248448), (361732234517999/2475880078570760549798248448)), (19/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((670248726655027/79228162514264337593543950336), (-707060524535361/79228162514264337593543950336)), (13/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-444736278431433/5070602400912917605986812821504), (51033773594659/158456325028528675187087900672)), (277/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-337749243820261/162259276829213363391578010288128), (-1464883357863613/162259276829213363391578010288128)), (91/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((447648815615195/2596148429267413814265248164610048), (511647813496875/2596148429267413814265248164610048)), (967/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-270797338102993/2535301200456458802993406410752), (-425186241422239/2535301200456458802993406410752)), (31/5070602400912917605986812821504), by norm_num⟩
  | 1 => ⟨((633937247118063/10141204801825835211973625643008), (732242722834731/20282409603651670423947251286016)), (49/20282409603651670423947251286016), by norm_num⟩
  | 2 => ⟨((-289666591767349/20282409603651670423947251286016), (-50763308441025/81129638414606681695789005144064)), (21/40564819207303340847894502572032), by norm_num⟩
  | 3 => ⟨((1202758728137777/649037107316853453566312041152512), (-560618120296707/649037107316853453566312041152512)), (13/162259276829213363391578010288128), by norm_num⟩
  | 4 => ⟨((-746717853465763/5192296858534827628530496329220096), (243197892684923/1298074214633706907132624082305024)), (53/5192296858534827628530496329220096), by norm_num⟩
  | 5 => ⟨((168861998264379/41538374868278621028243970633760768), (-478313500814587/20769187434139310514121985316880384)), (91/83076749736557242056487941267521536), by norm_num⟩
  | 6 => ⟨((411100107100479/664613997892457936451903530140172288), (652369472351643/332306998946228968225951765070086144)), (9/83076749736557242056487941267521536), by norm_num⟩
  | 7 => ⟨((-155037061087049/1329227995784915872903807060280344576), (-620406948559575/5316911983139663491615228241121378304)), (51/5316911983139663491615228241121378304), by norm_num⟩
  | 8 => ⟨((496988140913699/42535295865117307932921825928971026432), (313640084620407/85070591730234615865843651857942052864)), (65/85070591730234615865843651857942052864), by norm_num⟩
  | 9 => ⟨((-1144379340419777/1361129467683753853853498429727072845824), (201511556565179/1361129467683753853853498429727072845824)), (77/1361129467683753853853498429727072845824), by norm_num⟩
  | 10 => ⟨((973826476549561/21778071482940061661655974875633165533184), (-373433489425621/10889035741470030830827987437816582766592)), (87/21778071482940061661655974875633165533184), by norm_num⟩
  | 11 => ⟨((-261588770550577/174224571863520493293247799005065324265472), (1121211661675011/348449143727040986586495598010130648530944)), (47/174224571863520493293247799005065324265472), by norm_num⟩
  | 12 => ⟨((-51931265294263/5575186299632655785383929568162090376495104), (-1196739167327521/5575186299632655785383929568162090376495104)), (49/2787593149816327892691964784081045188247552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((169698129172157/8796093022208), (641190523771763/35184372088832)), (7/17592186044416), by norm_num⟩
  | 1 => ⟨((756733323438357/562949953421312), (278936659582969/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((1077411735871517/144115188075855872), (-582076454570939/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((-486859064412847/9223372036854775808), (371182429762075/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((165360785190509/1180591620717411303424), (-480817084666805/295147905179352825856)), (25/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((500211854874765/37778931862957161709568), (36103271997067/1180591620717411303424)), (35/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-357984240788669/604462909807314587353088), (-565068106714981/1208925819614629174706176)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((87139066235311/4835703278458516698824704), (245659627652917/77371252455336267181195264)), (117/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-273795945868463/618970019642690137449562112), (361732234527127/2475880078570760549798248448)), (153/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((670248726588415/79228162514264337593543950336), (-707060524523631/79228162514264337593543950336)), (209/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-55592034775587/633825300114114700748351602688), (816540377427597/2535301200456458802993406410752)), (555/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-337749244063885/162259276829213363391578010288128), (-366220839335377/40564819207303340847894502572032)), (729/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((895297631182025/5192296858534827628530496329220096), (31977988308725/162259276829213363391578010288128)), (121/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((812838112551217/4194304), (-293735262190077/2097152)), (821/4194304), by norm_num⟩
  | 1 => ⟨((619091639433541/2097152), (-294158784786347/2097152)), (1323/4194304), by norm_num⟩
  | 2 => ⟨((908781135542359/4194304), (-62428599623227/1048576)), (537/2097152), by norm_num⟩
  | 3 => ⟨((864832814932347/8388608), (-43011991618389/4194304)), (1169/8388608), by norm_num⟩
  | 4 => ⟨((603436062316581/16777216), (77245946202593/33554432)), (1923/33554432), by norm_num⟩
  | 5 => ⟨((660570493080287/67108864), (297399597693299/134217728)), (2551/134217728), by norm_num⟩
  | 6 => ⟨((1183349022312329/536870912), (464049034470001/536870912)), (2843/536870912), by norm_num⟩
  | 7 => ⟨((446000220917603/1073741824), (512099759874185/2147483648)), (685/536870912), by norm_num⟩
  | 8 => ⟨((576772781062135/8589934592), (902767659528073/17179869184)), (2329/8589934592), by norm_num⟩
  | 9 => ⟨((161950351458141/17179869184), (670545466786803/68719476736)), (3549/68719476736), by norm_num⟩
  | 10 => ⟨((635871216030905/549755813888), (865620664588121/549755813888)), (4907/549755813888), by norm_num⟩
  | 11 => ⟨((544929924426161/4398046511104), (495488470073601/2199023255552)), (3109/2199023255552), by norm_num⟩
  | 12 => ⟨((201228565437305/17592186044416), (510428123087615/17592186044416)), (3641/17592186044416), by norm_num⟩
  | _ => zero

private def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609106329001805/10141204801825835211973625643008), (-203801787909/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((453072062193397/158456325028528675187087900672), (-499387974853/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((963744718181791/19807040628566084398385987584), (-563205284051/19807040628566084398385987584)), (1/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1929659780646463/2475880078570760549798248448), (-1199221296579/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((226420812362849/19342813113834066795298816), (-1201919492817/154742504910672534362390528)), (1/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1587261330682387/9671406556917033397649408), (-1129674514487/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1291826280393743/604462909807314587353088), (-495674934911/302231454903657293676544)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1941559309672159/75557863725914323419136), (-1616372963045/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1337936134005907/4722366482869645213696), (-1217051230853/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((838554847727421/295147905179352825856), (-1681238270773/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1893226501819133/73786976294838206464), (-2113305951445/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((237671171837429/1152921504606846976), (-299218658353/1152921504606846976)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1672921593084027/1152921504606846976), (-301783710021/144115188075855872)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1263993562141815/144115188075855872), (-1067903900837/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((399112652500475/9007199254740992), (-203184553653/2251799813685248)), (3/36028797018963968), by norm_num⟩
  | 3 => ⟨((405375553851691/2251799813685248), (-1036931437415/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 2 => ⟨((1248087970924633/2251799813685248), (-1069137360839/562949953421312)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((656996791333699/562949953421312), (-843349560595/140737488355328)), (5/1125899906842624), by norm_num⟩
  | 0 => ⟨((1521929982859505/1125899906842624), (-7441347205635/562949953421312)), (11/1125899906842624), by norm_num⟩
  | _ => zero

private def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1521929982859505/1125899906842624), (-7441347205635/562949953421312)), (41965964889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2057065076618331/1125899906842624), (-40235226439917/1125899906842624)), (31/1125899906842624), by norm_num⟩
  | 2 => ⟨((939225998307893/281474976710656), (-73511400663925/562949953421312)), (59/562949953421312), by norm_num⟩
  | 3 => ⟨((782302662108383/70368744177664), (-122646459522689/140737488355328)), (103/140737488355328), by norm_num⟩
  | 4 => ⟨((540222903418819/4398046511104), (-85217745555937/4398046511104)), (155/8796093022208), by norm_num⟩
  | 5 => ⟨((1011026715576059/68719476736), (-327109560253081/68719476736)), (345/68719476736), by norm_num⟩
  | 6 => ⟨((812838112551217/4194304), (-293735262190077/2097152)), (821/4194304), by norm_num⟩
  | _ => zero

private def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((169698129172157/8796093022208), (641190523771763/35184372088832)), (7/17592186044416), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9420800/334203049), (-45841920/334203049)), 0, by norm_num⟩
  | 1 => ⟨((1006365078323200/111691677960896401), (431867559936000/111691677960896401)), 0, by norm_num⟩
  | 2 => ⟨((-452153497299655/1152921504606846976), (1299245316342029/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-610893343673891/18446744073709551616), (-40166524017901/1152921504606846976)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((26343321379595/9223372036854775808), (-525431739140011/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((386476296101651/4722366482869645213696), (1043535593286729/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-616135504795077/37778931862957161709568), (47192120802899/18889465931478580854784)), (5/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((4421666753315/75557863725914323419136), (-1394793239401975/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((1514612390907591/19342813113834066795298816), (392174309502775/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-192977794972443/77371252455336267181195264), (98350605293297/19342813113834066795298816)), (1/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-776357590123659/2475880078570760549798248448), (-150239660659607/618970019642690137449562112)), (11/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((3259901400931/154742504910672534362390528), (-44775491197379/2475880078570760549798248448)), (15/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((149487126388935/158456325028528675187087900672), (1077328550698511/633825300114114700748351602688)), (21/633825300114114700748351602688), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse0 : F_base c=value ((23/16), (17907/2560)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (17907/2560)))⁻¹=value ((9420800/334203049), (-45841920/334203049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using contains_exact ((9420800/334203049), (-45841920/334203049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5324800/119866083), (-15280640/119866083)), 0, by norm_num⟩
  | 1 => ⟨((34190743961600/4789292617920963), (81366351872000/14367877853762889)), 0, by norm_num⟩
  | 2 => ⟨((-1197964894759965/2305843009213693952), (759216961184815/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-174274405684593/18446744073709551616), (-745777227554247/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((1645026433686847/590295810358705651712), (174606873812755/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-190671810546339/2361183241434822606848), (403905916271151/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-344160851146689/37778931862957161709568), (-42249695587929/4722366482869645213696)), (7/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((934029928355395/1208925819614629174706176), (-461745781539661/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((138971655341029/19342813113834066795298816), (279166192858191/4835703278458516698824704)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-1188215928824921/309485009821345068724781056), (-127557041784867/154742504910672534362390528)), (23/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((170612376609753/1237940039285380274899124224), (-2189718199211/9671406556917033397649408)), (1/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((900856277481091/79228162514264337593543950336), (1094427266619365/79228162514264337593543950336)), (45/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-718149055516425/633825300114114700748351602688), (529794848381513/1267650600228229401496703205376)), (63/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (17907/2560)))⁻¹=value ((5324800/119866083), (-15280640/119866083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using contains_exact ((5324800/119866083), (-15280640/119866083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-650330000588800/40059610410287067), (-388054908928000/40059610410287067)), 0, by norm_num⟩
  | 1 => ⟨((134834876773035/72057594037927936), (-1035593934477005/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 2 => ⟨((587315800321309/4611686018427387904), (270014177578607/1152921504606846976)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-1746475751957193/73786976294838206464), (412451373071323/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((40946134607233/590295810358705651712), (-1225470352092777/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((1535639834388657/9444732965739290427392), (235723760744427/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-67993663412097/9444732965739290427392), (216190903154615/18889465931478580854784)), (3/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-863283260302355/1208925819614629174706176), (-466523728931157/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((687820367783281/9671406556917033397649408), (-724490461929989/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((416304748935149/309485009821345068724781056), (914361884131243/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-1117582343343165/2475880078570760549798248448), (-10097695910103/618970019642690137449562112)), (9/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((192053309948895/19807040628566084398385987584), (-1263621492467747/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((1316097561072165/633825300114114700748351602688), (812431126507755/633825300114114700748351602688)), (39/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22528000/398100649), (-45841920/398100649)), 0, by norm_num⟩
  | 1 => ⟨((796985422643200/158484126734221201), (1032726773760000/158484126734221201)), 0, by norm_num⟩
  | 2 => ⟨((-298299205833797/576460752303423488), (60622579417609/576460752303423488)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((79196636992533/9223372036854775808), (-302241432397491/9223372036854775808)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((970302219345211/590295810358705651712), (839138215930427/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-1212289917387887/9444732965739290427392), (513968737319289/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((75340817044937/151115727451828646838272), (-674727713131973/75557863725914323419136)), (9/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((1209027916314085/2417851639229258349412352), (42519774378191/151115727451828646838272)), (13/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-1174054663269499/38685626227668133590597632), (805786043968329/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-210794449834265/618970019642690137449562112), (-361585283161625/154742504910672534362390528)), (27/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((713908224363197/4951760157141521099596496896), (115146512762977/2475880078570760549798248448)), (19/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-535341984457259/79228162514264337593543950336), (4323479894269/618970019642690137449562112)), (53/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-267449612960303/1267650600228229401496703205376), (-185923946441829/316912650057057350374175801344)), (37/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (17907/2560)))⁻¹=value ((22528000/398100649), (-45841920/398100649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using contains_exact ((22528000/398100649), (-45841920/398100649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1172596312317359/576460752303423488), (190405876167481/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 1 => ⟨((-68882456127051/576460752303423488), (-543754640084439/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((1193703886341725/18446744073709551616), (93206846571339/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-103951258319639/36893488147419103232), (488814412054191/73786976294838206464)), (3/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-316889039867201/590295810358705651712), (-8764672030861/18446744073709551616)), (1/295147905179352825856), by norm_num⟩
  | 5 => ⟨((271509289796531/4722366482869645213696), (-630207406276461/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((364085607038141/302231454903657293676544), (433015514446675/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1192799230500707/2417851639229258349412352), (-32785870324281/604462909807314587353088)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((324820874295391/19342813113834066795298816), (-1438262211378589/38685626227668133590597632)), (9/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((749561726421469/309485009821345068724781056), (680333642754485/309485009821345068724781056)), (15/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-1101852984381073/4951760157141521099596496896), (317661794060291/2475880078570760549798248448)), (3/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-333992511071385/79228162514264337593543950336), (-767066206272107/39614081257132168796771975168)), (9/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((1900521810108439/1267650600228229401496703205376), (43921452358335/316912650057057350374175801344)), (27/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29081600/449710249), (-45841920/449710249)), 0, by norm_num⟩
  | 1 => ⟨((627871085363200/202239308055642001), (1333156380672000/202239308055642001)), 0, by norm_num⟩
  | 2 => ⟨((-1006188486925831/2305843009213693952), (-126607190990891/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((155947025446651/9223372036854775808), (-755040340422471/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((293019656245413/590295810358705651712), (899306618614929/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-442484222778589/4722366482869645213696), (-452582675112915/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((40147992868261/9444732965739290427392), (-604615769323499/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((321474970616625/4835703278458516698824704), (1673275494072061/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-1530855354692107/77371252455336267181195264), (-603490781877135/77371252455336267181195264)), (15/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((1284113926904309/1237940039285380274899124224), (-936191626428849/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((99134659779761/19807040628566084398385987584), (765757049145539/9903520314283042199192993792)), (55/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-1300224603857455/316912650057057350374175801344), (-711468904201217/316912650057057350374175801344)), (37/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((626427461549099/2535301200456458802993406410752), (-692252636432967/5070602400912917605986812821504)), (25/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (17907/2560)))⁻¹=value ((29081600/449710249), (-45841920/449710249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using contains_exact ((29081600/449710249), (-45841920/449710249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14468104415557/4611686018427387904), (675130679131631/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-1306551388161383/18446744073709551616), (-509604973975409/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 2 => ⟨((619657101871205/73786976294838206464), (-20721237201703/2305843009213693952)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((100287525922379/147573952589676412928), (26456479033769/18446744073709551616)), (5/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-841626307968319/4722366482869645213696), (115797145221513/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((103037670717627/18889465931478580854784), (-1322136345554705/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((832695173215063/604462909807314587353088), (659838155597355/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-83180832099681/604462909807314587353088), (98766636129263/1208925819614629174706176)), (9/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-93556910448907/38685626227668133590597632), (-133189020281145/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((1437010966738345/1237940039285380274899124224), (134496047679805/618970019642690137449562112)), (13/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-247187115236617/4951760157141521099596496896), (51447717098257/618970019642690137449562112)), (23/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-771489705858005/158456325028528675187087900672), (-479669002120771/79228162514264337593543950336)), (35/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((731538129092429/1267650600228229401496703205376), (-497583880647075/2535301200456458802993406410752)), (53/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11878400/171475683), (-15280640/171475683)), 0, by norm_num⟩
  | 1 => ⟨((15400262041600/9801303286772163), (181509554176000/29403909860316489)), 0, by norm_num⟩
  | 2 => ⟨((-1519394587155553/4611686018427387904), (-331573442298273/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((328691333741005/18446744073709551616), (-178919803460191/18446744073709551616)), (1/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-27299918278517/147573952589676412928), (166738392532023/147573952589676412928)), (1/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-829912192713551/18889465931478580854784), (-894912399247493/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((274474640166511/75557863725914323419136), (-47854295591171/151115727451828646838272)), (9/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-540195065967505/4835703278458516698824704), (208932920145375/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-296432089486297/77371252455336267181195264), (-424122679305963/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((384494654868907/618970019642690137449562112), (517496174554197/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-1221229623716111/39614081257132168796771975168), (809643478233797/39614081257132168796771975168)), (27/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((99577195122691/633825300114114700748351602688), (-329824483967137/158456325028528675187087900672)), (69/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((885345314237005/10141204801825835211973625643008), (802107987395533/10141204801825835211973625643008)), (89/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (17907/2560)))⁻¹=value ((11878400/171475683), (-15280640/171475683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using contains_exact ((11878400/171475683), (-15280640/171475683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((242654996779009/9223372036854775808), (368982058475027/18446744073709551616)), (3/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-1353349875196541/147573952589676412928), (359890447893097/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-273820893543/2305843009213693952), (-287534135224869/147573952589676412928)), (7/590295810358705651712), by norm_num⟩
  | 3 => ⟨((1255243233521859/4722366482869645213696), (59610952727241/590295810358705651712)), (5/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-471464197970345/18889465931478580854784), (118421805906633/4722366482869645213696)), (11/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-433493676680889/302231454903657293676544), (-1111869198996183/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((1964738984267537/4835703278458516698824704), (39582817198163/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-329875355689855/19342813113834066795298816), (1371728643977537/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-737793925296329/309485009821345068724781056), (-843798134732759/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((1504468390958175/4951760157141521099596496896), (-496052487146461/4951760157141521099596496896)), (9/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-20904351880705/9903520314283042199192993792), (539012512725191/19807040628566084398385987584)), (1/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-39934747355661/19807040628566084398385987584), (-80980648490723/79228162514264337593543950336)), (25/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((349517084888541/2535301200456458802993406410752), (-605696811979253/5070602400912917605986812821504)), (5/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42188800/592251049), (-45841920/592251049)), 0, by norm_num⟩
  | 1 => ⟨((160793391923200/350761305041600401), (1934015594496000/350761305041600401)), 0, by norm_num⟩
  | 2 => ⟨((-529693686985323/2305843009213693952), (-205962943509411/1152921504606846976)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((1113868577178521/73786976294838206464), (-186502444128933/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-259640897691723/590295810358705651712), (796016332869655/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-393969179540441/37778931862957161709568), (-775182733504563/18889465931478580854784)), (1/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((296133934348475/151115727451828646838272), (19986353373093/18889465931478580854784)), (11/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-1071072160349861/9671406556917033397649408), (369018970193855/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((381874694472129/154742504910672534362390528), (-873527831522001/154742504910672534362390528)), (9/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((323286658935195/2475880078570760549798248448), (734269161894299/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-1277819855735149/79228162514264337593543950336), (-436513635591091/79228162514264337593543950336)), (53/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((249624917055453/316912650057057350374175801344), (-542496013467381/1267650600228229401496703205376)), (1/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-233096339562391/20282409603651670423947251286016), (927449909487603/20282409603651670423947251286016)), (77/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (17907/2560)))⁻¹=value ((42188800/592251049), (-45841920/592251049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using contains_exact ((42188800/592251049), (-45841920/592251049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((505049233096663/147573952589676412928), (-180481075181237/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-441507091533057/1180591620717411303424), (1430293891912113/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-28457955091529/147573952589676412928), (-884151081665229/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((1543858177315993/37778931862957161709568), (-535528083138009/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-112408398977677/151115727451828646838272), (219294832008969/37778931862957161709568)), (5/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-707321708880835/1208925819614629174706176), (-467345089555775/1208925819614629174706176)), (3/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((319204475359389/4835703278458516698824704), (-23669020461775/604462909807314587353088)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((107401993481905/154742504910672534362390528), (1206257187012375/154742504910672534362390528)), (3/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-875549474176893/1237940039285380274899124224), (-322457649307315/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((973726508057655/19807040628566084398385987584), (-965544016404999/19807040628566084398385987584)), (5/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((331434162106951/158456325028528675187087900672), (909657490761525/158456325028528675187087900672)), (9/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-1316864183298645/2535301200456458802993406410752), (-102101529419127/2535301200456458802993406410752)), (29/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((418488462873065/20282409603651670423947251286016), (-191909717810735/5070602400912917605986812821504)), (3/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((119/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((48742400/683182249), (-45841920/683182249)), 0, by norm_num⟩
  | 1 => ⟨((-137169964236800/466737985348698001), (2234445201408000/466737985348698001)), 0, by norm_num⟩
  | 2 => ⟨((-86546066223039/576460752303423488), (-833055309958339/4611686018427387904)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((842370349125909/73786976294838206464), (207630977536673/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-1073054902188799/2361183241434822606848), (392933605922893/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 5 => ⟨((190609278062665/37778931862957161709568), (-128071171486803/4722366482869645213696)), (3/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((441199677666599/604462909807314587353088), (21472259237825/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-77583511768153/1208925819614629174706176), (-155344340979121/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((109411904124815/38685626227668133590597632), (-122255876192223/77371252455336267181195264)), (21/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-474162530090489/9903520314283042199192993792), (1497963822566397/9903520314283042199192993792)), (47/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-266738300516355/79228162514264337593543950336), (-554761911540627/79228162514264337593543950336)), (53/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((900089337232903/2535301200456458802993406410752), (346909040697189/2535301200456458802993406410752)), (15/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-1399930776059923/81129638414606681695789005144064), (570334353988875/81129638414606681695789005144064)), (67/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (17907/2560)))⁻¹=value ((48742400/683182249), (-45841920/683182249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using contains_exact ((48742400/683182249), (-45841920/683182249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((959299502375901/4722366482869645213696), (-645238472386259/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((266969615079213/4722366482869645213696), (18903287561163/147573952589676412928)), (13/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((-308234150101841/9444732965739290427392), (-29194429057919/9444732965739290427392)), (15/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((488458353463611/151115727451828646838272), (-358002347681195/75557863725914323419136)), (13/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((459493533397423/1208925819614629174706176), (448224002524631/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1026331251035899/9671406556917033397649408), (-39111480410387/19342813113834066795298816)), (39/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((229620787374889/38685626227668133590597632), (-207185566232373/19342813113834066795298816)), (21/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((891577924706551/1237940039285380274899124224), (42199486078731/38685626227668133590597632)), (21/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-322430426055929/2475880078570760549798248448), (17484153764717/1237940039285380274899124224)), (41/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((87314108713893/19807040628566084398385987584), (-922983591562581/79228162514264337593543950336)), (37/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((973597726335453/1267650600228229401496703205376), (1055581663892265/1267650600228229401496703205376)), (67/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-241096766138715/2535301200456458802993406410752), (71095105901723/2535301200456458802993406410752)), (57/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((224573607211981/162259276829213363391578010288128), (-83924615096079/10141204801825835211973625643008)), (95/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6144000/87468961), (-15280640/262406883)), 0, by norm_num⟩
  | 1 => ⟨((-53120332595200/68857372245775689), (31294750720000/7650819138419521)), 0, by norm_num⟩
  | 2 => ⟨((-424286483822877/4611686018427387904), (-766094370528397/4611686018427387904)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((297657752398123/36893488147419103232), (232837868705333/73786976294838206464)), (3/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-442999569777531/1180591620717411303424), (146494154857455/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 5 => ⟨((361383424696733/37778931862957161709568), (-1154786441574607/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((263641701658397/2417851639229258349412352), (985625479057847/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-1066478735181305/38685626227668133590597632), (-492448724799023/19342813113834066795298816)), (21/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((132264821007335/77371252455336267181195264), (113238015698259/1237940039285380274899124224)), (11/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-620972007736773/9903520314283042199192993792), (922239672388169/19807040628566084398385987584)), (23/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((268258197045139/316912650057057350374175801344), (-548406667245301/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((720436871992537/10141204801825835211973625643008), (1482620884905773/10141204801825835211973625643008)), (25/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-1095534934525113/162259276829213363391578010288128), (-124378838545475/40564819207303340847894502572032)), (13/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (17907/2560)))⁻¹=value ((6144000/87468961), (-15280640/262406883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using contains_exact ((6144000/87468961), (-15280640/262406883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-31058715690413/18889465931478580854784), (-1172066249315033/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((936259099701869/75557863725914323419136), (509806248706143/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-117267308994141/37778931862957161709568), (546177314604837/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((9106826104043/1208925819614629174706176), (-815892590131649/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((107914227296839/1208925819614629174706176), (130261975934271/2417851639229258349412352)), (23/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-949774925381805/77371252455336267181195264), (521832754404717/77371252455336267181195264)), (7/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((34583543133721/1237940039285380274899124224), (-1047493182606855/618970019642690137449562112)), (31/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((201046302429009/1237940039285380274899124224), (235039658282123/2475880078570760549798248448)), (33/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-1330472800762181/79228162514264337593543950336), (394957310019071/39614081257132168796771975168)), (65/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-10974167314525/158456325028528675187087900672), (-1213211667036455/633825300114114700748351602688)), (61/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((814354718338741/5070602400912917605986812821504), (400453415158253/5070602400912917605986812821504)), (7/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-1053613769419737/81129638414606681695789005144064), (381710344954337/40564819207303340847894502572032)), (97/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-32867873712437/162259276829213363391578010288128), (-1779016365160367/1298074214633706907132624082305024)), (165/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((151/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61849600/904366249), (-45841920/904366249)), 0, by norm_num⟩
  | 1 => ⟨((-861945695436800/817878312330330001), (2835304415232000/817878312330330001)), 0, by norm_num⟩
  | 2 => ⟨((-238997145492105/4611686018427387904), (-1339719801242651/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((50299910988075/9223372036854775808), (269576436929515/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-1317913365085511/4722366482869645213696), (3922218841371/295147905179352825856)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((86951035462199/9444732965739290427392), (-284385144994065/37778931862957161709568)), (5/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-299870933752547/2417851639229258349412352), (296633070039535/604462909807314587353088)), (11/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-317092952991929/38685626227668133590597632), (-385389022938995/19342813113834066795298816)), (11/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((972102050610953/1237940039285380274899124224), (293121633668711/618970019642690137449562112)), (11/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-384793837883651/9903520314283042199192993792), (36728981682423/9903520314283042199192993792)), (43/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((195634173124491/158456325028528675187087900672), (-176135375951833/158456325028528675187087900672)), (21/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-284876551815797/20282409603651670423947251286016), (175700043508453/2535301200456458802993406410752)), (81/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-414132375954263/324518553658426726783156020576256), (-884554084114733/324518553658426726783156020576256)), (39/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (17907/2560)))⁻¹=value ((61849600/904366249), (-45841920/904366249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using contains_exact ((61849600/904366249), (-45841920/904366249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-509277789465417/302231454903657293676544), (-616071167633057/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((785038692218073/604462909807314587353088), (-168850471763791/1208925819614629174706176)), (31/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-195304506637843/1208925819614629174706176), (96298655895851/302231454903657293676544)), (21/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-350549190352189/9671406556917033397649408), (-297528742544569/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((450089344612257/38685626227668133590597632), (53389894694113/154742504910672534362390528)), (57/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-279847257293955/309485009821345068724781056), (422935186715655/309485009821345068724781056)), (37/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((-433712157188503/4951760157141521099596496896), (-924995422390335/4951760157141521099596496896)), (21/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((1873614666765137/79228162514264337593543950336), (192364951128405/79228162514264337593543950336)), (45/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-239788594579443/158456325028528675187087900672), (649486998579525/316912650057057350374175801344)), (23/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-258492695384163/2535301200456458802993406410752), (-597897584423155/2535301200456458802993406410752)), (11/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((247955980618483/10141204801825835211973625643008), (222320984411137/81129638414606681695789005144064)), (41/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-213649377944127/162259276829213363391578010288128), (9268149346913/5070602400912917605986812821504)), (73/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-439393928590099/5192296858534827628530496329220096), (-931160977316435/5192296858534827628530496329220096)), (63/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((167/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68403200/1034619049), (-45841920/1034619049)), 0, by norm_num⟩
  | 1 => ⟨((-1288758070476800/1070436576553664401), (3135734022144000/1070436576553664401)), 0, by norm_num⟩
  | 2 => ⟨((-57873213428837/2305843009213693952), (-1139179512897331/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((1052476706403887/295147905179352825856), (1040946574352555/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-925649024884561/4722366482869645213696), (-177507064151665/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1105019206167879/151115727451828646838272), (-468446466212425/151115727451828646838272)), (5/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-836827651874405/4835703278458516698824704), (639458084172453/2417851639229258349412352)), (5/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-21438359413441/154742504910672534362390528), (-1946126854543071/154742504910672534362390528)), (9/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((701171269174609/2475880078570760549798248448), (1021736679039385/2475880078570760549798248448)), (17/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-1466058136127649/79228162514264337593543950336), (-583743687493091/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((61396027572913/79228162514264337593543950336), (-105457109508083/633825300114114700748351602688)), (7/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-889622024307517/40564819207303340847894502572032), (919517514976679/40564819207303340847894502572032)), (51/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((289196993401999/1298074214633706907132624082305024), (-1603371555924191/1298074214633706907132624082305024)), (91/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (17907/2560)))⁻¹=value ((68403200/1034619049), (-45841920/1034619049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using contains_exact ((68403200/1034619049), (-45841920/1034619049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-60967479508781/302231454903657293676544), (-290657205734661/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((423978911139355/4835703278458516698824704), (-167462162599051/2417851639229258349412352)), (15/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((2505864720173/1208925819614629174706176), (1255570659751819/38685626227668133590597632)), (21/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((-914541396721573/154742504910672534362390528), (-539872139823623/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((1308700960266389/1237940039285380274899124224), (-629236240282967/1237940039285380274899124224)), (1/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-226975258257969/9903520314283042199192993792), (1689920491986133/9903520314283042199192993792)), (43/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-338508003201321/19807040628566084398385987584), (-289539175577675/19807040628566084398385987584)), (25/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((405628994388751/158456325028528675187087900672), (-496079145932117/633825300114114700748351602688)), (111/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((-194018461024109/2535301200456458802993406410752), (1445786492488011/5070602400912917605986812821504)), (29/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-3323938785263/158456325028528675187087900672), (-900343007228941/40564819207303340847894502572032)), (113/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((948597086328361/324518553658426726783156020576256), (-205480866410463/324518553658426726783156020576256)), (107/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-230196086007635/2596148429267413814265248164610048), (1375313929353867/5192296858534827628530496329220096)), (195/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-684460813225653/41538374868278621028243970633760768), (-391032029745367/20769187434139310514121985316880384)), (171/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((183/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24985600/392659683), (-15280640/392659683)), 0, by norm_num⟩
  | 1 => ⟨((-65130374758400/51393875551220163), (381795958784000/154181626653660489)), 0, by norm_num⟩
  | 2 => ⟨((-36263812268579/4611686018427387904), (-1908192048683605/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((41744403101945/18446744073709551616), (231553114203345/73786976294838206464)), (1/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-628356080985969/4722366482869645213696), (-263553919853903/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1607672159564953/302231454903657293676544), (-245841811710993/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-741854279718809/4835703278458516698824704), (156414146949845/1208925819614629174706176)), (7/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((45715114630455/19342813113834066795298816), (-137362783033483/19342813113834066795298816)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((9746574046127/154742504910672534362390528), (1346516936414065/4951760157141521099596496896)), (21/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-577974460898801/79228162514264337593543950336), (-294174832418805/39614081257132168796771975168)), (19/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((954776836112803/2535301200456458802993406410752), (239126143014909/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-1120957360825023/81129638414606681695789005144064), (351037453633983/81129638414606681695789005144064)), (53/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((115335066264657/324518553658426726783156020576256), (-527679889919017/1298074214633706907132624082305024)), (11/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (17907/2560)))⁻¹=value ((24985600/392659683), (-15280640/392659683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using contains_exact ((24985600/392659683), (-15280640/392659683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1174120971129939/77371252455336267181195264), (155731985709223/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((508819873534701/154742504910672534362390528), (-637735416025369/77371252455336267181195264)), (53/154742504910672534362390528), by norm_num⟩
  | 2 => ⟨((112242567148231/77371252455336267181195264), (357574826538143/154742504910672534362390528)), (39/309485009821345068724781056), by norm_num⟩
  | 3 => ⟨((-186606330658275/309485009821345068724781056), (-92343537906247/2475880078570760549798248448)), (81/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((667473785139751/9903520314283042199192993792), (-416093107196255/4951760157141521099596496896)), (65/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((185112013432621/39614081257132168796771975168), (1246637870976073/79228162514264337593543950336)), (89/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-1338126173181731/633825300114114700748351602688), (-427691109253855/633825300114114700748351602688)), (27/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((539334902488385/2535301200456458802993406410752), (-428549934215323/2535301200456458802993406410752)), (123/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((55723762362415/20282409603651670423947251286016), (1242852431476665/40564819207303340847894502572032)), (131/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-935300590132045/324518553658426726783156020576256), (-246198873273143/162259276829213363391578010288128)), (131/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((733622306254521/2596148429267413814265248164610048), (-26261675754679/162259276829213363391578010288128)), (63/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((-24415724888691/20769187434139310514121985316880384), (1285733605041803/41538374868278621028243970633760768)), (29/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-194904033916013/83076749736557242056487941267521536), (-259938488945733/166153499473114484112975882535043072)), (13/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((199/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((81510400/1334446249), (-45841920/1334446249)), 0, by norm_num⟩
  | 1 => ⟨((-2271231839436800/1780746791470170001), (3736593235968000/1780746791470170001)), 0, by norm_num⟩
  | 2 => ⟨((6713049183221/2305843009213693952), (-793138901556593/9223372036854775808)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((409701349042127/295147905179352825856), (789900984625021/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-417284689515073/4722366482869645213696), (-68348423602183/1180591620717411303424)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1116170758829003/302231454903657293676544), (75663997098379/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-566216034512273/4835703278458516698824704), (134887435135623/2417851639229258349412352)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((405087847803145/154742504910672534362390528), (-1149741631716153/309485009821345068724781056)), (5/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-79921577222527/4951760157141521099596496896), (784480662715785/4951760157141521099596496896)), (1/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-11033662867947/4951760157141521099596496896), (-810608489748621/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((395305929184625/2535301200456458802993406410752), (598148153024037/5070602400912917605986812821504)), (39/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-1101440825131313/162259276829213363391578010288128), (-150020335811499/162259276829213363391578010288128)), (61/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((1158905906180741/5192296858534827628530496329220096), (-458784394068453/5192296858534827628530496329220096)), (47/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (17907/2560)))⁻¹=value ((81510400/1334446249), (-45841920/1334446249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using contains_exact ((81510400/1334446249), (-45841920/1334446249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-976284670655693/1237940039285380274899124224), (949745410387281/1237940039285380274899124224)), (53/1237940039285380274899124224), by norm_num⟩
  | 1 => ⟨((-176774093439993/2475880078570760549798248448), (-1617749366839187/2475880078570760549798248448)), (43/1237940039285380274899124224), by norm_num⟩
  | 2 => ⟨((449116228872589/2475880078570760549798248448), (544890689330091/4951760157141521099596496896)), (67/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((-902034617005083/19807040628566084398385987584), (180146009752199/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((91451334219349/39614081257132168796771975168), (-174019369459429/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((574475960107815/633825300114114700748351602688), (702633038724797/633825300114114700748351602688)), (85/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((-2016660172470557/10141204801825835211973625643008), (66020434050071/5070602400912917605986812821504)), (53/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((264418732008327/20282409603651670423947251286016), (-869954366151965/40564819207303340847894502572032)), (31/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((386354634924183/324518553658426726783156020576256), (861918908870945/324518553658426726783156020576256)), (67/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((-805194830012165/2596148429267413814265248164610048), (-282143948183327/5192296858534827628530496329220096)), (137/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((459127125585261/20769187434139310514121985316880384), (-241558390930431/10384593717069655257060992658440192)), (267/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((237902973143263/332306998946228968225951765070086144), (250988751442291/83076749736557242056487941267521536)), (251/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-719917360567179/2658455991569831745807614120560689152), (-504775099913127/5316911983139663491615228241121378304)), (227/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-104633614990401/2305843009213693952), (597534348311239/2305843009213693952)), (23/72057594037927936), by norm_num⟩
  | 1 => ⟨((-1063240018450233/4611686018427387904), (127094437718221/576460752303423488)), (1529/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-432019904404401/2305843009213693952), (241892378556307/9223372036854775808)), (6601/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-1200936624681037/18446744073709551616), (-612346877321261/18446744073709551616)), (9747/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-738908743364805/73786976294838206464), (-1333930065118487/73786976294838206464)), (11003/36893488147419103232), by norm_num⟩
  | 5 => ⟨((88199659380977/295147905179352825856), (-672034600205071/147573952589676412928)), (20173/147573952589676412928), by norm_num⟩
  | 6 => ⟨((69296254197959/147573952589676412928), (-794793814091157/1180591620717411303424)), (15605/295147905179352825856), by norm_num⟩
  | 7 => ⟨((1054395769694295/9444732965739290427392), (-256291691629279/4722366482869645213696)), (167365/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((9577398581551/590295810358705651712), (10358456363095/37778931862957161709568)), (198277/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((1027031286117911/604462909807314587353088), (488747160413621/604462909807314587353088)), (105391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((644336183075327/4835703278458516698824704), (88551927573811/604462909807314587353088)), (25445/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((275847111454127/38685626227668133590597632), (1381301459104019/77371252455336267181195264)), (5773247/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1495266632357/19342813113834066795298816), (2146213850773195/1237940039285380274899124224)), (18944943/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-104633614990401/2305843009213693952), (597534348311239/2305843009213693952)), (46485/1152921504606846976), by norm_num⟩
  | 1 => ⟨((-1063240018450233/4611686018427387904), (127094437718221/576460752303423488)), (93763/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-432019904404401/2305843009213693952), (241892378556307/9223372036854775808)), (23471/576460752303423488), by norm_num⟩
  | 3 => ⟨((-1200936624681037/18446744073709551616), (-612346877321261/18446744073709551616)), (747617/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-738908743364805/73786976294838206464), (-1333930065118487/73786976294838206464)), (1486743/36893488147419103232), by norm_num⟩
  | 5 => ⟨((88199659380977/295147905179352825856), (-672034600205071/147573952589676412928)), (11846263/295147905179352825856), by norm_num⟩
  | 6 => ⟨((69296254197959/147573952589676412928), (-794793814091157/1180591620717411303424)), (47286085/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((1054395769694295/9444732965739290427392), (-256291691629279/4722366482869645213696)), (94489171/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((9577398581551/590295810358705651712), (10358456363095/37778931862957161709568)), (47229861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1027031286117911/604462909807314587353088), (488747160413621/604462909807314587353088)), (24179359521/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((644336183075327/4835703278458516698824704), (88551927573811/604462909807314587353088)), (193429759619/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((275847111454127/38685626227668133590597632), (1381301459104019/77371252455336267181195264)), (3094855871461/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1495266632357/19342813113834066795298816), (2146213850773195/1237940039285380274899124224)), (49517620516359/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

private def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1560828692041339/2251799813685248), 0), (3/2251799813685248), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-85357819096011/140737488355328), (-682367172567975/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-1560828692041339/2251799813685248), 0), (3/2251799813685248), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-591291446778717/1125899906842624), (330146653767965/2251799813685248)), (167/1125899906842624), by norm_num⟩
  | 1 => ⟨((819703998447757/2251799813685248), (-457680444461131/4503599627370496)), (117/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1136351030835553/9007199254740992), (317239909675655/9007199254740992)), (329/9007199254740992), by norm_num⟩
  | 3 => ⟨((525105675433367/18014398509481984), (-293191931937029/36028797018963968)), (307/36028797018963968), by norm_num⟩
  | 4 => ⟨((-45496939802833/9007199254740992), (203225160985075/144115188075855872)), (215/144115188075855872), by norm_num⟩
  | 5 => ⟨((1614647068080089/2305843009213693952), (-225383915769033/1152921504606846976)), (241/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-1492250750452127/18446744073709551616), (208298967678487/9223372036854775808)), (225/9223372036854775808), by norm_num⟩
  | 7 => ⟨((295528400104101/36893488147419103232), (-330015639222607/147573952589676412928)), (361/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-204844677307549/295147905179352825856), (114374704933919/590295810358705651712)), (505/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1009688963757791/18889465931478580854784), (-281879126230477/18889465931478580854784)), (315/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-139972611694241/37778931862957161709568), (156306977284285/151115727451828646838272)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((564489432154037/2417851639229258349412352), (-157590895427563/2417851639229258349412352)), (361/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-130424752784485/9671406556917033397649408), (145644913130043/38685626227668133590597632)), (337/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791592864105769/5070602400912917605986812821504), (3737648560577/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890512280737637/316912650057057350374175801344), (2217015065273/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946139364267143/19807040628566084398385987584), (4987981762363/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473052820425995/618970019642690137449562112), (2649699453057/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886938160948893/77371252455336267181195264), (1324756366121/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194008740381039/1208925819614629174706176), (2483719678451/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260989334652743/604462909807314587353088), (4346112157851/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891365695109627/75557863725914323419136), (3530843399049/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300217584248457/4722366482869645213696), (2647806131631/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625127121841995/590295810358705651712), (3640202478327/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828068244108695/73786976294838206464), (71085246133/576460752303423488)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827817653308121/9223372036854775808), (10234079767105/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399764330414135/288230376151711744), (10231330711393/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74938022160825/9007199254740992), (4474657778671/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498258931179815/36028797018963968), (13417760404989/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497499875951755/9007199254740992), (16761293499351/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((280541057418673/562949953421312), (16744864356833/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((560103688871801/562949953421312), (25075984020491/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1114159878973283/1125899906842624), (24992642236021/562949953421312)), (1/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114159878973283/1125899906842624), (24992642236021/562949953421312)), (3818992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100323127944955/1125899906842624), (98928151888727/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((1066634964045977/1125899906842624), (193361652961275/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 3 => ⟨((488640868962807/562949953421312), (366367025169403/1125899906842624)), (17/1125899906842624), by norm_num⟩
  | 4 => ⟨((729065517425403/1125899906842624), (636013558399269/1125899906842624)), (41/1125899906842624), by norm_num⟩
  | 5 => ⟨((112819338077115/1125899906842624), (102961096103179/140737488355328)), (25/281474976710656), by norm_num⟩
  | 6 => ⟨((-591291446778717/1125899906842624), (330146653767965/2251799813685248)), (167/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85357819096011/140737488355328), (-682367172567975/70368744177664)), (1/35184372088832), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1236927473467587/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67644471205259/70368744177664), (-1081526380243363/70368744177664)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1236927473467587/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1624425367285939/4503599627370496), (-285984276689199/2251799813685248)), (527/2251799813685248), by norm_num⟩
  | 1 => ⟨((446153417631135/1125899906842624), (314185840736615/2251799813685248)), (587/2251799813685248), by norm_num⟩
  | 2 => ⟨((-980299254481681/4503599627370496), (-345168425558767/4503599627370496)), (653/4503599627370496), by norm_num⟩
  | 3 => ⟨((1435958410061015/18014398509481984), (505608365305447/18014398509481984)), (969/18014398509481984), by norm_num⟩
  | 4 => ⟨((-197195194413669/9007199254740992), (-555467563377959/72057594037927936)), (1077/72057594037927936), by norm_num⟩
  | 5 => ⟨((173312851079323/36028797018963968), (244097396433423/144115188075855872)), (479/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1015486015892535/1152921504606846976), (-178778932902433/576460752303423488)), (711/1152921504606846976), by norm_num⟩
  | 7 => ⟨((637500237731519/4611686018427387904), (448934246037907/9223372036854775808)), (113/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1400731190401377/73786976294838206464), (-493204679501197/73786976294838206464)), (1005/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1367875999018367/590295810358705651712), (481636197092117/590295810358705651712)), (993/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-300553076379149/1180591620717411303424), (-105826288958555/1180591620717411303424)), (883/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((15008695595779/590295810358705651712), (338216906222577/37778931862957161709568)), (357/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-1407038926370283/604462909807314587353088), (-247712832940955/302231454903657293676544)), (529/302231454903657293676544), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582723585084529/10141204801825835211973625643008), (-3651277310283/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780476952522573/633825300114114700748351602688), (-4329036491787/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472915687825071/9903520314283042199192993792), (-1217429972511/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472889223742205/618970019642690137449562112), (-5173566467715/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886611017738025/77371252455336267181195264), (-5172991464489/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775728318095469/4835703278458516698824704), (-4849068394907/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157556601925679/75557863725914323419136), (-530290445027/75557863725914323419136)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890494051685303/75557863725914323419136), (-1723157309585/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299564027179437/4722366482869645213696), (-1292117078363/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406057191603913/147573952589676412928), (-7105012331879/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57092054023931/2305843009213693952), (-4439408375121/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913277707176921/4611686018427387904), (-9985299875875/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597795822729247/1152921504606846976), (-9981085589163/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598952688813655/72057594037927936), (-8728704595771/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((748303070097403/18014398509481984), (-13083555772759/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((747718414579311/4503599627370496), (-4084448531237/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120105619077893/2251799813685248), (-16312771145129/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117130633541721/1125899906842624), (-24406435186315/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((554025781039527/562949953421312), (-12140251428185/281474976710656)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554025781039527/562949953421312), (-12140251428185/281474976710656)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088391681625111/1125899906842624), (-95582383316873/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1044018614342515/1125899906842624), (-184796304324641/1125899906842624)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((468880575699879/562949953421312), (-342713913384481/1125899906842624)), (9/281474976710656), by norm_num⟩
  | 4 => ⟨((42296341465203/70368744177664), (-570892300572985/1125899906842624)), (83/1125899906842624), by norm_num⟩
  | 5 => ⟨((234587441898159/2251799813685248), (-1372578463183929/2251799813685248)), (369/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1624425367285939/4503599627370496), (-285984276689199/2251799813685248)), (527/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67644471205259/70368744177664), (-1081526380243363/70368744177664)), (1/8796093022208), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1560828692041339/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-85357819096011/70368744177664), (-682367172567975/35184372088832)), (7/70368744177664), by norm_num⟩
  | 1 => ⟨((-1560828692041339/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((572655472881553/2251799813685248), (-346767756830249/2251799813685248)), (187/2251799813685248), by norm_num⟩
  | 1 => ⟨((-793869052920141/2251799813685248), (480722185911967/2251799813685248)), (133/1125899906842624), by norm_num⟩
  | 2 => ⟨((1100536191530779/4503599627370496), (-666422455594987/4503599627370496)), (377/4503599627370496), by norm_num⟩
  | 3 => ⟨((-1017111411018319/9007199254740992), (38494070513125/562949953421312)), (357/9007199254740992), by norm_num⟩
  | 4 => ⟨((705007906862695/18014398509481984), (-426912903111173/18014398509481984)), (253/18014398509481984), by norm_num⟩
  | 5 => ⟨((-97734848582869/9007199254740992), (473461560217873/72057594037927936)), (287/72057594037927936), by norm_num⟩
  | 6 => ⟨((90326179650225/36028797018963968), (-437571394091375/288230376151711744)), (271/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1144856443525569/2305843009213693952), (693260292818563/2305843009213693952)), (439/2305843009213693952), by norm_num⟩
  | 8 => ⟨((396777007987817/4611686018427387904), (-480531417361349/9223372036854775808)), (311/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-977866184525391/73786976294838206464), (592140439314655/73786976294838206464)), (49/9223372036854775808), by norm_num⟩
  | 10 => ⟨((1084488302029897/590295810358705651712), (-5130505950081/4611686018427387904)), (111/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-1093396376585113/4722366482869645213696), (82762373449185/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 12 => ⟨((252628205221477/9444732965739290427392), (-152977348834005/9444732965739290427392)), (215/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689317695/10141204801825835211973625643008), (-709253262731/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780097890218465/633825300114114700748351602688), (-420278959147/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891236922906543/39614081257132168796771975168), (-472762711289/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891105214272931/2475880078570760549798248448), (-15695256153/38685626227668133590597632)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443192802950841/38685626227668133590597632), (-502178252713/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551034899325139/9671406556917033397649408), (-235358904549/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630042352841571/302231454903657293676544), (-823607589245/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889897579082035/75557863725914323419136), (-167260476599/9444732965739290427392)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649559082294857/2361183241434822606848), (-1003319216351/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811809064233771/295147905179352825856), (-1379168117535/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826186063962113/73786976294838206464), (-53855207539/2305843009213693952)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114106611437877/576460752303423488), (-968985864419/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596952425857743/1152921504606846976), (-484238135505/288230376151711744)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598587206158051/72057594037927936), (-846843782213/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495523689038617/36028797018963968), (-634560303571/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((373527055289679/2251799813685248), (-1584398789991/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237627236019209/4503599627370496), (-6325598507661/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((278820969909563/281474976710656), (-9458459133837/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209442851762437/2251799813685248), (-9398740642073/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209442851762437/2251799813685248), (-9398740642073/1125899906842624)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2167725718883019/2251799813685248), (-9221947795267/562949953421312)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1043093185863749/1125899906842624), (-35510533916033/1125899906842624)), (23/2251799813685248), by norm_num⟩
  | 3 => ⟨((1930513342742983/2251799813685248), (-16449417807517/281474976710656)), (45/2251799813685248), by norm_num⟩
  | 4 => ⟨((1647377537650867/2251799813685248), (-28204834519277/281474976710656)), (83/2251799813685248), by norm_num⟩
  | 5 => ⟨((1182582893557441/2251799813685248), (-330146653767945/2251799813685248)), (139/2251799813685248), by norm_num⟩
  | 6 => ⟨((572655472881553/2251799813685248), (-346767756830249/2251799813685248)), (187/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85357819096011/70368744177664), (-682367172567975/35184372088832)), (7/70368744177664), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-453016498919635/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-49548679569335/35184372088832), (-792203754507217/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-453016498919635/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-953303484351913/4503599627370496), (68963704897539/562949953421312)), (677/4503599627370496), by norm_num⟩
  | 1 => ⟨((191785346221437/562949953421312), (-221985602488033/1125899906842624)), (551/2251799813685248), by norm_num⟩
  | 2 => ⟨((-617333214516161/2251799813685248), (714544089317531/4503599627370496)), (897/4503599627370496), by norm_num⟩
  | 3 => ⟨((1324745973396163/9007199254740992), (-766676231635555/9007199254740992)), (973/9007199254740992), by norm_num⟩
  | 4 => ⟨((-266512049241025/4503599627370496), (616958896878185/18014398509481984)), (791/18014398509481984), by norm_num⟩
  | 5 => ⟨((686295353870415/36028797018963968), (-794365631239417/72057594037927936)), (1029/72057594037927936), by norm_num⟩
  | 6 => ⟨((-368183253882141/72057594037927936), (106540180270947/36028797018963968)), (279/72057594037927936), by norm_num⟩
  | 7 => ⟨((1354441342905753/1152921504606846976), (-195965491800715/288230376151711744)), (1037/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1089944623720337/4611686018427387904), (630788584065729/4611686018427387904)), (843/4611686018427387904), by norm_num⟩
  | 9 => ⟨((194910911096581/4611686018427387904), (-451206694189337/18446744073709551616)), (609/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1003830431570911/147573952589676412928), (290475663988951/73786976294838206464)), (99/18446744073709551616), by norm_num⟩
  | 11 => ⟨((587491910627385/590295810358705651712), (-680003703655689/1180591620717411303424)), (117/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-1260709005616079/9444732965739290427392), (729615827506045/9444732965739290427392)), (507/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353601713/10141204801825835211973625643008), (213054861027/633825300114114700748351602688)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889894091469017/316912650057057350374175801344), (2019333113359/316912650057057350374175801344)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945444027670127/19807040628566084398385987584), (4542910574513/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890733976347287/2475880078570760549798248448), (1206536580573/618970019642690137449562112)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772399337269027/154742504910672534362390528), (2412681517079/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550685590861145/9671406556917033397649408), (282684098499/604462909807314587353088)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259778385036141/604462909807314587353088), (1978372541179/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944699270876807/37778931862957161709568), (1607037535817/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298742779338183/4722366482869645213696), (602468376223/590295810358705651712)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101443760989931/36893488147419103232), (6624932932243/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57047997772887/2305843009213693952), (4138918582461/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824970679939893/9223372036854775808), (9307989127213/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798106351257617/576460752303423488), (9302266566053/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196521964675213/144115188075855872), (8133044743233/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494534658371689/36028797018963968), (6093344290837/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492853849697923/9007199254740992), (7605409958213/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((279383053188551/562949953421312), (7588501050925/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((278323626273117/281474976710656), (22680936224951/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1100475514572147/1125899906842624), (5627934500847/140737488355328)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100475514572147/1125899906842624), (5627934500847/140737488355328)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1073824802216715/1125899906842624), (88013566082139/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((15894970312753/17592186044416), (167885528040551/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 3 => ⟨((447050921724523/562949953421312), (151688680270207/562949953421312)), (33/1125899906842624), by norm_num⟩
  | 4 => ⟨((1256559804777371/2251799813685248), (963674499558529/2251799813685248)), (141/2251799813685248), by norm_num⟩
  | 5 => ⟨((288779667682155/2251799813685248), (1075508252265497/2251799813685248)), (279/2251799813685248), by norm_num⟩
  | 6 => ⟨((-953303484351913/4503599627370496), (68963704897539/562949953421312)), (677/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-49548679569335/35184372088832), (-792203754507217/35184372088832)), (1/8796093022208), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2017341819488257/1125899906842624), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6895211297079/4398046511104), (-1763893552811339/70368744177664)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-2017341819488257/1125899906842624), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1873924264802779/9007199254740992), (62217621087543/4503599627370496)), (359/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1678810773038301/4503599627370496), (-870929779191/35184372088832)), (165/2251799813685248), by norm_num⟩
  | 2 => ⟨((376003137454181/1125899906842624), (99871787449483/4503599627370496)), (303/4503599627370496), by norm_num⟩
  | 3 => ⟨((-224569060664329/1125899906842624), (-119297480580895/9007199254740992)), (185/4503599627370496), by norm_num⟩
  | 4 => ⟨((402373740940961/4503599627370496), (53438097621467/9007199254740992)), (85/4503599627370496), by norm_num⟩
  | 5 => ⟨((-1153531136799493/36028797018963968), (-76598573944637/36028797018963968)), (125/18014398509481984), by norm_num⟩
  | 6 => ⟨((688950112469965/72057594037927936), (91497480129779/144115188075855872)), (305/144115188075855872), by norm_num⟩
  | 7 => ⟨((-705390221625025/288230376151711744), (-93680843676021/576460752303423488)), (319/576460752303423488), by norm_num⟩
  | 8 => ⟨((1263889609097515/2305843009213693952), (20981692342723/576460752303423488)), (73/576460752303423488), by norm_num⟩
  | 9 => ⟨((-1006482744515297/9223372036854775808), (-133668074437347/18446744073709551616)), (475/18446744073709551616), by norm_num⟩
  | 10 => ⟨((360674997619985/18446744073709551616), (95800415242639/73786976294838206464)), (347/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-1879979177598297/590295810358705651712), (-31209327484905/147573952589676412928)), (461/590295810358705651712), by norm_num⟩
  | 12 => ⟨((140352937225555/295147905179352825856), (74559477399091/2361183241434822606848)), (281/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581933546190685/10141204801825835211973625643008), (86371250295/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779550721795661/633825300114114700748351602688), (102301383275/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945310728102595/19807040628566084398385987584), (14384141679/4951760157141521099596496896)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236306425143085/309485009821345068724781056), (15280706225/309485009821345068724781056)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772117533909719/154742504910672534362390528), (122223656925/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550422219950769/9671406556917033397649408), (114561316539/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629774377420581/302231454903657293676544), (25054449111/151115727451828646838272)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236128366018501/9444732965739290427392), (162810140993/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649232705919859/2361183241434822606848), (122069313175/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622720975882883/590295810358705651712), (167783105271/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228133149577549/9223372036854775808), (104817812469/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912222797600295/4611686018427387904), (920749693/36028797018963968)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595693222311177/1152921504606846976), (235551832403/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196073715564793/144115188075855872), (3217623437/2251799813685248)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493874854269313/36028797018963968), (154266154861/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492051040549573/9007199254740992), (385037015571/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233524442292557/4503599627370496), (768192207197/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112221206905143/1125899906842624), (1147595248643/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197307100692137/2251799813685248), (2276487074377/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197307100692137/2251799813685248), (2276487074377/2251799813685248)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144130789520331/2251799813685248), (4442793877823/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((2041601156644485/2251799813685248), (8460726470479/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((1850992114657975/2251799813685248), (15341886825999/2251799813685248)), (41/2251799813685248), by norm_num⟩
  | 4 => ⟨((1521421404431065/2251799813685248), (3152779319715/281474976710656)), (69/2251799813685248), by norm_num⟩
  | 5 => ⟨((1027661035710685/2251799813685248), (17041322807863/1125899906842624)), (95/2251799813685248), by norm_num⟩
  | 6 => ⟨((1873924264802779/9007199254740992), (62217621087543/4503599627370496)), (359/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6895211297079/4398046511104), (-1763893552811339/70368744177664)), (1/8796093022208), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2190900055545493/1125899906842624), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-29953711696911/17592186044416), (-478911710139809/17592186044416)), (9/70368744177664), by norm_num⟩
  | 1 => ⟨((-2190900055545493/1125899906842624), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-814622926925969/9007199254740992), (-712306734130643/4503599627370496)), (1279/9007199254740992), by norm_num⟩
  | 1 => ⟨((396295755289597/2251799813685248), (693042451592631/2251799813685248)), (627/2251799813685248), by norm_num⟩
  | 2 => ⟨((-771155932245567/4503599627370496), (-337149585070069/1125899906842624)), (1229/4503599627370496), by norm_num⟩
  | 3 => ⟨((500200051686953/4503599627370496), (437375199558423/2251799813685248)), (803/4503599627370496), by norm_num⟩
  | 4 => ⟨((-486672178567817/9007199254740992), (-212773209941457/2251799813685248)), (787/9007199254740992), by norm_num⟩
  | 5 => ⟨((189404066307595/9007199254740992), (1324920155750905/36028797018963968)), (617/18014398509481984), by norm_num⟩
  | 6 => ⟨((-245708863266863/36028797018963968), (-53711991203409/4503599627370496)), (403/36028797018963968), by norm_num⟩
  | 7 => ⟨((546431280850095/288230376151711744), (955599623393675/288230376151711744)), (903/288230376151711744), by norm_num⟩
  | 8 => ⟨((-531653087583747/1152921504606846976), (-929755502797593/1152921504606846976)), (885/1152921504606846976), by norm_num⟩
  | 9 => ⟨((459799617291469/4611686018427387904), (804098075126161/4611686018427387904)), (771/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-357891496727687/18446744073709551616), (-625881042089535/18446744073709551616)), (1209/36893488147419103232), by norm_num⟩
  | 11 => ⟨((506490687813093/147573952589676412928), (885751470475157/147573952589676412928)), (431/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-657056913211669/1180591620717411303424), (-1149061850625517/1180591620717411303424)), (563/590295810358705651712), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847528133/10141204801825835211973625643008), (-2722767991059/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889668544265297/316912650057057350374175801344), (-3224232342637/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118148802074475/2475880078570760549798248448), (-3626706708733/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890195371987395/2475880078570760549798248448), (-3852705283689/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221482636489291/19342813113834066795298816), (-3761670829/151115727451828646838272)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775090683591249/4835703278458516698824704), (-3610402598865/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259337570544549/604462909807314587353088), (-3158300995029/604462909807314587353088)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888682932763159/75557863725914323419136), (-1282684242417/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649103348795591/2361183241434822606848), (-3846738599333/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622364078599691/590295810358705651712), (-2643565293455/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114038583070663/4611686018427387904), (-6605711577009/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56998104586541/288230376151711744), (-7427024586251/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595183981626265/1152921504606846976), (-1855381356303/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195624770037757/144115188075855872), (-6487650958631/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493194731999777/36028797018963968), (-9719115786967/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491189191423437/9007199254740992), (-1515909899451/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((557941449407045/1125899906842624), (-12094887135245/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110858789148249/1125899906842624), (-18061460115279/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((547878233007477/562949953421312), (-8950024211837/281474976710656)), (1/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547878233007477/562949953421312), (-8950024211837/281474976710656)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532640858476841/562949953421312), (-69683259348429/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((501807209048961/562949953421312), (-131863057649225/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 3 => ⟨((879166991866345/1125899906842624), (-470164941188641/2251799813685248)), (77/2251799813685248), by norm_num⟩
  | 4 => ⟨((1274839490162429/2251799813685248), (-183565827882963/562949953421312)), (153/2251799813685248), by norm_num⟩
  | 5 => ⟨((241156675743399/1125899906842624), (-415697638852849/1125899906842624)), (137/1125899906842624), by norm_num⟩
  | 6 => ⟨((-814622926925969/9007199254740992), (-712306734130643/4503599627370496)), (1279/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29953711696911/17592186044416), (-478911710139809/17592186044416)), (9/70368744177664), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1170621519031005/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8002295540251/4398046511104), (-1023550758851963/35184372088832)), (9/70368744177664), by norm_num⟩
  | 1 => ⟨((-1170621519031005/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-999606356052923/9007199254740992), (1064289821425943/9007199254740992)), (29/281474976710656), by norm_num⟩
  | 1 => ⟨((1039311491051827/4503599627370496), (-276641058382515/1125899906842624)), (973/4503599627370496), by norm_num⟩
  | 2 => ⟨((-540296872309595/2251799813685248), (1150517817869757/4503599627370496)), (255/1125899906842624), by norm_num⟩
  | 3 => ⟨((749010507413505/4503599627370496), (-797478181640403/4503599627370496)), (713/4503599627370496), by norm_num⟩
  | 4 => ⟨((-6084076422931/70368744177664), (103644328717897/1125899906842624)), (187/2251799813685248), by norm_num⟩
  | 5 => ⟨((161938960084449/4503599627370496), (-689671432625649/18014398509481984)), (157/4503599627370496), by norm_num⟩
  | 6 => ⟨((-897980268842763/72057594037927936), (478043809037207/36028797018963968)), (439/36028797018963968), by norm_num⟩
  | 7 => ⟨((533513564182991/144115188075855872), (-1136073320291235/288230376151711744)), (263/72057594037927936), by norm_num⟩
  | 8 => ⟨((-138676283551473/144115188075855872), (295299757075967/288230376151711744)), (69/72057594037927936), by norm_num⟩
  | 9 => ⟨((32041024984745/144115188075855872), (-272914925382991/1152921504606846976)), (1029/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-213207802852097/4611686018427387904), (908017013097351/18446744073709551616)), (863/18446744073709551616), by norm_num⟩
  | 11 => ⟨((644877326924997/73786976294838206464), (-343303326833941/36893488147419103232)), (329/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-55874362620637/36893488147419103232), (951838932287183/590295810358705651712)), (115/73786976294838206464), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581605650423851/10141204801825835211973625643008), (1514197648923/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111197222513843/39614081257132168796771975168), (896364326893/158456325028528675187087900672)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236272071472407/4951760157141521099596496896), (2016489956649/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889978286213021/2475880078570760549798248448), (267765255305/154742504910672534362390528)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771643940943665/154742504910672534362390528), (4283347439331/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549977718946195/9671406556917033397649408), (2007342830495/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259159309214917/604462909807314587353088), (1755948763811/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888393128663735/75557863725914323419136), (5705047976743/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324497307856051/1180591620717411303424), (2138611978957/2361183241434822606848)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405516219789239/147573952589676412928), (5878645201421/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456060763794537/18446744073709551616), (7344500852747/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823517911816373/9223372036854775808), (8257332256541/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594762077055573/1152921504606846976), (4125397801123/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195255077042111/144115188075855872), (1803023912435/36028797018963968)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((373159786016725/9007199254740992), (2700862641467/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490492881966441/9007199254740992), (13478618862739/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((557591936480215/1125899906842624), (6720056956427/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((554901765320523/562949953421312), (10032018408913/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1093619496191853/1125899906842624), (39744310064157/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093619496191853/1125899906842624), (39744310064157/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1060861613904903/1125899906842624), (77209620650465/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((994285576837163/1125899906842624), (145499119903003/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 3 => ⟨((107406729556321/140737488355328), (513962832691763/2251799813685248)), (31/1125899906842624), by norm_num⟩
  | 4 => ⟨((37318909468669/70368744177664), (784482764585801/2251799813685248)), (31/562949953421312), by norm_num⟩
  | 5 => ⟨((90007181718129/562949953421312), (832075138285651/2251799813685248)), (219/2251799813685248), by norm_num⟩
  | 6 => ⟨((-999606356052923/9007199254740992), (1064289821425943/9007199254740992)), (29/281474976710656), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8002295540251/4398046511104), (-1023550758851963/35184372088832)), (9/70368744177664), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log9 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1236927473467587/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67644471205259/35184372088832), (-1081526380243363/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1236927473467587/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((513280473197399/4503599627370496), (825224535281583/9007199254740992)), (469/9007199254740992), by norm_num⟩
  | 1 => ⟨((-563896235388045/2251799813685248), (-906601815370777/4503599627370496)), (523/4503599627370496), by norm_num⟩
  | 2 => ⟨((1239006667461983/4503599627370496), (996003895295153/4503599627370496)), (583/4503599627370496), by norm_num⟩
  | 3 => ⟨((-453729316871819/2251799813685248), (-729481412621707/4503599627370496)), (433/4503599627370496), by norm_num⟩
  | 4 => ⟨((498472603244367/4503599627370496), (801417244261179/9007199254740992)), (483/9007199254740992), by norm_num⟩
  | 5 => ⟨((-109525625497729/2251799813685248), (-704357466316691/18014398509481984)), (431/18014398509481984), by norm_num⟩
  | 6 => ⟨((320869861588977/18014398509481984), (257938589370217/18014398509481984)), (5/562949953421312), by norm_num⟩
  | 7 => ⟨((-402870369148441/72057594037927936), (-161928288002193/36028797018963968)), (51/18014398509481984), by norm_num⟩
  | 8 => ⟨((442598338286735/288230376151711744), (88948203541099/72057594037927936)), (455/576460752303423488), by norm_num⟩
  | 9 => ⟨((-864433730463809/2305843009213693952), (-347447429209613/1152921504606846976)), (225/1152921504606846976), by norm_num⟩
  | 10 => ⟨((379871007610703/4611686018427387904), (610736024633319/9223372036854775808)), (401/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1214053693294125/73786976294838206464), (-121993109417177/9223372036854775808)), (649/73786976294838206464), by norm_num⟩
  | 12 => ⟨((222295717759305/73786976294838206464), (714790022072235/295147905179352825856)), (241/147573952589676412928), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403063675/10141204801825835211973625643008), (110249470415/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779002924464891/633825300114114700748351602688), (130507256879/79228162514264337593543950336)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945002622889239/19807040628566084398385987584), (73397953681/2475880078570760549798248448)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118112296969305/154742504910672534362390528), (623760251857/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771462967455817/154742504910672534362390528), (1247245295315/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193726081534209/1208925819614629174706176), (292250034469/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629505985744453/302231454903657293676544), (255645721729/151115727451828646838272)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((7375604769015/295147905179352825856), (830574725019/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297811476320919/4722366482869645213696), (155672876367/590295810358705651712)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810911025020661/295147905179352825856), (427905877425/147573952589676412928)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823941892506063/73786976294838206464), (2138362837251/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823182363611329/9223372036854775808), (2404055234351/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594430597505537/1152921504606846976), (300256638635/144115188075855872)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298742400324475/36028797018963968), (1049773119385/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492220047260517/36028797018963968), (3144824287561/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489984918381615/9007199254740992), (3923176104819/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((278674919169673/562949953421312), (7822837847507/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218272653541591/2251799813685248), (2918909985047/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1092519490068983/1125899906842624), (1444864021937/140737488355328)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092519490068983/1125899906842624), (1444864021937/140737488355328)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120020119864403/2251799813685248), (44864865016781/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1995058541711405/2251799813685248), (84478572147063/2251799813685248)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((1764420589946361/2251799813685248), (74846660848485/1125899906842624)), (49/2251799813685248), by norm_num⟩
  | 4 => ⟨((1372578463183945/2251799813685248), (234587441898169/2251799813685248)), (21/562949953421312), by norm_num⟩
  | 5 => ⟨((812212683642987/2251799813685248), (571968553378429/4503599627370496)), (15/281474976710656), by norm_num⟩
  | 6 => ⟨((513280473197399/4503599627370496), (825224535281583/9007199254740992)), (469/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67644471205259/35184372088832), (-1081526380243363/35184372088832)), (5/35184372088832), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-648120085424803/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35444067171669/17592186044416), (-566693670395603/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-648120085424803/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((419759916486263/4503599627370496), (-429510798878125/4503599627370496)), (231/4503599627370496), by norm_num⟩
  | 1 => ⟨((-966532926337695/4503599627370496), (988985162776735/4503599627370496)), (539/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112762154036545/4503599627370496), (-142326405812625/562949953421312)), (629/4503599627370496), by norm_num⟩
  | 3 => ⟨((-427038257988749/2251799813685248), (873916427636191/4503599627370496)), (489/4503599627370496), by norm_num⟩
  | 4 => ⟨((983291926983039/9007199254740992), (-251533367349713/2251799813685248)), (285/4503599627370496), by norm_num⟩
  | 5 => ⟨((-905645333253015/18014398509481984), (926683171280071/18014398509481984)), (133/4503599627370496), by norm_num⟩
  | 6 => ⟨((347554240648003/18014398509481984), (-177813904676495/9007199254740992)), (413/36028797018963968), by norm_num⟩
  | 7 => ⟨((-914597958311951/144115188075855872), (935843762823227/144115188075855872)), (275/72057594037927936), by norm_num⟩
  | 8 => ⟨((1052969812445945/576460752303423488), (-1077429948824109/576460752303423488)), (641/576460752303423488), by norm_num⟩
  | 9 => ⟨((-1077578930449231/2305843009213693952), (275652682100859/576460752303423488)), (83/288230376151711744), by norm_num⟩
  | 10 => ⟨((992486872710747/9223372036854775808), (-126942751329853/1152921504606846976)), (619/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-831012901125835/36893488147419103232), (106289631591189/4611686018427387904)), (131/9223372036854775808), by norm_num⟩
  | 12 => ⟨((637825972739361/147573952589676412928), (-81580307080567/18446744073709551616)), (407/147573952589676412928), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314707869/10141204801825835211973625643008), (-1038024046877/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778860556696451/633825300114114700748351602688), (-307142211495/158456325028528675187087900672)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236230637126561/4951760157141521099596496896), (-345474020999/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944813305531219/1237940039285380274899124224), (-1467962828849/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221411605854097/19342813113834066795298816), (-1467623462737/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549649185253263/9671406556917033397649408), (-687768262581/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258872458911243/604462909807314587353088), (-601617053441/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887928152429565/75557863725914323419136), (-1954580014257/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297641509558259/4722366482869645213696), (-1465344279103/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621588401918419/590295810358705651712), (-1006944458287/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823649916626395/73786976294838206464), (-1257961384929/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822854006640099/9223372036854775808), (-2828436688969/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594102385425955/1152921504606846976), (-1412984081577/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149335322345671/18014398509481984), (-2469947809993/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491789839620199/36028797018963968), (-1849689969687/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((372361932449049/2251799813685248), (-4614542299909/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114163344911075/2251799813685248), (-9200098562621/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216667944875777/2251799813685248), (-6863949371511/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((2181846724289437/2251799813685248), (-27168093577431/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2181846724289437/2251799813685248), (-27168093577431/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2113738971846819/2251799813685248), (-26324105551859/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1982911882235261/2251799813685248), (-49420279250233/1125899906842624)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((217724176282691/281474976710656), (-174075969547743/2251799813685248)), (49/2251799813685248), by norm_num⟩
  | 4 => ⟨((333460130714391/562949953421312), (-134649792046535/1125899906842624)), (21/562949953421312), by norm_num⟩
  | 5 => ⟨((757886320112639/2251799813685248), (-319036084707869/2251799813685248)), (241/4503599627370496), by norm_num⟩
  | 6 => ⟨((419759916486263/4503599627370496), (-429510798878125/4503599627370496)), (231/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-35444067171669/17592186044416), (-566693670395603/17592186044416)), (5/35184372088832), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1349895032131027/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-36911192284833/17592186044416), (-590150643075447/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1349895032131027/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-586464616314233/9007199254740992), (-234138615259569/2251799813685248)), (639/9007199254740992), by norm_num⟩
  | 1 => ⟨((703140365561705/4503599627370496), (561439878710477/2251799813685248)), (193/1125899906842624), by norm_num⟩
  | 2 => ⟨((-843028479347065/4503599627370496), (-1346274031120343/4503599627370496)), (933/4503599627370496), by norm_num⟩
  | 3 => ⟨((673831335153575/4503599627370496), (269018677926223/1125899906842624)), (47/281474976710656), by norm_num⟩
  | 4 => ⟨((-403944243307043/4503599627370496), (-1290157232187515/9007199254740992)), (227/2251799813685248), by norm_num⟩
  | 5 => ⟨((774892793200059/18014398509481984), (1237464771291629/18014398509481984)), (439/9007199254740992), by norm_num⟩
  | 6 => ⟨((-309685294289991/18014398509481984), (-494551820889119/18014398509481984)), (707/36028797018963968), by norm_num⟩
  | 7 => ⟨((848677603695019/144115188075855872), (677647699122197/72057594037927936)), (61/9007199254740992), by norm_num⟩
  | 8 => ⟨((-254380001753767/144115188075855872), (-50779006698369/18014398509481984)), (295/144115188075855872), by norm_num⟩
  | 9 => ⟨((542201425510933/1152921504606846976), (865868374182513/1152921504606846976)), (317/576460752303423488), by norm_num⟩
  | 10 => ⟨((-260028447027441/2305843009213693952), (-830504672527143/4611686018427387904)), (613/4611686018427387904), by norm_num⟩
  | 11 => ⟨((113367451621855/4611686018427387904), (724168446650835/18446744073709551616)), (539/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-362457701777659/73786976294838206464), (-578826698311259/73786976294838206464)), (869/147573952589676412928), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790621340788033/5070602400912917605986812821504), (-2774893235445/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778727026290571/633825300114114700748351602688), (-3283814300195/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944847310836235/19807040628566084398385987584), (-923400828715/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944733199243023/1237940039285380274899124224), (-1961806210111/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771132260485155/154742504910672534362390528), (-3922666356935/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549498238690755/9671406556917033397649408), (-3676494730451/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629369992055781/302231454903657293676544), (-3215928149473/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471928034495183/18889465931478580854784), (-1305999966241/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648739424665125/2361183241434822606848), (-3916352451999/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621363690053499/590295810358705651712), (-336394279681/36893488147419103232)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911683723916643/36893488147419103232), (-6723873043821/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822534061609231/9223372036854775808), (-1889710658077/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593779735992577/1152921504606846976), (-7551953525903/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((298599306281275/36028797018963968), (-6600214688373/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((745677878014287/18014398509481984), (-9884846734247/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488894571947627/9007199254740992), (-6164504068203/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113594436086777/2251799813685248), (-24576991397163/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107441507680325/1125899906842624), (-2291460363819/140737488355328)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((2177967351302439/2251799813685248), (-72520892203267/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2177967351302439/2251799813685248), (-72520892203267/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052110066520263/1125899906842624), (-140286125388335/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((489393211657487/562949953421312), (-131091977019607/1125899906842624)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((1671263582684209/2251799813685248), (-227926206463831/1125899906842624)), (27/1125899906842624), by norm_num⟩
  | 4 => ⟨((17939264937667/35184372088832), (-338329158824247/1125899906842624)), (103/2251799813685248), by norm_num⟩
  | 5 => ⟨((382048562082775/2251799813685248), (-690008211709731/2251799813685248)), (335/4503599627370496), by norm_num⟩
  | 6 => ⟨((-586464616314233/9007199254740992), (-234138615259569/2251799813685248)), (639/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-36911192284833/17592186044416), (-590150643075447/17592186044416)), (5/35184372088832), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1398878082754463/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-76501145150635/35184372088832), (-1223130362689657/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1398878082754463/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1002377140487861/9007199254740992), (209394651257065/9007199254740992)), (377/4503599627370496), by norm_num⟩
  | 1 => ⟨((1245406810996883/4503599627370496), (-16260192541835/281474976710656)), (471/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1547359833168711/4503599627370496), (40405060574039/562949953421312)), (1177/4503599627370496), by norm_num⟩
  | 3 => ⟨((320420394921315/1125899906842624), (-267740809881377/4503599627370496)), (245/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1592429540135345/9007199254740992), (332655459446929/9007199254740992)), (153/1125899906842624), by norm_num⟩
  | 5 => ⟨((791407750720233/9007199254740992), (-165323552653591/9007199254740992)), (1223/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1311049588305647/36028797018963968), (136937865118495/18014398509481984)), (509/18014398509481984), by norm_num⟩
  | 7 => ⟨((930810240052149/72057594037927936), (-388888927589395/144115188075855872)), (1453/144115188075855872), by norm_num⟩
  | 8 => ⟨((-1156488277598175/288230376151711744), (241588170548953/288230376151711744)), (907/288230376151711744), by norm_num⟩
  | 9 => ⟨((1277229071735811/1152921504606846976), (-33351336194845/144115188075855872)), (1007/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-317379501365887/1152921504606846976), (132599931343817/2305843009213693952)), (503/2305843009213693952), by norm_num⟩
  | 11 => ⟨((17924055305693/288230376151711744), (-59908809301397/4611686018427387904)), (457/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-237544555841517/18446744073709551616), (198490398151897/73786976294838206464)), (381/36893488147419103232), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581143507296841/10141204801825835211973625643008), (478002476359/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889302240202533/316912650057057350374175801344), (4524784188057/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944778246039387/19807040628566084398385987584), (1272346886567/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472329821335381/618970019642690137449562112), (5406271661757/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885492376709181/77371252455336267181195264), (5404918774633/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774679766289039/4835703278458516698824704), (316604631273/604462909807314587353088)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258618198368097/604462909807314587353088), (2215513901045/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887513453322635/75557863725914323419136), (7197726193937/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297329151592429/4722366482869645213696), (5395937867051/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621156745130643/590295810358705651712), (7415585662019/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911553551632263/36893488147419103232), (2315935056559/18446744073709551616)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822238890646257/9223372036854775808), (2603453790169/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593481716680321/1152921504606846976), (2600988275571/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194133261807903/144115188075855872), (4546184612267/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490953438127615/36028797018963968), (13616387077169/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((744190283347599/4503599627370496), (8490860361347/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((556531929176543/1125899906842624), (8461816829859/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((69162782615951/70368744177664), (12620217729407/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 0 => ⟨((33973346670883/35184372088832), (24951017044429/562949953421312)), (1/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((33973346670883/35184372088832), (24951017044429/562949953421312)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1047516375712007/1125899906842624), (96368870781759/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((966341316414325/1125899906842624), (44829904345519/281474976710656)), (19/1125899906842624), by norm_num⟩
  | 3 => ⟨((1601669933804069/2251799813685248), (615628277671151/2251799813685248)), (39/1125899906842624), by norm_num⟩
  | 4 => ⟨((60683358354507/140737488355328), (875773500604163/2251799813685248)), (155/2251799813685248), by norm_num⟩
  | 5 => ⟨((156082338895301/4503599627370496), (1510468256769385/4503599627370496)), (509/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1002377140487861/9007199254740992), (209394651257065/9007199254740992)), (377/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-76501145150635/35184372088832), (-1223130362689657/35184372088832)), (5/35184372088832), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-360984530327749/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-78965366009195/35184372088832), (-631264646931543/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-360984530327749/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57912434327157/2251799813685248), (463110293533253/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | 1 => ⟨((148542461216475/2251799813685248), (-1187854449831941/4503599627370496)), (675/4503599627370496), by norm_num⟩
  | 2 => ⟨((-381003890452953/4503599627370496), (380848313481783/1125899906842624)), (109/562949953421312), by norm_num⟩
  | 3 => ⟨((10179746708413/140737488355328), (-1302475515940545/4503599627370496)), (751/4503599627370496), by norm_num⟩
  | 4 => ⟨((-208884278230921/4503599627370496), (835195934430271/4503599627370496)), (485/4503599627370496), by norm_num⟩
  | 5 => ⟨((214311038092887/9007199254740992), (-1713788220297129/18014398509481984)), (501/9007199254740992), by norm_num⟩
  | 6 => ⟨((-183232319817755/18014398509481984), (1465259998158757/36028797018963968)), (863/36028797018963968), by norm_num⟩
  | 7 => ⟨((134280463137925/36028797018963968), (-1073805054511827/72057594037927936)), (637/72057594037927936), by norm_num⟩
  | 8 => ⟨((-172211293822629/144115188075855872), (688563896152265/144115188075855872)), (823/288230376151711744), by norm_num⟩
  | 9 => ⟨((196316998861321/576460752303423488), (-1569894687117301/1152921504606846976)), (945/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-201417264035249/2305843009213693952), (100667509225095/288230376151711744)), (61/288230376151711744), by norm_num⟩
  | 11 => ⟨((187863666170499/9223372036854775808), (-1502295639878753/18446744073709551616)), (229/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-80310131639065/18446744073709551616), (642218706037379/36893488147419103232)), (197/18446744073709551616), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275803727/10141204801825835211973625643008), (591343714503/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778503305027317/633825300114114700748351602688), (2798514121659/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889443073877213/39614081257132168796771975168), (1573853501739/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889199304719997/2475880078570760549798248448), (3343672449189/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885432682177893/77371252455336267181195264), (3342810667321/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387312058365429/2417851639229258349412352), (3132969603857/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314630359829911/151115727451828646838272), (685108320949/151115727451828646838272)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943678697903437/37778931862957161709568), (2225744412921/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297213136442787/4722366482869645213696), (3337116355343/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620998892982625/590295810358705651712), (4586098163149/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911456143980793/36893488147419103232), (5728969396513/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822023155665737/9223372036854775808), (1610017602439/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398317566086421/288230376151711744), (6433799910789/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193953048484567/144115188075855872), (5622527073717/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((372673176710301/9007199254740992), (4209855531339/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((372017843461167/2251799813685248), (10500035928335/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((556389814824097/1125899906842624), (20926408264615/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((553120088961899/562949953421312), (7801490180357/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1086663941521289/1125899906842624), (30840176987833/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086663941521289/1125899906842624), (30840176987833/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2095901062101899/2251799813685248), (3720680239773/70368744177664)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1944500364103213/2251799813685248), (221637539717727/2251799813685248)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((828661243398399/1125899906842624), (382782051993101/2251799813685248)), (51/2251799813685248), by norm_num⟩
  | 4 => ⟨((288679716344195/562949953421312), (35215902544649/140737488355328)), (93/2251799813685248), by norm_num⟩
  | 5 => ⟨((902295794787981/4503599627370496), (1155753666056863/4503599627370496)), (285/4503599627370496), by norm_num⟩
  | 6 => ⟨((-57912434327157/2251799813685248), (463110293533253/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-78965366009195/35184372088832), (-631264646931543/17592186044416)), (5/35184372088832), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-742828600391541/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-81246878167825/35184372088832), (-649503503281803/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-742828600391541/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((318343242331827/4503599627370496), (78591493540283/1125899906842624)), (5/140737488355328), by norm_num⟩
  | 1 => ⟨((-840126067009295/4503599627370496), (-103703728536447/562949953421312)), (107/1125899906842624), by norm_num⟩
  | 2 => ⟨((277142606867715/1125899906842624), (547360169805083/2251799813685248)), (571/4503599627370496), by norm_num⟩
  | 3 => ⟨((-975193637337231/4503599627370496), (-963009912042371/4503599627370496)), (509/4503599627370496), by norm_num⟩
  | 4 => ⟨((321698989551123/2251799813685248), (635359591716891/4503599627370496)), (85/1125899906842624), by norm_num⟩
  | 5 => ⟨((-679185661043771/9007199254740992), (-83837519373091/1125899906842624)), (363/9007199254740992), by norm_num⟩
  | 6 => ⟨((298734982824525/9007199254740992), (590005386662179/18014398509481984)), (81/4503599627370496), by norm_num⟩
  | 7 => ⟨((-901004281183487/72057594037927936), (-889747451533319/72057594037927936)), (247/36028797018963968), by norm_num⟩
  | 8 => ⟨((297225244034001/72057594037927936), (146755908342219/36028797018963968)), (165/72057594037927936), by norm_num⟩
  | 9 => ⟨((-174309879736581/144115188075855872), (-688528454355339/576460752303423488)), (391/576460752303423488), by norm_num⟩
  | 10 => ⟨((736022025189085/2305843009213693952), (726826425646049/2305843009213693952)), (209/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-176582210939411/2305843009213693952), (-87188027543603/1152921504606846976)), (203/4611686018427387904), by norm_num⟩
  | 12 => ⟨((621347437412427/36893488147419103232), (153396135429095/9223372036854775808)), (361/36893488147419103232), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634289/10141204801825835211973625643008), (507440284759/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778406798243905/633825300114114700748351602688), (600296727795/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236166839688853/4951760157141521099596496896), (675198228277/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944542227549631/1237940039285380274899124224), (1434458340149/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770750828363469/154742504910672534362390528), (44814948859/4835703278458516698824704)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549141188982337/9671406556917033397649408), (336011219427/2417851639229258349412352)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78651756760603/37778931862957161709568), (1175635834251/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887206356112763/75557863725914323419136), (954826060087/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81068775103187/295147905179352825856), (357894455271/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620844767264359/590295810358705651712), (1967345555747/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822720956048243/73786976294838206464), (1228786048033/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910904863353535/4611686018427387904), (2762556809793/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593059105566219/1152921504606846976), (2759794675063/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193770832839167/144115188075855872), (602929132135/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((745212232903559/18014398509481984), (1805688065635/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((371936233765487/2251799813685248), (2251696321403/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224932842579909/4503599627370496), (4487191559425/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((276450805117575/281474976710656), (6690424991889/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171840253567677/2251799813685248), (13220240098345/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171840253567677/2251799813685248), (13220240098345/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2094409529373511/2251799813685248), (51003200964699/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((1946864869416277/2251799813685248), (47438315555323/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((1679226200151419/2251799813685248), (164057194529729/2251799813685248)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((310072619602365/562949953421312), (244683508456997/2251799813685248)), (73/2251799813685248), by norm_num⟩
  | 5 => ⟨((656563892819025/2251799813685248), (269543166242977/2251799813685248)), (97/2251799813685248), by norm_num⟩
  | 6 => ⟨((318343242331827/4503599627370496), (78591493540283/1125899906842624)), (5/140737488355328), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81246878167825/35184372088832), (-649503503281803/17592186044416)), (1/8796093022208), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190562091821633/70368744177664), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20842728792991/8796093022208), (-1332966944628899/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-190562091821633/70368744177664), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1655680860777285/18014398509481984), (-4870430702983/281474976710656)), (215/9007199254740992), by norm_num⟩
  | 1 => ⟨((-280229180499313/1125899906842624), (26378741689335/562949953421312)), (295/4503599627370496), by norm_num⟩
  | 2 => ⟨((47429668037867/140737488355328), (-71434956736627/1125899906842624)), (405/4503599627370496), by norm_num⟩
  | 3 => ⟨((-685023584363503/2251799813685248), (257932598608467/4503599627370496)), (371/4503599627370496), by norm_num⟩
  | 4 => ⟨((1855078255395341/9007199254740992), (-349247212766237/9007199254740992)), (509/9007199254740992), by norm_num⟩
  | 5 => ⟨((-502364504258369/4503599627370496), (189155796953199/9007199254740992)), (35/1125899906842624), by norm_num⟩
  | 6 => ⟨((906952197855659/18014398509481984), (-21343474749115/2251799813685248)), (1/70368744177664), by norm_num⟩
  | 7 => ⟨((-701734880512317/36028797018963968), (264224919252849/72057594037927936)), (201/36028797018963968), by norm_num⟩
  | 8 => ⟨((237541660536477/36028797018963968), (-178883586429723/144115188075855872)), (69/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1143599540597261/576460752303423488), (107650162712199/288230376151711744)), (337/576460752303423488), by norm_num⟩
  | 10 => ⟨((1238769986357923/2305843009213693952), (-233217635825165/2305843009213693952)), (185/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-609936601941083/4611686018427387904), (114830011926713/4611686018427387904)), (369/9223372036854775808), by norm_num⟩
  | 12 => ⟨((137644911462179/4611686018427387904), (-103655145630235/18446744073709551616)), (169/18446744073709551616), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171580859/10141204801825835211973625643008), (-242399533851/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889157252081921/316912650057057350374175801344), (-286727617653/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889230948485169/39614081257132168796771975168), (-80625585359/9903520314283042199192993792)), (1/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888974280473299/2475880078570760549798248448), (-342575950839/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885320371812393/77371252455336267181195264), (-171241428561/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549038079988675/9671406556917033397649408), (-80244700555/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258337983185569/604462909807314587353088), (-140378807919/302231454903657293676544)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943530040863207/37778931862957161709568), (-228022946739/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296990852100209/4722366482869645213696), (-341872427277/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620694390268013/590295810358705651712), (-469811509167/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822533364815573/73786976294838206464), (-586870048781/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910799604185839/4611686018427387904), (-164921761231/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796424619204809/576460752303423488), (-659010525869/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149198491272531/18014398509481984), (-287937030687/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490151570349017/36028797018963968), (-862293129349/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487406359914699/9007199254740992), (-1075215221673/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224263291892165/4503599627370496), (-2142497809353/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105310499558399/1125899906842624), (-798497053151/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((542486055289167/562949953421312), (-3154689691993/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542486055289167/562949953421312), (-3154689691993/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045523249013193/1125899906842624), (-12160051928381/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((485425876167235/562949953421312), (-5645980128013/562949953421312)), (25/2251799813685248), by norm_num⟩
  | 3 => ⟨((837042094876217/1125899906842624), (-19473879223593/1125899906842624)), (45/2251799813685248), by norm_num⟩
  | 4 => ⟨((1243912060684861/2251799813685248), (-28955427674551/1125899906842624)), (69/2251799813685248), by norm_num⟩
  | 5 => ⟨((85707193983597/281474976710656), (-127961661557173/4503599627370496)), (161/4503599627370496), by norm_num⟩
  | 6 => ⟨((1655680860777285/18014398509481984), (-4870430702983/281474976710656)), (215/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20842728792991/8796093022208), (-1332966944628899/35184372088832)), (5/35184372088832), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-390207173010335/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-85357819096011/35184372088832), (-1364734345135951/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-390207173010335/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((737850361943835/18014398509481984), (-1410984778031185/18014398509481984)), (609/18014398509481984), by norm_num⟩
  | 1 => ⟨((-63929862257063/562949953421312), (244505030176329/1125899906842624)), (427/4503599627370496), by norm_num⟩
  | 2 => ⟨((354502430216551/2251799813685248), (-1355823778395575/4503599627370496)), (299/2251799813685248), by norm_num⟩
  | 3 => ⟨((-81907453335417/562949953421312), (1253047239108033/4503599627370496)), (559/4503599627370496), by norm_num⟩
  | 4 => ⟨((454191362770317/4503599627370496), (-868546160896157/4503599627370496)), (49/562949953421312), by norm_num⟩
  | 5 => ⟨((-503714340062279/9007199254740992), (963248516178137/9007199254740992)), (55/1125899906842624), by norm_num⟩
  | 6 => ⟨((232765449747855/9007199254740992), (-890230657556569/18014398509481984)), (411/18014398509481984), by norm_num⟩
  | 7 => ⟨((-368778777655985/36028797018963968), (44075776452383/2251799813685248)), (329/36028797018963968), by norm_num⟩
  | 8 => ⟨((255617969982589/72057594037927936), (-977632005726711/144115188075855872)), (461/144115188075855872), by norm_num⟩
  | 9 => ⟨((-629976445133825/576460752303423488), (301174608175393/144115188075855872)), (287/288230376151711744), by norm_num⟩
  | 10 => ⟨((698666234821901/2305843009213693952), (-10437916525651/18014398509481984)), (643/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-704405135737067/9223372036854775808), (1347027765187501/9223372036854775808)), (655/9223372036854775808), by norm_num⟩
  | 12 => ⟨((81376072301349/4611686018427387904), (-622458998383787/18446744073709551616)), (611/36893488147419103232), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580815611530007/10141204801825835211973625643008), (-709253262731/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778226031638953/633825300114114700748351602688), (-838877587095/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472282839025679/9903520314283042199192993792), (-943538384869/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944434190775701/1237940039285380274899124224), (-2004522944469/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885267376274325/77371252455336267181195264), (-2003965036363/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548938615525161/9671406556917033397649408), (-469531162355/2417851639229258349412352)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629125427022613/302231454903657293676544), (-821383363477/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886918313822107/75557863725914323419136), (-1334192890901/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296884366203407/4722366482869645213696), (-500079611431/1180591620717411303424)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202568464073501/73786976294838206464), (-1374430542099/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822349629016785/73786976294838206464), (-1716856396895/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821391972206867/9223372036854775808), (-3859679604795/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592641337107955/1152921504606846976), (-3855624404443/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((298351317615355/36028797018963968), (-3369114624349/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489876094097297/36028797018963968), (-5044571888753/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((743529712617061/4503599627370496), (-393113744329/562949953421312)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111780851763523/2251799813685248), (-12532075273907/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((552387372545917/562949953421312), (-4669905414883/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167725718883019/2251799813685248), (-18443895590535/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167725718883019/2251799813685248), (-18443895590535/1125899906842624)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043093185863749/1125899906842624), (-35510533916035/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1930513342742983/2251799813685248), (-131595342460143/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((1647377537650867/2251799813685248), (-56409669038557/562949953421312)), (41/2251799813685248), by norm_num⟩
  | 4 => ⟨((591291446778719/1125899906842624), (-330146653767963/2251799813685248)), (69/2251799813685248), by norm_num⟩
  | 5 => ⟨((1145310945763089/4503599627370496), (-346767756830267/2251799813685248)), (93/2251799813685248), by norm_num⟩
  | 6 => ⟨((737850361943835/18014398509481984), (-1410984778031185/18014398509481984)), (609/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85357819096011/35184372088832), (-1364734345135951/35184372088832)), (1/8796093022208), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-797478660034543/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-43612114220639/17592186044416), (-174321903872541/4398046511104)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-797478660034543/281474976710656), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-135208017508665/4503599627370496), (-704911484117215/9007199254740992)), (429/9007199254740992), by norm_num⟩
  | 1 => ⟨((47884144928617/562949953421312), (499291155794841/2251799813685248)), (153/1125899906842624), by norm_num⟩
  | 2 => ⟨((-271331996760959/2251799813685248), (-707299182583597/2251799813685248)), (873/4503599627370496), by norm_num⟩
  | 3 => ⟨((512494289261711/4503599627370496), (667976494111967/2251799813685248)), (415/2251799813685248), by norm_num⟩
  | 4 => ⟨((-363001414772221/4503599627370496), (-236564989579239/1125899906842624)), (37/281474976710656), by norm_num⟩
  | 5 => ⟨((411384180897577/9007199254740992), (1072382536339871/9007199254740992)), (169/2251799813685248), by norm_num⟩
  | 6 => ⟨((-388513050284217/18014398509481984), (-1012762837296991/18014398509481984)), (643/18014398509481984), by norm_num⟩
  | 7 => ⟨((78624311314659/9007199254740992), (819820909998305/36028797018963968)), (131/9007199254740992), by norm_num⟩
  | 8 => ⟨((-111379723991961/36028797018963968), (-580681885485877/72057594037927936)), (747/144115188075855872), by norm_num⟩
  | 9 => ⟨((280500018018953/288230376151711744), (1462396148098053/576460752303423488)), (473/288230376151711744), by norm_num⟩
  | 10 => ⟨((-317886557623723/1152921504606846976), (-828656056217563/1152921504606846976)), (135/288230376151711744), by norm_num⟩
  | 11 => ⟨((163752806719205/2305843009213693952), (853730689494035/4611686018427387904)), (35/288230376151711744), by norm_num⟩
  | 12 => ⟨((-77324439520585/4611686018427387904), (-806267060568271/18446744073709551616)), (133/4611686018427387904), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790373256241827/5070602400912917605986812821504), (-2523289224621/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889070521358797/316912650057057350374175801344), (-2984188396397/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889035582960531/39614081257132168796771975168), (-839120921557/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944383203795665/1237940039285380274899124224), (-3565361506179/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885216268493675/77371252455336267181195264), (-3564346622735/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774421265971871/4835703278458516698824704), (-835124242935/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314541631163397/151115727451828646838272), (-2921857230461/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886780798575763/75557863725914323419136), (-1186499560649/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296780810280077/4722366482869645213696), (-3557732174679/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405101160614475/147573952589676412928), (-4889012627949/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455542442970675/18446744073709551616), (-3053482337143/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821188233806503/9223372036854775808), (-6864425385947/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796217926884881/576460752303423488), (-6857044273883/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193223514932633/144115188075855872), (-5991618548089/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((744799779590351/18014398509481984), (-8970858822873/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((185838369907461/1125899906842624), (-11184625852495/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222836501289619/4503599627370496), (-22282600761663/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104205717734173/1125899906842624), (-33207945156273/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((270656392198577/281474976710656), (-65556087191259/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270656392198577/281474976710656), (-65556087191259/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2080120470653743/2251799813685248), (-63036417137999/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1914471609194719/2251799813685248), (-29115230600989/281474976710656)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((801791734478007/1125899906842624), (-396058527348591/2251799813685248)), (51/2251799813685248), by norm_num⟩
  | 4 => ⟨((1072305615334321/2251799813685248), (-282046789121921/1125899906842624)), (91/2251799813685248), by norm_num⟩
  | 5 => ⟨((369321359122299/2251799813685248), (-1074483988938549/4503599627370496)), (133/2251799813685248), by norm_num⟩
  | 6 => ⟨((-135208017508665/4503599627370496), (-704911484117215/9007199254740992)), (429/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43612114220639/17592186044416), (-174321903872541/4398046511104)), (5/35184372088832), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1627134646477921/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-88983925979261/35184372088832), (-711354983263675/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1627134646477921/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1320222627515369/18014398509481984), (-565752562510741/18014398509481984)), (825/18014398509481984), by norm_num⟩
  | 1 => ⟨((119247943647059/562949953421312), (408808807159607/4503599627370496)), (601/4503599627370496), by norm_num⟩
  | 2 => ⟨((-689341777009305/2251799813685248), (-295402357648337/2251799813685248)), (875/4503599627370496), by norm_num⟩
  | 3 => ⟨((1328302669203767/4503599627370496), (569215087841797/4503599627370496)), (849/4503599627370496), by norm_num⟩
  | 4 => ⟨((-959822130251165/4503599627370496), (-205655401758289/2251799813685248)), (309/2251799813685248), by norm_num⟩
  | 5 => ⟨((138712138894085/1125899906842624), (237768226040379/4503599627370496)), (719/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1069145729964889/18014398509481984), (-229079521824061/9007199254740992)), (697/18014398509481984), by norm_num⟩
  | 7 => ⟨((13795663495383/562949953421312), (189178565769321/18014398509481984)), (145/9007199254740992), by norm_num⟩
  | 8 => ⟨((-1275987076751811/144115188075855872), (-546796383698947/144115188075855872)), (211/36028797018963968), by norm_num⟩
  | 9 => ⟨((409786334453769/144115188075855872), (351209961058487/288230376151711744)), (273/144115188075855872), by norm_num⟩
  | 10 => ⟨((-236886969575393/288230376151711744), (-406050941014105/1152921504606846976)), (159/288230376151711744), by norm_num⟩
  | 11 => ⟨((995914773344471/4611686018427387904), (213388758577151/2305843009213693952)), (673/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-959521311382139/18446744073709551616), (-411181894162613/18446744073709551616)), (653/18446744073709551616), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197585170521229/1267650600228229401496703205376), (-891226514997/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778059243473611/633825300114114700748351602688), (-131741147989/19807040628566084398385987584)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888943316341459/39614081257132168796771975168), (-2370810262751/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888668049320827/2475880078570760549798248448), (-2518334941585/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770333813495473/154742504910672534362390528), (-2517602746469/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387187397735451/2417851639229258349412352), (-73733587585/151115727451828646838272)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258084813907841/604462909807314587353088), (-2063762888337/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235830911632491/9444732965739290427392), (-6704314406281/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296680047045939/4722366482869645213696), (-5025686080977/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132532015761/295147905179352825856), (-6906176718959/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821993757878555/73786976294838206464), (-8626511338381/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455247025817947/2305843009213693952), (-303009119659/288230376151711744)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592233085836091/1152921504606846976), (-9685632125951/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193043134260369/144115188075855872), (-8462945682269/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((372330772884283/9007199254740992), (-6335239010767/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((743175551179575/4503599627370496), (-7898128234533/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((69440442407931/140737488355328), (-15733604582149/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((551805498519587/562949953421312), (-23444161367027/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((540643111122373/562949953421312), (-46265648028471/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540643111122373/562949953421312), (-46265648028471/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073078392024321/2251799813685248), (-177729503208505/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1894513987096237/2251799813685248), (-327246845379009/2251799813685248)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((1546359817746875/2251799813685248), (-275323642019943/1125899906842624)), (55/2251799813685248), by norm_num⟩
  | 4 => ⟨((927265488624605/2251799813685248), (-378141444286375/1125899906842624)), (103/2251799813685248), by norm_num⟩
  | 5 => ⟨((63917200165139/1125899906842624), (-622857341002393/2251799813685248)), (309/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1320222627515369/18014398509481984), (-565752562510741/18014398509481984)), (825/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88983925979261/35184372088832), (-711354983263675/17592186044416)), (5/35184372088832), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1657571786173643/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-90648457056371/35184372088832), (-1449323143311105/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1657571786173643/562949953421312), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1286186962137687/18014398509481984), (235868034563553/9007199254740992)), (249/4503599627370496), by norm_num⟩
  | 1 => ⟨((946774756453469/4503599627370496), (-347249517454151/4503599627370496)), (737/4503599627370496), by norm_num⟩
  | 2 => ⟨((-348465062174051/1125899906842624), (255613753672185/2251799813685248)), (1091/4503599627370496), by norm_num⟩
  | 3 => ⟨((1368045482590577/4503599627370496), (-250879699974477/2251799813685248)), (269/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1007031611053065/4503599627370496), (23084373990201/281474976710656)), (199/1125899906842624), by norm_num⟩
  | 5 => ⟨((1186057251534969/9007199254740992), (-54376424469123/1125899906842624)), (471/4503599627370496), by norm_num⟩
  | 6 => ⟨((-582045533823763/9007199254740992), (426954836678895/18014398509481984)), (929/18014398509481984), by norm_num⟩
  | 7 => ⟨((489656444982979/18014398509481984), (-359183560988851/36028797018963968)), (393/18014398509481984), by norm_num⟩
  | 8 => ⟨((-1441763523007951/144115188075855872), (264398519412845/72057594037927936)), (1163/144115188075855872), by norm_num⟩
  | 9 => ⟨((943374381307765/288230376151711744), (-346002358485811/288230376151711744)), (765/288230376151711744), by norm_num⟩
  | 10 => ⟨((-1111083320107843/1152921504606846976), (407513132483657/1152921504606846976)), (905/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1189642558846253/4611686018427387904), (-109081595618827/1152921504606846976)), (487/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-291902493461851/4611686018427387904), (428245469399661/18446744073709551616)), (961/18446744073709551616), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580619739151533/10141204801825835211973625643008), (454294915189/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777985996157161/633825300114114700748351602688), (537189199679/79228162514264337593543950336)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944430455942997/19807040628566084398385987584), (1208400457401/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472145122481543/618970019642690137449562112), (5134349919081/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770246248897985/154742504910672534362390528), (5132829181247/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548667493631029/9671406556917033397649408), (4810411965051/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258012973291103/604462909807314587353088), (4207495516883/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943265270933631/37778931862957161709568), (3417076556853/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296592474800139/4722366482869645213696), (2561483528313/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405036159483145/147573952589676412928), (7039778815837/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910921602038661/36893488147419103232), (549579703633/4611686018427387904)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910409350736641/4611686018427387904), (9883573293657/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592063648591989/1152921504606846976), (2468126015765/288230376151711744)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192894837508281/144115188075855872), (4312999232285/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489100569859239/36028797018963968), (12914138259723/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((743036410142705/4503599627370496), (16099226759861/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((555384304713697/1125899906842624), (8017086813615/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103192853464783/1125899906842624), (11944516884815/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1080448340061511/1125899906842624), (23565800023891/562949953421312)), (1/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080448340061511/1125899906842624), (23565800023891/562949953421312)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1034858623521915/1125899906842624), (11307234934159/140737488355328)), (17/2251799813685248), by norm_num⟩
  | 2 => ⟨((471955693512381/562949953421312), (332573494569109/2251799813685248)), (35/2251799813685248), by norm_num⟩
  | 3 => ⟨((1533559811108867/2251799813685248), (278816888285149/1125899906842624)), (35/1125899906842624), by norm_num⟩
  | 4 => ⟨((906319581817621/2251799813685248), (189884718851967/562949953421312)), (131/2251799813685248), by norm_num⟩
  | 5 => ⟨((217173728893821/4503599627370496), (1222817324613397/4503599627370496)), (389/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1286186962137687/18014398509481984), (235868034563553/9007199254740992)), (249/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90648457056371/35184372088832), (-1449323143311105/35184372088832)), (5/35184372088832), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-421611835964985/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23056897279335/8796093022208), (-1474570927075193/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-421611835964985/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-629894969305709/18014398509481984), (287110093551019/4503599627370496)), (49/1125899906842624), by norm_num⟩
  | 1 => ⟨((471749172124603/4503599627370496), (-860104973313893/4503599627370496)), (591/4503599627370496), by norm_num⟩
  | 2 => ⟨((-706617109978025/4503599627370496), (1288322113600361/4503599627370496)), (891/4503599627370496), by norm_num⟩
  | 3 => ⟨((352805946901103/2251799813685248), (-1286489378148631/4503599627370496)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((-528456080716705/4503599627370496), (60218402339129/281474976710656)), (169/1125899906842624), by norm_num⟩
  | 5 => ⟨((316622587231777/4503599627370496), (-577274276317401/4503599627370496)), (815/9007199254740992), by norm_num⟩
  | 6 => ⟨((-632344335404265/18014398509481984), (1152906120171041/18014398509481984)), (819/18014398509481984), by norm_num⟩
  | 7 => ⟨((541238381019887/36028797018963968), (-15418741395421/562949953421312)), (353/18014398509481984), by norm_num⟩
  | 8 => ⟨((-405351321426847/72057594037927936), (739046739453529/72057594037927936)), (133/18014398509481984), by norm_num⟩
  | 9 => ⟨((269849785716925/144115188075855872), (-983993852909237/288230376151711744)), (713/288230376151711744), by norm_num⟩
  | 10 => ⟨((-646718169667057/1152921504606846976), (147389107106947/144115188075855872)), (215/288230376151711744), by norm_num⟩
  | 11 => ⟨((176126772069579/1152921504606846976), (-321118767222245/1152921504606846976)), (943/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-351752436883817/9223372036854775808), (641323903074367/9223372036854775808)), (947/18446744073709551616), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580561275814025/10141204801825835211973625643008), (2699624513701/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777921306339231/633825300114114700748351602688), (1595991475667/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888788397888845/39614081257132168796771975168), (3590159009461/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944251895567017/1237940039285380274899124224), (3813523341979/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770169940480063/154742504910672534362390528), (3812375552487/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548596368949895/9671406556917033397649408), (111652591949/302231454903657293676544)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257951153304987/604462909807314587353088), (390631734133/75557863725914323419136)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886430860100805/75557863725914323419136), (5075928405899/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648259195738907/2361183241434822606848), (1902474305527/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101252742107707/36893488147419103232), (2614279913231/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227714862114311/9223372036854775808), (6530836052819/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820681118090011/9223372036854775808), (7340507868747/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397982221748069/288230376151711744), (7332161909323/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((596390043732191/72057594037927936), (6406262640627/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488934757158723/36028797018963968), (599416332405/2251799813685248)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485876555353011/9007199254740992), (1494450207913/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((277647188681429/562949953421312), (11906628339791/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205927557560793/2251799813685248), (35475816348511/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((540075559198573/562949953421312), (69980136650681/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540075559198573/562949953421312), (69980136650681/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2070347686521489/2251799813685248), (134273255392291/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((947755260043701/1125899906842624), (61726695679973/562949953421312)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568521833487735/2251799813685248), (415680293853961/2251799813685248)), (13/562949953421312), by norm_num⟩
  | 4 => ⟨((1015841027042979/2251799813685248), (579095541884321/2251799813685248)), (93/2251799813685248), by norm_num⟩
  | 5 => ⟨((618688518721767/4503599627370496), (1044975679362955/4503599627370496)), (265/4503599627370496), by norm_num⟩
  | 6 => ⟨((-629894969305709/18014398509481984), (287110093551019/4503599627370496)), (49/1125899906842624), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-23056897279335/8796093022208), (-1474570927075193/35184372088832)), (5/35184372088832), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-428478441126635/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93729658996451/35184372088832), (-1498586610401299/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-428478441126635/140737488355328), 0), (1/140737488355328), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14112601162861/1125899906842624), (1234619941163335/18014398509481984)), (599/18014398509481984), by norm_num⟩
  | 1 => ⟨((-10741532723743/281474976710656), (-1879414056466273/9007199254740992)), (459/4503599627370496), by norm_num⟩
  | 2 => ⟨((2043927337061/35184372088832), (1430479566171091/4503599627370496)), (11/70368744177664), by norm_num⟩
  | 3 => ⟨((-265505392587029/4503599627370496), (-1451709045304251/4503599627370496)), (45/281474976710656), by norm_num⟩
  | 4 => ⟨((789391723699/17592186044416), (552470095184355/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 5 => ⟨((-246100051451369/9007199254740992), (-1345606080767971/9007199254740992)), (677/9007199254740992), by norm_num⟩
  | 6 => ⟨((249752376189527/18014398509481984), (1365575968411721/18014398509481984)), (173/4503599627370496), by norm_num⟩
  | 7 => ⟨((-217250489481073/36028797018963968), (-4640096736881/140737488355328)), (303/18014398509481984), by norm_num⟩
  | 8 => ⟨((165355997457881/72057594037927936), (226030058058263/18014398509481984)), (929/144115188075855872), by norm_num⟩
  | 9 => ⟨((-55936671608073/72057594037927936), (-611692074096275/144115188075855872)), (633/288230376151711744), by norm_num⟩
  | 10 => ⟨((34060090360469/144115188075855872), (744924097825475/576460752303423488)), (97/144115188075855872), by norm_num⟩
  | 11 => ⟨((-37707894303031/576460752303423488), (-412352387314643/1152921504606846976)), (865/4611686018427387904), by norm_num⟩
  | 12 => ⟨((306140080759683/18446744073709551616), (836944063618833/9223372036854775808)), (883/18446744073709551616), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98781604094205/633825300114114700748351602688), (113156567659/633825300114114700748351602688)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777858562437345/633825300114114700748351602688), (2140554652847/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944358996471059/19807040628566084398385987584), (300946081325/4951760157141521099596496896)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472107306855045/618970019642690137449562112), (2557346626047/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110630978013713/9671406556917033397649408), (2556565026001/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548527008155499/9671406556917033397649408), (149746848099/604462909807314587353088)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628945375281655/302231454903657293676544), (523906519343/151115727451828646838272)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886333245034671/75557863725914323419136), (1701918621861/37778931862957161709568)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324111412905123/1180591620717411303424), (637879481861/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619944621533071/590295810358705651712), (876532129801/147573952589676412928)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821595977633497/73786976294838206464), (4379350111825/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910272203404045/4611686018427387904), (2461110399769/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795897068840085/576460752303423488), (4916541567725/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192664383311987/144115188075855872), (4295592790163/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488765589647163/36028797018963968), (1607661783279/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((742836372086901/4503599627370496), (8016055507989/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220792703908713/4503599627370496), (7982765593541/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205406945564775/2251799813685248), (23782477090415/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1079742368383671/1125899906842624), (46905442694241/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079742368383671/1125899906842624), (46905442694241/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069977170905079/2251799813685248), (89965002176421/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((1899241558001737/2251799813685248), (2584397982919/35184372088832)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((198716645864057/281474976710656), (139505006347225/1125899906842624)), (45/2251799813685248), by norm_num⟩
  | 4 => ⟨((1087754310978961/2251799813685248), (393952844640417/2251799813685248)), (19/562949953421312), by norm_num⟩
  | 5 => ⟨((913056827703185/4503599627370496), (380605684817715/2251799813685248)), (201/4503599627370496), by norm_num⟩
  | 6 => ⟨((14112601162861/1125899906842624), (1234619941163335/18014398509481984)), (599/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93729658996451/35184372088832), (-1498586610401299/35184372088832)), (5/35184372088832), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log22 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-870051102570681/281474976710656), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23790459835917/8796093022208), (-1521484872434881/35184372088832)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-870051102570681/281474976710656), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((890614998916905/18014398509481984), (811736414866867/18014398509481984)), (523/18014398509481984), by norm_num⟩
  | 1 => ⟨((-86029024101557/562949953421312), (-627277929822591/4503599627370496)), (409/4503599627370496), by norm_num⟩
  | 2 => ⟨((531838731437797/2251799813685248), (484735677784087/2251799813685248)), (639/4503599627370496), by norm_num⟩
  | 3 => ⟨((-1095957398142975/4503599627370496), (-998892372458687/4503599627370496)), (665/4503599627370496), by norm_num⟩
  | 4 => ⟨((846912711183015/4503599627370496), (385952341200701/2251799813685248)), (65/562949953421312), by norm_num⟩
  | 5 => ⟨((-261784314455549/2251799813685248), (-954396057299521/9007199254740992)), (325/4503599627370496), by norm_num⟩
  | 6 => ⟨((1078915239473873/18014398509481984), (983359576810205/18014398509481984)), (677/18014398509481984), by norm_num⟩
  | 7 => ⟨((-952849373939713/36028797018963968), (-868458913953375/36028797018963968)), (151/9007199254740992), by norm_num⟩
  | 8 => ⟨((368162233312943/36028797018963968), (671110843006835/72057594037927936)), (59/9007199254740992), by norm_num⟩
  | 9 => ⟨((-505780041286007/144115188075855872), (-460984912587381/144115188075855872)), (655/288230376151711744), by norm_num⟩
  | 10 => ⟨((156338757967637/144115188075855872), (569969574066107/576460752303423488)), (409/576460752303423488), by norm_num⟩
  | 11 => ⟨((-702908709793857/2305843009213693952), (-640654600203961/2305843009213693952)), (465/2305843009213693952), by norm_num⟩
  | 12 => ⟨((181060055234011/2305843009213693952), (41256053482703/576460752303423488)), (121/2305843009213693952), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790226321341111/5070602400912917605986812821504), (962755325133/10141204801825835211973625643008)), (1/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777797638378221/633825300114114700748351602688), (569093075973/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888649566143487/39614081257132168796771975168), (640080603275/19807040628566084398385987584)), (1/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888356673617961/2475880078570760549798248448), (1359796210815/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221252907826981/19342813113834066795298816), (1359374471035/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548459325228107/9671406556917033397649408), (1273965648657/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257831706425619/604462909807314587353088), (1114272227885/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886237632532387/75557863725914323419136), (1809853336943/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162046779295589/590295810358705651712), (169582034991/590295810358705651712)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619846896898133/590295810358705651712), (932105446879/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455368632980071/18446744073709551616), (2328477794055/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227551094378201/1152921504606846976), (2617084306527/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591659701633939/1152921504606846976), (653505307703/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192548115947395/144115188075855872), (2283827339693/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((744296954075897/18014398509481984), (3418870325095/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485462881769675/9007199254740992), (4261590689085/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220387118746725/4503599627370496), (265227981647/140737488355328)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204833642443969/2251799813685248), (12641597049807/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1079238395523523/1125899906842624), (24928014448597/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079238395523523/1125899906842624), (24928014448597/2251799813685248)), (26711470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2068745464527135/2251799813685248), (23894904114999/1125899906842624)), (15/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899557813814093/2251799813685248), (21952428547507/562949953421312)), (29/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598991757719067/2251799813685248), (18518478830215/281474976710656)), (13/562949953421312), by norm_num⟩
  | 4 => ⟨((562844629021711/1125899906842624), (210398063522695/2251799813685248)), (41/1125899906842624), by norm_num⟩
  | 5 => ⟨((543080674004881/2251799813685248), (420717398733635/4503599627370496)), (195/4503599627370496), by norm_num⟩
  | 6 => ⟨((890614998916905/18014398509481984), (811736414866867/18014398509481984)), (523/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-23790459835917/8796093022208), (-1521484872434881/35184372088832)), (3/17592186044416), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-441281580702527/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-48265172889339/17592186044416), (-771682545472671/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-441281580702527/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151110937455223/18014398509481984), (16944768471317/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | 1 => ⟨((-225581355392727/1125899906842624), (-53130223532073/2251799813685248)), (421/9007199254740992), by norm_num⟩
  | 2 => ⟨((1414618070110707/4503599627370496), (83294754287919/2251799813685248)), (335/4503599627370496), by norm_num⟩
  | 3 => ⟨((-1478508925526993/4503599627370496), (-43528370047835/1125899906842624)), (89/1125899906842624), by norm_num⟩
  | 4 => ⟨((1158964046047377/4503599627370496), (68241476256905/2251799813685248)), (71/1125899906842624), by norm_num⟩
  | 5 => ⟨((-726785012570279/4503599627370496), (-85588301635997/4503599627370496)), (181/4503599627370496), by norm_num⟩
  | 6 => ⟨((1519220135425403/18014398509481984), (178907749820579/18014398509481984)), (3/140737488355328), by norm_num⟩
  | 7 => ⟨((-340250424810675/9007199254740992), (-160275489927807/36028797018963968)), (349/36028797018963968), by norm_num⟩
  | 8 => ⟨((266713309740327/18014398509481984), (62817858952981/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 9 => ⟨((-371679128889829/72057594037927936), (-43770007423139/72057594037927936)), (393/288230376151711744), by norm_num⟩
  | 10 => ⟨((932318207052515/576460752303423488), (219584968170285/1152921504606846976)), (125/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1063010307497671/2305843009213693952), (-62591581600265/1152921504606846976)), (289/2305843009213693952), by norm_num⟩
  | 12 => ⟨((1111020890210671/9223372036854775808), (4088657126531/288230376151711744)), (307/9223372036854775808), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988610693/5070602400912917605986812821504), (19087004123/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777738420121871/633825300114114700748351602688), (90254157927/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888582998349855/39614081257132168796771975168), (203024002721/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888286014847395/2475880078570760549798248448), (215652674447/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884976340981981/77371252455336267181195264), (215584841653/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548393238809157/9671406556917033397649408), (202038746889/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257773963684879/604462909807314587353088), (176711895341/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471535988957501/18889465931478580854784), (143510943369/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648152056271033/2361183241434822606848), (215148411871/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619750699647553/590295810358705651712), (295637446265/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821354615279495/73786976294838206464), (184629806999/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910137150850039/4611686018427387904), (415022557781/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795762906653659/576460752303423488), (414529997521/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192431597747743/144115188075855872), (181080203363/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488420395188793/36028797018963968), (542135897785/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((742624097273445/4503599627370496), (675741049573/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219964321925835/4503599627370496), (672856642333/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((137763485729287/140737488355328), (2004209489525/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((2157305633735005/2251799813685248), (3951345317853/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157305633735005/2251799813685248), (3951345317853/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066769859350157/2251799813685248), (7571063345179/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((1896918324869863/2251799813685248), (434309408577/70368744177664)), (23/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597880041425275/2251799813685248), (11707605207691/1125899906842624)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((1133614249007683/2251799813685248), (33230926800087/2251799813685248)), (59/2251799813685248), by norm_num⟩
  | 5 => ⟨((1140400637084991/4503599627370496), (66917231095527/4503599627370496)), (123/4503599627370496), by norm_num⟩
  | 6 => ⟨((1151110937455223/18014398509481984), (16944768471317/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-48265172889339/17592186044416), (-771682545472671/17592186044416)), (5/35184372088832), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-894542627882399/281474976710656), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-97840599924637/35184372088832), (-391078487243411/8796093022208)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-894542627882399/281474976710656), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((495720405082419/9007199254740992), (-513862722439507/18014398509481984)), (393/18014398509481984), by norm_num⟩
  | 1 => ⟨((-196928266519227/1125899906842624), (408270848330475/4503599627370496)), (317/4503599627370496), by norm_num⟩
  | 2 => ⟨((1251697263430421/4503599627370496), (-162188341669509/1125899906842624)), (255/2251799813685248), by norm_num⟩
  | 3 => ⟨((-331496773540091/1125899906842624), (687257707307419/4503599627370496)), (547/4503599627370496), by norm_num⟩
  | 4 => ⟨((65844661931067/281474976710656), (-546035497286123/4503599627370496)), (55/562949953421312), by norm_num⟩
  | 5 => ⟨((-1339250432371155/9007199254740992), (694132081462443/9007199254740992)), (283/4503599627370496), by norm_num⟩
  | 6 => ⟨((1418736655464097/18014398509481984), (-183832426688259/4503599627370496)), (303/9007199254740992), by norm_num⟩
  | 7 => ⟨((-644117351736101/18014398509481984), (166922670793937/9007199254740992)), (139/9007199254740992), by norm_num⟩
  | 8 => ⟨((1023519808439245/72057594037927936), (-530489233288581/72057594037927936)), (447/72057594037927936), by norm_num⟩
  | 9 => ⟨((-180711169313741/36028797018963968), (749299262138275/288230376151711744)), (319/144115188075855872), by norm_num⟩
  | 10 => ⟨((918895718118705/576460752303423488), (-476262678023087/576460752303423488)), (205/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1061927293329991/2305843009213693952), (550395792052015/2305843009213693952)), (479/2305843009213693952), by norm_num⟩
  | 12 => ⟨((281238508509867/2305843009213693952), (-583062485046099/9223372036854775808)), (513/9223372036854775808), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790176734201499/5070602400912917605986812821504), (-622882012437/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444420201052663/158456325028528675187087900672), (-736289365365/633825300114114700748351602688)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944259090444711/19807040628566084398385987584), (-828127741707/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236027143195769/309485009821345068724781056), (-439818149443/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769883811878909/154742504910672534362390528), (-879355846029/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774164336130501/4835703278458516698824704), (-206024562453/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314429366780953/151115727451828646838272), (-90098531727/75557863725914323419136)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886052147384779/75557863725914323419136), (-9146273413/590295810358705651712)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296235254891755/4722366482869645213696), (-54847148183/295147905179352825856)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619656018286817/590295810358705651712), (-602922510685/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821236260524367/73786976294838206464), (-1506118899707/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820141148535857/9223372036854775808), (-846376355693/4611686018427387904)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795696327632015/576460752303423488), (-845358142101/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192315079247693/144115188075855872), (-738544522513/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((744122803852087/18014398509481984), (-1105533169953/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((371257423675467/2251799813685248), (-2755858646021/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219527281923625/4503599627370496), (-5487867759977/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((550890033074599/562949953421312), (-4086216798425/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((538998541241205/562949953421312), (-16108923531619/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((538998541241205/562949953421312), (-16108923531619/2251799813685248)), (26711470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((16126167560835/17592186044416), (-7711774582927/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((472928518493831/562949953421312), (-14138250789491/562949953421312)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((793894704533867/1125899906842624), (-47509601585945/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((1115572771304693/2251799813685248), (-133999908462085/2251799813685248)), (73/2251799813685248), by norm_num⟩
  | 5 => ⟨((272348062459701/1125899906842624), (-132770815886139/2251799813685248)), (163/4503599627370496), by norm_num⟩
  | 6 => ⟨((495720405082419/9007199254740992), (-513862722439507/18014398509481984)), (393/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-97840599924637/35184372088832), (-391078487243411/8796093022208)), (3/17592186044416), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-453016498919635/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-49548679569335/17592186044416), (-792203754507217/17592186044416)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-453016498919635/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((268409298037839/9007199254740992), (-467134527842773/9007199254740992)), (277/9007199254740992), by norm_num⟩
  | 1 => ⟨((-215994050155961/2251799813685248), (751824019317161/4503599627370496)), (225/2251799813685248), by norm_num⟩
  | 2 => ⟨((86907253295299/562949953421312), (-605007040083813/2251799813685248)), (365/2251799813685248), by norm_num⟩
  | 3 => ⟨((-745983084367827/4503599627370496), (649147511733617/2251799813685248)), (395/2251799813685248), by norm_num⟩
  | 4 => ⟨((600306729008053/4503599627370496), (-1044762616146343/4503599627370496)), (641/4503599627370496), by norm_num⟩
  | 5 => ⟨((-772925127003891/9007199254740992), (1345184451135807/9007199254740992)), (13/140737488355328), by norm_num⟩
  | 6 => ⟨((414658334291001/9007199254740992), (-90207952286451/1125899906842624)), (225/4503599627370496), by norm_num⟩
  | 7 => ⟨((-381352482236977/18014398509481984), (1327397471203297/36028797018963968)), (835/36028797018963968), by norm_num⟩
  | 8 => ⟨((306881571456521/36028797018963968), (-1068181907511869/72057594037927936)), (339/36028797018963968), by norm_num⟩
  | 9 => ⟨((-109757074606551/36028797018963968), (382038324294617/72057594037927936)), (489/144115188075855872), by norm_num⟩
  | 10 => ⟨((141317757623713/144115188075855872), (-61486696312255/36028797018963968)), (635/576460752303423488), by norm_num⟩
  | 11 => ⟨((-661649910748441/2305843009213693952), (1151523143624903/2305843009213693952)), (375/1152921504606846976), by norm_num⟩
  | 12 => ⟨((709922967411453/9223372036854775808), (-617768334798405/4611686018427387904)), (811/9223372036854775808), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940098043/10141204801825835211973625643008), (-683397415511/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222203087064847/79228162514264337593543950336), (-1615550111869/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118028438401381/2475880078570760549798248448), (-1817053539417/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472037492171409/618970019642690137449562112), (-482516238403/618970019642690137449562112)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442454141195567/38685626227668133590597632), (-964720770431/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774132776788797/4835703278458516698824704), (-904094670229/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628831081914633/302231454903657293676544), (-1581503874871/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885962140121635/75557863725914323419136), (-2568703575421/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648083813819351/2361183241434822606848), (-962721568829/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619562833212289/590295810358705651712), (-2645723147777/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910559741680135/36893488147419103232), (-3304514313715/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820009368415897/9223372036854775808), (-232122036265/576460752303423488)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49726886540433/36028797018963968), (-3709425230895/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((596099380940423/72057594037927936), (-12658831725/562949953421312)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((744035001101279/18014398509481984), (-4850836827315/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((742404111065133/4503599627370496), (-6045815442767/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219078482915969/4503599627370496), (-6019299139813/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202872449667437/2251799813685248), (-17925871413379/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((538640440172723/562949953421312), (-35326959246681/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538640440172723/562949953421312), (-35326959246681/2251799813685248)), (26711470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515242114149863/562949953421312), (-67602914834439/2251799813685248)), (15/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884279765553305/2251799813685248), (-15468457076113/281474976710656)), (29/2251799813685248), by norm_num⟩
  | 3 => ⟨((1569942732418915/2251799813685248), (-1617978011173/17592186044416)), (53/2251799813685248), by norm_num⟩
  | 4 => ⟨((1075508252265499/2251799813685248), (-36097458460271/281474976710656)), (85/2251799813685248), by norm_num⟩
  | 5 => ⟨((476651742175955/2251799813685248), (-275854819590169/2251799813685248)), (207/4503599627370496), by norm_num⟩
  | 6 => ⟨((268409298037839/9007199254740992), (-467134527842773/9007199254740992)), (277/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-49548679569335/17592186044416), (-792203754507217/17592186044416)), (3/17592186044416), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1834145294321331/562949953421312), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-50152410391599/17592186044416), (-801856440073537/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1834145294321331/562949953421312), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-56565615893963/36028797018963968), (-2081554497735689/36028797018963968)), (1121/36028797018963968), by norm_num⟩
  | 1 => ⟨((46074059328793/9007199254740992), (1695476375693923/9007199254740992)), (919/9007199254740992), by norm_num⟩
  | 2 => ⟨((-18764216648967/2251799813685248), (-1381006427486395/4503599627370496)), (753/4503599627370496), by norm_num⟩
  | 3 => ⟨((20378543100895/2251799813685248), (1499817420126279/4503599627370496)), (823/4503599627370496), by norm_num⟩
  | 4 => ⟨((-16598815181737/2251799813685248), (-1221637486044435/4503599627370496)), (675/4503599627370496), by norm_num⟩
  | 5 => ⟨((43264433823101/9007199254740992), (49752660799983/281474976710656)), (885/9007199254740992), by norm_num⟩
  | 6 => ⟨((-46986567352835/18014398509481984), (-1729055700371005/18014398509481984)), (967/18014398509481984), by norm_num⟩
  | 7 => ⟨((43739077835939/36028797018963968), (804775770203583/18014398509481984)), (453/18014398509481984), by norm_num⟩
  | 8 => ⟨((-35626534518381/72057594037927936), (-1311018575391933/72057594037927936)), (743/72057594037927936), by norm_num⟩
  | 9 => ⟨((51588750567129/288230376151711744), (949205573725847/144115188075855872)), (541/144115188075855872), by norm_num⟩
  | 10 => ⟨((-33616225924723/576460752303423488), (-1237041357450751/576460752303423488)), (355/288230376151711744), by norm_num⟩
  | 11 => ⟨((39827239747887/2305843009213693952), (1465600059672613/2305843009213693952)), (423/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-21626831990257/4611686018427387904), (-795844413423903/4611686018427387904)), (231/2305843009213693952), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236909883/10141204801825835211973625643008), (-130095435331/633825300114114700748351602688)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777570011173537/633825300114114700748351602688), (-1230111627027/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472098351983863/9903520314283042199192993792), (-2767070116029/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236010549345203/309485009821345068724781056), (-1469578547443/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884875429691843/77371252455336267181195264), (-734548945713/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387050953801895/2417851639229258349412352), (-2753537551299/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157201000418293/75557863725914323419136), (-1204162405547/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942936934131259/37778931862957161709568), (-1955807623535/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324025298905451/1180591620717411303424), (-2932038888577/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809735559542295/295147905179352825856), (-2014418684481/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910502143291705/36893488147419103232), (-2515987839861/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819879011817479/9223372036854775808), (-1413845010521/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591129064940859/1152921504606846976), (-5648396894441/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((596041403907291/72057594037927936), (-2467250839919/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((371973488558631/9007199254740992), (-3693043688735/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484584477048701/9007199254740992), (-9205253776167/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109310007353541/2251799813685248), (-18328674983573/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202157571619069/2251799813685248), (-27289247242367/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((538256227018305/562949953421312), (-6721039339377/281474976710656)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538256227018305/562949953421312), (-6721039339377/281474976710656)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1028649437432617/1125899906842624), (-51409774591415/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874903255240133/2251799813685248), (-93938431632517/1125899906842624)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((386353671362165/562949953421312), (-78215421366305/562949953421312)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((1017152635793047/2251799813685248), (-429435192501311/2251799813685248)), (5/140737488355328), by norm_num⟩
  | 5 => ⟨((23597371277609/140737488355328), (-387957344432091/2251799813685248)), (103/2251799813685248), by norm_num⟩
  | 6 => ⟨((-56565615893963/36028797018963968), (-2081554497735689/36028797018963968)), (1121/36028797018963968), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50152410391599/17592186044416), (-801856440073537/17592186044416)), (5/35184372088832), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-463847802550345/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6341669175493/2199023255552), (-1622289570365045/35184372088832)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-463847802550345/140737488355328), 0), (5/562949953421312), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-132734840755537/4503599627370496), (-214015055486613/4503599627370496)), (385/9007199254740992), by norm_num⟩
  | 1 => ⟨((437472381565313/4503599627370496), (705358709752741/4503599627370496)), (319/2251799813685248), by norm_num⟩
  | 2 => ⟨((-180229700377709/1125899906842624), (-581186809840083/2251799813685248)), (529/2251799813685248), by norm_num⟩
  | 3 => ⟨((396005127235845/2251799813685248), (638498971302131/2251799813685248)), (1169/4503599627370496), by norm_num⟩
  | 4 => ⟨((-163146037183829/1125899906842624), (-526097112130851/2251799813685248)), (969/4503599627370496), by norm_num⟩
  | 5 => ⟨((860324358228763/9007199254740992), (693572102903709/4503599627370496)), (1285/9007199254740992), by norm_num⟩
  | 6 => ⟨((-29536341005957/562949953421312), (-761966835327397/9007199254740992)), (355/4503599627370496), by norm_num⟩
  | 7 => ⟨((445014681482553/18014398509481984), (717519539012767/18014398509481984)), (21/562949953421312), by norm_num⟩
  | 8 => ⟨((-366673948285843/36028797018963968), (-591206837189177/36028797018963968)), (557/36028797018963968), by norm_num⟩
  | 9 => ⟨((537110007361709/144115188075855872), (433004730987091/72057594037927936)), (821/144115188075855872), by norm_num⟩
  | 10 => ⟨((-708090785345031/576460752303423488), (-1141690364433233/576460752303423488)), (17/9007199254740992), by norm_num⟩
  | 11 => ⟨((424318493603293/1152921504606846976), (1368300070058533/2305843009213693952)), (1311/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-233080755690859/2305843009213693952), (-375807817887935/2305843009213693952)), (181/1152921504606846976), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790109610521411/5070602400912917605986812821504), (-2769281546963/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777516669622997/633825300114114700748351602688), (-1636461882681/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944166638930927/19807040628566084398385987584), (-3681118312703/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888020341260913/2475880078570760549798248448), (-3910037169421/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769686620178767/154742504910672534362390528), (-1954371389639/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774071696914581/4835703278458516698824704), (-3663071563991/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628777468863435/302231454903657293676544), (-400476673363/75557863725914323419136)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235723408483147/9444732965739290427392), (-325226328693/4722366482869645213696)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648017961550133/2361183241434822606848), (-3900463575671/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619380846590507/590295810358705651712), (-5359479546225/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910445331631073/36893488147419103232), (-6693866525689/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819750111735807/9223372036854775808), (-1880766793877/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49718713315799/36028797018963968), (-1878415208503/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((297991836903071/36028797018963968), (-3281942067747/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487717773652607/36028797018963968), (-307022518263/1125899906842624)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((742179522815325/4503599627370496), (-12244039096677/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218153643620613/4503599627370496), (-24377785674501/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201419623600033/2251799813685248), (-18145984346027/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((2100974325023/2199023255552), (-71491212072997/2251799813685248)), (1/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2100974325023/2199023255552), (-71491212072997/2251799813685248)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2053202544928273/2251799813685248), (-34151799134211/562949953421312)), (17/2251799813685248), by norm_num⟩
  | 2 => ⟨((1863833160855269/2251799813685248), (-31139784482655/281474976710656)), (17/1125899906842624), by norm_num⟩
  | 3 => ⟨((757574921935881/1125899906842624), (-206197238628145/1125899906842624)), (65/2251799813685248), by norm_num⟩
  | 4 => ⟨((943960396299353/2251799813685248), (-277484447787499/1125899906842624)), (7/140737488355328), by norm_num⟩
  | 5 => ⟨((32366928844113/281474976710656), (-930577674652947/4503599627370496)), (299/4503599627370496), by norm_num⟩
  | 6 => ⟨((-132734840755537/4503599627370496), (-214015055486613/4503599627370496)), (385/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6341669175493/2199023255552), (-1622289570365045/35184372088832)), (3/17592186044416), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((534608460063907/1125899906842624), (330146653767965/2251799813685248)), (167/1125899906842624), by norm_num⟩
  | 1 => ⟨((819703998447757/2251799813685248), (-457680444461131/4503599627370496)), (117/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1136351030835553/9007199254740992), (317239909675655/9007199254740992)), (329/9007199254740992), by norm_num⟩
  | 3 => ⟨((525105675433367/18014398509481984), (-293191931937029/36028797018963968)), (307/36028797018963968), by norm_num⟩
  | 4 => ⟨((-45496939802833/9007199254740992), (203225160985075/144115188075855872)), (215/144115188075855872), by norm_num⟩
  | 5 => ⟨((1614647068080089/2305843009213693952), (-225383915769033/1152921504606846976)), (241/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-1492250750452127/18446744073709551616), (208298967678487/9223372036854775808)), (225/9223372036854775808), by norm_num⟩
  | 7 => ⟨((295528400104101/36893488147419103232), (-330015639222607/147573952589676412928)), (361/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-204844677307549/295147905179352825856), (114374704933919/590295810358705651712)), (505/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1009688963757791/18889465931478580854784), (-281879126230477/18889465931478580854784)), (315/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-139972611694241/37778931862957161709568), (156306977284285/151115727451828646838272)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((564489432154037/2417851639229258349412352), (-157590895427563/2417851639229258349412352)), (361/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-130424752784485/9671406556917033397649408), (145644913130043/38685626227668133590597632)), (337/77371252455336267181195264), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial2 : Sound J_initial2 F_initial2 c := by
  apply sound_round (sound_add (A_q0 hcre) (A_term2 hcre) S_q0 S_term2)
  intro k
  fin_cases k <;> norm_num [J_initial2, J_q0, J_term2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((514008472969689/4503599627370496), (22081188539383/1125899906842624)), (861/2251799813685248), by norm_num⟩
  | 1 => ⟨((1712010833710027/2251799813685248), (42672809253025/1125899906842624)), (411/1125899906842624), by norm_num⟩
  | 2 => ⟨((-774237384949729/2251799813685248), (-46637117680235/1125899906842624)), (819/4503599627370496), by norm_num⟩
  | 3 => ⟨((980532042747191/9007199254740992), (89753099834233/4503599627370496)), (281/4503599627370496), by norm_num⟩
  | 4 => ⟨((-121346067108251/4503599627370496), (-226927491442711/36028797018963968)), (593/36028797018963968), by norm_num⟩
  | 5 => ⟨((1588333692144595/288230376151711744), (107962203481147/72057594037927936)), (1019/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1108751687795793/1152921504606846976), (-331520494845055/1152921504606846976)), (185/288230376151711744), by norm_num⟩
  | 7 => ⟨((1348882575489063/9223372036854775808), (214154134293247/4611686018427387904)), (927/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-181492794966033/9223372036854775808), (-478907841384457/73786976294838206464)), (511/36893488147419103232), by norm_num⟩
  | 9 => ⟨((699714389567899/295147905179352825856), (472827474397415/590295810358705651712)), (251/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-152463610247297/590295810358705651712), (-209210281397043/2361183241434822606848)), (889/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((969376665507263/37778931862957161709568), (335754548481521/37778931862957161709568)), (359/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-1415190473419313/604462909807314587353088), (-493149964114253/604462909807314587353088)), (531/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial3 : Sound J_initial3 F_initial3 c := by
  apply sound_round (sound_add (A_initial2 hcre) (A_term3 hcre) S_initial2 S_term3)
  intro k
  fin_cases k <;> norm_num [J_initial3, J_initial2, J_term3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((414829854683199/1125899906842624), (-302605379751483/2251799813685248)), (1049/2251799813685248), by norm_num⟩
  | 1 => ⟨((459070890394943/1125899906842624), (566067804418017/2251799813685248)), (17/35184372088832), by norm_num⟩
  | 2 => ⟨((-447938578368679/4503599627370496), (-852970926315927/4503599627370496)), (299/1125899906842624), by norm_num⟩
  | 3 => ⟨((-4572421033891/1125899906842624), (397705663939233/4503599627370496)), (919/9007199254740992), by norm_num⟩
  | 4 => ⟨((219623638429691/18014398509481984), (-1080753297665057/36028797018963968)), (1099/36028797018963968), by norm_num⟩
  | 5 => ⟨((-384795365626803/72057594037927936), (145355940924755/18014398509481984)), (271/36028797018963968), by norm_num⟩
  | 6 => ⟨((111355378813213/72057594037927936), (-520451517802639/288230376151711744)), (913/576460752303423488), by norm_num⟩
  | 7 => ⟨((-807635799653303/2305843009213693952), (400168679982593/1152921504606846976)), (21/72057594037927936), by norm_num⟩
  | 8 => ⟨((612061221009601/9223372036854775808), (-270197448767203/4611686018427387904)), (439/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-100367198391677/9223372036854775808), (162810968403583/18446744073709551616)), (259/36893488147419103232), by norm_num⟩
  | 10 => ⟨((116503086472825/73786976294838206464), (-709007331959629/590295810358705651712)), (139/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-972224293396705/4722366482869645213696), (352034153076835/2361183241434822606848)), (273/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((922063416297201/37778931862957161709568), (-642731268093161/37778931862957161709568)), (497/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial4 : Sound J_initial4 F_initial4 c := by
  apply sound_round (sound_add (A_initial3 hcre) (A_term4 hcre) S_initial3 S_term4)
  intro k
  fin_cases k <;> norm_num [J_initial4, J_initial3, J_term4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((706015934380883/4503599627370496), (-26750560161327/2251799813685248)), (2775/4503599627370496), by norm_num⟩
  | 1 => ⟨((842641582837817/1125899906842624), (122096599441951/2251799813685248)), (1639/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1682605007401001/4503599627370496), (-34606709249599/1125899906842624)), (2093/4503599627370496), by norm_num⟩
  | 3 => ⟨((1288166605125035/9007199254740992), (28735096242911/9007199254740992)), (473/2251799813685248), by norm_num⟩
  | 4 => ⟨((-846424558534409/18014398509481984), (153164496091313/36028797018963968)), (2681/36028797018963968), by norm_num⟩
  | 5 => ⟨((987795342114027/72057594037927936), (-212941867540397/72057594037927936)), (1571/72057594037927936), by norm_num⟩
  | 6 => ⟨((-250808471747/70368744177664), (331869924364937/288230376151711744)), (1573/288230376151711744), by norm_num⟩
  | 7 => ⟨((475311721539551/576460752303423488), (-383693287220267/1152921504606846976)), (687/576460752303423488), by norm_num⟩
  | 8 => ⟨((-48994625825971/288230376151711744), (180295567649263/2305843009213693952)), (1063/4611686018427387904), by norm_num⟩
  | 9 => ⟨((289454623801485/9223372036854775808), (-144197862892877/9223372036854775808)), (1477/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-770824258625261/147573952589676412928), (403699494987995/147573952589676412928)), (233/36893488147419103232), by norm_num⟩
  | 11 => ⟨((465963873952797/590295810358705651712), (-62998328389659/147573952589676412928)), (537/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-1030193151541779/9444732965739290427392), (568933010482755/9444732965739290427392)), (1139/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial5 : Sound J_initial5 F_initial5 c := by
  apply sound_round (sound_add (A_initial4 hcre) (A_term5 hcre) S_initial4 S_term5)
  intro k
  fin_cases k <;> norm_num [J_initial5, J_initial4, J_term5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((25671532293473/70368744177664), (8716500764889/4503599627370496)), (2955/4503599627370496), by norm_num⟩
  | 1 => ⟨((1691755558312967/4503599627370496), (66357093573727/2251799813685248)), (451/562949953421312), by norm_num⟩
  | 2 => ⟨((-178592457584277/4503599627370496), (-38555049548913/4503599627370496)), (599/1125899906842624), by norm_num⟩
  | 3 => ⟨((-508385880189597/9007199254740992), (-1415037255281/140737488355328)), (1131/4503599627370496), by norm_num⟩
  | 4 => ⟨((763070405229435/18014398509481984), (366916886577181/36028797018963968)), (3361/36028797018963968), by norm_num⟩
  | 5 => ⟨((-1319266931484959/72057594037927936), (-366139015429671/72057594037927936)), (2071/72057594037927936), by norm_num⟩
  | 6 => ⟨((432122237401037/72057594037927936), (514864884624495/288230376151711744)), (2183/288230376151711744), by norm_num⟩
  | 7 => ⟨((-935468721710499/576460752303423488), (-142763743643077/288230376151711744)), (1007/576460752303423488), by norm_num⟩
  | 8 => ⟨((871932602489747/2305843009213693952), (264222337020155/2305843009213693952)), (103/288230376151711744), by norm_num⟩
  | 9 => ⟨((-179257030178453/2305843009213693952), (-422063800223101/18446744073709551616)), (607/9223372036854775808), by norm_num⟩
  | 10 => ⟨((528643930583655/36893488147419103232), (74412540684159/18446744073709551616)), (407/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-353503825911375/147573952589676412928), (-23551913968641/36893488147419103232)), (499/295147905179352825856), by norm_num⟩
  | 12 => ⟨((865275209918995/2361183241434822606848), (54198182504945/590295810358705651712)), (1133/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial6 : Sound J_initial6 F_initial6 c := by
  apply sound_round (sound_add (A_initial5 hcre) (A_term6 hcre) S_initial5 S_term6)
  intro k
  fin_cases k <;> norm_num [J_initial6, J_initial5, J_term6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((154458325414911/562949953421312), (-351795116682877/2251799813685248)), (3595/4503599627370496), by norm_num⟩
  | 1 => ⟨((2426120184465/4398046511104), (379699772583179/1125899906842624)), (19/17592186044416), by norm_num⟩
  | 2 => ⟨((-237437097457461/1125899906842624), (-346788347457297/1125899906842624)), (1813/2251799813685248), by norm_num⟩
  | 3 => ⟨((492014223184309/9007199254740992), (414734603473927/2251799813685248)), (967/2251799813685248), by norm_num⟩
  | 4 => ⟨((-210273951906199/18014398509481984), (-759363618121533/9007199254740992)), (3255/18014398509481984), by norm_num⟩
  | 5 => ⟨((24495699871975/9007199254740992), (570925324018035/18014398509481984)), (2271/36028797018963968), by norm_num⟩
  | 6 => ⟨((-59295489132689/72057594037927936), (-182668909524605/18014398509481984)), (169/9007199254740992), by norm_num⟩
  | 7 => ⟨((157393839989691/576460752303423488), (406417939875299/144115188075855872)), (2813/576460752303423488), by norm_num⟩
  | 8 => ⟨((-191373572677747/2305843009213693952), (-1595288668575031/2305843009213693952)), (1297/1152921504606846976), by norm_num⟩
  | 9 => ⟨((101285556934563/4611686018427387904), (349291062535193/2305843009213693952)), (1075/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-187139062871719/36893488147419103232), (-8616695334459/288230376151711744)), (101/2305843009213693952), by norm_num⟩
  | 11 => ⟨((76493430950859/73786976294838206464), (791543814600593/147573952589676412928)), (2223/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-56104827063043/295147905179352825856), (-1040665485615627/1180591620717411303424)), (705/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial7 : Sound J_initial7 F_initial7 c := by
  apply sound_round (sound_add (A_initial6 hcre) (A_term7 hcre) S_initial6 S_term7)
  intro k
  fin_cases k <;> norm_num [J_initial7, J_initial6, J_term7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1471726850585653/9007199254740992), (-342890645305565/9007199254740992)), (4059/4503599627370496), by norm_num⟩
  | 1 => ⟨((880914639985997/1125899906842624), (12882339275083/140737488355328)), (2919/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1015171067224517/2251799813685248), (-29579446494929/562949953421312)), (581/562949953421312), by norm_num⟩
  | 3 => ⟨((1990035238011319/9007199254740992), (31991025307451/4503599627370496)), (2647/4503599627370496), by norm_num⟩
  | 4 => ⟨((-1767797516176535/18014398509481984), (69791011621643/9007199254740992)), (4751/18014398509481984), by norm_num⟩
  | 5 => ⟨((348373620040873/9007199254740992), (-59373054303807/9007199254740992)), (3527/36028797018963968), by norm_num⟩
  | 6 => ⟨((-239318939493863/18014398509481984), (112705989987997/36028797018963968)), (1115/36028797018963968), by norm_num⟩
  | 7 => ⟨((286431012090207/72057594037927936), (-323237440540637/288230376151711744)), (2459/288230376151711744), by norm_num⟩
  | 8 => ⟨((-602548527375329/576460752303423488), (11986084188011/36028797018963968)), (1201/576460752303423488), by norm_num⟩
  | 9 => ⟨((1126598356446403/4611686018427387904), (-196538788230789/2305843009213693952)), (263/576460752303423488), by norm_num⟩
  | 10 => ⟨((-118300092855531/2305843009213693952), (356548511691975/18446744073709551616)), (209/2305843009213693952), by norm_num⟩
  | 11 => ⟨((45085672367241/4611686018427387904), (-581669492735171/147573952589676412928)), (607/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-503099728028139/295147905179352825856), (215753094739685/295147905179352825856)), (813/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial8 : Sound J_initial8 F_initial8 c := by
  apply sound_round (sound_add (A_initial7 hcre) (A_term8 hcre) S_initial7 S_term8)
  intro k
  fin_cases k <;> norm_num [J_initial8, J_initial7, J_term8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((624571949245113/2251799813685248), (241166944988009/4503599627370496)), (2147/2251799813685248), by norm_num⟩
  | 1 => ⟨((1197933044583949/2251799813685248), (-61795869821015/562949953421312)), (3181/2251799813685248), by norm_num⟩
  | 2 => ⟨((-791335466987051/4503599627370496), (759368323335721/4503599627370496)), (5231/4503599627370496), by norm_num⟩
  | 3 => ⟨((175117970524043/9007199254740992), (-43593149207141/281474976710656)), (385/562949953421312), by norm_num⟩
  | 4 => ⟨((226092896800933/18014398509481984), (435604127941411/4503599627370496)), (5717/18014398509481984), by norm_num⟩
  | 5 => ⟨((-89728881950043/9007199254740992), (-823103574924305/18014398509481984)), (4389/36028797018963968), by norm_num⟩
  | 6 => ⟨((40775461047557/9007199254740992), (628583168728431/36028797018963968)), (1435/36028797018963968), by norm_num⟩
  | 7 => ⟨((-58219678529117/36028797018963968), (-1618663744558181/288230376151711744)), (3275/288230376151711744), by norm_num⟩
  | 8 => ⟨((282648149198141/576460752303423488), (112920371917121/72057594037927936)), (207/72057594037927936), by norm_num⟩
  | 9 => ⟨((-9410454757519/72057594037927936), (-891433646650015/2305843009213693952)), (1503/2305843009213693952), by norm_num⟩
  | 10 => ⟨((143270821899641/4611686018427387904), (1578020560958613/18446744073709551616)), (1237/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-492682935418269/73786976294838206464), (-633389810852501/36893488147419103232)), (233/9223372036854775808), by norm_num⟩
  | 12 => ⟨((386083143009081/295147905179352825856), (58158944800745/18446744073709551616)), (1295/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial9 : Sound J_initial9 F_initial9 c := by
  apply sound_round (sound_add (A_initial8 hcre) (A_term9 hcre) S_initial8 S_term9)
  intro k
  fin_cases k <;> norm_num [J_initial9, J_initial8, J_term9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1668903814976489/4503599627370496), (-47085963472529/1125899906842624)), (4525/4503599627370496), by norm_num⟩
  | 1 => ⟨((1429333162830203/4503599627370496), (494618204208615/4503599627370496)), (6901/4503599627370496), by norm_num⟩
  | 2 => ⟨((160713343524747/2251799813685248), (-379242923165279/4503599627370496)), (1465/1125899906842624), by norm_num⟩
  | 3 => ⟨((-1533035061430953/9007199254740992), (176426040321935/4503599627370496)), (3569/4503599627370496), by norm_num⟩
  | 4 => ⟨((548169187691753/4503599627370496), (-67462606758015/4503599627370496)), (3429/9007199254740992), by norm_num⟩
  | 5 => ⟨((-1085103097153101/18014398509481984), (51789798177883/9007199254740992)), (2727/18014398509481984), by norm_num⟩
  | 6 => ⟨((429105162743117/18014398509481984), (-82672449977549/36028797018963968)), (231/4503599627370496), by norm_num⟩
  | 7 => ⟨((-1147476672428419/144115188075855872), (15813986318017/18014398509481984)), (547/36028797018963968), by norm_num⟩
  | 8 => ⟨((667808980822043/288230376151711744), (-174066973487141/576460752303423488)), (2297/576460752303423488), by norm_num⟩
  | 9 => ⟨((-1378713482689839/2305843009213693952), (211177081753421/2305843009213693952)), (2167/2305843009213693952), by norm_num⟩
  | 10 => ⟨((1279028516510029/9223372036854775808), (-113265865079759/4611686018427387904)), (1857/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-538677184417485/18446744073709551616), (216927241877011/36893488147419103232)), (1457/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1661735088487803/295147905179352825856), (-11710681139911/9223372036854775808)), (2109/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial10 : Sound J_initial10 F_initial10 c := by
  apply sound_round (sound_add (A_initial9 hcre) (A_term10 hcre) S_initial9 S_term10)
  intro k
  fin_cases k <;> norm_num [J_initial10, J_initial9, J_term10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((343917876704843/1125899906842624), (-328310542204627/2251799813685248)), (4845/4503599627370496), by norm_num⟩
  | 1 => ⟨((533118382097977/1125899906842624), (12636702825231/35184372088832)), (3837/2251799813685248), by norm_num⟩
  | 2 => ⟨((-521601792297571/4503599627370496), (-862758477142811/2251799813685248)), (6793/4503599627370496), by norm_num⟩
  | 3 => ⟨((-46343097780951/2251799813685248), (1252500752026827/4503599627370496)), (2161/2251799813685248), by norm_num⟩
  | 4 => ⟨((72112472192355/2251799813685248), (-1425082445703545/9007199254740992)), (4337/9007199254740992), by norm_num⟩
  | 5 => ⟨((-155105151976521/9007199254740992), (1341044367647395/18014398509481984)), (3605/18014398509481984), by norm_num⟩
  | 6 => ⟨((59709934226563/9007199254740992), (-1071776091755787/36028797018963968)), (2555/36028797018963968), by norm_num⟩
  | 7 => ⟨((-37349883591675/18014398509481984), (740903644394265/72057594037927936)), (791/36028797018963968), by norm_num⟩
  | 8 => ⟨((159048977314509/288230376151711744), (-1798995187834949/576460752303423488)), (3477/576460752303423488), by norm_num⟩
  | 9 => ⟨((-294310631667973/2305843009213693952), (1942913830118447/2305843009213693952)), (3435/2305843009213693952), by norm_num⟩
  | 10 => ⟨((238914728400265/9223372036854775808), (-471885268803451/2305843009213693952)), (3083/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-85207377930065/18446744073709551616), (1665264135178681/36893488147419103232)), (2535/36893488147419103232), by norm_num⟩
  | 12 => ⟨((13244017586073/18446744073709551616), (-672512147430547/73786976294838206464)), (481/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial11 : Sound J_initial11 F_initial11 c := by
  apply sound_round (sound_add (A_initial10 hcre) (A_term11 hcre) S_initial10 S_term11)
  intro k
  fin_cases k <;> norm_num [J_initial11, J_initial10, J_term11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((437241468287721/2251799813685248), (-275961879390361/2251799813685248)), (5223/4503599627370496), by norm_num⟩
  | 1 => ⟨((422235042423599/562949953421312), (84833430060013/281474976710656)), (2155/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1034480812733141/2251799813685248), (-701138234846655/2251799813685248)), (3985/2251799813685248), by norm_num⟩
  | 3 => ⟨((594497692061679/2251799813685248), (492379971072725/2251799813685248)), (2651/2251799813685248), by norm_num⟩
  | 4 => ⟨((-325994912841481/2251799813685248), (-136553373282077/1125899906842624)), (2781/4503599627370496), by norm_num⟩
  | 5 => ⟨((19884456210741/281474976710656), (252599315585053/4503599627370496)), (2415/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1072209851399395/36028797018963968), (-797900361518797/36028797018963968)), (3573/36028797018963968), by norm_num⟩
  | 7 => ⟨((781410705685449/72057594037927936), (34153698787473/4503599627370496)), (2309/72057594037927936), by norm_num⟩
  | 8 => ⟨((-498719650141833/144115188075855872), (-328954711684261/144115188075855872)), (1323/144115188075855872), by norm_num⟩
  | 9 => ⟨((8828701217983/9007199254740992), (44040389093779/72057594037927936)), (1363/576460752303423488), by norm_num⟩
  | 10 => ⟨((-143757580157927/576460752303423488), (-169642668729817/1152921504606846976)), (637/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1061932161634287/18446744073709551616), (74124603797969/2305843009213693952)), (1091/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-56075134563861/4611686018427387904), (-237010874639325/36893488147419103232)), (431/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial12 : Sound J_initial12 F_initial12 c := by
  apply sound_round (sound_add (A_initial11 hcre) (A_term12 hcre) S_initial11 S_term12)
  intro k
  fin_cases k <;> norm_num [J_initial12, J_initial11, J_term12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((94832258490141/562949953421312), (-88813465247469/4503599627370496)), (1371/1125899906842624), by norm_num⟩
  | 1 => ⟨((1837482630910871/2251799813685248), (42370107782067/1125899906842624)), (581/281474976710656), by norm_num⟩
  | 2 => ⟨((-612491378979809/1125899906842624), (60558392116911/2251799813685248)), (2211/1125899906842624), by norm_num⟩
  | 3 => ⟨((757373639396287/2251799813685248), (-317715573795095/4503599627370496)), (6053/4503599627370496), by norm_num⟩
  | 4 => ⟨((-860874103913883/4503599627370496), (288982441301963/4503599627370496)), (1633/2251799813685248), by norm_num⟩
  | 5 => ⟨((850613636836599/9007199254740992), (-175847739489229/4503599627370496)), (2917/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1438674491034905/36028797018963968), (83419954579995/4503599627370496)), (1109/9007199254740992), by norm_num⟩
  | 7 => ⟨((1049971631961299/72057594037927936), (-527345873912259/72057594037927936)), (1473/36028797018963968), by norm_num⟩
  | 8 => ⟨((-335465471982231/72057594037927936), (89902296117001/36028797018963968)), (3469/288230376151711744), by norm_num⟩
  | 9 => ⟨((761353876812233/576460752303423488), (-216312115404209/288230376151711744)), (459/144115188075855872), by norm_num⟩
  | 10 => ⟨((-776447584666957/2305843009213693952), (233027368170563/1152921504606846976)), (881/1152921504606846976), by norm_num⟩
  | 11 => ⟨((359414873493821/4611686018427387904), (-113662351186875/2305843009213693952)), (775/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-304610669894509/18446744073709551616), (202603915699027/18446744073709551616)), (157/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial13 : Sound J_initial13 F_initial13 c := by
  apply sound_round (sound_add (A_initial12 hcre) (A_term13 hcre) S_initial12 S_term13)
  intro k
  fin_cases k <;> norm_num [J_initial13, J_initial12, J_term13, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1077001310252955/4503599627370496), (225552508913663/4503599627370496)), (1411/1125899906842624), by norm_num⟩
  | 1 => ⟨((88588724837889/140737488355328), (-165037349290827/1125899906842624)), (4863/2251799813685248), by norm_num⟩
  | 2 => ⟨((-167674386056047/562949953421312), (303959280960997/1125899906842624)), (1177/562949953421312), by norm_num⟩
  | 3 => ⟨((539553641455343/4503599627370496), (-640362742918733/2251799813685248)), (3281/2251799813685248), by norm_num⟩
  | 4 => ⟨((-217476124811637/4503599627370496), (462171016509427/2251799813685248)), (1803/2251799813685248), by norm_num⟩
  | 5 => ⟨((42856993948207/2251799813685248), (-511197816981593/4503599627370496)), (205/562949953421312), by norm_num⟩
  | 6 => ⟨((-243734559736805/36028797018963968), (923685204982159/18014398509481984)), (1271/9007199254740992), by norm_num⟩
  | 7 => ⟨((37241837694453/18014398509481984), (-708546662722789/36028797018963968)), (215/4503599627370496), by norm_num⟩
  | 8 => ⟨((-19120113974115/36028797018963968), (59164551114805/9007199254740992)), (4129/288230376151711744), by norm_num⟩
  | 9 => ⟨((64114357865909/576460752303423488), (-1121152685163757/576460752303423488)), (2227/576460752303423488), by norm_num⟩
  | 10 => ⟨((-2526597467367/144115188075855872), (1192881161987175/2305843009213693952)), (545/576460752303423488), by norm_num⟩
  | 11 => ⟨((6250451614999/4611686018427387904), (-288038406274081/2305843009213693952)), (489/2305843009213693952), by norm_num⟩
  | 12 => ⟨((12126097623409/36893488147419103232), (509396186557217/18446744073709551616)), (1617/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial14 : Sound J_initial14 F_initial14 c := by
  apply sound_round (sound_add (A_initial13 hcre) (A_term14 hcre) S_initial13 S_term14)
  intro k
  fin_cases k <;> norm_num [J_initial14, J_initial13, J_term14, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((372730381361819/1125899906842624), (147625617665935/4503599627370496)), (719/562949953421312), by norm_num⟩
  | 1 => ⟨((428480618203799/1125899906842624), (-112279865912157/1125899906842624)), (10021/4503599627370496), by norm_num⟩
  | 2 => ⟨((22044286095421/562949953421312), (116262162112185/562949953421312)), (9821/4503599627370496), by norm_num⟩
  | 3 => ⟨((-830493527271663/4503599627370496), (-1022792887228999/4503599627370496)), (6933/4503599627370496), by norm_num⟩
  | 4 => ⟨((355031501443017/2251799813685248), (93714803329467/562949953421312)), (1931/2251799813685248), by norm_num⟩
  | 5 => ⟨((-416650516361955/4503599627370496), (-833239837009987/9007199254740992)), (445/1125899906842624), by norm_num⟩
  | 6 => ⟨((98135614748407/2251799813685248), (752937406989239/18014398509481984)), (2799/18014398509481984), by norm_num⟩
  | 7 => ⟨((-627251205123411/36028797018963968), (-144108550774091/9007199254740992)), (961/18014398509481984), by norm_num⟩
  | 8 => ⟨((109210773281181/18014398509481984), (767749231407157/144115188075855872)), (2341/144115188075855872), by norm_num⟩
  | 9 => ⟨((-134935647841419/72057594037927936), (-905852359739359/576460752303423488)), (641/144115188075855872), by norm_num⟩
  | 10 => ⟨((1198344426880051/2305843009213693952), (479831763081005/1152921504606846976)), (1275/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-150921537581521/1152921504606846976), (-461246800621449/4611686018427387904)), (2325/9223372036854775808), by norm_num⟩
  | 12 => ⟨((1113285389320841/36893488147419103232), (202870520463491/9223372036854775808)), (1955/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial15 : Sound J_initial15 F_initial15 c := by
  apply sound_round (sound_add (A_initial14 hcre) (A_term15 hcre) S_initial14 S_term15)
  intro k
  fin_cases k <;> norm_num [J_initial15, J_initial14, J_term15, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1675384115933235/4503599627370496), (-205120576841861/4503599627370496)), (5905/4503599627370496), by norm_num⟩
  | 1 => ⟨((300620893689673/1125899906842624), (33056291066043/281474976710656)), (653/281474976710656), by norm_num⟩
  | 2 => ⟨((442679574598235/2251799813685248), (-425726481498095/4503599627370496)), (10419/4503599627370496), by norm_num⟩
  | 3 => ⟨((-1485753153954999/4503599627370496), (115127175939517/2251799813685248)), (1873/1125899906842624), by norm_num⟩
  | 4 => ⟨((1164254365656351/4503599627370496), (-118827734260421/4503599627370496)), (2127/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1337015372786189/9007199254740992), (65004339584075/4503599627370496)), (125/281474976710656), by norm_num⟩
  | 6 => ⟨((625307908741483/9007199254740992), (-68646625283665/9007199254740992)), (1605/9007199254740992), by norm_num⟩
  | 7 => ⟨((-249007495694849/9007199254740992), (32194555035441/9007199254740992)), (2251/36028797018963968), by norm_num⟩
  | 8 => ⟨((692461063107313/72057594037927936), (-104941387159777/72057594037927936)), (1401/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1709461627865177/576460752303423488), (298846072962213/576460752303423488)), (1569/288230376151711744), by norm_num⟩
  | 10 => ⟨((29640791589093/36028797018963968), (-188194894560659/1152921504606846976)), (1597/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-477944359097309/2305843009213693952), (106133540986151/2305843009213693952)), (1491/4611686018427387904), by norm_num⟩
  | 12 => ⟨((1764293967731633/36893488147419103232), (-216717957456805/18446744073709551616)), (1283/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial16 : Sound J_initial16 F_initial16 c := by
  apply sound_round (sound_add (A_initial15 hcre) (A_term16 hcre) S_initial15 S_term16)
  intro k
  fin_cases k <;> norm_num [J_initial16, J_initial15, J_term16, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((770088049212285/2251799813685248), (-139394079725117/1125899906842624)), (765/562949953421312), by norm_num⟩
  | 1 => ⟨((396389183546907/1125899906842624), (763741484323185/2251799813685248)), (2765/1125899906842624), by norm_num⟩
  | 2 => ⟨((42836894459319/562949953421312), (-1840324846665289/4503599627370496)), (2823/1125899906842624), by norm_num⟩
  | 3 => ⟨((-121657358086661/562949953421312), (195775917512871/562949953421312)), (4161/2251799813685248), by norm_num⟩
  | 4 => ⟨((400626475442065/2251799813685248), (-1065087692577377/4503599627370496)), (2423/2251799813685248), by norm_num⟩
  | 5 => ⟨((-231407797972153/2251799813685248), (1202391215508021/9007199254740992)), (1169/2251799813685248), by norm_num⟩
  | 6 => ⟨((862102767198749/18014398509481984), (-1150056087864321/18014398509481984)), (3853/18014398509481984), by norm_num⟩
  | 7 => ⟨((-85191592190095/4503599627370496), (948599130140069/36028797018963968)), (2775/36028797018963968), by norm_num⟩
  | 8 => ⟨((469701615123391/72057594037927936), (-342811636322827/36028797018963968)), (1775/72057594037927936), by norm_num⟩
  | 9 => ⟨((-143557698978409/72057594037927936), (880621110530133/288230376151711744)), (2043/288230376151711744), by norm_num⟩
  | 10 => ⟨((630618773227253/1152921504606846976), (-508425475389111/576460752303423488)), (2137/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-39273944047263/288230376151711744), (1065997771466337/4611686018427387904)), (2051/4611686018427387904), by norm_num⟩
  | 12 => ⟨((143212306445869/4611686018427387904), (-255746254506269/4611686018427387904)), (227/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial17 : Sound J_initial17 F_initial17 c := by
  apply sound_round (sound_add (A_initial16 hcre) (A_term17 hcre) S_initial16 S_term17)
  intro k
  fin_cases k <;> norm_num [J_initial17, J_initial16, J_term17, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1181758243697/4398046511104), (-699014459528153/4503599627370496)), (6327/4503599627370496), by norm_num⟩
  | 1 => ⟨((634885070841025/1125899906842624), (242036471975747/562949953421312)), (5831/2251799813685248), by norm_num⟩
  | 2 => ⟨((-517994199172029/2251799813685248), (-607782390490491/1125899906842624)), (1521/562949953421312), by norm_num⟩
  | 3 => ⟨((22190237781905/281474976710656), (533855606986191/1125899906842624)), (4587/2251799813685248), by norm_num⟩
  | 4 => ⟨((-158569179367035/4503599627370496), (-1476398496093955/4503599627370496)), (683/562949953421312), by norm_num⟩
  | 5 => ⟨((46016479816017/2251799813685248), (1677927667588779/9007199254740992)), (5395/9007199254740992), by norm_num⟩
  | 6 => ⟨((-51760740691535/4503599627370496), (-1608215131512443/18014398509481984)), (2275/9007199254740992), by norm_num⟩
  | 7 => ⟨((25173715772969/4503599627370496), (1326956261678711/36028797018963968)), (3355/36028797018963968), by norm_num⟩
  | 8 => ⟨((-84145961626257/36028797018963968), (-119877683061891/9007199254740992)), (1099/36028797018963968), by norm_num⟩
  | 9 => ⟨((122670936496951/144115188075855872), (307957767897155/72057594037927936)), (2589/288230376151711744), by norm_num⟩
  | 10 => ⟨((-316929105074319/1152921504606846976), (-1422901891792327/1152921504606846976)), (2773/1152921504606846976), by norm_num⟩
  | 11 => ⟨((367531668588263/4611686018427387904), (1492775288620639/4611686018427387904)), (681/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-386672085598663/18446744073709551616), (-1434166912187689/18446744073709551616)), (2469/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial18 : Sound J_initial18 F_initial18 c := by
  apply sound_round (sound_add (A_initial17 hcre) (A_term18 hcre) S_initial17 S_term18)
  intro k
  fin_cases k <;> norm_num [J_initial18, J_initial17, J_term18, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((444286850505653/2251799813685248), (-72635055280797/562949953421312)), (6577/4503599627370496), by norm_num⟩
  | 1 => ⟨((108947344994299/140737488355328), (99315141146989/281474976710656)), (3101/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1214924323520131/2251799813685248), (-959951027308797/2251799813685248)), (3315/1125899906842624), by norm_num⟩
  | 3 => ⟨((13461635055477/35184372088832), (816831513997905/2251799813685248)), (2563/1125899906842624), by norm_num⟩
  | 4 => ⟨((-291400197605025/1125899906842624), (-276762128062685/1125899906842624)), (3131/2251799813685248), by norm_num⟩
  | 5 => ⟨((342530792699759/2251799813685248), (310729067958949/2251799813685248)), (1585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-685567015206833/9007199254740992), (-295315073708387/4503599627370496)), (685/2251799813685248), by norm_num⟩
  | 7 => ⟨((590351308074855/18014398509481984), (241943175172465/9007199254740992)), (4141/36028797018963968), by norm_num⟩
  | 8 => ⟨((-444586842378245/36028797018963968), (-694622945082283/72057594037927936)), (695/18014398509481984), by norm_num⟩
  | 9 => ⟨((1188716254301667/288230376151711744), (885828713102809/288230376151711744)), (1677/144115188075855872), by norm_num⟩
  | 10 => ⟨((-714006212591081/576460752303423488), (-507694379654335/576460752303423488)), (1839/576460752303423488), by norm_num⟩
  | 11 => ⟨((389293556858629/1152921504606846976), (264112226536333/1152921504606846976)), (925/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-388570514861517/4611686018427387904), (-251480360697007/4611686018427387904)), (429/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial19 : Sound J_initial19 F_initial19 c := by
  apply sound_round (sound_add (A_initial18 hcre) (A_term19 hcre) S_initial18 S_term19)
  intro k
  fin_cases k <;> norm_num [J_initial19, J_initial18, J_term19, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((731099958684879/4503599627370496), (-293970348695357/4503599627370496)), (13547/9007199254740992), by norm_num⟩
  | 1 => ⟨((989516052985543/1125899906842624), (182234321259483/1125899906842624)), (1625/562949953421312), by norm_num⟩
  | 2 => ⟨((-196029109813643/281474976710656), (-39473746313577/281474976710656)), (7077/2251799813685248), by norm_num⟩
  | 3 => ⟨((1214350590451631/2251799813685248), (86793412461795/1125899906842624)), (5575/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1694056871136805/4503599627370496), (-35888518706169/1125899906842624)), (3469/2251799813685248), by norm_num⟩
  | 5 => ⟨((1001684172631295/4503599627370496), (44183859600497/4503599627370496)), (7155/9007199254740992), by norm_num⟩
  | 6 => ⟨((-2003478365817931/18014398509481984), (-28354174662507/18014398509481984)), (6299/18014398509481984), by norm_num⟩
  | 7 => ⟨((1721940997169597/36028797018963968), (-4756687154271/9007199254740992)), (4847/36028797018963968), by norm_num⟩
  | 8 => ⟨((-1294525006183337/72057594037927936), (22211897185623/36028797018963968)), (207/4503599627370496), by norm_num⟩
  | 9 => ⟨((1728415825735517/288230376151711744), (-24541284951607/72057594037927936)), (4067/288230376151711744), by norm_num⟩
  | 10 => ⟨((-2074730594849219/1152921504606846976), (81862048773453/576460752303423488)), (2269/576460752303423488), by norm_num⟩
  | 11 => ⟨((35338770558013/72057594037927936), (-7125817585739/144115188075855872)), (1161/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-1128893466606851/9223372036854775808), (138363181680353/9223372036854775808)), (1095/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial20 : Sound J_initial20 F_initial20 c := by
  apply sound_round (sound_add (A_initial19 hcre) (A_term20 hcre) S_initial19 S_term20)
  intro k
  fin_cases k <;> norm_num [J_initial20, J_initial19, J_term20, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((787550363336323/4503599627370496), (14684636595477/4503599627370496)), (13847/9007199254740992), by norm_num⟩
  | 1 => ⟨((946549922090571/1125899906842624), (-52692435798801/1125899906842624)), (3365/1125899906842624), by norm_num⟩
  | 2 => ⟨((-179677691117155/281474976710656), (199724906288465/1125899906842624)), (3715/1125899906842624), by norm_num⟩
  | 3 => ⟨((270399473539529/562949953421312), (-69033462216067/281474976710656)), (371/140737488355328), by norm_num⟩
  | 4 => ⟨((-372993147467465/1125899906842624), (480693057772017/2251799813685248)), (1873/1125899906842624), by norm_num⟩
  | 5 => ⟨((439317073452805/2251799813685248), (-4911087349871/35184372088832)), (3917/4503599627370496), by norm_num⟩
  | 6 => ⟨((-438431497407101/4503599627370496), (668610896874607/9007199254740992)), (437/1125899906842624), by norm_num⟩
  | 7 => ⟨((376172626922131/9007199254740992), (-301722878314655/9007199254740992)), (2727/18014398509481984), by norm_num⟩
  | 8 => ⟨((-70573063045341/4503599627370496), (474272013302149/36028797018963968)), (3777/72057594037927936), by norm_num⟩
  | 9 => ⟨((188083642412903/36028797018963968), (-660774643999489/144115188075855872)), (2351/144115188075855872), by norm_num⟩
  | 10 => ⟨((-450562467991367/288230376151711744), (51674134162433/36028797018963968)), (1329/288230376151711744), by norm_num⟩
  | 11 => ⟨((245002270161073/576460752303423488), (-469358928000555/1152921504606846976)), (2755/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-487911713113505/4611686018427387904), (487653622649593/4611686018427387904)), (329/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial21 : Sound J_initial21 F_initial21 c := by
  apply sound_round (sound_add (A_initial20 hcre) (A_term21 hcre) S_initial20 S_term21)
  intro k
  fin_cases k <;> norm_num [J_initial21, J_initial20, J_term21, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1010204113065549/4503599627370496), (108809370156097/2251799813685248)), (7055/4503599627370496), by norm_num⟩
  | 1 => ⟨((774491873887457/1125899906842624), (-209511918254449/1125899906842624)), (6935/2251799813685248), by norm_num⟩
  | 2 => ⟨((-905582797499443/2251799813685248), (884185490361017/2251799813685248)), (3875/1125899906842624), by norm_num⟩
  | 3 => ⟨((133404798771657/562949953421312), (-131464235494735/281474976710656)), (3135/1125899906842624), by norm_num⟩
  | 4 => ⟨((-161264969671711/1125899906842624), (433322699486359/1125899906842624)), (4007/2251799813685248), by norm_num⟩
  | 5 => ⟨((22191594874657/281474976710656), (-34556787794789/140737488355328)), (4243/4503599627370496), by norm_num⟩
  | 6 => ⟨((-168702687538633/4503599627370496), (580145342639855/4503599627370496)), (959/2251799813685248), by norm_num⟩
  | 7 => ⟨((137960283437203/9007199254740992), (-518837606802999/9007199254740992)), (1515/9007199254740992), by norm_num⟩
  | 8 => ⟨((-196422271049785/36028797018963968), (1619654869611133/72057594037927936)), (4249/72057594037927936), by norm_num⟩
  | 9 => ⟨((246554528365605/144115188075855872), (-560879778293435/72057594037927936)), (2679/144115188075855872), by norm_num⟩
  | 10 => ⟨((-137884952056093/288230376151711744), (1396755720665035/576460752303423488)), (3067/576460752303423488), by norm_num⟩
  | 11 => ⟨((277100370850435/2305843009213693952), (-1579372456205071/2305843009213693952)), (805/576460752303423488), by norm_num⟩
  | 12 => ⟨((-125791602645483/4611686018427387904), (817702050511217/4611686018427387904)), (779/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial22 : Sound J_initial22 F_initial22 c := by
  apply sound_round (sound_add (A_initial21 hcre) (A_term22 hcre) S_initial21 S_term22)
  intro k
  fin_cases k <;> norm_num [J_initial22, J_initial21, J_term22, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1297981847429355/4503599627370496), (62877069313707/1125899906842624)), (3561/2251799813685248), by norm_num⟩
  | 1 => ⟨((274455259247365/562949953421312), (-472154060040971/2251799813685248)), (7041/2251799813685248), by norm_num⟩
  | 2 => ⟨((-99136881222045/1125899906842624), (120935030581117/281474976710656)), (3959/1125899906842624), by norm_num⟩
  | 3 => ⟨((-51408816919217/562949953421312), (-569385312026775/1125899906842624)), (6449/2251799813685248), by norm_num⟩
  | 4 => ⟨((128476041840133/1125899906842624), (934886875229623/2251799813685248)), (2075/1125899906842624), by norm_num⟩
  | 5 => ⟨((-371719494575767/4503599627370496), (-1191405511069245/4503599627370496)), (553/562949953421312), by norm_num⟩
  | 6 => ⟨((105551173158859/2251799813685248), (78109035011875/562949953421312)), (4029/9007199254740992), by norm_num⟩
  | 7 => ⟨((-6321566917921/281474976710656), (-558906479284951/9007199254740992)), (3205/18014398509481984), by norm_num⟩
  | 8 => ⟨((337004348430869/36028797018963968), (218161323439637/9007199254740992)), (283/4503599627370496), by norm_num⟩
  | 9 => ⟨((-496803729414053/144115188075855872), (-302324892858287/36028797018963968)), (719/36028797018963968), by norm_num⟩
  | 10 => ⟨((656548302940329/576460752303423488), (753274102375089/288230376151711744)), (1659/288230376151711744), by norm_num⟩
  | 11 => ⟨((-196477484161809/576460752303423488), (-53267363106425/72057594037927936)), (1755/1152921504606846976), by norm_num⟩
  | 12 => ⟨((107429710614963/1152921504606846976), (883120564535713/4611686018427387904)), (107/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial23 : Sound J_initial23 F_initial23 c := by
  apply sound_round (sound_add (A_initial22 hcre) (A_term23 hcre) S_initial22 S_term23)
  intro k
  fin_cases k <;> norm_num [J_initial23, J_initial22, J_term23, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((386460512492641/1125899906842624), (123042596644951/4503599627370496)), (7221/4503599627370496), by norm_num⟩
  | 1 => ⟨((351982251975503/1125899906842624), (-536037271751467/4503599627370496)), (14399/4503599627370496), by norm_num⟩
  | 2 => ⟨((855149738542241/4503599627370496), (321551780654959/1125899906842624)), (8173/2251799813685248), by norm_num⟩
  | 3 => ⟨((-434314407378525/1125899906842624), (-24848180324995/70368744177664)), (6723/2251799813685248), by norm_num⟩
  | 4 => ⟨((391854689564401/1125899906842624), (330934563293281/1125899906842624)), (4371/2251799813685248), by norm_num⟩
  | 5 => ⟨((-8135505552823/35184372088832), (-105542433792253/562949953421312)), (1177/1125899906842624), by norm_num⟩
  | 6 => ⟨((282893255091871/2251799813685248), (441039853406741/4503599627370496)), (4333/9007199254740992), by norm_num⟩
  | 7 => ⟨((-1048697634483045/18014398509481984), (-195991904245507/4503599627370496)), (3483/18014398509481984), by norm_num⟩
  | 8 => ⟨((212191063162623/9007199254740992), (303700338557129/18014398509481984)), (2489/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1219648406669017/144115188075855872), (-417324970182005/72057594037927936)), (799/36028797018963968), by norm_num⟩
  | 10 => ⟨((787722010529517/288230376151711744), (257571381681773/144115188075855872)), (1865/288230376151711744), by norm_num⟩
  | 11 => ⟨((-461959307494307/576460752303423488), (-72134989209599/144115188075855872)), (499/288230376151711744), by norm_num⟩
  | 12 => ⟨((496097929739793/2305843009213693952), (73948665251583/576460752303423488)), (1969/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial24 : Sound J_initial24 F_initial24 c := by
  apply sound_round (sound_add (A_initial23 hcre) (A_term24 hcre) S_initial23 S_term24)
  intro k
  fin_cases k <;> norm_num [J_initial24, J_initial23, J_term24, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((420011674747371/1125899906842624), (-27631166819109/1125899906842624)), (7361/4503599627370496), by norm_num⟩
  | 1 => ⟨((487970453795045/2251799813685248), (107893373782847/2251799813685248)), (14849/4503599627370496), by norm_num⟩
  | 2 => ⟨((1550407764904633/4503599627370496), (38096521226105/2251799813685248)), (4269/1125899906842624), by norm_num⟩
  | 3 => ⟨((-310405089235241/562949953421312), (-145994258666223/2251799813685248)), (7119/2251799813685248), by norm_num⟩
  | 4 => ⟨((270965685908207/562949953421312), (69743909256695/1125899906842624)), (4693/2251799813685248), by norm_num⟩
  | 5 => ⟨((-713903637131645/2251799813685248), (-21468405596265/562949953421312)), (5125/4503599627370496), by norm_num⟩
  | 6 => ⟨((1546231354658485/9007199254740992), (80208044260937/4503599627370496)), (4783/9007199254740992), by norm_num⟩
  | 7 => ⟨((-715025058360011/9007199254740992), (-30067220345095/4503599627370496)), (3901/18014398509481984), by norm_num⟩
  | 8 => ⟨((1155645824107013/36028797018963968), (18327430839581/9007199254740992)), (2829/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1658676705095221/144115188075855872), (-8821661471847/18014398509481984)), (3685/144115188075855872), by norm_num⟩
  | 10 => ⟨((1070357525776943/288230376151711744), (11624596432753/144115188075855872)), (4365/576460752303423488), by norm_num⟩
  | 11 => ⟨((-627371785181417/576460752303423488), (-329585466085/288230376151711744)), (593/288230376151711744), by norm_num⟩
  | 12 => ⟨((42098666974541/144115188075855872), (-26179012785741/4611686018427387904)), (2375/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial25 : Sound J_initial25 F_initial25 c := by
  apply sound_round (sound_add (A_initial24 hcre) (A_term25 hcre) S_initial24 S_term25)
  intro k
  fin_cases k <;> norm_num [J_initial25, J_initial24, J_term25, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1672975997002739/4503599627370496), (-370718979493397/4503599627370496)), (3751/2251799813685248), by norm_num⟩
  | 1 => ⟨((499488968627243/2251799813685248), (66470308463291/281474976710656)), (7655/2251799813685248), by norm_num⟩
  | 2 => ⟨((378219832901675/1125899906842624), (-163101673129273/562949953421312)), (2229/562949953421312), by norm_num⟩
  | 3 => ⟨((-1221241813840069/2251799813685248), (150978612849229/562949953421312)), (7531/2251799813685248), by norm_num⟩
  | 4 => ⟨((1067263928451091/2251799813685248), (-117832731127207/562949953421312)), (5031/2251799813685248), by norm_num⟩
  | 5 => ⟨((-351543764337935/1125899906842624), (78036916003701/562949953421312)), (87/70368744177664), by norm_num⟩
  | 6 => ⟨((380684517745517/2251799813685248), (-176027940415907/2251799813685248)), (1317/2251799813685248), by norm_num⟩
  | 7 => ⟨((-352045144450513/4503599627370496), (684506888823203/18014398509481984)), (4355/18014398509481984), by norm_num⟩
  | 8 => ⟨((568916278423911/18014398509481984), (-291099782168821/18014398509481984)), (1601/18014398509481984), by norm_num⟩
  | 9 => ⟨((-204110291226457/18014398509481984), (27457258810971/4503599627370496)), (1057/36028797018963968), by norm_num⟩
  | 10 => ⟨((526774706407291/144115188075855872), (-297635742929935/144115188075855872)), (2539/288230376151711744), by norm_num⟩
  | 11 => ⟨((-617414975244445/576460752303423488), (365740843985983/576460752303423488)), (699/288230376151711744), by norm_num⟩
  | 12 => ⟨((1325530511195055/4611686018427387904), (-205505856552411/1152921504606846976)), (2837/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial26 : Sound J_initial26 F_initial26 c := by
  apply sound_round (sound_add (A_initial25 hcre) (A_term26 hcre) S_initial25 S_term26)
  intro k
  fin_cases k <;> norm_num [J_initial26, J_initial25, J_term26, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_endpointHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-132734840755537/9007199254740992), (-214015055486613/9007199254740992)), (385/18014398509481984), by norm_num⟩
  | 1 => ⟨((437472381565313/9007199254740992), (705358709752741/9007199254740992)), (319/4503599627370496), by norm_num⟩
  | 2 => ⟨((-180229700377709/2251799813685248), (-581186809840083/4503599627370496)), (529/4503599627370496), by norm_num⟩
  | 3 => ⟨((396005127235845/4503599627370496), (638498971302131/4503599627370496)), (1169/9007199254740992), by norm_num⟩
  | 4 => ⟨((-163146037183829/2251799813685248), (-526097112130851/4503599627370496)), (969/9007199254740992), by norm_num⟩
  | 5 => ⟨((860324358228763/18014398509481984), (693572102903709/9007199254740992)), (1285/18014398509481984), by norm_num⟩
  | 6 => ⟨((-29536341005957/1125899906842624), (-761966835327397/18014398509481984)), (355/9007199254740992), by norm_num⟩
  | 7 => ⟨((445014681482553/36028797018963968), (717519539012767/36028797018963968)), (21/1125899906842624), by norm_num⟩
  | 8 => ⟨((-366673948285843/72057594037927936), (-591206837189177/72057594037927936)), (557/72057594037927936), by norm_num⟩
  | 9 => ⟨((537110007361709/288230376151711744), (433004730987091/144115188075855872)), (821/288230376151711744), by norm_num⟩
  | 10 => ⟨((-708090785345031/1152921504606846976), (-1141690364433233/1152921504606846976)), (17/18014398509481984), by norm_num⟩
  | 11 => ⟨((424318493603293/2305843009213693952), (1368300070058533/4611686018427387904)), (1311/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-233080755690859/4611686018427387904), (-375807817887935/4611686018427387904)), (181/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_endpointHalf : Sound J_endpointHalf F_endpointHalf c := by
  apply sound_round (sound_scale (A_term27 hcre) S_term27)
  intro k
  fin_cases k <;> norm_num [J_endpointHalf, J_term27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initialHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((803304288312485/2251799813685248), (-14928953351147/140737488355328)), (475/281474976710656), by norm_num⟩
  | 1 => ⟨((608857064018571/2251799813685248), (708102145144513/2251799813685248)), (7815/2251799813685248), by norm_num⟩
  | 2 => ⟨((576209965425641/2251799813685248), (-471500048718567/1125899906842624)), (9181/2251799813685248), by norm_num⟩
  | 3 => ⟨((-511619625111073/1125899906842624), (461581968523991/1125899906842624)), (7825/2251799813685248), by norm_num⟩
  | 4 => ⟨((452058945633631/1125899906842624), (-367189740287127/1125899906842624)), (2637/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1191093967794549/4503599627370496), (485540689740731/2251799813685248)), (2945/2251799813685248), by norm_num⟩
  | 6 => ⟨((321611835733603/2251799813685248), (-542547589663663/4503599627370496)), (703/1125899906842624), by norm_num⟩
  | 7 => ⟨((-148209154632597/2251799813685248), (521633329164793/9007199254740992)), (1173/4503599627370496), by norm_num⟩
  | 8 => ⟨((238623895676225/9007199254740992), (-438901491466115/18014398509481984)), (1741/18014398509481984), by norm_num⟩
  | 9 => ⟨((-682163663065401/72057594037927936), (327909253234541/36028797018963968)), (145/4503599627370496), by norm_num⟩
  | 10 => ⟨((219131679119581/72057594037927936), (-440347038484089/144115188075855872)), (703/72057594037927936), by norm_num⟩
  | 11 => ⟨((-255667675921811/288230376151711744), (1073556705486599/1152921504606846976)), (3125/1152921504606846976), by norm_num⟩
  | 12 => ⟨((273112438876049/1152921504606846976), (-299457811024395/1152921504606846976)), (25/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initialHalf : Sound J_initialHalf F_initialHalf c := by
  apply sound_round (sound_add (A_initial26 hcre) (A_endpointHalf hcre) S_initial26 S_endpointHalf)
  intro k
  fin_cases k <;> norm_num [J_initialHalf, J_initial26, J_endpointHalf, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor1 : Sound J_risingFactor1 F_risingFactor1 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q0 hcre) S_variable S_q0)
  intro k
  fin_cases k <;> norm_num [J_risingFactor1, J_variable, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-317972649/1638400), (196977/5120)), 0, by norm_num⟩
  | 1 => ⟨((11/4), (17907/640)), 0, by norm_num⟩
  | 2 => ⟨(1, 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising2 : Sound J_rising2 F_rising2 c := by
  apply sound_round (sound_mul (A_variable hcre) (A_risingFactor1 hcre) S_variable S_risingFactor1)
  intro k
  fin_cases k <;> norm_num [J_rising2, J_variable, J_risingFactor1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor2 : Sound J_risingFactor2 F_risingFactor2 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q3 hcre) S_variable S_q3)
  intro k
  fin_cases k <;> norm_num [J_risingFactor2, J_variable, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2873581041/2621440), (-5461976110443/2097152000)), 0, by norm_num⟩
  | 1 => ⟨((-946340347/1638400), (161163/1024)), 0, by norm_num⟩
  | 2 => ⟨((45/8), (53721/1280)), 0, by norm_num⟩
  | 3 => ⟨(1, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising3 : Sound J_rising3 F_rising3 c := by
  apply sound_round (sound_mul (A_rising2 hcre) (A_risingFactor2 hcre) S_rising2 S_risingFactor2)
  intro k
  fin_cases k <;> norm_num [J_rising3, J_rising2, J_risingFactor2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((31/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor3 : Sound J_risingFactor3 F_risingFactor3 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q4 hcre) S_variable S_q4)
  intro k
  fin_cases k <;> norm_num [J_risingFactor3, J_variable, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((86405236639014801/2684354560000), (-106651834482417/4194304000)), 0, by norm_num⟩
  | 1 => ⟨((-18140978593/3276800), (-5282275784043/524288000)), 0, by norm_num⟩
  | 2 => ⟨((-936305147/819200), (1020699/2560)), 0, by norm_num⟩
  | 3 => ⟨((19/2), (17907/320)), 0, by norm_num⟩
  | 4 => ⟨(1, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising4 : Sound J_rising4 F_rising4 c := by
  apply sound_round (sound_mul (A_rising3 hcre) (A_risingFactor3 hcre) S_rising3 S_risingFactor3)
  intro k
  fin_cases k <;> norm_num [J_rising4, J_rising3, J_risingFactor3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor4 : Sound J_risingFactor4 F_risingFactor4 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q5 hcre) S_variable S_q5)
  intro k
  fin_cases k <;> norm_num [J_risingFactor4, J_variable, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((550453091461407/1073741824), (700833628941161/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((78463254877888401/536870912000), (-127502218744989/838860800)), 0, by norm_num⟩
  | 2 => ⟨((-21870634381/1310720), (-5058567214443/209715200)), 0, by norm_num⟩
  | 3 => ⟨((-307937449/163840), (411861/512)), 0, by norm_num⟩
  | 4 => ⟨((115/8), (17907/256)), 0, by norm_num⟩
  | 5 => ⟨(1, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising5 : Sound J_rising5 F_rising5 c := by
  apply sound_round (sound_mul (A_rising4 hcre) (A_risingFactor4 hcre) S_rising4 S_risingFactor4)
  intro k
  fin_cases k <;> norm_num [J_rising5, J_rising4, J_risingFactor4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((47/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor5 : Sound J_risingFactor5 F_risingFactor5 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q6 hcre) S_variable S_q6)
  intro k
  fin_cases k <;> norm_num [J_risingFactor5, J_variable, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-208545571185049/134217728), (1219931440783025/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((469447320917889/134217728), (99186092576527/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((207001286521511603/536870912000), (-442197273214683/838860800)), 0, by norm_num⟩
  | 3 => ⟨((-25547042169/655360), (-4790850401643/104857600)), 0, by norm_num⟩
  | 4 => ⟨((-908861947/327680), (1450467/1024)), 0, by norm_num⟩
  | 5 => ⟨((81/4), (53721/640)), 0, by norm_num⟩
  | 6 => ⟨(1, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising6 : Sound J_rising6 F_rising6 c := by
  apply sound_round (sound_mul (A_rising5 hcre) (A_risingFactor5 hcre) S_rising5 S_risingFactor5)
  intro k
  fin_cases k <;> norm_num [J_rising6, J_rising5, J_risingFactor5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor6 : Sound J_risingFactor6 F_risingFactor6 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q7 hcre) S_variable S_q7)
  intro k
  fin_cases k <;> norm_num [J_risingFactor6, J_variable, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1156275065260257/8388608), (85461073433593/2097152)), (1/2097152), by norm_num⟩
  | 1 => ⟨((15231805343009/8388608), (285976090068989/4194304)), (3/16777216), by norm_num⟩
  | 2 => ⟨((1815034103558653/134217728), (435934098238135/134217728)), (1/134217728), by norm_num⟩
  | 3 => ⟨((406279377594588407/536870912000), (-1163164929425331/838860800)), 0, by norm_num⟩
  | 4 => ⟨((-204122600899/2621440), (-31353877419501/419430400)), 0, by norm_num⟩
  | 5 => ⟨((-6240177629/1638400), (11657457/5120)), 0, by norm_num⟩
  | 6 => ⟨((217/8), (125349/1280)), 0, by norm_num⟩
  | 7 => ⟨(1, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising7 : Sound J_rising7 F_rising7 c := by
  apply sound_round (sound_mul (A_rising6 hcre) (A_risingFactor6 hcre) S_rising6 S_risingFactor6)
  intro k
  fin_cases k <;> norm_num [J_rising7, J_rising6, J_risingFactor6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((63/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor7 : Sound J_risingFactor7 F_risingFactor7 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q8 hcre) S_variable S_q8)
  intro k
  fin_cases k <;> norm_num [J_risingFactor7, J_variable, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-868000899693593/524288), (-842755230115867/524288)), (3/262144), by norm_num⟩
  | 1 => ⟨((-564865389424139/524288), (632382286137507/1048576)), (3/524288), by norm_num⟩
  | 2 => ⟨((263701641605121/4194304), (296689526683905/1048576)), (1/2097152), by norm_num⟩
  | 3 => ⟨((652311990887553/16777216), (12227891875347/4194304)), (1/33554432), by norm_num⟩
  | 4 => ⟨((319262164907842807/268435456000), (-257079435235707/83886080)), 0, by norm_num⟩
  | 5 => ⟨((-45781109003/327680), (-28863744325101/262144000)), 0, by norm_num⟩
  | 6 => ⟨((-2033706143/409600), (877443/256)), 0, by norm_num⟩
  | 7 => ⟨(35, (17907/160)), 0, by norm_num⟩
  | 8 => ⟨(1, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising8 : Sound J_rising8 F_rising8 c := by
  apply sound_round (sound_mul (A_rising7 hcre) (A_risingFactor7 hcre) S_rising7 S_risingFactor7)
  intro k
  fin_cases k <;> norm_num [J_rising8, J_rising7, J_risingFactor7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor8 : Sound J_risingFactor8 F_risingFactor8 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q9 hcre) S_variable S_q9)
  intro k
  fin_cases k <;> norm_num [J_risingFactor8, J_variable, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((255406625252227/32768), (-613207800901597/16384)), (5/16384), by norm_num⟩
  | 1 => ⟨((-1288080739687323/65536), (-742367171650911/65536)), (5/32768), by norm_num⟩
  | 2 => ⟨((-1173820720526551/262144), (1046947006531425/262144)), (5/262144), by norm_num⟩
  | 3 => ⟨((24061758979045/65536), (894179088580349/1048576)), (1/524288), by norm_num⟩
  | 4 => ⟨((1548702949042029/16777216), (-32063173098819/4194304)), (1/16777216), by norm_num⟩
  | 5 => ⟨((1999528228580492463/1342177280000), (-12575323322558451/2097152000)), 0, by norm_num⟩
  | 6 => ⟨((-759327944193/3276800), (-78196660584903/524288000)), 0, by norm_num⟩
  | 7 => ⟨((-2547795441/409600), (6285357/1280)), 0, by norm_num⟩
  | 8 => ⟨((351/8), (161163/1280)), 0, by norm_num⟩
  | 9 => ⟨(1, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising9 : Sound J_rising9 F_rising9 c := by
  apply sound_round (sound_mul (A_rising8 hcre) (A_risingFactor8 hcre) S_rising8 S_risingFactor8)
  intro k
  fin_cases k <;> norm_num [J_rising9, J_rising8, J_risingFactor8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor9 : Sound J_risingFactor9 F_risingFactor9 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q10 hcre) S_variable S_q10)
  intro k
  fin_cases k <;> norm_num [J_risingFactor9, J_variable, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1229968941634665/2048), (-266804852744159/1024)), (1/128), by norm_num⟩
  | 1 => ⟨((-113961457336387/4096), (-1737734706829325/4096)), (17/4096), by norm_num⟩
  | 2 => ⟨((-980950862807933/8192), (-17680538023017/512)), (3/4096), by norm_num⟩
  | 3 => ⟨((-837684418573349/65536), (1150233156333039/65536)), (5/65536), by norm_num⟩
  | 4 => ⟨((726483970236009/524288), (1084577573504513/524288)), (3/524288), by norm_num⟩
  | 5 => ⟨((1601467090932011/8388608), (-96504955154119/2097152)), (1/8388608), by norm_num⟩
  | 6 => ⟨((345746752419272421/268435456000), (-4492546832798829/419430400)), 0, by norm_num⟩
  | 7 => ⟨((-118570755963/327680), (-9839702155329/52428800)), 0, by norm_num⟩
  | 8 => ⟨((-2473453041/327680), (6930009/1024)), 0, by norm_num⟩
  | 9 => ⟨((215/4), (17907/128)), 0, by norm_num⟩
  | 10 => ⟨(1, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising10 : Sound J_rising10 F_rising10 c := by
  apply sound_round (sound_mul (A_rising9 hcre) (A_risingFactor9 hcre) S_rising9 S_risingFactor9)
  intro k
  fin_cases k <;> norm_num [J_rising10, J_rising9, J_risingFactor9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor10 : Sound J_risingFactor10 F_risingFactor10 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q11 hcre) S_variable S_q11)
  intro k
  fin_cases k <;> norm_num [J_risingFactor10, J_variable, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1302564290221379/128), (712754235227273/128)), (13/64), by norm_num⟩
  | 1 => ⟨((797851376944701/128), (-21054089188871/4)), (15/128), by norm_num⟩
  | 2 => ⟨((-216818628686937/256), (-39600063138231/16)), (13/512), by norm_num⟩
  | 3 => ⟨((-2065562942976073/4096), (-92087338717195/4096)), (3/1024), by norm_num⟩
  | 4 => ⟨((-436688530011015/16384), (486875681140739/8192)), (5/16384), by norm_num⟩
  | 5 => ⟨((538125861132645/131072), (1111235937492935/262144)), (1/65536), by norm_num⟩
  | 6 => ⟨((1487983764216379/4194304), (-605997143321743/4194304)), (1/4194304), by norm_num⟩
  | 7 => ⟨((-5778212321996367/268435456000), (-7471847447341893/419430400)), 0, by norm_num⟩
  | 8 => ⟨((-1411947804597/2621440), (-92140708758219/419430400)), 0, by norm_num⟩
  | 9 => ⟨((-2923235139/327680), (9257919/1024)), 0, by norm_num⟩
  | 10 => ⟨((517/8), (196977/1280)), 0, by norm_num⟩
  | 11 => ⟨(1, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising11 : Sound J_rising11 F_rising11 c := by
  apply sound_round (sound_mul (A_rising10 hcre) (A_risingFactor10 hcre) S_rising10 S_risingFactor10)
  intro k
  fin_cases k <;> norm_num [J_rising11, J_rising10, J_risingFactor10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359736775093025/562949953421312), (-255525356987735/562949953421312)), (179/281474976710656), by norm_num⟩
  | 1 => ⟨((-601112790251771/281474976710656), (203854502455817/140737488355328)), (605/281474976710656), by norm_num⟩
  | 2 => ⟨((502127929646587/140737488355328), (-649828724815079/281474976710656)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-1118306969684575/281474976710656), (689693705534703/281474976710656)), (1153/281474976710656), by norm_num⟩
  | 4 => ⟨((466907247387561/140737488355328), (-274163196192455/140737488355328)), (487/140737488355328), by norm_num⟩
  | 5 => ⟨((-1247394698874005/562949953421312), (348286439921797/281474976710656)), (329/140737488355328), by norm_num⟩
  | 6 => ⟨((347081642283051/281474976710656), (-736364688128119/1125899906842624)), (1481/1125899906842624), by norm_num⟩
  | 7 => ⟨((-662110081515877/1125899906842624), (666197723297289/2251799813685248)), (1427/2251799813685248), by norm_num⟩
  | 8 => ⟨((1105010116802909/4503599627370496), (-263248634264345/2251799813685248)), (301/1125899906842624), by norm_num⟩
  | 9 => ⟨((-819503849733891/9007199254740992), (369188500626397/9007199254740992)), (903/9007199254740992), by norm_num⟩
  | 10 => ⟨((546904075049107/18014398509481984), (-465063791798383/36028797018963968)), (1217/36028797018963968), by norm_num⟩
  | 11 => ⟨((-165875859068807/18014398509481984), (265712498595599/72057594037927936)), (1491/144115188075855872), by norm_num⟩
  | 12 => ⟨((737772997282219/288230376151711744), (-555323780960113/576460752303423488)), (837/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct1 : Sound J_zetaCorrProduct1 F_zetaCorrProduct1 c := by
  apply sound_round (sound_mul (A_variable hcre) (A_term27 hcre) S_variable S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct1, J_variable, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35529558033879/18014398509481984), (-403793156721359/288230376151711744)), (283/144115188075855872), by norm_num⟩
  | 1 => ⟨((-949906631508971/144115188075855872), (644280896650483/144115188075855872)), (957/144115188075855872), by norm_num⟩
  | 2 => ⟨((396743055523229/36028797018963968), (-64180614796551/9007199254740992)), (405/36028797018963968), by norm_num⟩
  | 3 => ⟨((-55225035539979/4503599627370496), (544943174743469/72057594037927936)), (57/4503599627370496), by norm_num⟩
  | 4 => ⟨((368914368306221/36028797018963968), (-433245544600423/72057594037927936)), (385/36028797018963968), by norm_num⟩
  | 5 => ⟨((-246398952864001/36028797018963968), (34398660733017/9007199254740992)), (1041/144115188075855872), by norm_num⟩
  | 6 => ⟨((1096949387956309/288230376151711744), (-581819012841971/288230376151711744)), (1171/288230376151711744), by norm_num⟩
  | 7 => ⟨((-523148706382915/288230376151711744), (131594612009341/144115188075855872)), (141/72057594037927936), by norm_num⟩
  | 8 => ⟨((873094413276373/1152921504606846976), (-207998920900223/576460752303423488)), (953/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-161877303651139/576460752303423488), (583408988644183/4611686018427387904)), (357/1152921504606846976), by norm_num⟩
  | 10 => ⟨((864243476620811/9223372036854775808), (-367457810803661/9223372036854775808)), (481/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1048499257323817/36893488147419103232), (419891355805391/36893488147419103232)), (1179/36893488147419103232), by norm_num⟩
  | 12 => ⟨((582931750939037/73786976294838206464), (-219387172724983/73786976294838206464)), (331/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr1 : Sound J_zetaCorr1 F_zetaCorr1 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct1 hcre) S_zetaCorrProduct1)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr1, J_zetaCorrProduct1, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((25242046345835/70368744177664), (-484035775310475/4503599627370496)), (3805/2251799813685248), by norm_num⟩
  | 1 => ⟨((594014772901243/2251799813685248), (718169034154677/2251799813685248)), (7831/2251799813685248), by norm_num⟩
  | 2 => ⟨((601006406395843/2251799813685248), (-59940328196017/140737488355328)), (9207/2251799813685248), by norm_num⟩
  | 3 => ⟨((-131356470999017/281474976710656), (940193411258715/2251799813685248)), (7855/2251799813685248), by norm_num⟩
  | 4 => ⟨((927175039286401/2251799813685248), (-747918403843017/2251799813685248)), (5299/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1221893836902549/4503599627370496), (494140354923985/2251799813685248)), (1481/1125899906842624), by norm_num⟩
  | 6 => ⟨((660363505654023/4503599627370496), (-551638511739319/4503599627370496)), (2831/4503599627370496), by norm_num⟩
  | 7 => ⟨((-304592507802427/4503599627370496), (529857992415377/9007199254740992)), (591/2251799813685248), by norm_num⟩
  | 8 => ⟨((981779783119787/36028797018963968), (-445401457744247/18014398509481984)), (3513/36028797018963968), by norm_num⟩
  | 9 => ⟨((-702398326021793/72057594037927936), (664934271916647/72057594037927936)), (293/9007199254740992), by norm_num⟩
  | 10 => ⟨((225883581280681/72057594037927936), (-55761070847237/18014398509481984)), (2843/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1055436305478613/1152921504606846976), (1086678310355517/1152921504606846976)), (3163/1152921504606846976), by norm_num⟩
  | 12 => ⟨((564441494968943/2305843009213693952), (-302885735598223/1152921504606846976)), (811/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart1 : Sound J_zetaPart1 F_zetaPart1 c := by
  apply sound_round (sound_add (A_initialHalf hcre) (A_zetaCorr1 hcre) S_initialHalf S_zetaCorr1)
  intro k
  fin_cases k <;> norm_num [J_zetaPart1, J_initialHalf, J_zetaCorr1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-201120428471547/2199023255552), (1133406734073641/8796093022208)), (87/549755813888), by norm_num⟩
  | 1 => ⟨((716742253250035/2199023255552), (-441861216479391/1099511627776)), (1223/2199023255552), by norm_num⟩
  | 2 => ⟨((-316476224378657/549755813888), (685168723807637/1099511627776)), (537/549755813888), by norm_num⟩
  | 3 => ⟨((739693896340499/1099511627776), (-351874417737885/549755813888)), (627/549755813888), by norm_num⟩
  | 4 => ⟨((-644125796913343/1099511627776), (67260853844937/137438953472)), (1099/1099511627776), by norm_num⟩
  | 5 => ⟨((446173160929617/1099511627776), (-652503568189527/2199023255552)), (1537/2199023255552), by norm_num⟩
  | 6 => ⟨((-256245550992375/1099511627776), (40777865044403/274877906944)), (1791/4398046511104), by norm_num⟩
  | 7 => ⟨((251140977235099/2199023255552), (-68999118106439/1099511627776)), (1787/8796093022208), by norm_num⟩
  | 8 => ⟨((-428967361286837/8796093022208), (402017181780913/17592186044416)), (1559/17592186044416), by norm_num⟩
  | 9 => ⟨((1297672683161973/70368744177664), (-509566941133517/70368744177664)), (1207/35184372088832), by norm_num⟩
  | 10 => ⟨((-880173633781893/140737488355328), (141178799433627/70368744177664)), (841/70368744177664), by norm_num⟩
  | 11 => ⟨((135238401461791/70368744177664), (-272800827547579/562949953421312)), (133/35184372088832), by norm_num⟩
  | 12 => ⟨((-607655905856597/1125899906842624), (226108534473277/2251799813685248)), (1233/1125899906842624), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct2 : Sound J_zetaCorrProduct2 F_zetaCorrProduct2 c := by
  apply sound_round (sound_mul (A_rising3 hcre) (A_term27 hcre) S_rising3 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct2, J_rising3, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((238096105951533/36893488147419103232), (-670890898286735/73786976294838206464)), (825/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-106064275000975/4611686018427387904), (523096712821661/18446744073709551616)), (181/4611686018427387904), by norm_num⟩
  | 2 => ⟨((374659885241155/9223372036854775808), (-811135926360951/18446744073709551616)), (1273/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-218921366731905/4611686018427387904), (833131962616179/18446744073709551616)), (743/9223372036854775808), by norm_num⟩
  | 4 => ⟨((762547321291589/18446744073709551616), (-318506628196057/9223372036854775808)), (651/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-1056402803084295/36893488147419103232), (772465332766461/36893488147419103232)), (455/9223372036854775808), by norm_num⟩
  | 6 => ⟨((606711792753771/36893488147419103232), (-386198496090139/36893488147419103232)), (2121/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-1189251418743851/147573952589676412928), (163368996974439/36893488147419103232)), (529/36893488147419103232), by norm_num⟩
  | 8 => ⟨((507832342437305/147573952589676412928), (-475927414410747/295147905179352825856)), (1847/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-1536247784517095/1180591620717411303424), (301625014742569/590295810358705651712)), (1429/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1041992185265889/2361183241434822606848), (-334268603577627/2361183241434822606848)), (249/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-640407083613943/4722366482869645213696), (322954834737851/9444732965739290427392)), (315/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((719372497574881/18889465931478580854784), (-267678236316563/37778931862957161709568)), (365/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr2 : Sound J_zetaCorr2 F_zetaCorr2 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct2 hcre) S_zetaCorrProduct2)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr2, J_zetaCorrProduct2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1615520030599499/4503599627370496), (-484076723241279/4503599627370496)), (7611/4503599627370496), by norm_num⟩
  | 1 => ⟨((593962983704465/2251799813685248), (718232888733879/2251799813685248)), (979/281474976710656), by norm_num⟩
  | 2 => ⟨((150274469023597/562949953421312), (-959144266752283/2251799813685248)), (1151/281474976710656), by norm_num⟩
  | 3 => ⟨((-65684916449421/140737488355328), (940295111937745/2251799813685248)), (491/140737488355328), by norm_num⟩
  | 4 => ⟨((927268123676207/2251799813685248), (-747996164250291/2251799813685248)), (1325/562949953421312), by norm_num⟩
  | 5 => ⟨((-1222022792322847/4503599627370496), (123546875616567/562949953421312)), (5925/4503599627370496), by norm_num⟩
  | 6 => ⟨((330218783576081/2251799813685248), (-68960706888803/562949953421312)), (177/281474976710656), by norm_num⟩
  | 7 => ⟨((-304628800875509/4503599627370496), (132474469356101/2251799813685248)), (2365/9007199254740992), by norm_num⟩
  | 8 => ⟨((981903765625265/36028797018963968), (-445430506048349/18014398509481984)), (1757/18014398509481984), by norm_num⟩
  | 9 => ⟨((-43905755696585/4503599627370496), (332485545688227/36028797018963968)), (2345/72057594037927936), by norm_num⟩
  | 10 => ⟨((451830760717201/144115188075855872), (-446108968914345/144115188075855872)), (711/72057594037927936), by norm_num⟩
  | 11 => ⟨((-1055592654864261/1152921504606846976), (1086717733553117/1152921504606846976)), (791/288230376151711744), by norm_num⟩
  | 12 => ⟨((282264654497263/1152921504606846976), (-18930869030607/72057594037927936)), (1623/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart2 : Sound J_zetaPart2 F_zetaPart2 c := by
  apply sound_round (sound_add (A_zetaPart1 hcre) (A_zetaCorr2 hcre) S_zetaPart1 S_zetaCorr2)
  intro k
  fin_cases k <;> norm_num [J_zetaPart2, J_zetaPart1, J_zetaCorr2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13714686658095/34359738368), (-1167547971041257/34359738368)), (617/17179869184), by norm_num⟩
  | 1 => ⟨((-13793190458373/1073741824), (235208576182221/2147483648)), (283/2147483648), by norm_num⟩
  | 2 => ⟨((169718469884355/4294967296), (-1502601204697741/8589934592)), (1037/4294967296), by norm_num⟩
  | 3 => ⟨((-134766654160639/2147483648), (396153870328249/2147483648)), (1263/4294967296), by norm_num⟩
  | 4 => ⟨((574686200116919/8589934592), (-1240403573028489/8589934592)), (2303/8589934592), by norm_num⟩
  | 5 => ⟨((-460231819764905/8589934592), (191969023165061/2147483648)), (839/4294967296), by norm_num⟩
  | 6 => ⟨((294783591384941/8589934592), (-390955778220855/8589934592)), (127/1073741824), by norm_num⟩
  | 7 => ⟨((-628673046423119/34359738368), (671978280884701/34359738368)), (1053/17179869184), by norm_num⟩
  | 8 => ⟨((8963753477267/1073741824), (-991740746764579/137438953472)), (3811/137438953472), by norm_num⟩
  | 9 => ⟨((-914331656360689/274877906944), (635115180330611/274877906944)), (3063/274877906944), by norm_num⟩
  | 10 => ⟨((1292452513816861/1099511627776), (-709025740929151/1099511627776)), (2211/549755813888), by norm_num⟩
  | 11 => ⟨((-25627478174921/68719476736), (171823377748673/1099511627776)), (1449/1099511627776), by norm_num⟩
  | 12 => ⟨((235873961433907/2199023255552), (-283960801394135/8796093022208)), (869/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct3 : Sound J_zetaCorrProduct3 F_zetaCorrProduct3 c := by
  apply sound_round (sound_mul (A_rising5 hcre) (A_term27 hcre) S_rising5 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct3, J_rising5, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8688106126675/9444732965739290427392), (-369814525598483/4722366482869645213696)), (391/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-69902699501809/2361183241434822606848), (1192016776012353/4722366482869645213696)), (1435/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((107514820773673/1180591620717411303424), (-951881662187169/2361183241434822606848)), (1315/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-341492889447369/2361183241434822606848), (250959205537033/590295810358705651712)), (1601/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((91014377882347/590295810358705651712), (-785782289529557/2361183241434822606848)), (365/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-291551895619149/2361183241434822606848), (972882450979071/4722366482869645213696)), (2127/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((746968907187707/9444732965739290427392), (-495332540465259/4722366482869645213696)), (161/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-796515193160499/18889465931478580854784), (106422748924069/2361183241434822606848)), (2669/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((363420235584045/18889465931478580854784), (-314128535082237/18889465931478580854784)), (2415/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-144804811503867/18889465931478580854784), (804677237903607/151115727451828646838272)), (1941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((818754732329297/302231454903657293676544), (-449160162190135/302231454903657293676544)), (1401/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1039022790996525/1208925819614629174706176), (435393028842729/1208925819614629174706176)), (3673/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((597694445537315/2417851639229258349412352), (-359772212057319/4835703278458516698824704)), (4405/4835703278458516698824704), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr3 : Sound J_zetaCorr3 F_zetaCorr3 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct3 hcre) S_zetaCorrProduct3)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr3, J_zetaCorrProduct3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1615520034742311/4503599627370496), (-242038537961947/2251799813685248)), (1903/1125899906842624), by norm_num⟩
  | 1 => ⟨((74245364630007/281474976710656), (718233457131771/2251799813685248)), (7833/2251799813685248), by norm_num⟩
  | 2 => ⟨((300549040581317/1125899906842624), (-29973286704293/70368744177664)), (9209/2251799813685248), by norm_num⟩
  | 3 => ⟨((-525479494431867/1125899906842624), (235074017317785/562949953421312)), (7857/2251799813685248), by norm_num⟩
  | 4 => ⟨((927268470868505/2251799813685248), (-747996913630679/2251799813685248)), (5301/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1222023348413957/4503599627370496), (494187966372771/2251799813685248)), (2963/2251799813685248), by norm_num⟩
  | 6 => ⟨((660437923334693/4503599627370496), (-275843063748173/2251799813685248)), (2833/4503599627370496), by norm_num⟩
  | 7 => ⟨((-609257981559059/9007199254740992), (529898283394973/9007199254740992)), (1183/4503599627370496), by norm_num⟩
  | 8 => ⟨((490952229397177/18014398509481984), (-445430805624665/18014398509481984)), (3515/36028797018963968), by norm_num⟩
  | 9 => ⟨((-351246321765939/36028797018963968), (664971475076461/72057594037927936)), (1173/36028797018963968), by norm_num⟩
  | 10 => ⟨((451831151129881/144115188075855872), (-892218366181201/288230376151711744)), (2845/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1055593645753611/1152921504606846976), (543359074388133/576460752303423488)), (3165/1152921504606846976), by norm_num⟩
  | 12 => ⟨((35283117437523/144115188075855872), (-605787980532183/2305843009213693952)), (203/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart3 : Sound J_zetaPart3 F_zetaPart3 c := by
  apply sound_round (sound_add (A_zetaPart2 hcre) (A_zetaCorr3 hcre) S_zetaPart2 S_zetaCorr3)
  intro k
  fin_cases k <;> norm_num [J_zetaPart3, J_zetaPart2, J_zetaCorr3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((805179255352549/134217728), (717952361943617/134217728)), (515/67108864), by norm_num⟩
  | 1 => ⟨((-1086937259291/65536), (-330943747101207/16777216)), (955/33554432), by norm_num⟩
  | 2 => ⟨((732691154877463/33554432), (590924889750553/16777216)), (887/16777216), by norm_num⟩
  | 3 => ⟨((-596321494734325/33554432), (-171388740623477/4194304)), (2201/33554432), by norm_num⟩
  | 4 => ⟨((316865287127351/33554432), (1167153175710721/33554432)), (513/8388608), by norm_num⟩
  | 5 => ⟨((-187395366603053/67108864), (-1558696925674413/67108864)), (1531/33554432), by norm_num⟩
  | 6 => ⟨((-22113387956063/67108864), (1702794055983585/134217728)), (1905/67108864), by norm_num⟩
  | 7 => ⟨((135687173702657/134217728), (-1565525434229799/268435456)), (4063/268435456), by norm_num⟩
  | 8 => ⟨((-202869796862555/268435456), (617876557387919/268435456)), (3791/536870912), by norm_num⟩
  | 9 => ⟨((423665394263257/1073741824), (-849402820856103/1073741824)), (393/134217728), by norm_num⟩
  | 10 => ⟨((-178529654848591/1073741824), (1026527342640205/4294967296)), (293/268435456), by norm_num⟩
  | 11 => ⟨((1026577960921085/17179869184), (-274080721245559/4294967296)), (6351/17179869184), by norm_num⟩
  | 12 => ⟨((-161956344535321/8589934592), (517459383425983/34359738368)), (3939/34359738368), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct4 : Sound J_zetaCorrProduct4 F_zetaCorrProduct4 c := by
  apply sound_round (sound_mul (A_rising7 hcre) (A_term27 hcre) S_rising7 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct4, J_rising7, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1146368425565599/2417851639229258349412352), (-1022179736153335/2417851639229258349412352)), (1467/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((396164978000541/302231454903657293676544), (235589441601471/151115727451828646838272)), (1361/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-521581995598577/302231454903657293676544), (-841325246505833/302231454903657293676544)), (79/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((424504312862727/302231454903657293676544), (61003385097825/18889465931478580854784)), (49/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-225567386334069/302231454903657293676544), (-1661726304470609/604462909807314587353088)), (1461/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((133401432005951/604462909807314587353088), (1109592012425199/604462909807314587353088)), (2181/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((31483783973065/1208925819614629174706176), (-1212170661404871/1208925819614629174706176)), (2713/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-24147960012155/302231454903657293676544), (278613258366163/604462909807314587353088)), (2893/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((288834477637295/4835703278458516698824704), (-879697497890137/4835703278458516698824704)), (675/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-37699418154373/1208925819614629174706176), (1209331422714611/19342813113834066795298816)), (4477/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((254180367893281/19342813113834066795298816), (-182688905259245/9671406556917033397649408)), (1669/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-730791654751567/154742504910672534362390528), (195110270665495/38685626227668133590597632)), (2261/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((922336925404385/618970019642690137449562112), (-11511394332551/9671406556917033397649408)), (5609/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr4 : Sound J_zetaCorr4 F_zetaCorr4 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct4 hcre) S_zetaCorrProduct4)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr4, J_zetaCorrProduct4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1615520032607033/4503599627370496), (-121019269456963/1125899906842624)), (7613/4503599627370496), by norm_num⟩
  | 1 => ⟨((593962919991715/2251799813685248), (718233460642327/2251799813685248)), (3917/1125899906842624), by norm_num⟩
  | 2 => ⟨((601098077276545/2251799813685248), (-479572590402869/1125899906842624)), (4605/1125899906842624), by norm_num⟩
  | 3 => ⟨((-525479492850465/1125899906842624), (470148038271655/1125899906842624)), (3929/1125899906842624), by norm_num⟩
  | 4 => ⟨((927268469187897/2251799813685248), (-186999229955273/562949953421312)), (2651/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1222023347420039/4503599627370496), (988375941012647/4503599627370496)), (5927/4503599627370496), by norm_num⟩
  | 6 => ⟨((660437923451979/4503599627370496), (-275843066006017/2251799813685248)), (1417/2251799813685248), by norm_num⟩
  | 7 => ⟨((-152314495569681/2251799813685248), (264949143773317/4503599627370496)), (2367/9007199254740992), by norm_num⟩
  | 8 => ⟨((981904460946339/36028797018963968), (-890861617803587/36028797018963968)), (879/9007199254740992), by norm_num⟩
  | 9 => ⟨((-351246322889469/36028797018963968), (166242869895393/18014398509481984)), (2347/72057594037927936), by norm_num⟩
  | 10 => ⟨((903662306047345/288230376151711744), (-892218371625755/288230376151711744)), (1423/144115188075855872), by norm_num⟩
  | 11 => ⟨((-1055593651198433/1152921504606846976), (1086718154591005/1152921504606846976)), (1583/576460752303423488), by norm_num⟩
  | 12 => ⟨((564529882436341/2305843009213693952), (-605787983276713/2305843009213693952)), (1625/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart4 : Sound J_zetaPart4 F_zetaPart4 c := by
  apply sound_round (sound_add (A_zetaPart3 hcre) (A_zetaCorr4 hcre) S_zetaPart3 S_zetaCorr4)
  intro k
  fin_cases k <;> norm_num [J_zetaPart4, J_zetaPart3, J_zetaCorr4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1052927561319173/524288), (192072520609175/262144)), (1027/524288), by norm_num⟩
  | 1 => ⟨((13639700360007/2048), (-300677415083623/262144)), (2051/262144), by norm_num⟩
  | 2 => ⟨((-702606512393541/65536), (-13644897624029/131072)), (1019/65536), by norm_num⟩
  | 3 => ⟨((1464736402717443/131072), (282885420394667/131072)), (2685/131072), by norm_num⟩
  | 4 => ⟨((-1110394300696925/131072), (-433887865864493/131072)), (165/8192), by norm_num⟩
  | 5 => ⟨((650268537408791/131072), (805858836402869/262144)), (4133/262144), by norm_num⟩
  | 6 => ⟨((-607885294548587/262144), (-138013747486943/65536)), (2685/262144), by norm_num⟩
  | 7 => ⟨((918692252744739/1048576), (1206669643379869/1048576)), (5951/1048576), by norm_num⟩
  | 8 => ⟨((-277347066323843/1048576), (-548854807685167/1048576)), (2875/1048576), by norm_num⟩
  | 9 => ⟨((250288947579987/4194304), (853845129958997/4194304)), (9843/8388608), by norm_num⟩
  | 10 => ⟨((-119094595062369/16777216), (-289170023344975/4194304)), (3779/8388608), by norm_num⟩
  | 11 => ⟨((-55123091565597/33554432), (1381900222489605/67108864)), (10517/67108864), by norm_num⟩
  | 12 => ⟨((392839488488287/268435456), (-367152660277113/67108864)), (6687/134217728), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct5 : Sound J_zetaCorrProduct5 F_zetaCorrProduct5 c := by
  apply sound_round (sound_mul (A_rising9 hcre) (A_term27 hcre) S_rising9 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct5, J_rising9, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-425399878821295/77371252455336267181195264), (310401702809167/154742504910672534362390528)), (415/77371252455336267181195264), by norm_num⟩
  | 1 => ⟨((705364611928895/38685626227668133590597632), (-242957142807853/77371252455336267181195264)), (829/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((-567728942068529/19342813113834066795298816), (-11025521619965/38685626227668133590597632)), (103/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((1183554711855929/38685626227668133590597632), (114290315855569/19342813113834066795298816)), (1085/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((-897234754437475/38685626227668133590597632), (-175297762487609/19342813113834066795298816)), (1067/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((525438153919019/38685626227668133590597632), (162790045558003/19342813113834066795298816)), (835/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-982382226994735/154742504910672534362390528), (-223039204645993/38685626227668133590597632)), (1085/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((92791657125501/38685626227668133590597632), (975028366487085/309485009821345068724781056)), (4809/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-112052730633993/154742504910672534362390528), (-443492557811353/309485009821345068724781056)), (4647/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((404483240375777/2475880078570760549798248448), (86241833759589/154742504910672534362390528)), (3977/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-192464622141069/9903520314283042199192993792), (-467317591100323/2475880078570760549798248448)), (12215/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-89082506085723/19807040628566084398385987584), (279155095177531/4951760157141521099596496896)), (8499/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((317427099333911/79228162514264337593543950336), (-1186685222638637/79228162514264337593543950336)), (10807/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr5 : Sound J_zetaCorr5 F_zetaCorr5 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct5 hcre) S_zetaCorrProduct5)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr5, J_zetaCorrProduct5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1615520032582271/4503599627370496), (-242038538909409/2251799813685248)), (3807/2251799813685248), by norm_num⟩
  | 1 => ⟨((593962920032773/2251799813685248), (89779182579407/281474976710656)), (7835/2251799813685248), by norm_num⟩
  | 2 => ⟨((601098077210453/2251799813685248), (-239786295201595/562949953421312)), (9211/2251799813685248), by norm_num⟩
  | 3 => ⟨((-525479492816019/1125899906842624), (940296076556615/2251799813685248)), (7859/2251799813685248), by norm_num⟩
  | 4 => ⟨((927268469135671/2251799813685248), (-747996919841499/2251799813685248)), (5303/2251799813685248), by norm_num⟩
  | 5 => ⟨((-611011673679435/2251799813685248), (494187970525275/2251799813685248)), (741/562949953421312), by norm_num⟩
  | 6 => ⟨((165109480855847/1125899906842624), (-551686132037999/4503599627370496)), (2835/4503599627370496), by norm_num⟩
  | 7 => ⟨((-609257982257119/9007199254740992), (529898287575011/9007199254740992)), (37/140737488355328), by norm_num⟩
  | 8 => ⟨((490952230460125/18014398509481984), (-55678851115951/2251799813685248)), (3517/36028797018963968), by norm_num⟩
  | 9 => ⟨((-351246322883583/36028797018963968), (664971479621731/72057594037927936)), (587/18014398509481984), by norm_num⟩
  | 10 => ⟨((56478894127609/18014398509481984), (-446109185840079/144115188075855872)), (2847/288230376151711744), by norm_num⟩
  | 11 => ⟨((-527796825601809/576460752303423488), (1086718154656001/1152921504606846976)), (3167/1152921504606846976), by norm_num⟩
  | 12 => ⟨((564529882445579/2305843009213693952), (-302893991655625/1152921504606846976)), (813/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart5 : Sound J_zetaPart5 F_zetaPart5 c := by
  apply sound_round (sound_add (A_zetaPart4 hcre) (A_zetaCorr5 hcre) S_zetaPart4 S_zetaCorr5)
  intro k
  fin_cases k <;> norm_num [J_zetaPart5, J_zetaPart4, J_zetaCorr5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-72317357208009/2048), (-1326496916779745/2048)), (1411/2048), by norm_num⟩
  | 1 => ⟨((-162539072976223/512), (127593570241935/64)), (1425/512), by norm_num⟩
  | 2 => ⟨((586458096911559/512), (-47035148868447/16)), (2861/512), by norm_num⟩
  | 3 => ⟨((-467568441521223/256), (176006087725713/64)), (1903/256), by norm_num⟩
  | 4 => ⟨((239357128292853/128), (-926458017684791/512)), (59/8), by norm_num⟩
  | 5 => ⟨((-718113343131953/512), (442923497449485/512)), (373/64), by norm_num⟩
  | 6 => ⟨((844393913816589/1024), (-294765003902993/1024)), (3915/1024), by norm_num⟩
  | 7 => ⟨((-810339550644351/2048), (193267110778349/4096)), (4387/2048), by norm_num⟩
  | 8 => ⟨((1302284738591751/8192), (64459690406373/4096)), (8581/8192), by norm_num⟩
  | 9 => ⟨((-222545663731505/4096), (-291126460113547/16384)), (1861/4096), by norm_num⟩
  | 10 => ⟨((521613277688525/32768), (615982429547343/65536)), (11601/65536), by norm_num⟩
  | 11 => ⟨((-523123676735311/131072), (-3810601902065/1024)), (8203/131072), by norm_num⟩
  | 12 => ⟨((220613098080445/262144), (1279705046403057/1048576)), (21233/1048576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct6 : Sound J_zetaCorrProduct6 F_zetaCorrProduct6 c := by
  apply sound_round (sound_mul (A_rising11 hcre) (A_term27 hcre) S_rising11 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct6, J_rising11, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16620696761449/4951760157141521099596496896), (304868759866011/4951760157141521099596496896)), (649/9903520314283042199192993792), by norm_num⟩
  | 1 => ⟨((149425407571483/4951760157141521099596496896), (-1876788972673989/9903520314283042199192993792)), (1311/4951760157141521099596496896), by norm_num⟩
  | 2 => ⟨((-269571305379061/2475880078570760549798248448), (1383691177494275/4951760157141521099596496896)), (2631/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((53730622783923/309485009821345068724781056), (-647223609976515/2475880078570760549798248448)), (875/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-220045776042609/1237940039285380274899124224), (106463913842019/618970019642690137449562112)), (217/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((330087950592991/2475880078570760549798248448), (-407188394258023/4951760157141521099596496896)), (343/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((-776268145330081/9903520314283042199192993792), (270983339817975/9903520314283042199192993792)), (225/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((1489922581803297/39614081257132168796771975168), (-177674304826645/39614081257132168796771975168)), (8067/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-598608150874161/39614081257132168796771975168), (-118518154860067/79228162514264337593543950336)), (3945/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((51147665446589/9903520314283042199192993792), (33454794254051/19807040628566084398385987584)), (1711/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-29970592295947/19807040628566084398385987584), (-283142458938007/316912650057057350374175801344)), (5333/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((120229504166517/316912650057057350374175801344), (224202383097691/633825300114114700748351602688)), (3771/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-811256062746225/10141204801825835211973625643008), (-588229170465469/5070602400912917605986812821504)), (19521/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr6 : Sound J_zetaCorr6 F_zetaCorr6 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct6 hcre) S_zetaCorrProduct6)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr6, J_zetaCorrProduct6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((807760016291143/2251799813685248), (-484077077818541/4503599627370496)), (7615/4503599627370496), by norm_num⟩
  | 1 => ⟨((593962920032841/2251799813685248), (718233460634829/2251799813685248)), (1959/562949953421312), by norm_num⟩
  | 2 => ⟨((18784314912819/70368744177664), (-959145180805751/2251799813685248)), (2303/562949953421312), by norm_num⟩
  | 3 => ⟨((-1050958985631647/2251799813685248), (470148038278013/1125899906842624)), (1965/562949953421312), by norm_num⟩
  | 4 => ⟨((927268469135271/2251799813685248), (-93499614980139/281474976710656)), (663/281474976710656), by norm_num⟩
  | 5 => ⟨((-611011673679135/2251799813685248), (247093985262545/1125899906842624)), (5929/4503599627370496), by norm_num⟩
  | 6 => ⟨((660437923423035/4503599627370496), (-137921533009469/1125899906842624)), (709/1125899906842624), by norm_num⟩
  | 7 => ⟨((-152314495564195/2251799813685248), (529898287574971/9007199254740992)), (2369/9007199254740992), by norm_num⟩
  | 8 => ⟨((490952230459853/18014398509481984), (-445430808927635/18014398509481984)), (1759/18014398509481984), by norm_num⟩
  | 9 => ⟨((-351246322883397/36028797018963968), (664971479621853/72057594037927936)), (2349/72057594037927936), by norm_num⟩
  | 10 => ⟨((225915576510327/72057594037927936), (-27881824115013/9007199254740992)), (89/9007199254740992), by norm_num⟩
  | 11 => ⟨((-1055593651203181/1152921504606846976), (1086718154656409/1152921504606846976)), (99/36028797018963968), by norm_num⟩
  | 12 => ⟨((564529882445395/2305843009213693952), (-605787983311517/2305843009213693952)), (1627/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart6 : Sound J_zetaPart6 F_zetaPart6 c := by
  apply sound_round (sound_add (A_zetaPart5 hcre) (A_zetaCorr6 hcre) S_zetaPart5 S_zetaCorr6)
  intro k
  fin_cases k <;> norm_num [J_zetaPart6, J_zetaPart5, J_zetaCorr6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-1, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q13 : Sound J_q13 F_q13 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (-1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_sminusone : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_sminusone : Sound J_sminusone F_sminusone c := by
  apply sound_round (sound_add (A_variable hcre) (A_q13 hcre) S_variable S_q13)
  intro k
  fin_cases k <;> norm_num [J_sminusone, J_variable, J_q13, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaRegularPart : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((410638917347825/281474976710656), (1416336404096775/281474976710656)), (6719/281474976710656), by norm_num⟩
  | 1 => ⟨((-1164307404876999/281474976710656), (997203840383071/281474976710656)), (14303/281474976710656), by norm_num⟩
  | 2 => ⟨((54441862786795/8796093022208), (577962174176987/140737488355328)), (8617/140737488355328), by norm_num⟩
  | 3 => ⟨((-776382952458917/140737488355328), (-986214636688781/140737488355328)), (7511/140737488355328), by norm_num⟩
  | 4 => ⟨((581093280611555/140737488355328), (875383543065019/140737488355328)), (5171/140737488355328), by norm_num⟩
  | 5 => ⟨((-369372972651903/140737488355328), (-1169716032544229/281474976710656)), (5895/281474976710656), by norm_num⟩
  | 6 => ⟨((801678087308201/562949953421312), (1287095007852205/562949953421312)), (2873/281474976710656), by norm_num⟩
  | 7 => ⟨((-94002517999035/140737488355328), (-605814595327203/562949953421312)), (2445/562949953421312), by norm_num⟩
  | 8 => ⟨((618952803126585/2251799813685248), (498988776194577/1125899906842624)), (3697/2251799813685248), by norm_num⟩
  | 9 => ⟨((-113300415555559/1125899906842624), (-730787938779051/4503599627370496)), (2513/4503599627370496), by norm_num⟩
  | 10 => ⟨((298720851230191/9007199254740992), (481672114975939/9007199254740992)), (3101/18014398509481984), by norm_num⟩
  | 11 => ⟨((-716026172085367/72057594037927936), (-1154518968742389/72057594037927936)), (877/18014398509481984), by norm_num⟩
  | 12 => ⟨((393320355902731/144115188075855872), (1268355581855463/288230376151711744)), (229/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaRegularPart : Sound J_zetaRegularPart F_zetaRegularPart c := by
  apply sound_round (sound_mul (A_sminusone hcre) (A_zetaPart6 hcre) S_sminusone S_zetaPart6)
  intro k
  fin_cases k <;> norm_num [J_zetaRegularPart, J_sminusone, J_zetaPart6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaIntegral : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-447980087549937/562949953421312), (-722300812267319/562949953421312)), (651/562949953421312), by norm_num⟩
  | 1 => ⟨((369117321945733/140737488355328), (595146411353875/140737488355328)), (539/140737488355328), by norm_num⟩
  | 2 => ⟨((-38017202423423/8796093022208), (-245188185401285/35184372088832)), (893/140737488355328), by norm_num⟩
  | 3 => ⟨((83532331526311/17592186044416), (538733507036173/70368744177664)), (987/140737488355328), by norm_num⟩
  | 4 => ⟨((-550617875495423/140737488355328), (-887788876720811/140737488355328)), (409/70368744177664), by norm_num⟩
  | 5 => ⟨((725898677255519/281474976710656), (1170402923650009/281474976710656)), (1085/281474976710656), by norm_num⟩
  | 6 => ⟨((-797481207160839/562949953421312), (-642909517307491/281474976710656)), (1199/562949953421312), by norm_num⟩
  | 7 => ⟨((46935142187613/70368744177664), (302703555521011/281474976710656)), (1135/1125899906842624), by norm_num⟩
  | 8 => ⟨((-77345285966545/281474976710656), (-15588461527449/35184372088832)), (941/2251799813685248), by norm_num⟩
  | 9 => ⟨((226593284355721/2251799813685248), (182673870885179/1125899906842624)), (693/4503599627370496), by norm_num⟩
  | 10 => ⟨((-298725800067435/9007199254740992), (-240825311247635/4503599627370496)), (919/18014398509481984), by norm_num⟩
  | 11 => ⟨((716037457955557/72057594037927936), (1154503184111887/72057594037927936)), (1107/72057594037927936), by norm_num⟩
  | 12 => ⟨((-786647550456649/288230376151711744), (-1268351385371781/288230376151711744)), (1223/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaIntegral : Sound J_zetaIntegral F_zetaIntegral c := by
  apply sound_round (sound_scale (A_term27 hcre) S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaIntegral, J_term27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23331109196607/35184372088832), (263796499490779/70368744177664)), (3523/140737488355328), by norm_num⟩
  | 1 => ⟨((-106518190246383/70368744177664), (546874165772705/70368744177664)), (1923/35184372088832), by norm_num⟩
  | 2 => ⟨((4106165090843/2199023255552), (-402790567428153/140737488355328)), (4755/70368744177664), by norm_num⟩
  | 3 => ⟨((-108124300248429/140737488355328), (91252377383565/140737488355328)), (4249/70368744177664), by norm_num⟩
  | 4 => ⟨((7618851279033/35184372088832), (-775333353487/8796093022208)), (5989/140737488355328), by norm_num⟩
  | 5 => ⟨((-12847268048287/281474976710656), (171722776445/70368744177664)), (1745/70368744177664), by norm_num⟩
  | 6 => ⟨((2098440073681/281474976710656), (1275973237223/562949953421312)), (6945/562949953421312), by norm_num⟩
  | 7 => ⟨((-132233623809/140737488355328), (-407484285181/562949953421312)), (6025/1125899906842624), by norm_num⟩
  | 8 => ⟨((190515394225/2251799813685248), (158007316209/1125899906842624)), (2319/1125899906842624), by norm_num⟩
  | 9 => ⟨((-7546755397/2251799813685248), (-92455238335/4503599627370496)), (1603/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1237209311/2251799813685248), (21492480669/9007199254740992)), (1005/4503599627370496), by norm_num⟩
  | 11 => ⟨((5642935095/36028797018963968), (-7892315251/36028797018963968)), (4615/72057594037927936), by norm_num⟩
  | 12 => ⟨((-6838651187/288230376151711744), (2098241841/144115188075855872)), (4887/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaFinite : Sound J_zetaFinite F_zetaFinite c := by
  apply sound_round (sound_add (A_zetaRegularPart hcre) (A_zetaIntegral hcre) S_zetaRegularPart S_zetaIntegral)
  intro k
  fin_cases k <;> norm_num [J_zetaFinite, J_zetaRegularPart, J_zetaIntegral, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23331109196607/35184372088832), (263796499490779/70368744177664)), (16895545/281474976710656), by norm_num⟩
  | 1 => ⟨((-106518190246383/70368744177664), (546874165772705/70368744177664)), (4225971/70368744177664), by norm_num⟩
  | 2 => ⟨((4106165090843/2199023255552), (-402790567428153/140737488355328)), (16907519/281474976710656), by norm_num⟩
  | 3 => ⟨((-108124300248429/140737488355328), (91252377383565/140737488355328)), (67621979/1125899906842624), by norm_num⟩
  | 4 => ⟨((7618851279033/35184372088832), (-775333353487/8796093022208)), (135203813/2251799813685248), by norm_num⟩
  | 5 => ⟨((-12847268048287/281474976710656), (171722776445/70368744177664)), (1081310631/18014398509481984), by norm_num⟩
  | 6 => ⟨((2098440073681/281474976710656), (1275973237223/562949953421312)), (8648689205/144115188075855872), by norm_num⟩
  | 7 => ⟨((-132233623809/140737488355328), (-407484285181/562949953421312)), (69181459877/1152921504606846976), by norm_num⟩
  | 8 => ⟨((190515394225/2251799813685248), (158007316209/1125899906842624)), (138355329865/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-7546755397/2251799813685248), (-92455238335/4503599627370496)), (4427271104795/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-1237209311/2251799813685248), (21492480669/9007199254740992)), (35417880348883/590295810358705651712), by norm_num⟩
  | 11 => ⟨((5642935095/36028797018963968), (-7892315251/36028797018963968)), (283342291420819/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-6838651187/288230376151711744), (2098241841/144115188075855872)), (1133368276163147/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := by
  apply sound_round (zeta_sound hc S_zetaFinite)
  intro k
  fin_cases k <;> norm_num [J_zetaActual,J_zetaFinite,inflate,zero,size]

private def J_negativeHalfLogPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1288851271837807/2251799813685248), 0), (7/2251799813685248), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piArg : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35242026964315/70368744177664), (-1126926744374981/140737488355328)), (7/140737488355328), by norm_num⟩
  | 1 => ⟨((-1288851271837807/2251799813685248), 0), (7/2251799813685248), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piPower : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-208404547788361/2251799813685248), (-1348659977821177/2251799813685248)), (295/1125899906842624), by norm_num⟩
  | 1 => ⟨((119283457100133/2251799813685248), (771925691230445/2251799813685248)), (343/2251799813685248), by norm_num⟩
  | 2 => ⟨((-136547338229957/9007199254740992), (-1767292816812893/18014398509481984)), (797/18014398509481984), by norm_num⟩
  | 3 => ⟨((208413091873357/72057594037927936), (1348715269635125/72057594037927936)), (309/36028797018963968), by norm_num⟩
  | 4 => ⟨((-59644173717427/144115188075855872), (-1543914676652759/576460752303423488)), (359/288230376151711744), by norm_num⟩
  | 5 => ⟨((109242349073811/2305843009213693952), (1413892217252741/4611686018427387904)), (667/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1302635226929/288230376151711744), (-1079016450972723/36893488147419103232)), (517/36893488147419103232), by norm_num⟩
  | 7 => ⟨((218136206573837/590295810358705651712), (1411637004287577/590295810358705651712)), (343/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-124853517425445/4722366482869645213696), (-1615943066778907/9444732965739290427392)), (199/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((254086316000579/151115727451828646838272), (822141476610199/75557863725914323419136)), (821/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-116344079804495/1208925819614629174706176), (-94112991867205/151115727451828646838272)), (381/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((96860032868257/19342813113834066795298816), (78351966863339/2417851639229258349412352)), (161/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-295676198316397/1237940039285380274899124224), (-14948639680591/9671406556917033397649408)), (249/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395830848504431/2535301200456458802993406410752), (-561461707753/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781194582678763/633825300114114700748351602688), (-83273322129/19807040628566084398385987584)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892470398389033/39614081257132168796771975168), (-187356096337/2475880078570760549798248448)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892415414869755/2475880078570760549798248448), (-3184890010731/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774080999452457/154742504910672534362390528), (-1592352941261/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552262386547515/9671406556917033397649408), (-373183260599/1208925819614629174706176)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261158318369665/604462909807314587353088), (-2612087094811/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945820688700027/37778931862957161709568), (-2122137215865/37778931862957161709568)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300425293957269/4722366482869645213696), (-3182884508927/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625414262631587/590295810358705651712), (-2187971933445/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914214739525159/36893488147419103232), (-5469145991093/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914113607937985/4611686018427387904), (-6151710899183/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599470848463445/1152921504606846976), (-6150362137811/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599687323542003/72057594037927936), (-1345012091603/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498817275005771/36028797018963968), (-4033516337621/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((23409583928709/140737488355328), (-10078464623679/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122901037314081/2251799813685248), (-5035231216795/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((140171342717845/140737488355328), (-15085643260887/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116718446550789/1125899906842624), (-30090816230875/1125899906842624)), (1/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116718446550789/1125899906842624), (-30090816230875/1125899906842624)), (3816844749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((553403825718387/562949953421312), (-59690864796359/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 2 => ⟨((542437285284181/562949953421312), (-117357334299385/1125899906842624)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((258277863530061/281474976710656), (-28270272267837/140737488355328)), (25/1125899906842624), by norm_num⟩
  | 4 => ⟨((902540216618239/1125899906842624), (-207523542108847/562949953421312)), (57/1125899906842624), by norm_num⟩
  | 5 => ⟨((570490108927125/1125899906842624), (-665417383943289/1125899906842624)), (67/562949953421312), by norm_num⟩
  | 6 => ⟨((-208404547788361/2251799813685248), (-1348659977821177/2251799813685248)), (295/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-35242026964315/70368744177664), (-1126926744374981/140737488355328)), (7/140737488355328), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piGamma : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1470249312796247/9223372036854775808), (1841448463101/576460752303423488)), (257883/9223372036854775808), by norm_num⟩
  | 1 => ⟨((286604144555531/4611686018427387904), (1068537226344805/9223372036854775808)), (408039/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-528205509286165/18446744073709551616), (792368295865827/18446744073709551616)), (225753/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-465910255860419/36893488147419103232), (-117902718340643/73786976294838206464)), (7333915/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-188080203383559/295147905179352825856), (-1230972036917679/590295810358705651712)), (14626493/295147905179352825856), by norm_num⟩
  | 5 => ⟨((31513844582767/147573952589676412928), (-775773738772373/4722366482869645213696)), (232931915/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((351243969446745/18889465931478580854784), (569330022070399/37778931862957161709568)), (29022485/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-328180668512181/302231454903657293676544), (664718091964043/604462909807314587353088)), (14834179475/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-160442067851665/9671406556917033397649408), (-603025533844837/4835703278458516698824704)), (474336404527/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1152845308573033/77371252455336267181195264), (127421091741865/38685626227668133590597632)), (948399635845/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-313677430650753/618970019642690137449562112), (417286839246565/309485009821345068724781056)), (30345829374537/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-905049099149195/9903520314283042199192993792), (-5034577911097/77371252455336267181195264)), (60689857571627/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((152486411703981/19807040628566084398385987584), (-23521492486711/4951760157141521099596496896)), (971029741121557/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((216121563274043/2305843009213693952), (1382792331198937/2305843009213693952)), (2848689/288230376151711744), by norm_num⟩
  | 1 => ⟨((-95001818633475/144115188075855872), (111241422723715/72057594037927936)), (12050331/576460752303423488), by norm_num⟩
  | 2 => ⟨((-500157796219869/576460752303423488), (-127683014269895/576460752303423488)), (29414081/1152921504606846976), by norm_num⟩
  | 3 => ⟨((17416112293467/576460752303423488), (-453309901035675/2305843009213693952)), (244728175/9223372036854775808), by norm_num⟩
  | 4 => ⟨((187545822453821/9223372036854775808), (43798698212119/73786976294838206464)), (1974114013/73786976294838206464), by norm_num⟩
  | 5 => ⟨((726728429068751/2361183241434822606848), (200827338380393/590295810358705651712)), (63243776549/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((646482408794587/4722366482869645213696), (149322010102711/4722366482869645213696)), (252932929723/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((8719864288415/75557863725914323419136), (462567779798991/37778931862957161709568)), (2022916130611/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((275382685824625/9671406556917033397649408), (1921874512921871/9671406556917033397649408)), (16180357931341/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-86446273405161/9671406556917033397649408), (1151135035551435/19342813113834066795298816)), (258860370647103/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-94998297101135/38685626227668133590597632), (39194020853009/77371252455336267181195264)), (2070790161186579/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-509354074609/9671406556917033397649408), (9507764689355/77371252455336267181195264)), (2070752573621671/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-462866745721/38685626227668133590597632), (1800662871/38685626227668133590597632)), (2070738854665653/77371252455336267181195264), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((100639/1073741824), (643913/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-707819/1073741824), (828813/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-29113/33554432), (-59457/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((4055/134217728), (-211089/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21833/1073741824), (637/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((165/536870912), (365/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((147/1073741824), (17/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (13/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨43,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/1048576)) (K:=(2783767/1073741824)) (L:=(667371651/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiRectangle.Tile043
