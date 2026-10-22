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
namespace Reinmann.XiBand97.Tile027Terms2
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

private def J_log16 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-69045391/1048576)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1635215371048861/18014398509481984), (-208180692574209/18014398509481984)), (554691319/18014398509481984), by norm_num⟩
  | 1 => ⟨((1080937313/4294967296), (68807535/2147483648)), (369/4294967296), by norm_num⟩
  | 2 => ⟨((-749248651/2147483648), (-47693749/1073741824)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((1384905573/4294967296), (88156767/2147483648)), (477/4294967296), by norm_num⟩
  | 4 => ⟨((-959943393/4294967296), (-122211229/4294967296)), (83/1073741824), by norm_num⟩
  | 5 => ⟨((532305645/4294967296), (67768295/4294967296)), (185/4294967296), by norm_num⟩
  | 6 => ⟨((-122988719/2147483648), (-125262407/17179869184)), (343/17179869184), by norm_num⟩
  | 7 => ⟨((1558844047/68719476736), (198457793/68719476736)), (273/34359738368), by norm_num⟩
  | 8 => ⟨((-270127089/34359738368), (-34390115/34359738368)), (95/34359738368), by norm_num⟩
  | 9 => ⟨((665734507/274877906944), (10594405/34359738368)), (235/274877906944), by norm_num⟩
  | 10 => ⟨((-1476646389/2199023255552), (-93996569/1099511627776)), (523/2199023255552), by norm_num⟩
  | 11 => ⟨((744387841/4398046511104), (189537329/8796093022208)), (529/8796093022208), by norm_num⟩
  | 12 => ⟨((-1375920889/35184372088832), (-175169687/35184372088832)), (491/35184372088832), by norm_num⟩
  | 13 => ⟨((73362745/8796093022208), (9339875/8796093022208)), (421/140737488355328), by norm_num⟩
  | 14 => ⟨((-464925073/281474976710656), (-236760065/1125899906842624)), (669/1125899906842624), by norm_num⟩
  | 15 => ⟨((1374982415/4503599627370496), (87525105/2251799813685248)), (497/4503599627370496), by norm_num⟩
  | 16 => ⟨((-29783287/562949953421312), (-15166945/2251799813685248)), (347/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-981831479579/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778269374311029/633825300114114700748351602688), (-4645356478415/633825300114114700748351602688)), (92657/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((14759215202765/309485009821345068724781056), (-5224909807087/39614081257132168796771975168)), (104269/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888918829905461/2475880078570760549798248448), (-1387527291489/618970019642690137449562112)), (27705/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110661522133847/9671406556917033397649408), (-5548582098325/154742504910672534362390528)), (221717/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774492108994153/4835703278458516698824704), (-5200173491647/9671406556917033397649408)), (207941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629144928952637/302231454903657293676544), (-4548529898191/604462909807314587353088)), (91015/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886980012352247/75557863725914323419136), (-7388320686217/75557863725914323419136)), (147975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296929169261547/4722366482869645213696), (-1384645210961/1180591620717411303424)), (222097/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405151732400553/147573952589676412928), (-3805613983451/295147905179352825856)), (305601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455605018652633/18446744073709551616), (-9507556145921/73786976294838206464)), (382327/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821466315248031/9223372036854775808), (-10687095919711/9223372036854775808)), (430567/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796354778635857/576460752303423488), (-5337985214939/576460752303423488)), (431129/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193458091948517/144115188075855872), (-4664482720561/72057594037927936)), (377871/144115188075855872), by norm_num⟩
  | 4 => ⟨((744970813328203/18014398509481984), (-13968449549253/36028797018963968)), (568073/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487117462281007/9007199254740992), (-17416856651633/9007199254740992)), (712311/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111803261957129/2251799813685248), (-17351383502321/2251799813685248)), (715647/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104719960289013/1125899906842624), (-25863690017941/1125899906842624)), (1081835/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083403676539071/1125899906842624), (-51075632179757/1125899906842624)), (137329/70368744177664), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083403676539071/1125899906842624), (-51075632179757/1125899906842624)), (523868561059451081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((520097212468957/562949953421312), (-24573910766315/281474976710656)), (4428015/1125899906842624), by norm_num⟩
  | 2 => ⟨((476215692757933/562949953421312), (-45406602883067/281474976710656)), (4477531/562949953421312), by norm_num⟩
  | 3 => ⟨((194097491579189/281474976710656), (-614572196802331/2251799813685248)), (36079791/2251799813685248), by norm_num⟩
  | 4 => ⟨((903022782819681/2251799813685248), (-423792278758285/1125899906842624)), (69453433/2251799813685248), by norm_num⟩
  | 5 => ⟨((21549554174625/1125899906842624), (-169950312890155/562949953421312)), (215979577/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1635215371048861/18014398509481984), (-208180692574209/18014398509481984)), (554691319/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-69045391/1048576)), (1/8388608), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40997585/16777216), (-141110235/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-49826831962071/2251799813685248), (756400002239185/9007199254740992)), (270046915/9007199254740992), by norm_num⟩
  | 1 => ⟨((269260493/4294967296), (-510941167/2147483648)), (367/4294967296), by norm_num⟩
  | 2 => ⟨((-381436211/4294967296), (361901333/1073741824)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((180115027/2147483648), (-1367124915/4294967296)), (495/4294967296), by norm_num⟩
  | 4 => ⟨((-255152149/4294967296), (484169569/2147483648)), (11/134217728), by norm_num⟩
  | 5 => ⟨((289160189/8589934592), (-1097404547/8589934592)), (401/8589934592), by norm_num⟩
  | 6 => ⟨((-273084169/17179869184), (129549217/2147483648)), (381/17179869184), by norm_num⟩
  | 7 => ⟨((221058775/34359738368), (-838949875/34359738368)), (619/68719476736), by norm_num⟩
  | 8 => ⟨((-39144167/17179869184), (594230995/68719476736)), (441/137438953472), by norm_num⟩
  | 9 => ⟨((197162269/274877906944), (-748259193/274877906944)), (557/549755813888), by norm_num⟩
  | 10 => ⟨((-446882217/2199023255552), (211997793/274877906944)), (317/1099511627776), by norm_num⟩
  | 11 => ⟨((115101151/2199023255552), (-436825437/2199023255552)), (41/549755813888), by norm_num⟩
  | 12 => ⟨((-108702039/8796093022208), (1650159543/35184372088832)), (311/17592186044416), by norm_num⟩
  | 13 => ⟨((94761867/35184372088832), (-179817463/17592186044416)), (545/140737488355328), by norm_num⟩
  | 14 => ⟨((-76708739/140737488355328), (145560353/70368744177664)), (111/140737488355328), by norm_num⟩
  | 15 => ⟨((115910519/1125899906842624), (-879794207/2251799813685248)), (337/2251799813685248), by norm_num⟩
  | 16 => ⟨((-328399229/18014398509481984), (155790293/2251799813685248)), (479/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (2381740639801/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444549030871347/158456325028528675187087900672), (2816949564147/633825300114114700748351602688)), (184955/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889097564073541/39614081257132168796771975168), (3168390891069/39614081257132168796771975168)), (104055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888832284284781/2475880078570760549798248448), (1682787862133/1237940039285380274899124224)), (110579/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770498438119573/154742504910672534362390528), (1682315744527/77371252455336267181195264)), (55301/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548904340190073/9671406556917033397649408), (394167384601/1208925819614629174706176)), (207429/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314555158192185/151115727451828646838272), (2758169091871/604462909807314587353088)), (181549/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943434386374893/37778931862957161709568), (4480145629131/75557863725914323419136)), (147555/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648423416630913/2361183241434822606848), (209904106255/295147905179352825856)), (110707/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620495492738427/590295810358705651712), (4615220983477/590295810358705651712)), (4759/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1822283437509339/73786976294838206464), (5765024592489/73786976294838206464)), (190459/36893488147419103232), by norm_num⟩
  | 7 => ⟨((14229033191843/72057594037927936), (6480154304901/9223372036854775808)), (428805/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592564044073025/1152921504606846976), (6473287183267/1152921504606846976)), (214573/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193335878128813/144115188075855872), (5656408785295/144115188075855872)), (375887/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489768495297757/36028797018963968), (4234599096031/18014398509481984)), (282299/18014398509481984), by norm_num⟩
  | 3 => ⟨((743459404822641/4503599627370496), (5279783252529/4503599627370496)), (353547/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223262224535385/4503599627370496), (10519259528599/2251799813685248)), (354559/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209055012937645/2251799813685248), (15678435947765/1125899906842624)), (2137503/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083278941767135/1125899906842624), (61913878656379/2251799813685248)), (4315775/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083278941767135/1125899906842624), (61913878656379/2251799813685248)), (16463375100142668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041420224353433/1125899906842624), (59570127454461/1125899906842624)), (4271065/1125899906842624), by norm_num⟩
  | 2 => ⟨((480063759237221/562949953421312), (6887550030131/70368744177664)), (16706287/2251799813685248), by norm_num⟩
  | 3 => ⟨((1615952945330781/2251799813685248), (187950670317555/1125899906842624)), (15881707/1125899906842624), by norm_num⟩
  | 4 => ⟨((1096901282529907/2251799813685248), (67439262902213/281474976710656)), (14048339/562949953421312), by norm_num⟩
  | 5 => ⟨((405061298300847/2251799813685248), (16425575115677/70368744177664)), (163346091/4503599627370496), by norm_num⟩
  | 6 => ⟨((-49826831962071/2251799813685248), (756400002239185/9007199254740992)), (270046915/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-141110235/2097152)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2614043/1048576), (-1151656409/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1327052791077591/18014398509481984), (337856548640915/9007199254740992)), (276858147/18014398509481984), by norm_num⟩
  | 1 => ⟨((-57156025/268435456), (-58205785/536870912)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((330404321/1073741824), (672945429/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((-636660879/2147483648), (-324177077/2147483648)), (273/4294967296), by norm_num⟩
  | 4 => ⟨((7188229/33554432), (234248067/2147483648)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((-531882345/4294967296), (-270825599/4294967296)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((512445903/8589934592), (521857775/17179869184)), (225/17179869184), by norm_num⟩
  | 7 => ⟨((-423188333/17179869184), (-215480425/17179869184)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((611585803/68719476736), (622818535/137438953472)), (17/8589934592), by norm_num⟩
  | 9 => ⟨((-785649037/274877906944), (-100009839/68719476736)), (177/274877906944), by norm_num⟩
  | 10 => ⟨((908327115/1099511627776), (462504983/1099511627776)), (207/1099511627776), by norm_num⟩
  | 11 => ⟨((-954692015/4398046511104), (-486113215/4398046511104)), (219/4398046511104), by norm_num⟩
  | 12 => ⟨((459902473/8796093022208), (468349303/17592186044416)), (213/17592186044416), by norm_num⟩
  | 13 => ⟨((-409012037/35184372088832), (-52065523/8796093022208)), (191/70368744177664), by norm_num⟩
  | 14 => ⟨((168885263/70368744177664), (343974211/281474976710656)), (159/281474976710656), by norm_num⟩
  | 15 => ⟨((-520683941/1125899906842624), (-530247117/2251799813685248)), (247/2251799813685248), by norm_num⟩
  | 16 => ⟨((752485079/9007199254740992), (383152823/9007199254740992)), (45/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (613487384203/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778124145198861/633825300114114700748351602688), (362764588747/316912650057057350374175801344)), (184543/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944508413254937/19807040628566084398385987584), (816044409891/39614081257132168796771975168)), (207621/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888746814732983/2475880078570760549798248448), (108353350061/309485009821345068724781056)), (220607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770413321592639/154742504910672534362390528), (108322372957/19342813113834066795298816)), (55155/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548824918264517/9671406556917033397649408), (812154590907/9671406556917033397649408)), (206843/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314537878274463/151115727451828646838272), (355186086161/302231454903657293676544)), (181001/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378577425861/37778931862957161709568), (1153861714343/75557863725914323419136)), (147075/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162095466632929/590295810358705651712), (864965090079/4722366482869645213696)), (110317/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810191112623067/295147905179352825856), (1188626749583/590295810358705651712)), (151703/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822143343948619/73786976294838206464), (742366919493/36893488147419103232)), (379309/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910580344860839/4611686018427387904), (834441815717/4611686018427387904)), (426793/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12440711235315/9007199254740992), (833541548769/576460752303423488)), (213441/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193204862847851/144115188075855872), (728337351285/72057594037927936)), (373623/144115188075855872), by norm_num⟩
  | 4 => ⟨((744788842302151/18014398509481984), (136310781969/2251799813685248)), (280317/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486690253106069/9007199254740992), (169947561275/562949953421312)), (350573/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111417412051999/2251799813685248), (5417216021805/4503599627370496)), (1403357/4503599627370496), by norm_num⟩
  | 1 => ⟨((276060955437771/281474976710656), (2018315441867/562949953421312)), (1053859/1125899906842624), by norm_num⟩
  | 0 => ⟨((541428695795787/562949953421312), (15937485574515/2251799813685248)), (2113139/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541428695795787/562949953421312), (15937485574515/2251799813685248)), (8060985569480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082807934412219/2251799813685248), (15328204534757/1125899906842624)), (8189245/2251799813685248), by norm_num⟩
  | 2 => ⟨((1926081106266445/2251799813685248), (56711446250697/2251799813685248)), (7686153/1125899906842624), by norm_num⟩
  | 3 => ⟨((102878046076025/140737488355328), (6063529963269/140737488355328)), (13535881/1125899906842624), by norm_num⟩
  | 4 => ⟨((599534699222503/1125899906842624), (70918317185777/1125899906842624)), (10477807/562949953421312), by norm_num⟩
  | 5 => ⟨((1259125951447099/4503599627370496), (151054251643291/2251799813685248)), (99829513/4503599627370496), by norm_num⟩
  | 6 => ⟨((1327052791077591/18014398509481984), (337856548640915/9007199254740992)), (276858147/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1151656409/16777216)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-36662477/524288)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((976821918172407/18014398509481984), (-516235566218665/9007199254740992)), (41381457/2251799813685248), by norm_num⟩
  | 1 => ⟨((-685737737/4294967296), (724803983/4294967296)), (235/4294967296), by norm_num⟩
  | 2 => ⟨((1009556461/4294967296), (-533535275/2147483648)), (87/1073741824), by norm_num⟩
  | 3 => ⟨((-247714783/1073741824), (130913505/536870912)), (43/536870912), by norm_num⟩
  | 4 => ⟨((729381063/4294967296), (-385466827/2147483648)), (255/4294967296), by norm_num⟩
  | 5 => ⟨((-859047213/8589934592), (113498355/1073741824)), (151/4294967296), by norm_num⟩
  | 6 => ⟨((421568683/8589934592), (-891170615/17179869184)), (299/17179869184), by norm_num⟩
  | 7 => ⟨((-709304721/34359738368), (374856785/17179869184)), (127/17179869184), by norm_num⟩
  | 8 => ⟨((522126117/68719476736), (-551871465/68719476736)), (189/68719476736), by norm_num⟩
  | 9 => ⟨((-683274885/274877906944), (90275103/34359738368)), (249/274877906944), by norm_num⟩
  | 10 => ⟨((402372241/549755813888), (-850590503/1099511627776)), (295/1099511627776), by norm_num⟩
  | 11 => ⟨((-107705501/549755813888), (910731575/4398046511104)), (159/2199023255552), by norm_num⟩
  | 12 => ⟨((211421517/4398046511104), (-223466129/4398046511104)), (157/8796093022208), by norm_num⟩
  | 13 => ⟨((-766175699/70368744177664), (809824469/70368744177664)), (287/70368744177664), by norm_num⟩
  | 14 => ⟨((40284957/17592186044416), (-340639819/140737488355328)), (243/281474976710656), by norm_num⟩
  | 15 => ⟨((-1012194967/2251799813685248), (267464843/562949953421312)), (3/17592186044416), by norm_num⟩
  | 16 => ⟨((745086579/9007199254740992), (-787533909/9007199254740992)), (285/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-66196037649/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778051750672813/633825300114114700748351602688), (-78279454783/39614081257132168796771975168)), (184647/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888935369495723/39614081257132168796771975168), (-1408720721643/39614081257132168796771975168)), (1623/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((472165061926741/618970019642690137449562112), (-1496378164519/2475880078570760549798248448)), (110373/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770326733289701/154742504910672534362390528), (-1495942314013/154742504910672534362390528)), (220767/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774371859576027/4835703278458516698824704), (-1401983001849/9671406556917033397649408)), (206991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157260055165979/75557863725914323419136), (-1226272404477/604462909807314587353088)), (45285/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886641621018149/75557863725914323419136), (-248978183535/9444732965739290427392)), (36799/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648338522912209/2361183241434822606848), (-1458115943/4611686018427387904)), (110415/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405065742628817/147573952589676412928), (-1025897832345/295147905179352825856)), (303701/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821994186090319/73786976294838206464), (-2562898565533/73786976294838206464)), (189857/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455248191125849/2305843009213693952), (-1440362411071/4611686018427387904)), (106825/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796121480077351/576460752303423488), (-2877558049405/1152921504606846976)), (427453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298264405881119/36028797018963968), (-1257152608227/72057594037927936)), (374193/144115188075855872), by norm_num⟩
  | 4 => ⟨((744678242625573/18014398509481984), (-3764353012309/36028797018963968)), (561633/36028797018963968), by norm_num⟩
  | 3 => ⟨((185801645299467/1125899906842624), (-1173258329905/2251799813685248)), (702645/9007199254740992), by norm_num⟩
  | 2 => ⟨((555569721141867/1125899906842624), (-9348944496991/4503599627370496)), (703553/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207649396180019/2251799813685248), (-13930966386147/2251799813685248)), (2115223/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082010638973627/1125899906842624), (-27494253839925/2251799813685248)), (531103/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1082010638973627/1125899906842624), (-27494253839925/2251799813685248)), (2025997162938976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2079328779120649/2251799813685248), (-26422486567981/1125899906842624)), (8270153/2251799813685248), by norm_num⟩
  | 2 => ⟨((1918827577049255/2251799813685248), (-48797443185517/1125899906842624)), (15661609/2251799813685248), by norm_num⟩
  | 3 => ⟨((1630861893797215/2251799813685248), (-166327182558249/2251799813685248)), (28049049/2251799813685248), by norm_num⟩
  | 4 => ⟨((1168863132941877/2251799813685248), (-240924315108605/2251799813685248)), (22386291/1125899906842624), by norm_num⟩
  | 5 => ⟨((145238987274715/562949953421312), (-500235497042425/4503599627370496)), (56061667/2251799813685248), by norm_num⟩
  | 6 => ⟨((976821918172407/18014398509481984), (-516235566218665/9007199254740992)), (41381457/2251799813685248), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-36662477/524288)), (1/8388608), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-1193636861/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-302128840256981/9007199254740992), (-1218188332779355/18014398509481984)), (243486477/18014398509481984), by norm_num⟩
  | 1 => ⟨((431583937/4294967296), (870076681/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((-161613741/1073741824), (-1303258397/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((645535333/4294967296), (650702207/2147483648)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-241731379/2147483648), (-974664801/4294967296)), (101/2147483648), by norm_num⟩
  | 5 => ⟨((579329995/8589934592), (36497935/268435456)), (61/2147483648), by norm_num⟩
  | 6 => ⟨((-289252927/8589934592), (-583136223/8589934592)), (123/8589934592), by norm_num⟩
  | 7 => ⟨((495156759/34359738368), (499120001/17179869184)), (53/8589934592), by norm_num⟩
  | 8 => ⟨((-370839271/68719476736), (-186903737/17179869184)), (5/2147483648), by norm_num⟩
  | 9 => ⟨((246874483/137438953472), (995401879/274877906944)), (215/274877906944), by norm_num⟩
  | 10 => ⟨((-591655885/1099511627776), (-596391507/549755813888)), (65/274877906944), by norm_num⟩
  | 11 => ⟨((644524593/4398046511104), (1299366753/4398046511104)), (285/4398046511104), by norm_num⟩
  | 12 => ⟨((-160901927/4398046511104), (-648759153/8796093022208)), (287/17592186044416), by norm_num⟩
  | 13 => ⟨((4634799/549755813888), (598002687/35184372088832)), (267/70368744177664), by norm_num⟩
  | 14 => ⟨((-507780277/281474976710656), (-511844557/140737488355328)), (115/140737488355328), by norm_num⟩
  | 15 => ⟨((405646337/1125899906842624), (817786271/1125899906842624)), (185/1125899906842624), by norm_num⟩
  | 16 => ⟨((-75950489/1125899906842624), (-1224934363/9007199254740992)), (279/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-330743309213/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777979197909059/633825300114114700748351602688), (-3128708611325/633825300114114700748351602688)), (92509/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888853522570627/39614081257132168796771975168), (-1759501381799/19807040628566084398385987584)), (26023/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888572983521061/2475880078570760549798248448), (-3737954357243/2475880078570760549798248448)), (110621/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885119564968725/77371252455336267181195264), (-3736845392577/154742504910672534362390528)), (55323/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548661230941805/9671406556917033397649408), (-218882165713/604462909807314587353088)), (103759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258007904410391/604462909807314587353088), (-191448302053/37778931862957161709568)), (1419/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1886523074736381/75557863725914323419136), (-2487724475449/37778931862957161709568)), (36907/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648293773627401/2361183241434822606848), (-1864828279573/2361183241434822606848)), (55383/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50629342325471/18446744073709551616), (-2562571464283/295147905179352825856)), (19047/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910918867467889/36893488147419103232), (-6401729304295/73786976294838206464)), (47645/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820814793056659/9223372036854775808), (-3597744284595/4611686018427387904)), (107277/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592062539478883/1152921504606846976), (-7187424518335/1152921504606846976)), (214743/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596448503898587/72057594037927936), (-3139967057145/72057594037927936)), (94057/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489110085717027/36028797018963968), (-4700900385215/18014398509481984)), (282597/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486095623462505/9007199254740992), (-5860314918891/4503599627370496)), (353995/9007199254740992), by norm_num⟩
  | 2 => ⟨((555403840292841/1125899906842624), (-23346614366289/4503599627370496)), (710239/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206583600474529/2251799813685248), (-8696017607545/562949953421312)), (1071001/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161611244642635/2251799813685248), (-34314650333857/1125899906842624)), (541167/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161611244642635/2251799813685248), (-34314650333857/1125899906842624)), (2064388277293968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2072943235755949/2251799813685248), (-131761151354307/2251799813685248)), (4287887/2251799813685248), by norm_num⟩
  | 2 => ⟨((475145773577449/562949953421312), (-121295590209825/1125899906842624)), (65597/17592186044416), by norm_num⟩
  | 3 => ⟨((1578011329410067/2251799813685248), (-409507713369667/2251799813685248)), (3995689/562949953421312), by norm_num⟩
  | 4 => ⟨((257840769672643/562949953421312), (-286973916265041/1125899906842624)), (28213905/2251799813685248), by norm_num⟩
  | 5 => ⟨((652183805289855/4503599627370496), (-1051511950517903/4503599627370496)), (80454915/4503599627370496), by norm_num⟩
  | 6 => ⟨((-302128840256981/9007199254740992), (-1218188332779355/18014398509481984)), (243486477/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1193636861/16777216)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22027651/8388608), (-151634637/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1302257205848603/18014398509481984), (31538185194571/9007199254740992)), (107519325/4503599627370496), by norm_num⟩
  | 1 => ⟨((1890540735/8589934592), (-22892645/2147483648)), (313/4294967296), by norm_num⟩
  | 2 => ⟨((-719474211/2147483648), (69697171/4294967296)), (239/2147483648), by norm_num⟩
  | 3 => ⟨((730151793/2147483648), (-35365767/2147483648)), (487/4294967296), by norm_num⟩
  | 4 => ⟨((-1111481759/4294967296), (1682373/134217728)), (373/4294967296), by norm_num⟩
  | 5 => ⟨((676786231/4294967296), (-32780943/4294967296)), (57/1073741824), by norm_num⟩
  | 6 => ⟨((-1373660577/17179869184), (33267439/8589934592)), (465/17179869184), by norm_num⟩
  | 7 => ⟨((1194897271/34359738368), (-57876265/34359738368)), (203/17179869184), by norm_num⟩
  | 8 => ⟨((-113684111/8589934592), (44051397/68719476736)), (155/34359738368), by norm_num⟩
  | 9 => ⟨((307656735/68719476736), (-29803437/137438953472)), (421/274877906944), by norm_num⟩
  | 10 => ⟨((-1498668533/1099511627776), (36294893/549755813888)), (515/1099511627776), by norm_num⟩
  | 11 => ⟨((1659174537/4398046511104), (-20091021/1099511627776)), (143/1099511627776), by norm_num⟩
  | 12 => ⟨((-420949509/4398046511104), (5097297/1099511627776)), (583/17592186044416), by norm_num⟩
  | 13 => ⟨((197167727/8796093022208), (-76400419/70368744177664)), (137/17592186044416), by norm_num⟩
  | 14 => ⟨((-686036079/140737488355328), (16614485/70368744177664)), (479/281474976710656), by norm_num⟩
  | 15 => ⟨((1113947859/1125899906842624), (-6744423/140737488355328)), (195/562949953421312), by norm_num⟩
  | 16 => ⟨((-847859813/4503599627370496), (82134189/9007199254740992)), (149/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (2014615462379/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777907460469901/633825300114114700748351602688), (4764046957509/633825300114114700748351602688)), (92669/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888772455566777/39614081257132168796771975168), (669788000237/4951760157141521099596496896)), (104283/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888486363171713/2475880078570760549798248448), (2845834867297/1237940039285380274899124224)), (27709/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770151962685049/154742504910672534362390528), (5689950667553/154742504910672534362390528)), (110875/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548578931044001/9671406556917033397649408), (5332502641909/9671406556917033397649408)), (103987/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628967655973717/302231454903657293676544), (1166028537879/151115727451828646838272)), (91031/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((14737531449579/590295810358705651712), (3787881668707/37778931862957161709568)), (148003/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296497310888401/4722366482869645213696), (2839414534249/2361183241434822606848)), (111071/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620013338689065/590295810358705651712), (1950881857083/147573952589676412928)), (305669/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821678407993845/73786976294838206464), (9747118608857/73786976294838206464)), (382421/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820632383898307/9223372036854775808), (5477744425871/4611686018427387904)), (430685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795938090812831/576460752303423488), (2735743005933/288230376151711744)), (431261/1152921504606846976), by norm_num⟩
  | 5 => ⟨((582387458537/70368744177664), (597564351139/9007199254740992)), (94501/36028797018963968), by norm_num⟩
  | 4 => ⟨((744425009569333/18014398509481984), (14313428971003/36028797018963968)), (284153/18014398509481984), by norm_num⟩
  | 3 => ⟨((742877581617021/4503599627370496), (8921321760925/4503599627370496)), (356331/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110444296777701/2251799813685248), (17769048376055/2251799813685248)), (358045/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102689910801261/1125899906842624), (1654375101193/70368744177664)), (1082727/1125899906842624), by norm_num⟩
  | 0 => ⟨((33730548365577/35184372088832), (52208227284669/1125899906842624)), (2199979/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((33730548365577/35184372088832), (52208227284669/1125899906842624)), (8392253880027389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516178296318933/562949953421312), (50050975218783/562949953421312)), (4422179/1125899906842624), by norm_num⟩
  | 2 => ⟨((468842624226733/562949953421312), (183570329550751/1125899906842624)), (8895879/1125899906842624), by norm_num⟩
  | 3 => ⟨((751004200406295/1125899906842624), (611532833522263/2251799813685248)), (35436735/2251799813685248), by norm_num⟩
  | 4 => ⟨((13059392661967/35184372088832), (407908130971875/1125899906842624)), (66521901/2251799813685248), by norm_num⟩
  | 5 => ⟨((7329105382375/1125899906842624), (605613473950459/2251799813685248)), (24395759/562949953421312), by norm_num⟩
  | 6 => ⟨((-1302257205848603/18014398509481984), (31538185194571/9007199254740992)), (107519325/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-151634637/2097152)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile027Terms2
