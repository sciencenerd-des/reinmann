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
namespace Reinmann.XiBand97.Tile028Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30757/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30757/1280))
  have he : value ((69/80), (30757/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1771570105/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-277377275780539/2251799813685248), (-387870225273547/4503599627370496)), (244646877/9007199254740992), by norm_num⟩
  | 1 => ⟨((581226509/2147483648), (203189371/1073741824)), (259/4294967296), by norm_num⟩
  | 2 => ⟨((-638542585/2147483648), (-55806585/268435456)), (9/134217728), by norm_num⟩
  | 3 => ⟨((935347641/4294967296), (653971201/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-1027584413/8589934592), (-359230399/4294967296)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((903133491/17179869184), (631447889/17179869184)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((-20670699/1073741824), (-462477607/34359738368)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((830503641/137438953472), (580666951/137438953472)), (99/68719476736), by norm_num⟩
  | 8 => ⟨((-456200753/274877906944), (-79740981/68719476736)), (55/137438953472), by norm_num⟩
  | 9 => ⟨((891000451/2199023255552), (77870597/274877906944)), (217/2199023255552), by norm_num⟩
  | 10 => ⟨((-195772809/2199023255552), (-547517407/8796093022208)), (193/8796093022208), by norm_num⟩
  | 11 => ⟨((1251365317/70368744177664), (874922693/70368744177664)), (311/70368744177664), by norm_num⟩
  | 12 => ⟨((-458255105/140737488355328), (-160200137/70368744177664)), (115/140737488355328), by norm_num⟩
  | 13 => ⟨((1239248467/2251799813685248), (866450901/2251799813685248)), (157/1125899906842624), by norm_num⟩
  | 14 => ⟨((-777973483/9007199254740992), (-135984801/2251799813685248)), (199/9007199254740992), by norm_num⟩
  | 15 => ⟨((227917661/18014398509481984), (637416847/72057594037927936)), (235/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1001572573/576460752303423488), (-700273981/576460752303423488)), (65/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3297458414407/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779037707416221/633825300114114700748351602688), (-487940840353/79228162514264337593543950336)), (92585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890043937582739/39614081257132168796771975168), (-548839809003/4951760157141521099596496896)), (52091/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118114830944989/154742504910672534362390528), (-18219665265/9671406556917033397649408)), (55361/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771502874262533/154742504910672534362390528), (-2331608637995/77371252455336267181195264)), (55377/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774922694345413/4835703278458516698824704), (-4370685729123/9671406556917033397649408)), (51933/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259043440078777/604462909807314587353088), (-119477177843/18889465931478580854784)), (90917/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888204691180515/75557863725914323419136), (-6210787952659/75557863725914323419136)), (36951/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648923886054945/2361183241434822606848), (-1164079785013/1180591620717411303424)), (110909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621870159711465/590295810358705651712), (-6399560182455/590295810358705651712)), (152591/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823999337089335/73786976294838206464), (-7995133290767/73786976294838206464)), (47719/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455810822883805/2305843009213693952), (-140446731489/144115188075855872)), (214923/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797243455662579/576460752303423488), (-2245293906431/288230376151711744)), (215159/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195013695237955/144115188075855872), (-1962547500471/36028797018963968)), (188529/144115188075855872), by norm_num⟩
  | 4 => ⟨((373068963094007/9007199254740992), (-734913513913/2251799813685248)), (70831/9007199254740992), by norm_num⟩
  | 3 => ⟨((745018322227189/4503599627370496), (-7334559610799/4503599627370496)), (355085/9007199254740992), by norm_num⟩
  | 2 => ⟨((278681117928035/562949953421312), (-14625431369647/2251799813685248)), (178241/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109106591398007/1125899906842624), (-21829063508317/1125899906842624)), (33639/70368744177664), by norm_num⟩
  | 0 => ⟨((546097349340163/562949953421312), (-43222613457389/1125899906842624)), (1090493/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546097349340163/562949953421312), (-43222613457389/1125899906842624)), (4159900669578170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057839207795405/1125899906842624), (-83857381982833/1125899906842624)), (2199423/1125899906842624), by norm_num⟩
  | 2 => ⟨((493823528307489/562949953421312), (-39394099770947/281474976710656)), (1115141/281474976710656), by norm_num⟩
  | 3 => ⟨((422158480125397/562949953421312), (-552908356422287/2251799813685248)), (18148479/2251799813685248), by norm_num⟩
  | 4 => ⟨((70659502328845/140737488355328), (-25914265333145/70368744177664)), (36131617/2251799813685248), by norm_num⟩
  | 5 => ⟨((524452998054923/4503599627370496), (-1665365827336851/4503599627370496)), (125785697/4503599627370496), by norm_num⟩
  | 6 => ⟨((-277377275780539/2251799813685248), (-387870225273547/4503599627370496)), (244646877/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1771570105/33554432)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1856519791/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((106184688251577/2251799813685248), (72559099715123/562949953421312)), (21877953/1125899906842624), by norm_num⟩
  | 1 => ⟨((-58293171/536870912), (-637334829/2147483648)), (97/2147483648), by norm_num⟩
  | 2 => ⟨((268449973/2147483648), (1467517677/4294967296)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((-412085937/4294967296), (-563180721/2147483648)), (11/268435456), by norm_num⟩
  | 4 => ⟨((118607867/2147483648), (1296771533/8589934592)), (205/8589934592), by norm_num⟩
  | 5 => ⟨((-218483765/8589934592), (-1194370721/17179869184)), (3/268435456), by norm_num⟩
  | 6 => ⟨((167692487/17179869184), (458356703/17179869184)), (149/34359738368), by norm_num⟩
  | 7 => ⟨((-220643555/68719476736), (-1206177499/137438953472)), (199/137438953472), by norm_num⟩
  | 8 => ⟨((508050561/549755813888), (1388663165/549755813888)), (29/68719476736), by norm_num⟩
  | 9 => ⟨((-8123817/34359738368), (-11102483/17179869184)), (15/137438953472), by norm_num⟩
  | 10 => ⟨((239433983/4398046511104), (1308897887/8796093022208)), (223/8796093022208), by norm_num⟩
  | 11 => ⟨((-200478953/17592186044416), (-1095945005/35184372088832)), (189/35184372088832), by norm_num⟩
  | 12 => ⟨((153873283/70368744177664), (841168877/140737488355328)), (147/140737488355328), by norm_num⟩
  | 13 => ⟨((-218034663/562949953421312), (-1191915641/1125899906842624)), (211/1125899906842624), by norm_num⟩
  | 14 => ⟨((286881923/4503599627370496), (1568278393/9007199254740992)), (35/1125899906842624), by norm_num⟩
  | 15 => ⟨((-352304021/36028797018963968), (-120369815/4503599627370496)), (87/18014398509481984), by norm_num⟩
  | 16 => ⟨((202802497/144115188075855872), (1108646967/288230376151711744)), (203/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1589272751537/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222362980798765/79228162514264337593543950336), (470274203905/158456325028528675187087900672)), (46193/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889893727580069/39614081257132168796771975168), (2115864309061/39614081257132168796771975168)), (51973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889678190395555/2475880078570760549798248448), (2247650232011/2475880078570760549798248448)), (13807/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885672162132015/77371252455336267181195264), (1123568917839/77371252455336267181195264)), (110471/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549697337135711/9671406556917033397649408), (2106147444589/9671406556917033397649408)), (103583/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258914483668101/604462909807314587353088), (1842334900481/604462909807314587353088)), (22663/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117999765002695/4722366482869645213696), (1496387173153/37778931862957161709568)), (147341/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297692398125733/4722366482869645213696), (2243688721915/4722366482869645213696)), (27633/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621658086116517/590295810358705651712), (3083623079301/590295810358705651712)), (152025/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823736590981087/73786976294838206464), (3852356612853/73786976294838206464)), (95049/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227868865448899/1152921504606846976), (4330916205991/9223372036854775808)), (213951/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199274820490395/144115188075855872), (2163593868599/576460752303423488)), (214065/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597382952897263/72057594037927936), (3782098535853/144115188075855872)), (93717/72057594037927936), by norm_num⟩
  | 4 => ⟨((372978293964487/9007199254740992), (2832387905373/18014398509481984)), (281407/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489599014054465/9007199254740992), (7066340074181/9007199254740992)), (352207/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114310318062889/2251799813685248), (7044438084963/2251799813685248)), (352881/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108543717046137/1125899906842624), (21024101649683/2251799813685248)), (1062021/2251799813685248), by norm_num⟩
  | 0 => ⟨((545650182643091/562949953421312), (41613133153663/2251799813685248)), (1068803/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545650182643091/562949953421312), (41613133153663/2251799813685248)), (4077159885886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264344895764221/281474976710656), (80668676025821/2251799813685248)), (4222839/2251799813685248), by norm_num⟩
  | 2 => ⟨((495792173468339/562949953421312), (75759319725973/1125899906842624)), (1029281/281474976710656), by norm_num⟩
  | 3 => ⟨((868194443061739/1125899906842624), (266886088606263/2251799813685248)), (15611997/2251799813685248), by norm_num⟩
  | 4 => ⟨((1307317889303753/2251799813685248), (25724868797199/140737488355328)), (13888945/1125899906842624), by norm_num⟩
  | 5 => ⟨((170937401099141/562949953421312), (119479825779117/562949953421312)), (42408615/2251799813685248), by norm_num⟩
  | 6 => ⟨((106184688251577/2251799813685248), (72559099715123/562949953421312)), (21877953/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1856519791/33554432)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-966683065/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((546558565943175/9007199254740992), (-998893175197063/9007199254740992)), (150850779/9007199254740992), by norm_num⟩
  | 1 => ⟨((-624938107/4294967296), (571070009/2147483648)), (175/4294967296), by norm_num⟩
  | 2 => ⟨((374634033/2147483648), (-1369366075/4294967296)), (53/1073741824), by norm_num⟩
  | 3 => ⟨((-598888785/4294967296), (547266073/2147483648)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((718036293/8589934592), (-1312286729/8589934592)), (209/8589934592), by norm_num⟩
  | 5 => ⟨((-688710333/17179869184), (629345229/8589934592)), (203/17179869184), by norm_num⟩
  | 6 => ⟨((137621271/8589934592), (-251517325/8589934592)), (41/8589934592), by norm_num⟩
  | 7 => ⟨((-754288903/137438953472), (689271091/68719476736)), (227/137438953472), by norm_num⟩
  | 8 => ⟨((452176449/274877906944), (-826399945/274877906944)), (69/137438953472), by norm_num⟩
  | 9 => ⟨((-120474641/274877906944), (110090029/137438953472)), (149/1099511627776), by norm_num⟩
  | 10 => ⟨((462216915/4398046511104), (-6599609/34359738368)), (145/4398046511104), by norm_num⟩
  | 11 => ⟨((-403035547/17592186044416), (184147447/4398046511104)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((644291355/140737488355328), (-588755057/70368744177664)), (207/140737488355328), by norm_num⟩
  | 13 => ⟨((-475367137/562949953421312), (868783365/562949953421312)), (155/562949953421312), by norm_num⟩
  | 14 => ⟨((651360349/4503599627370496), (-595214721/2251799813685248)), (215/4503599627370496), by norm_num⟩
  | 15 => ⟨((-26031565/1125899906842624), (380603351/9007199254740992)), (35/4503599627370496), by norm_num⟩
  | 16 => ⟨((499367733/144115188075855872), (-14260109/2251799813685248)), (85/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-348491907231/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444694387047069/158456325028528675187087900672), (-1649705734179/633825300114114700748351602688)), (46181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944875846225249/19807040628566084398385987584), (-1855582560945/39614081257132168796771975168)), (103919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889527341532605/2475880078570760549798248448), (-1971140466629/2475880078570760549798248448)), (110425/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885596773380193/77371252455336267181195264), (-246334076835/19342813113834066795298816)), (110439/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549556059013535/9671406556917033397649408), (-230876078359/1208925819614629174706176)), (809/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1258790941062941/604462909807314587353088), (-1615635760343/604462909807314587353088)), (45311/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887795625268327/75557863725914323419136), (-2624476975219/75557863725914323419136)), (147287/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297542061182515/4722366482869645213696), (-983771665171/2361183241434822606848)), (110489/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621451574401423/590295810358705651712), (-42250770611/9223372036854775808)), (151961/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823478753461235/73786976294838206464), (-1689039315497/36893488147419103232)), (190009/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911330635698991/4611686018427387904), (-1898806816477/4611686018427387904)), (13365/576460752303423488), by norm_num⟩
  | 6 => ⟨((199238678736923/144115188075855872), (-3794210331507/1152921504606846976)), (213939/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597256747812403/72057594037927936), (-1658054539875/72057594037927936)), (93655/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491535722736163/36028797018963968), (-4966523074639/36028797018963968)), (281189/36028797018963968), by norm_num⟩
  | 3 => ⟨((744564613359765/4503599627370496), (-3097401980205/4503599627370496)), (43985/1125899906842624), by norm_num⟩
  | 2 => ⟨((2227687130031085/4503599627370496), (-6174821216861/2251799813685248)), (704943/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215702281345983/2251799813685248), (-4606210987743/562949953421312)), (1060383/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179890461618237/2251799813685248), (-36452968839941/2251799813685248)), (2132691/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179890461618237/2251799813685248), (-36452968839941/2251799813685248)), (8135570534712981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2109687360681589/2251799813685248), (-70577747265913/2251799813685248)), (4198221/2251799813685248), by norm_num⟩
  | 2 => ⟨((30848931335887/35184372088832), (-2066360712431/35184372088832)), (8129707/2251799813685248), by norm_num⟩
  | 3 => ⟨((1723286401051869/2251799813685248), (-115951515423073/1125899906842624)), (15210827/2251799813685248), by norm_num⟩
  | 4 => ⟨((161867020028443/281474976710656), (-88736871055567/562949953421312)), (13207235/1125899906842624), by norm_num⟩
  | 5 => ⟨((688725495527515/2251799813685248), (-816474589806423/4503599627370496)), (77415057/4503599627370496), by norm_num⟩
  | 6 => ⟨((546558565943175/9007199254740992), (-998893175197063/9007199254740992)), (150850779/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-966683065/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-2003521341/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-528061882322509/4503599627370496), (2551978420805/1125899906842624)), (342475987/18014398509481984), by norm_num⟩
  | 1 => ⟨((1251396639/4294967296), (-24190629/4294967296)), (205/4294967296), by norm_num⟩
  | 2 => ⟨((-1554801915/4294967296), (30055727/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((80490367/268435456), (-24895225/4294967296)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-1600088385/8589934592), (30931155/8589934592)), (269/8589934592), by norm_num⟩
  | 5 => ⟨((1590428107/17179869184), (-30744413/17179869184)), (269/17179869184), by norm_num⟩
  | 6 => ⟨((-658677563/17179869184), (25465665/34359738368)), (225/34359738368), by norm_num⟩
  | 7 => ⟨((1870574007/137438953472), (-18079943/68719476736)), (161/68719476736), by norm_num⟩
  | 8 => ⟨((-1162050447/274877906944), (22463485/274877906944)), (101/137438953472), by norm_num⟩
  | 9 => ⟨((320842987/274877906944), (-24808739/1099511627776)), (225/1099511627776), by norm_num⟩
  | 10 => ⟨((-1275623795/4398046511104), (1541185/274877906944)), (113/2199023255552), by norm_num⟩
  | 11 => ⟨((1152656745/17592186044416), (-2785237/2199023255552)), (103/8796093022208), by norm_num⟩
  | 12 => ⟨((-1909496273/140737488355328), (1153509/4398046511104)), (43/17592186044416), by norm_num⟩
  | 13 => ⟨((364993845/140737488355328), (-28222643/562949953421312)), (265/562949953421312), by norm_num⟩
  | 14 => ⟨((-259135895/562949953421312), (5009331/562949953421312)), (379/4503599627370496), by norm_num⟩
  | 15 => ⟨((171714269/2251799813685248), (-103731/70368744177664)), (253/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1706775715/144115188075855872), (32993517/144115188075855872)), (79/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (31774200521/79228162514264337593543950336)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889325459517949/316912650057057350374175801344), (4812653608455/633825300114114700748351602688)), (46337/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889608643570359/39614081257132168796771975168), (2706593446583/19807040628566084398385987584)), (104289/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118085911123533/154742504910672534362390528), (2875124815761/1237940039285380274899124224)), (55421/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771039913010121/154742504910672534362390528), (1437207618267/38685626227668133590597632)), (55441/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549411103416419/9671406556917033397649408), (673502607799/1208925819614629174706176)), (51997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314665795415501/151115727451828646838272), (4713010716313/604462909807314587353088)), (91037/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471896571658595/18889465931478580854784), (1913954034237/18889465931478580854784)), (74007/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297383545292689/4722366482869645213696), (5739389468137/4722366482869645213696)), (111079/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621231160988369/590295810358705651712), (7887643159849/590295810358705651712)), (152847/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455799890122185/18446744073709551616), (9853529090873/73786976294838206464)), (191227/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113896383278893/576460752303423488), (2769234491923/2305843009213693952)), (215363/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593583994310935/1152921504606846976), (1383323504303/144115188075855872)), (107827/576460752303423488), by norm_num⟩
  | 5 => ⟨((149277709013769/18014398509481984), (4835812422493/72057594037927936)), (189025/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491083893540307/36028797018963968), (7242083957469/18014398509481984)), (8881/1125899906842624), by norm_num⟩
  | 3 => ⟨((1488539867603925/9007199254740992), (9032255592615/4503599627370496)), (356389/9007199254740992), by norm_num⟩
  | 2 => ⟨((139152191267743/281474976710656), (18003508735153/2251799813685248)), (358115/2251799813685248), by norm_num⟩
  | 1 => ⟨((276705259659545/281474976710656), (26852917946409/1125899906842624)), (270749/562949953421312), by norm_num⟩
  | 0 => ⟨((1087524654371445/1125899906842624), (26548715813231/562949953421312)), (68773/70368744177664), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087524654371445/1125899906842624), (26548715813231/562949953421312)), (262348175317263581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1047953312234643/1125899906842624), (3205478436995/35184372088832)), (1114757/562949953421312), by norm_num⟩
  | 2 => ⟨((966057856293359/1125899906842624), (190947943414451/1125899906842624)), (4556569/1125899906842624), by norm_num⟩
  | 3 => ⟨((199131081537887/281474976710656), (163839396164347/562949953421312)), (18729825/2251799813685248), by norm_num⟩
  | 4 => ⟨((117034739945773/281474976710656), (927272940223269/2251799813685248)), (18701599/1125899906842624), by norm_num⟩
  | 5 => ⟨((7452366278249/2251799813685248), (771103340595279/2251799813685248)), (30954245/1125899906842624), by norm_num⟩
  | 6 => ⟨((-528061882322509/4503599627370496), (2551978420805/1125899906842624)), (342475987/18014398509481984), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-2003521341/33554432)), (1/16777216), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-258507235/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((89554966264957/2251799813685248), (918472216744491/9007199254740992)), (34704649/2251799813685248), by norm_num⟩
  | 1 => ⟨((-438125521/4294967296), (-561674767/2147483648)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((561884887/4294967296), (1440667333/4294967296)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((-480402093/4294967296), (-615873125/2147483648)), (193/4294967296), by norm_num⟩
  | 4 => ⟨((19253235/268435456), (98730211/536870912)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((-158027433/4294967296), (-202590393/2147483648)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((270221575/17179869184), (1385690929/34359738368)), (225/34359738368), by norm_num⟩
  | 7 => ⟨((-396059803/68719476736), (-1015493445/68719476736)), (167/68719476736), by norm_num⟩
  | 8 => ⟨((507936669/274877906944), (651172315/137438953472)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-289518185/549755813888), (-742321783/549755813888)), (249/1099511627776), by norm_num⟩
  | 10 => ⟨((297039793/2199023255552), (1523214225/4398046511104)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((-138525823/4398046511104), (-1420715399/17592186044416)), (243/17592186044416), by norm_num⟩
  | 12 => ⟨((473748961/70368744177664), (1214687683/70368744177664)), (105/35184372088832), by norm_num⟩
  | 13 => ⟨((-373889875/281474976710656), (-958649967/281474976710656)), (167/281474976710656), by norm_num⟩
  | 14 => ⟨((548004911/2251799813685248), (702539605/1125899906842624)), (247/2251799813685248), by norm_num⟩
  | 15 => ⟨((-374827959/9007199254740992), (-961055205/9007199254740992)), (171/9007199254740992), by norm_num⟩
  | 16 => ⟨((240353683/36028797018963968), (1232528965/72057594037927936)), (111/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (780867107283/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778555084220413/633825300114114700748351602688), (461952844987/158456325028528675187087900672)), (46191/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889501446850455/39614081257132168796771975168), (2078385779333/39614081257132168796771975168)), (51971/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889261486282795/2475880078570760549798248448), (1103893241899/1237940039285380274899124224)), (27613/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885463863030035/77371252455336267181195264), (1103612986055/77371252455336267181195264)), (110467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387326722205211/2417851639229258349412352), (258584873387/1208925819614629174706176)), (103579/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258572953863863/604462909807314587353088), (904749478303/302231454903657293676544)), (11331/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887441464930957/75557863725914323419136), (2939320319655/75557863725914323419136)), (147333/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162159562649371/590295810358705651712), (275439328135/590295810358705651712)), (110527/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621086527372371/590295810358705651712), (3028248050101/590295810358705651712)), (152017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911511295822383/36893488147419103232), (3782934648087/73786976294838206464)), (95043/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822148291501301/9223372036854775808), (4252537597599/9223372036854775808)), (13371/576460752303423488), by norm_num⟩
  | 6 => ⟨((1593396702776813/1152921504606846976), (1062115303389/288230376151711744)), (214047/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597032571950381/72057594037927936), (3712822394165/144115188075855872)), (187417/144115188075855872), by norm_num⟩
  | 4 => ⟨((745431882240411/18014398509481984), (5560083154999/36028797018963968)), (140689/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488290275946535/9007199254740992), (1733529355287/2251799813685248)), (88041/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113006111232835/2251799813685248), (3455095519191/1125899906842624)), (352827/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213197414772523/2251799813685248), (20611314285325/2251799813685248)), (530905/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174910765522189/2251799813685248), (20373912986209/1125899906842624)), (66781/70368744177664), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174910765522189/2251799813685248), (20373912986209/1125899906842624)), (254749298364138581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2099909780578651/2251799813685248), (39356467142609/1125899906842624)), (1051347/562949953421312), by norm_num⟩
  | 2 => ⟨((122219605562415/140737488355328), (146807064783493/2251799813685248)), (4068725/1125899906842624), by norm_num⟩
  | 3 => ⟨((1688640993076407/2251799813685248), (127490562474111/1125899906842624)), (3798635/562949953421312), by norm_num⟩
  | 4 => ⟨((618725743843521/1125899906842624), (191212192767545/1125899906842624)), (26230081/2251799813685248), by norm_num⟩
  | 5 => ⟨((1230160661093811/4503599627370496), (840628233348539/4503599627370496)), (9434559/562949953421312), by norm_num⟩
  | 6 => ⟨((89554966264957/2251799813685248), (918472216744491/9007199254740992)), (34704649/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-258507235/4194304)), (1/16777216), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-531952345/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((96581831458599/1125899906842624), (-254108987023887/4503599627370496)), (185347739/9007199254740992), by norm_num⟩
  | 1 => ⟨((-972309075/4294967296), (319770901/2147483648)), (235/4294967296), by norm_num⟩
  | 2 => ⟨((1282989695/4294967296), (-210973435/1073741824)), (39/536870912), by norm_num⟩
  | 3 => ⟨((-564313893/2147483648), (92795165/536870912)), (277/4294967296), by norm_num⟩
  | 4 => ⟨((372314179/2147483648), (-489783521/4294967296)), (185/4294967296), by norm_num⟩
  | 5 => ⟨((-393023385/4294967296), (129256679/2147483648)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((691474163/17179869184), (-56852631/2147483648)), (175/17179869184), by norm_num⟩
  | 7 => ⟨((-521382845/34359738368), (42867815/4294967296)), (133/34359738368), by norm_num⟩
  | 8 => ⟨((687979609/137438953472), (-452522485/137438953472)), (177/137438953472), by norm_num⟩
  | 9 => ⟨((-806941169/549755813888), (530770125/549755813888)), (105/274877906944), by norm_num⟩
  | 10 => ⟨((425912801/1099511627776), (-560293115/2199023255552)), (7/68719476736), by norm_num⟩
  | 11 => ⟨((-817460581/8796093022208), (33605583/549755813888)), (217/8796093022208), by norm_num⟩
  | 12 => ⟨((359554223/17592186044416), (-236498827/17592186044416)), (193/35184372088832), by norm_num⟩
  | 13 => ⟨((-583928743/140737488355328), (768164877/281474976710656)), (315/281474976710656), by norm_num⟩
  | 14 => ⟨((440291837/562949953421312), (-144802225/281474976710656)), (15/70368744177664), by norm_num⟩
  | 15 => ⟨((-1239419093/9007199254740992), (815234929/9007199254740992)), (341/9007199254740992), by norm_num⟩
  | 16 => ⟨((408862255/18014398509481984), (-537862929/36028797018963968)), (227/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-757869945017/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778457975270993/633825300114114700748351602688), (-224150328563/158456325028528675187087900672)), (184577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472348074820567/9903520314283042199192993792), (-1008476889971/39614081257132168796771975168)), (51915/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944572823298379/1237940039285380274899124224), (-1071257976949/2475880078570760549798248448)), (220653/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812032063085/154742504910672534362390528), (-1070978283581/154742504910672534362390528)), (220667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774599290199939/4835703278458516698824704), (-501872533905/4835703278458516698824704)), (206891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258478338591575/604462909807314587353088), (-54873748445/37778931862957161709568)), (90523/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943644002378899/37778931862957161709568), (-89135056427/4722366482869645213696)), (73557/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81072603705045/295147905179352825856), (-267283482911/1180591620717411303424)), (110349/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810464515398793/295147905179352825856), (-367317161869/147573952589676412928)), (303501/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822826336781257/73786976294838206464), (-229425104819/9223372036854775808)), (379439/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113870521899613/576460752303423488), (-2063197894583/9223372036854775808)), (106739/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398294454227235/288230376151711744), (-2061164761001/1152921504606846976)), (427065/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298468700867475/36028797018963968), (-1801234538049/144115188075855872)), (186903/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490580617149327/36028797018963968), (-674322290471/9007199254740992)), (280477/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487940463903939/9007199254740992), (-1681820837195/4503599627370496)), (701625/9007199254740992), by norm_num⟩
  | 2 => ⟨((556331227542825/1125899906842624), (-6703433307365/4503599627370496)), (175569/562949953421312), by norm_num⟩
  | 1 => ⟨((2212197035434861/2251799813685248), (-4997865939087/1125899906842624)), (2110101/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173031226110285/2251799813685248), (-19755029534045/2251799813685248)), (4233387/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173031226110285/2251799813685248), (-19755029534045/2251799813685248)), (16149089821822356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524211168746289/562949953421312), (-38127986146295/2251799813685248)), (2061221/562949953421312), by norm_num⟩
  | 2 => ⟨((975953506384915/1125899906842624), (-71008501051365/2251799813685248)), (3908563/562949953421312), by norm_num⟩
  | 3 => ⟨((52803577889039/70368744177664), (-61551648741635/1125899906842624)), (28090217/2251799813685248), by norm_num⟩
  | 4 => ⟨((315301190061597/562949953421312), (-184749483112665/2251799813685248)), (22614109/1125899906842624), by norm_num⟩
  | 5 => ⟨((86403388652609/281474976710656), (-103475862347381/1125899906842624)), (116170069/4503599627370496), by norm_num⟩
  | 6 => ⟨((96581831458599/1125899906842624), (-254108987023887/4503599627370496)), (185347739/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-531952345/8388608)), (1/8388608), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1091718349/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-270161505046975/4503599627370496), (-341820964160675/4503599627370496)), (158535843/9007199254740992), by norm_num⟩
  | 1 => ⟨((348859271/2147483648), (13793533/67108864)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-944728419/4294967296), (-597657277/2147483648)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((426395331/2147483648), (539495303/2147483648)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-577349981/4294967296), (-365245091/2147483648)), (11/268435456), by norm_num⟩
  | 5 => ⟨((625397093/8589934592), (395640817/4294967296)), (193/8589934592), by norm_num⟩
  | 6 => ⟨((-282267787/8589934592), (-178569199/4294967296)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((873594671/68719476736), (276328203/17179869184)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((-147858639/34359738368), (-374155323/68719476736)), (187/137438953472), by norm_num⟩
  | 9 => ⟨((711837541/549755813888), (900650131/549755813888)), (227/549755813888), by norm_num⟩
  | 10 => ⟨((-385538359/1099511627776), (-975602307/2199023255552)), (31/274877906944), by norm_num⟩
  | 11 => ⟨((759314349/8796093022208), (120090001/1099511627776)), (247/8796093022208), by norm_num⟩
  | 12 => ⟨((-342710229/17592186044416), (-867226003/35184372088832)), (225/35184372088832), by norm_num⟩
  | 13 => ⟨((571124003/140737488355328), (722612785/140737488355328)), (189/140737488355328), by norm_num⟩
  | 14 => ⟨((-883789983/1125899906842624), (-1118212399/1125899906842624)), (295/1125899906842624), by norm_num⟩
  | 15 => ⟨((319113019/2251799813685248), (100939177/562949953421312)), (215/4503599627370496), by norm_num⟩
  | 16 => ⟨((-864174075/36028797018963968), (-546696717/18014398509481984)), (293/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1458684922043/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444590081698297/158456325028528675187087900672), (-3451067937513/633825300114114700748351602688)), (92541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944641067147117/19807040628566084398385987584), (-3881651212113/39614081257132168796771975168)), (104129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944514092698697/1237940039285380274899124224), (-4123270590179/2475880078570760549798248448)), (110663/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885347054527237/77371252455336267181195264), (-2061082023281/77371252455336267181195264)), (110691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549087537270607/9671406556917033397649408), (-1931676691993/4835703278458516698824704)), (103803/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258380685953963/604462909807314587353088), (-3379259130593/604462909807314587353088)), (90859/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887128401529131/75557863725914323419136), (-171534172223/2361183241434822606848)), (147701/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324260288686667/1180591620717411303424), (-4114893578897/4722366482869645213696)), (55413/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810381017628703/295147905179352825856), (-2827424665835/295147905179352825856)), (76233/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911307821246027/36893488147419103232), (-3531934975423/36893488147419103232)), (190703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455422160718397/2305843009213693952), (-7940406317671/9223372036854775808)), (53677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796467385375779/576460752303423488), (-7932352689753/1152921504606846976)), (214917/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596829195807763/72057594037927936), (-3465877980955/72057594037927936)), (188287/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490248530144727/36028797018963968), (-10379547880735/36028797018963968)), (70725/9007199254740992), by norm_num⟩
  | 3 => ⟨((743756168622969/4503599627370496), (-3235706870109/2251799813685248)), (354449/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112214907775583/2251799813685248), (-12895502877753/2251799813685248)), (711375/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105379015592113/1125899906842624), (-9612622644275/562949953421312)), (536635/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169772194253547/2251799813685248), (-75960536931103/2251799813685248)), (2171467/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169772194253547/2251799813685248), (-75960536931103/2251799813685248)), (8283489235884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044085123199643/1125899906842624), (-146386956684165/2251799813685248)), (2165617/1125899906842624), by norm_num⟩
  | 2 => ⟨((963457277705083/1125899906842624), (-271499167511293/2251799813685248)), (8596139/2251799813685248), by norm_num⟩
  | 3 => ⟨((1616168490544571/2251799813685248), (-29040975050257/140737488355328)), (16784681/2251799813685248), by norm_num⟩
  | 4 => ⟨((532040136940301/1125899906842624), (-333494006177065/1125899906842624)), (31020493/2251799813685248), by norm_num⟩
  | 5 => ⟨((610528357325627/4503599627370496), (-1260731584659533/4503599627370496)), (47693931/2251799813685248), by norm_num⟩
  | 6 => ⟨((-270161505046975/4503599627370496), (-341820964160675/4503599627370496)), (158535843/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1091718349/16777216)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile028Terms1
