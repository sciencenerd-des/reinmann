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
namespace Reinmann.XiBand97.Tile022Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28609/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28609/1280))
  have he : value ((69/80), (28609/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-25747619/524288)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((136459904429143/2251799813685248), (619443865143775/4503599627370496)), (23264407/1125899906842624), by norm_num⟩
  | 1 => ⟨((-571886169/4294967296), (-10140667/33554432)), (197/4294967296), by norm_num⟩
  | 2 => ⟨((628281173/4294967296), (1426004657/4294967296)), (219/4294967296), by norm_num⟩
  | 3 => ⟨((-230079139/2147483648), (-522208747/2147483648)), (163/4294967296), by norm_num⟩
  | 4 => ⟨((505535539/8589934592), (573704947/4294967296)), (181/8589934592), by norm_num⟩
  | 5 => ⟨((-444310045/17179869184), (-126055861/2147483648)), (161/17179869184), by norm_num⟩
  | 6 => ⟨((325416317/34359738368), (1477189525/68719476736)), (119/34359738368), by norm_num⟩
  | 7 => ⟨((-408578703/137438953472), (-115918469/17179869184)), (19/17179869184), by norm_num⟩
  | 8 => ⟨((28054349/34359738368), (254698909/137438953472)), (169/549755813888), by norm_num⟩
  | 9 => ⟨((-219170507/1099511627776), (-994899027/2199023255552)), (167/2199023255552), by norm_num⟩
  | 10 => ⟨((96313365/2199023255552), (437203319/4398046511104)), (149/8796093022208), by norm_num⟩
  | 11 => ⟨((-307813953/35184372088832), (-1397285641/70368744177664)), (241/70368744177664), by norm_num⟩
  | 12 => ⟨((225445461/140737488355328), (1023383451/281474976710656)), (89/140737488355328), by norm_num⟩
  | 13 => ⟨((-76208355/281474976710656), (-1383755859/2251799813685248)), (61/562949953421312), by norm_num⟩
  | 14 => ⟨((47841963/1125899906842624), (868692109/9007199254740992)), (39/2251799813685248), by norm_num⟩
  | 15 => ⟨((-56063753/9007199254740992), (-254494887/18014398509481984)), (185/72057594037927936), by norm_num⟩
  | 16 => ⟨((7699041/9007199254740992), (1118364841/576460752303423488)), (103/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (188194258031/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779044159702437/633825300114114700748351602688), (1782272824661/633825300114114700748351602688)), (11547/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890051563849083/39614081257132168796771975168), (978868257/19342813113834066795298816)), (51967/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944922936257717/1237940039285380274899124224), (532401350961/618970019642690137449562112)), (110443/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771511985097241/154742504910672534362390528), (2129142118407/154742504910672534362390528)), (110457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549854496547023/9671406556917033397649408), (498894655093/2417851639229258349412352)), (103569/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259051975530083/604462909807314587353088), (436409829491/151115727451828646838272)), (90639/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472054905473579/18889465931478580854784), (2835741737889/75557863725914323419136)), (147317/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648929948693065/2361183241434822606848), (1062999858903/2361183241434822606848)), (55257/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621888337254333/590295810358705651712), (2921939470733/590295810358705651712)), (75999/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912012157182087/36893488147419103232), (3650460106783/73786976294838206464)), (190059/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823274487871241/9223372036854775808), (2052034196893/4611686018427387904)), (213903/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594521972494199/1152921504606846976), (4100696747777/1152921504606846976)), (107005/576460752303423488), by norm_num⟩
  | 5 => ⟨((18672636141421/2251799813685248), (1792159916225/72057594037927936)), (46845/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492337036080643/36028797018963968), (2684454149191/18014398509481984)), (281313/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490128225282591/9007199254740992), (3348951876359/4503599627370496)), (352065/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229677214878351/4503599627370496), (13356186228547/4503599627370496)), (352703/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218667687591591/2251799813685248), (9967741651227/1125899906842624)), (265327/562949953421312), by norm_num⟩
  | 0 => ⟨((2185742747348839/2251799813685248), (9869330555861/562949953421312)), (66733/70368744177664), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185742747348839/2251799813685248), (9869330555861/562949953421312)), (254566192895388581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1060465692730021/1125899906842624), (76638491761335/2251799813685248)), (1055125/562949953421312), by norm_num⟩
  | 2 => ⟨((1995060331787535/2251799813685248), (36092236424187/562949953421312)), (8237717/2251799813685248), by norm_num⟩
  | 3 => ⟨((1758337180297875/2251799813685248), (127908686620857/1125899906842624)), (15653269/2251799813685248), by norm_num⟩
  | 4 => ⟨((1343950333761153/2251799813685248), (399514376014527/2251799813685248)), (14001291/1125899906842624), by norm_num⟩
  | 5 => ⟨((365616595437865/1125899906842624), (476887399780337/2251799813685248)), (5420277/281474976710656), by norm_num⟩
  | 6 => ⟨((136459904429143/2251799813685248), (619443865143775/4503599627370496)), (23264407/1125899906842624), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-25747619/524288)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1726864607/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((448992246369819/9007199254740992), (-287945703061063/2251799813685248)), (43365339/2251799813685248), by norm_num⟩
  | 1 => ⟨((-15405459/134217728), (1264609305/4294967296)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((141889521/1073741824), (-1455935267/4294967296)), (225/4294967296), by norm_num⟩
  | 3 => ⟨((-13613029/134217728), (558735807/2147483648)), (175/4294967296), by norm_num⟩
  | 4 => ⟨((250761261/4294967296), (-321634185/2147483648)), (51/2147483648), by norm_num⟩
  | 5 => ⟨((-461919313/17179869184), (289293/4194304)), (95/8589934592), by norm_num⟩
  | 6 => ⟨((354536175/34359738368), (-909478229/34359738368)), (37/8589934592), by norm_num⟩
  | 7 => ⟨((-466485549/137438953472), (598328861/68719476736)), (197/137438953472), by norm_num⟩
  | 8 => ⟨((67132667/68719476736), (-344425779/137438953472)), (229/549755813888), by norm_num⟩
  | 9 => ⟨((-274806539/1099511627776), (704950813/1099511627776)), (237/2199023255552), by norm_num⟩
  | 10 => ⟨((123587/2147483648), (-1298567387/8796093022208)), (221/8796093022208), by norm_num⟩
  | 11 => ⟨((-105963365/8796093022208), (1087295239/35184372088832)), (187/35184372088832), by norm_num⟩
  | 12 => ⟨((325319553/140737488355328), (-52158121/8796093022208)), (145/140737488355328), by norm_num⟩
  | 13 => ⟨((-460969817/1125899906842624), (1182508425/1125899906842624)), (13/70368744177664), by norm_num⟩
  | 14 => ⟨((151631747/2251799813685248), (-777950363/4503599627370496)), (139/4503599627370496), by norm_num⟩
  | 15 => ⟨((-186210667/18014398509481984), (59709897/2251799813685248)), (173/36028797018963968), by norm_num⟩
  | 16 => ⟨((214382953/144115188075855872), (-549948475/144115188075855872)), (201/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-1561952877023/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222362988866531/79228162514264337593543950336), (-462190108695/158456325028528675187087900672)), (46191/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944946901924161/19807040628566084398385987584), (-2079492309829/39614081257132168796771975168)), (51971/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889678276175145/2475880078570760549798248448), (-552253205867/618970019642690137449562112)), (27613/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885672207688565/77371252455336267181195264), (-2208509246429/154742504910672534362390528)), (110467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549697428217645/9671406556917033397649408), (-129371406929/604462909807314587353088)), (103579/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157364321128039/75557863725914323419136), (-1810664950141/604462909807314587353088)), (11331/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((235999548668789/9444732965739290427392), (-2941328235203/75557863725914323419136)), (147333/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297692519375813/4722366482869645213696), (-1102559748853/2361183241434822606848)), (55263/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621658267883169/590295810358705651712), (-378826918313/73786976294838206464)), (152017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14247944068235/576460752303423488), (-946533589615/18446744073709551616)), (190085/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822951235518387/9223372036854775808), (-532058448473/1152921504606846976)), (213935/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797099457239245/576460752303423488), (-4252803357011/1152921504606846976)), (214047/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74672890993553/9007199254740992), (-3717084423575/144115188075855872)), (187417/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491913787518977/36028797018963968), (-43495304411/281474976710656)), (8793/1125899906842624), by norm_num⟩
  | 3 => ⟨((1489599929513019/9007199254740992), (-868108914229/1125899906842624)), (352161/9007199254740992), by norm_num⟩
  | 2 => ⟨((557155729417635/1125899906842624), (-3461673618565/1125899906842624)), (705647/4503599627370496), by norm_num⟩
  | 1 => ⟨((69284124247881/70368744177664), (-10331357466625/1125899906842624)), (1061791/2251799813685248), by norm_num⟩
  | 0 => ⟨((272826781278771/281474976710656), (-20448940303133/1125899906842624)), (1068457/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272826781278771/281474976710656), (-20448940303133/1125899906842624)), (4075840000632857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528702895760093/562949953421312), (-79282622258823/2251799813685248)), (1055035/562949953421312), by norm_num⟩
  | 2 => ⟨((991682802002789/1125899906842624), (-148918928643459/2251799813685248)), (8223987/2251799813685248), by norm_num⟩
  | 3 => ⟨((54283831205705/70368744177664), (-16395811422809/140737488355328)), (973437/140737488355328), by norm_num⟩
  | 4 => ⟨((1309458035537497/2251799813685248), (-202368814770201/1125899906842624)), (6914665/562949953421312), by norm_num⟩
  | 5 => ⟨((43045228439113/140737488355328), (-117680740993293/562949953421312)), (5263829/281474976710656), by norm_num⟩
  | 6 => ⟨((448992246369819/9007199254740992), (-287945703061063/2251799813685248)), (43365339/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1726864607/33554432)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1798344169/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-559317112342551/4503599627370496), (106267719492093/4503599627370496)), (48427149/2251799813685248), by norm_num⟩
  | 1 => ⟨((1279052601/4294967296), (-60753551/1073741824)), (7/134217728), by norm_num⟩
  | 2 => ⟨((-1533517093/4294967296), (145680653/2147483648)), (271/4294967296), by norm_num⟩
  | 3 => ⟨((306434449/1073741824), (-232884633/4294967296)), (109/2147483648), by norm_num⟩
  | 4 => ⟨((-1469595433/8589934592), (8725515/268435456)), (33/1073741824), by norm_num⟩
  | 5 => ⟨((1409574377/17179869184), (-267812751/17179869184)), (255/17179869184), by norm_num⟩
  | 6 => ⟨((-563335289/17179869184), (107031155/17179869184)), (103/17179869184), by norm_num⟩
  | 7 => ⟨((1543793173/137438953472), (-293313715/137438953472)), (71/34359738368), by norm_num⟩
  | 8 => ⟨((-231365897/68719476736), (175833893/274877906944)), (43/68719476736), by norm_num⟩
  | 9 => ⟨((493147725/549755813888), (-187391671/1099511627776)), (185/1099511627776), by norm_num⟩
  | 10 => ⟨((-946013279/4398046511104), (179738241/4398046511104)), (179/4398046511104), by norm_num⟩
  | 11 => ⟨((1649775105/35184372088832), (-313449803/35184372088832)), (315/35184372088832), by norm_num⟩
  | 12 => ⟨((-659331321/70368744177664), (125269967/70368744177664)), (127/70368744177664), by norm_num⟩
  | 13 => ⟨((486463833/281474976710656), (-184851853/562949953421312)), (95/281474976710656), by norm_num⟩
  | 14 => ⟨((-666565329/2251799813685248), (253288791/4503599627370496)), (131/2251799813685248), by norm_num⟩
  | 15 => ⟨((1704910775/36028797018963968), (-161962665/18014398509481984)), (169/18014398509481984), by norm_num⟩
  | 16 => ⟨((-255512343/36028797018963968), (97092377/72057594037927936)), (51/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1923849991975/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444691976465891/158456325028528675187087900672), (4553601242393/633825300114114700748351602688)), (92649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59054384394189/1237940039285380274899124224), (5121845062681/39614081257132168796771975168)), (104259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236189316152859/309485009821345068724781056), (5440808850695/2475880078570760549798248448)), (13851/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771179937999185/154742504910672534362390528), (679939171831/19342813113834066795298816)), (110845/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549542455108943/9671406556917033397649408), (5098167488923/9671406556917033397649408)), (103957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258778192561181/604462909807314587353088), (1114880103481/151115727451828646838272)), (91003/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943886662852399/37778931862957161709568), (3622070377321/37778931862957161709568)), (73977/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297523952453811/4722366482869645213696), (169714015021/147573952589676412928)), (111031/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810712214109285/295147905179352825856), (7463749541357/590295810358705651712)), (76387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823441454926781/73786976294838206464), (9324187376601/73786976294838206464)), (191127/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822614689409171/9223372036854775808), (10482150756351/9223372036854775808)), (107619/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796928540872499/576460752303423488), (5236351734523/576460752303423488)), (215513/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597230609078255/72057594037927936), (572061946955/9007199254740992)), (188883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491444396059163/36028797018963968), (13708247527927/36028797018963968)), (35493/4503599627370496), by norm_num⟩
  | 3 => ⟨((744496277066737/4503599627370496), (8549081217989/4503599627370496)), (356017/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113673278984109/2251799813685248), (1065155341033/140737488355328)), (357649/2251799813685248), by norm_num⟩
  | 1 => ⟨((4326219646525/4398046511104), (25424688964799/1125899906842624)), (135141/281474976710656), by norm_num⟩
  | 0 => ⟨((544468389693453/562949953421312), (50294148728519/1125899906842624)), (274387/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544468389693453/562949953421312), (50294148728519/1125899906842624)), (1046703339696788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((131367562173379/140737488355328), (97285998525435/1125899906842624)), (69409/35184372088832), by norm_num⟩
  | 2 => ⟨((486282731210879/562949953421312), (90808956513579/562949953421312)), (2265133/562949953421312), by norm_num⟩
  | 3 => ⟨((405408379028719/562949953421312), (627534680459023/2251799813685248)), (2322035/281474976710656), by norm_num⟩
  | 4 => ⟨((992937059422289/2251799813685248), (903838133542925/2251799813685248)), (18554571/1125899906842624), by norm_num⟩
  | 5 => ⟨((150102714549249/4503599627370496), (1594199223322765/4503599627370496)), (125033675/4503599627370496), by norm_num⟩
  | 6 => ⟨((-559317112342551/4503599627370496), (106267719492093/4503599627370496)), (48427149/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1798344169/33554432)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1863599897/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((281326881379815/4503599627370496), (893999415831765/9007199254740992)), (16995545/1125899906842624), by norm_num⟩
  | 1 => ⟨((-333343047/2147483648), (-1059296175/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((414163177/2147483648), (658063027/2147483648)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((-686104555/4294967296), (-68134383/268435456)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((426226443/4294967296), (677230325/4294967296)), (55/2147483648), by norm_num⟩
  | 5 => ⟨((-423653169/8589934592), (-673141655/8589934592)), (111/8589934592), by norm_num⟩
  | 6 => ⟨((350912859/17179869184), (557564725/17179869184)), (93/17179869184), by norm_num⟩
  | 7 => ⟨((-498277541/68719476736), (-791712167/68719476736)), (67/34359738368), by norm_num⟩
  | 8 => ⟨((619086587/274877906944), (491832707/137438953472)), (169/274877906944), by norm_num⟩
  | 9 => ⟨((-21366283/34359738368), (-543181495/549755813888)), (189/1099511627776), by norm_num⟩
  | 10 => ⟨((679593199/4398046511104), (1079804247/4398046511104)), (95/2199023255552), by norm_num⟩
  | 11 => ⟨((-307041029/8796093022208), (-15245527/274877906944)), (87/8796093022208), by norm_num⟩
  | 12 => ⟨((254322765/35184372088832), (808185843/70368744177664)), (73/35184372088832), by norm_num⟩
  | 13 => ⟨((-777807175/562949953421312), (-1235856231/562949953421312)), (113/281474976710656), by norm_num⟩
  | 14 => ⟨((552222349/2251799813685248), (438712481/1125899906842624)), (81/1125899906842624), by norm_num⟩
  | 15 => ⟨((-731851193/18014398509481984), (-1162836865/18014398509481984)), (217/18014398509481984), by norm_num⟩
  | 16 => ⟨((227322737/36028797018963968), (45149079/4503599627370496)), (137/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (657208500921/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444665506180831/158456325028528675187087900672), (1555368040149/633825300114114700748351602688)), (46177/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889621761841565/39614081257132168796771975168), (874730579235/19807040628566084398385987584)), (103907/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889389331851215/2475880078570760549798248448), (1858396080399/2475880078570760549798248448)), (110413/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885527791924459/77371252455336267181195264), (1857939040093/154742504910672534362390528)), (55213/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549426768459247/9671406556917033397649408), (108833274515/604462909807314587353088)), (51769/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258677861483095/604462909807314587353088), (1523180551289/604462909807314587353088)), (45305/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887611964011891/75557863725914323419136), (2474258825959/75557863725914323419136)), (73633/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324351099156453/1180591620717411303424), (1854898598137/4722366482869645213696)), (13809/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621262417807783/590295810358705651712), (1274596755281/295147905179352825856)), (151935/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455810626459333/18446744073709551616), (3184554950271/73786976294838206464)), (189973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911197882503423/4611686018427387904), (3579962904927/9223372036854775808)), (106897/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796822131698327/576460752303423488), (3576638948525/1152921504606846976)), (213889/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194281856850573/144115188075855872), (3125823491193/144115188075855872)), (187259/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491189027233367/36028797018963968), (2340636852417/18014398509481984)), (70275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488697189373931/9007199254740992), (5838556125523/9007199254740992)), (351747/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113413520488623/2251799813685248), (2909522700121/1125899906842624)), (704611/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214422075320169/2251799813685248), (17359884945917/2251799813685248)), (132465/281474976710656), by norm_num⟩
  | 0 => ⟨((1088684770582217/1125899906842624), (536446472425/35184372088832)), (1065353/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088684770582217/1125899906842624), (536446472425/35184372088832)), (4063999180320357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263109500472203/281474976710656), (66395512563037/2251799813685248)), (2092765/1125899906842624), by norm_num⟩
  | 2 => ⟨((1965580865710571/2251799813685248), (124126772107449/2251799813685248)), (8071697/2251799813685248), by norm_num⟩
  | 3 => ⟨((854449996111329/1125899906842624), (108349421957507/1125899906842624)), (14981339/2251799813685248), by norm_num⟩
  | 4 => ⟨((319009351653021/562949953421312), (164453629683437/1125899906842624)), (3202777/281474976710656), by norm_num⟩
  | 5 => ⟨((1350112446560083/4503599627370496), (372766676422737/2251799813685248)), (18261943/1125899906842624), by norm_num⟩
  | 6 => ⟨((281326881379815/4503599627370496), (893999415831765/9007199254740992)), (16995545/1125899906842624), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1863599897/33554432)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1923629349/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((175222581222783/2251799813685248), (-43331274661439/562949953421312)), (112010145/9007199254740992), by norm_num⟩
  | 1 => ⟨((-428616569/2147483648), (847950173/4294967296)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((549689897/2147483648), (-543737313/2147483648)), (91/2147483648), by norm_num⟩
  | 3 => ⟨((-469975583/2147483648), (29055389/134217728)), (79/2147483648), by norm_num⟩
  | 4 => ⟨((602731785/4294967296), (-596204811/4294967296)), (103/4294967296), by norm_num⟩
  | 5 => ⟨((-309195301/4294967296), (611694059/8589934592)), (107/8589934592), by norm_num⟩
  | 6 => ⟨((264356763/8589934592), (-1045976189/34359738368)), (93/17179869184), by norm_num⟩
  | 7 => ⟨((-193731917/17179869184), (766535987/68719476736)), (69/34359738368), by norm_num⟩
  | 8 => ⟨((124228139/34359738368), (-491531497/137438953472)), (179/274877906944), by norm_num⟩
  | 9 => ⟨((-283234565/274877906944), (560334843/549755813888)), (13/68719476736), by norm_num⟩
  | 10 => ⟨((581185853/2199023255552), (-287446099/1099511627776)), (109/2199023255552), by norm_num⟩
  | 11 => ⟨((-542077193/8796093022208), (536207045/8796093022208)), (103/8796093022208), by norm_num⟩
  | 12 => ⟨((926933699/70368744177664), (-114611993/8796093022208)), (89/35184372088832), by norm_num⟩
  | 13 => ⟨((-731550153/281474976710656), (180907051/70368744177664)), (71/140737488355328), by norm_num⟩
  | 14 => ⟨((268055585/562949953421312), (-132576407/281474976710656)), (211/2251799813685248), by norm_num⟩
  | 15 => ⟨((-733385601/9007199254740992), (11335059/140737488355328)), (73/4503599627370496), by norm_num⟩
  | 16 => ⟨((940548463/72057594037927936), (-465181637/36028797018963968)), (95/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1015977491295/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889278069447551/316912650057057350374175801344), (-601041698605/316912650057057350374175801344)), (92319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889502692441031/39614081257132168796771975168), (-1352083091287/39614081257132168796771975168)), (51933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889262887172445/2475880078570760549798248448), (-1436264142235/2475880078570760549798248448)), (55183/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885464607000671/77371252455336267181195264), (-1435899622457/154742504910672534362390528)), (110377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549308376195433/9671406556917033397649408), (-672884359695/4835703278458516698824704)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629287173837845/302231454903657293676544), (-1177160594133/604462909807314587353088)), (22641/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943721951449263/37778931862957161709568), (-478040143605/18889465931478580854784)), (147185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297278480916289/4722366482869645213696), (-1433486013711/4722366482869645213696)), (55203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621089494982733/590295810358705651712), (-492503225845/147573952589676412928)), (37959/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823026668907395/73786976294838206464), (-2460971564489/73786976294838206464)), (189837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822153383281119/9223372036854775808), (-2766470830569/9223372036854775808)), (213625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593402424437639/1152921504606846976), (-2763820499831/1152921504606846976)), (106849/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194070857331881/144115188075855872), (-603841150835/36028797018963968)), (46767/36028797018963968), by norm_num⟩
  | 4 => ⟨((372718436123723/9007199254740992), (-226068652983/2251799813685248)), (140383/18014398509481984), by norm_num⟩
  | 3 => ⟨((744152604526453/4503599627370496), (-2255490853841/4503599627370496)), (175623/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226049426326737/4503599627370496), (-8990863023145/4503599627370496)), (703359/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106635718482233/1125899906842624), (-13408800796065/2251799813685248)), (1057215/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175130912716049/2251799813685248), (-13254582724829/1125899906842624)), (2123187/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175130912716049/2251799813685248), (-13254582724829/1125899906842624)), (8099315651900481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050380172085167/1125899906842624), (-51213171694413/2251799813685248)), (4151785/2251799813685248), by norm_num⟩
  | 2 => ⟨((1958687094598081/2251799813685248), (-95556096541935/2251799813685248)), (7935459/2251799813685248), by norm_num⟩
  | 3 => ⟨((424918341286189/562949953421312), (-166235463711623/2251799813685248)), (14478519/2251799813685248), by norm_num⟩
  | 4 => ⟨((317663153424861/562949953421312), (-31368906362809/281474976710656)), (23994671/2251799813685248), by norm_num⟩
  | 5 => ⟨((344520308808541/1125899906842624), (-283215107251041/2251799813685248)), (4053467/281474976710656), by norm_num⟩
  | 6 => ⟨((175222581222783/2251799813685248), (-43331274661439/562949953421312)), (112010145/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1923629349/33554432)), (1/16777216), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1979207939/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-352094343817825/4503599627370496), (-74937370944067/1125899906842624)), (42184843/2251799813685248), by norm_num⟩
  | 1 => ⟨((886151465/4294967296), (754409859/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-292325565/1073741824), (-497732717/2147483648)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((514309283/2147483648), (875696783/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-678645841/4294967296), (-577753503/4294967296)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((5596829/67108864), (609889847/8589934592)), (91/4294967296), by norm_num⟩
  | 6 => ⟨((-630201711/17179869184), (-8382991/268435456)), (81/8589934592), by norm_num⟩
  | 7 => ⟨((950364825/68719476736), (809076803/68719476736)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((-313508407/68719476736), (-533800017/137438953472)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((367718515/274877906944), (313050855/274877906944)), (97/274877906944), by norm_num⟩
  | 10 => ⟨((-388172097/1099511627776), (-660927323/2199023255552)), (207/2199023255552), by norm_num⟩
  | 11 => ⟨((46564019/549755813888), (634263671/8796093022208)), (201/8796093022208), by norm_num⟩
  | 12 => ⟨((-655387283/35184372088832), (-278976365/17592186044416)), (179/35184372088832), by norm_num⟩
  | 13 => ⟨((1064372069/281474976710656), (453067459/140737488355328)), (293/281474976710656), by norm_num⟩
  | 14 => ⟨((-401276987/562949953421312), (-341620285/562949953421312)), (223/1125899906842624), by norm_num⟩
  | 15 => ⟨((1129592505/9007199254740992), (480829609/4503599627370496)), (79/2251799813685248), by norm_num⟩
  | 16 => ⟨((-745264845/36028797018963968), (-158617113/9007199254740992)), (105/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-1586792863935/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889225427600153/316912650057057350374175801344), (-1877262156395/316912650057057350374175801344)), (46285/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889383891678635/39614081257132168796771975168), (-1055746783285/9903520314283042199192993792)), (104165/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118071011927607/154742504910672534362390528), (-1121470087743/618970019642690137449562112)), (110703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885400994413263/77371252455336267181195264), (-4484706645965/154742504910672534362390528)), (55367/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549188541102789/9671406556917033397649408), (-4203165689585/9671406556917033397649408)), (51923/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258468930934685/604462909807314587353088), (-3676523491407/604462909807314587353088)), (45449/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887271549723001/75557863725914323419136), (-5972014156575/75557863725914323419136)), (147771/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297148297403195/4722366482869645213696), (-2238483405645/2361183241434822606848)), (55441/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810454500845399/295147905179352825856), (-6152509392325/590295810358705651712)), (152551/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911399409511715/36893488147419103232), (-7685658901539/73786976294838206464)), (47705/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821893986568167/9223372036854775808), (-4319762591439/4611686018427387904)), (107427/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593139203451525/1152921504606846976), (-539436187677/72057594037927936)), (215081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193836247261191/144115188075855872), (-3771249643785/72057594037927936)), (188451/144115188075855872), by norm_num⟩
  | 4 => ⟨((372628318107655/9007199254740992), (-2823638009497/9007199254740992)), (70797/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487839703711639/9007199254740992), (-14084635516793/9007199254740992)), (354881/9007199254740992), by norm_num⟩
  | 2 => ⟨((278134238369955/562949953421312), (-14034383818703/2251799813685248)), (89057/562949953421312), by norm_num⟩
  | 1 => ⟨((552924428375905/562949953421312), (-20926226969847/1125899906842624)), (537717/1125899906842624), by norm_num⟩
  | 0 => ⟨((271443328956553/281474976710656), (-41352742960007/1125899906842624)), (544493/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271443328956553/281474976710656), (-41352742960007/1125899906842624)), (2077075960399436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((261389497604443/281474976710656), (-79757897783487/1125899906842624)), (4360689/2251799813685248), by norm_num⟩
  | 2 => ⟨((965299119808457/1125899906842624), (-296266148774467/2251799813685248)), (8716855/2251799813685248), by norm_num⟩
  | 3 => ⟨((1616234227298407/2251799813685248), (-254006107383939/1125899906842624)), (8620329/1125899906842624), by norm_num⟩
  | 4 => ⟨((1045446692388159/2251799813685248), (-729253750181081/2251799813685248)), (32528121/2251799813685248), by norm_num⟩
  | 5 => ⟨((498399325785367/4503599627370496), (-1354287208667543/4503599627370496)), (6409059/281474976710656), by norm_num⟩
  | 6 => ⟨((-352094343817825/4503599627370496), (-74937370944067/1125899906842624)), (42184843/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1979207939/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-2030950369/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-145926636580507/2251799813685248), (646994520206099/9007199254740992)), (79498561/4503599627370496), by norm_num⟩
  | 1 => ⟨((753739657/4294967296), (-104432919/536870912)), (13/268435456), by norm_num⟩
  | 2 => ⟨((-510291207/2147483648), (565619175/2147483648)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((230315701/1073741824), (-7977735/33554432)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-38981655/268435456), (172832855/1073741824)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((675611383/8589934592), (-187216019/2147483648)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((-152465795/4294967296), (337993585/8589934592)), (179/17179869184), by norm_num⟩
  | 7 => ⟨((235934301/17179869184), (-261515313/17179869184)), (279/68719476736), by norm_num⟩
  | 8 => ⟨((-638921931/137438953472), (177049149/34359738368)), (191/137438953472), by norm_num⟩
  | 9 => ⟨((768992295/549755813888), (-213092437/137438953472)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((-104123487/274877906944), (923304027/2199023255552)), (127/1099511627776), by norm_num⟩
  | 11 => ⟨((820281105/8796093022208), (-909219511/8796093022208)), (63/2199023255552), by norm_num⟩
  | 12 => ⟨((-740454137/35184372088832), (51296085/2199023255552)), (229/35184372088832), by norm_num⟩
  | 13 => ⟨((616980607/140737488355328), (-683876299/140737488355328)), (193/140737488355328), by norm_num⟩
  | 14 => ⟨((-477375559/562949953421312), (529134671/562949953421312)), (301/1125899906842624), by norm_num⟩
  | 15 => ⟨((172367597/1125899906842624), (-382112867/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | 16 => ⟨((-933560211/36028797018963968), (517390413/18014398509481984)), (75/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (5863826993/19807040628566084398385987584)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778359949969899/633825300114114700748351602688), (1775755355163/316912650057057350374175801344)), (46275/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889281689395125/39614081257132168796771975168), (998656298293/9903520314283042199192993792)), (104141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472256921259751/618970019642690137449562112), (2121638356387/1237940039285380274899124224)), (27669/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770693577614057/154742504910672534362390528), (4242137838901/154742504910672534362390528)), (110705/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774543503022147/4835703278458516698824704), (993948616069/2417851639229258349412352)), (103817/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258380188156705/604462909807314587353088), (869402681691/151115727451828646838272)), (11359/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887127530838583/75557863725914323419136), (2824425226207/37778931862957161709568)), (36931/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297040447736657/4722366482869645213696), (4234654934731/4722366482869645213696)), (27711/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620760975487637/590295810358705651712), (1454857407729/147573952589676412928)), (76247/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822614186518979/73786976294838206464), (3634728992177/36893488147419103232)), (95371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227710853090201/1152921504606846976), (8171504023699/9223372036854775808)), (53689/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592932727823431/1152921504606846976), (510200898373/72057594037927936)), (214971/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193656351800609/144115188075855872), (3566747218067/72057594037927936)), (188341/144115188075855872), by norm_num⟩
  | 4 => ⟨((372561241866375/9007199254740992), (10681624657743/36028797018963968)), (70749/9007199254740992), by norm_num⟩
  | 3 => ⟨((46484593975039/281474976710656), (13319494467217/9007199254740992)), (354593/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224416539260753/4503599627370496), (13270776702061/2251799813685248)), (711733/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105365812357293/1125899906842624), (39569348554399/2251799813685248)), (268497/562949953421312), by norm_num⟩
  | 0 => ⟨((2169693702932105/2251799813685248), (78170413734885/2251799813685248)), (1086815/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169693702932105/2251799813685248), (78170413734885/2251799813685248)), (4145870213035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043933861790635/1125899906842624), (150640259765013/2251799813685248)), (4339663/2251799813685248), by norm_num⟩
  | 2 => ⟨((1925792478068173/2251799813685248), (139673577697183/1125899906842624)), (8628095/2251799813685248), by norm_num⟩
  | 3 => ⟨((1612328863912285/2251799813685248), (477808593249495/2251799813685248)), (16898621/2251799813685248), by norm_num⟩
  | 4 => ⟨((263267553715265/562949953421312), (21382467638761/70368744177664)), (31370855/2251799813685248), by norm_num⟩
  | 5 => ⟨((569121564958687/4503599627370496), (1279956893006881/4503599627370496)), (96813003/4503599627370496), by norm_num⟩
  | 6 => ⟨((-145926636580507/2251799813685248), (646994520206099/9007199254740992)), (79498561/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-2030950369/33554432)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile022Terms1
