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
namespace Reinmann.XiBand97.Tile008Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11709/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11709/640))
  have he : value ((69/80), (11709/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-948778201/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1252501778353109/18014398509481984), (-3657161056011/18014398509481984)), (19520203/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1846092305/8589934592), (5390377/8589934592)), (117/8589934592), by norm_num⟩
  | 2 => ⟨((713293711/2147483648), (-4165471/4294967296)), (23/1073741824), by norm_num⟩
  | 3 => ⟨((-734940381/2147483648), (4291883/4294967296)), (97/4294967296), by norm_num⟩
  | 4 => ⟨((1135865959/4294967296), (-1658299/2147483648)), (19/1073741824), by norm_num⟩
  | 5 => ⟨((-175550495/1073741824), (2050349/4294967296)), (3/268435456), by norm_num⟩
  | 6 => ⟨((1447024087/17179869184), (-528143/2147483648)), (101/17179869184), by norm_num⟩
  | 7 => ⟨((-638973269/17179869184), (3731457/34359738368)), (91/34359738368), by norm_num⟩
  | 8 => ⟨((1975093501/137438953472), (-2883523/68719476736)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-678344207/137438953472), (1980687/137438953472)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((1677432593/1099511627776), (-2448955/549755813888)), (63/549755813888), by norm_num⟩
  | 11 => ⟨((-942730065/2199023255552), (2752663/2199023255552)), (9/274877906944), by norm_num⟩
  | 12 => ⟨((971339551/8796093022208), (-5672399/17592186044416)), (75/8796093022208), by norm_num⟩
  | 13 => ⟨((-1847662639/70368744177664), (2697481/35184372088832)), (145/70368744177664), by norm_num⟩
  | 14 => ⟨((1631772473/281474976710656), (-1191147/70368744177664)), (65/140737488355328), by norm_num⟩
  | 15 => ⟨((-672517065/562949953421312), (3927345/1125899906842624)), (109/1125899906842624), by norm_num⟩
  | 16 => ⟨((2078778799/9007199254740992), (-6069795/9007199254740992)), (171/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-3803465307/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444464459142721/158456325028528675187087900672), (-2248405055/316912650057057350374175801344)), (92201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944358655787113/19807040628566084398385987584), (-2528875455/19807040628566084398385987584)), (51863/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118026792786635/154742504910672534362390528), (-5372399843/2475880078570760549798248448)), (55105/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885047654452275/77371252455336267181195264), (-5370757639/154742504910672534362390528)), (110209/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548526906111031/9671406556917033397649408), (-1258335289/2417851639229258349412352)), (51661/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257890877139505/604462909807314587353088), (-1100607545/151115727451828646838272)), (90407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943166927523707/37778931862957161709568), (-7150681995/75557863725914323419136)), (146911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296446462495391/4722366482869645213696), (-5360154527/4722366482869645213696)), (110183/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619946309917501/590295810358705651712), (-7365573081/590295810358705651712)), (75751/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910799473442545/36893488147419103232), (-9200012823/73786976294838206464)), (94689/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820548925793091/9223372036854775808), (-5170231177/4611686018427387904)), (213051/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591800126541617/1152921504606846976), (-10328535795/1152921504606846976)), (213053/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192671272586025/144115188075855872), (-1128008753/18014398509481984)), (186423/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488779210146811/36028797018963968), (-13509353825/36028797018963968)), (279637/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485695495629777/9007199254740992), (-16839981833/9007199254740992)), (349553/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220855281860975/4503599627370496), (-33540248037/4503599627370496)), (87391/562949953421312), by norm_num⟩
  | 1 => ⟨((2205543143033433/2251799813685248), (-49962533673/2251799813685248)), (1048761/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159924323685859/2251799813685248), (-98542383505/2251799813685248)), (2097855/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159924323685859/2251799813685248), (-98542383505/2251799813685248)), (8002681740767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035898716659037/1125899906842624), (-47260882107/562949953421312)), (4024705/2251799813685248), by norm_num⟩
  | 2 => ⟨((476545977009069/562949953421312), (-173931934181/1125899906842624)), (462915/140737488355328), by norm_num⟩
  | 3 => ⟨((403403640519515/562949953421312), (-588944455923/2251799813685248)), (3135491/562949953421312), by norm_num⟩
  | 4 => ⟨((144537249285581/281474976710656), (-844062020573/2251799813685248)), (1123839/140737488355328), by norm_num⟩
  | 5 => ⟨((1187516164643303/4503599627370496), (-1733701575973/4503599627370496)), (72189/8796093022208), by norm_num⟩
  | 6 => ⟨((1252501778353109/18014398509481984), (-3657161056011/18014398509481984)), (19520203/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-948778201/16777216)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-962422421/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((825707980398617/18014398509481984), (-878170965588065/18014398509481984)), (4406211/562949953421312), by norm_num⟩
  | 1 => ⟨((-38579145/268435456), (656485553/4294967296)), (107/4294967296), by norm_num⟩
  | 2 => ⟨((60482343/268435456), (-1029203327/4294967296)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((-1011424195/4294967296), (537843513/2147483648)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((396414339/2147483648), (-210800653/1073741824)), (143/4294967296), by norm_num⟩
  | 5 => ⟨((-994363893/8589934592), (1057542765/8589934592)), (91/4294967296), by norm_num⟩
  | 6 => ⟨((519637039/8589934592), (-1105306407/17179869184)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((-931039389/34359738368), (990194813/34359738368)), (175/34359738368), by norm_num⟩
  | 8 => ⟨((729817155/68719476736), (-776187527/68719476736)), (139/68719476736), by norm_num⟩
  | 9 => ⟨((-1017038875/274877906944), (1081658445/274877906944)), (49/68719476736), by norm_num⟩
  | 10 => ⟨((318891951/274877906944), (-678306759/549755813888)), (125/549755813888), by norm_num⟩
  | 11 => ⟨((-727188267/2199023255552), (773391607/2199023255552)), (9/137438953472), by norm_num⟩
  | 12 => ⟨((760031535/8796093022208), (-808321637/8796093022208)), (19/1099511627776), by norm_num⟩
  | 13 => ⟨((-733253687/35184372088832), (779842405/35184372088832)), (149/35184372088832), by norm_num⟩
  | 14 => ⟨((656889341/140737488355328), (-174656525/35184372088832)), (135/140737488355328), by norm_num⟩
  | 15 => ⟨((-549246061/562949953421312), (146035873/140737488355328)), (57/281474976710656), by norm_num⟩
  | 16 => ⟨((215269731/1125899906842624), (-457894635/2251799813685248)), (181/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-265790991397/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777797945376847/633825300114114700748351602688), (-1256891619091/633825300114114700748351602688)), (23081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888649903072985/39614081257132168796771975168), (-1413673667677/39614081257132168796771975168)), (103873/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944178510140171/1237940039285380274899124224), (-375403528739/618970019642690137449562112)), (55187/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770023596552729/154742504910672534362390528), (-375287105967/38685626227668133590597632)), (110385/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548459624784203/9671406556917033397649408), (-1406832048871/9671406556917033397649408)), (103497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314457988759997/151115727451828646838272), (-615241833709/302231454903657293676544)), (90571/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886238011250039/75557863725914323419136), (-1998609479755/75557863725914323419136)), (73599/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648187248154447/2361183241434822606848), (-187268364211/590295810358705651712)), (110417/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404961805304569/147573952589676412928), (-2058636325205/590295810358705651712)), (37963/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821474883627741/73786976294838206464), (-1285661718475/36893488147419103232)), (47465/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820409077010089/9223372036854775808), (-2890029928429/9223372036854775808)), (213653/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591659931721699/1152921504606846976), (-1443323765959/576460752303423488)), (106865/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192548214180359/144115188075855872), (-1261008290179/72057594037927936)), (46775/36028797018963968), by norm_num⟩
  | 4 => ⟨((23259278906827/562949953421312), (-943859449189/9007199254740992)), (280823/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485462451186611/9007199254740992), (-4706048944941/9007199254740992)), (87833/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110192595116115/2251799813685248), (-9372469043735/4503599627370496)), (351789/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204828103847015/2251799813685248), (-6980018250797/1125899906842624)), (1057665/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158455265033007/2251799813685248), (-27527825898249/2251799813685248)), (2124589/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158455265033007/2251799813685248), (-27527825898249/2251799813685248)), (8104663857466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034321817072753/1125899906842624), (-6596676621061/281474976710656)), (2062491/1125899906842624), by norm_num⟩
  | 2 => ⟨((1899148150729949/2251799813685248), (-96961891661879/2251799813685248)), (7772279/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597549688086601/2251799813685248), (-81776806322569/1125899906842624)), (13779489/2251799813685248), by norm_num⟩
  | 4 => ⟨((140188706293305/281474976710656), (-58016929675259/562949953421312)), (21553519/2251799813685248), by norm_num⟩
  | 5 => ⟨((1069303285700843/4503599627370496), (-462325619667139/4503599627370496)), (51824067/4503599627370496), by norm_num⟩
  | 6 => ⟨((825707980398617/18014398509481984), (-878170965588065/18014398509481984)), (4406211/562949953421312), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-962422421/16777216)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-1950971713/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-27911857385633/18014398509481984), (-290403762595827/4503599627370496)), (95107175/9007199254740992), by norm_num⟩
  | 1 => ⟨((5287253/1073741824), (440081973/2147483648)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-33606349/4294967296), (-174825525/536870912)), (29/536870912), by norm_num⟩
  | 3 => ⟨((35600929/4294967296), (1481613145/4294967296)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-28285417/4294967296), (-588580791/2147483648)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((35957031/8589934592), (748216575/4294967296)), (255/8589934592), by norm_num⟩
  | 6 => ⟨((-38091127/17179869184), (-99078023/1073741824)), (17/1073741824), by norm_num⟩
  | 7 => ⟨((34587329/34359738368), (1439429899/34359738368)), (249/34359738368), by norm_num⟩
  | 8 => ⟨((-13740049/34359738368), (-571823213/34359738368)), (25/8589934592), by norm_num⟩
  | 9 => ⟨((38814769/274877906944), (807682201/137438953472)), (71/68719476736), by norm_num⟩
  | 10 => ⟨((-24671085/549755813888), (-1026743005/549755813888)), (363/1099511627776), by norm_num⟩
  | 11 => ⟨((14255643/1099511627776), (1186561651/2199023255552)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((-30203467/8796093022208), (-1227525/8589934592)), (225/8796093022208), by norm_num⟩
  | 13 => ⟨((7383711/8796093022208), (614579677/17592186044416)), (111/17592186044416), by norm_num⟩
  | 14 => ⟨((-26818093/140737488355328), (-558047799/70368744177664)), (203/140737488355328), by norm_num⟩
  | 15 => ⟨((22727825/562949953421312), (945869837/562949953421312)), (347/1125899906842624), by norm_num⟩
  | 16 => ⟨((-18057563/2251799813685248), (-1503012629/4503599627370496)), (277/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (-1038715683609/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888869515130537/316912650057057350374175801344), (-2455827897449/633825300114114700748351602688)), (46221/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944291754229583/19807040628566084398385987584), (-21579303803/309485009821345068724781056)), (104013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888286319823653/2475880078570760549798248448), (-2933964714121/2475880078570760549798248448)), (27633/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769952720624001/154742504910672534362390528), (-2933041944187/154742504910672534362390528)), (110553/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387098248082217/2417851639229258349412352), (-2748746744549/9671406556917033397649408)), (103665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9826355199667/4722366482869645213696), (-75130429185/18889465931478580854784)), (11341/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943071308666011/37778931862957161709568), (-3904946313033/75557863725914323419136)), (147473/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648151323161969/2361183241434822606848), (-365888012805/590295810358705651712)), (6915/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101234245834241/36893488147419103232), (-4022160621837/590295810358705651712)), (38047/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910675016941775/36893488147419103232), (-5023792355699/73786976294838206464)), (190321/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820267605795475/9223372036854775808), (-5646396959711/9223372036854775808)), (107115/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397879298653621/288230376151711744), (-5639692112311/1152921504606846976)), (53595/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192421899437033/144115188075855872), (-2463598598137/72057594037927936)), (93875/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488401549235391/36028797018963968), (-7375752840941/36028797018963968)), (35245/4503599627370496), by norm_num⟩
  | 3 => ⟨((742608574678725/4503599627370496), (-9193419469931/9007199254740992)), (22065/562949953421312), by norm_num⟩
  | 2 => ⟨((1109939953129001/2251799813685248), (-18308238164025/4503599627370496)), (707849/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102016907845271/1125899906842624), (-6816650619985/562949953421312)), (133277/281474976710656), by norm_num⟩
  | 0 => ⟨((1078361629831097/1125899906842624), (-6719331905595/281474976710656)), (2150295/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078361629831097/1125899906842624), (-6719331905595/281474976710656)), (8202724465377043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064377849023663/2251799813685248), (-6435625104023/140737488355328)), (4221673/2251799813685248), by norm_num⟩
  | 2 => ⟨((943923402173931/1125899906842624), (-94399595051909/1125899906842624)), (4063343/1125899906842624), by norm_num⟩
  | 3 => ⟨((1566889028527009/2251799813685248), (-79142014653079/562949953421312)), (7494561/1125899906842624), by norm_num⟩
  | 4 => ⟨((1045797178626959/2251799813685248), (-440560492817473/2251799813685248)), (25074493/2251799813685248), by norm_num⟩
  | 5 => ⟨((799003699640839/4503599627370496), (-409216589861053/2251799813685248)), (33102113/2251799813685248), by norm_num⟩
  | 6 => ⟨((-27911857385633/18014398509481984), (-290403762595827/4503599627370496)), (95107175/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1950971713/33554432)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-247003985/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-781594863538591/18014398509481984), (-804633465622009/18014398509481984)), (51576047/4503599627370496), by norm_num⟩
  | 1 => ⟨((299913503/2147483648), (308753873/2147483648)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-965384325/4294967296), (-496920189/2147483648)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((517908711/2147483648), (1066349589/4294967296)), (281/4294967296), by norm_num⟩
  | 4 => ⟨((-833541915/4294967296), (-53631983/268435456)), (57/1073741824), by norm_num⟩
  | 5 => ⟨((33538349/268435456), (552431019/4294967296)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((-143941041/2147483648), (-592735617/8589934592)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((132379525/4294967296), (545126385/17179869184)), (75/8589934592), by norm_num⟩
  | 8 => ⟨((-426113253/34359738368), (-877347071/68719476736)), (61/17179869184), by norm_num⟩
  | 9 => ⟨((609602511/137438953472), (627571395/137438953472)), (11/8589934592), by norm_num⟩
  | 10 => ⟨((-392446957/274877906944), (-808029757/549755813888)), (229/549755813888), by norm_num⟩
  | 11 => ⟨((459359281/1099511627776), (945799073/2199023255552)), (135/1099511627776), by norm_num⟩
  | 12 => ⟨((-492873495/4398046511104), (-1014803257/8796093022208)), (73/2199023255552), by norm_num⟩
  | 13 => ⟨((976306817/35184372088832), (502542411/17592186044416)), (291/35184372088832), by norm_num⟩
  | 14 => ⟨((-897888689/140737488355328), (-462177605/70368744177664)), (269/140737488355328), by norm_num⟩
  | 15 => ⟨((770717919/562949953421312), (3099359/2199023255552)), (233/562949953421312), by norm_num⟩
  | 16 => ⟨((-620211319/2251799813685248), (-638492913/2251799813685248)), (95/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-3050288410355/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444420268611753/158456325028528675187087900672), (-1802838767147/316912650057057350374175801344)), (23139/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236064764953017/4951760157141521099596496896), (-4055404792797/39614081257132168796771975168)), (26037/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888216588540237/2475880078570760549798248448), (-4307646361761/2475880078570760549798248448)), (27671/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769882702099237/154742504910672534362390528), (-2153136471881/77371252455336267181195264)), (110713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548327045040515/9671406556917033397649408), (-4035672102781/9671406556917033397649408)), (51913/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257715457065447/604462909807314587353088), (-3529754841533/604462909807314587353088)), (90879/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943023891515815/37778931862957161709568), (-5733118535387/75557863725914323419136)), (147737/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296231022061143/4722366482869645213696), (-1074362147017/1180591620717411303424)), (13857/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404912160270587/147573952589676412928), (-5905109673675/590295810358705651712)), (152511/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455306176831727/18446744073709551616), (-7375567606363/73786976294838206464)), (190765/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820124951444681/9223372036854775808), (-8289517801605/9223372036854775808)), (214785/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591372467977329/1152921504606846976), (-4139766079629/576460752303423488)), (215003/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192292939420483/144115188075855872), (-7233369232005/144115188075855872)), (94187/72057594037927936), by norm_num⟩
  | 4 => ⟨((372050869634883/9007199254740992), (-10827642115015/36028797018963968)), (283053/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484961497145979/9007199254740992), (-13495401992413/9007199254740992)), (354681/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219344569150621/4503599627370496), (-26873631293543/4503599627370496)), (177989/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203171282058761/2251799813685248), (-40018491446633/2251799813685248)), (1074445/2251799813685248), by norm_num⟩
  | 0 => ⟨((538690846347539/562949953421312), (-39437504407483/1125899906842624)), (135941/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538690846347539/562949953421312), (-39437504407483/1125899906842624)), (518573761523199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((514786433481183/562949953421312), (-150952122816519/2251799813685248)), (1078757/562949953421312), by norm_num⟩
  | 2 => ⟨((1872855031129821/2251799813685248), (-34509330917811/281474976710656)), (4235117/1125899906842624), by norm_num⟩
  | 3 => ⟨((761916919938655/1125899906842624), (-229615345511811/1125899906842624)), (16166569/2251799813685248), by norm_num⟩
  | 4 => ⟨((234387703021665/562949953421312), (-621539501903389/2251799813685248)), (28474423/2251799813685248), by norm_num⟩
  | 5 => ⟨((437596779095311/4503599627370496), (-258781824748349/1125899906842624)), (39429969/2251799813685248), by norm_num⟩
  | 6 => ⟨((-781594863538591/18014398509481984), (-804633465622009/18014398509481984)), (51576047/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-247003985/4194304)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-2000109037/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-540381434838533/9007199254740992), (-89220061272231/18014398509481984)), (90654143/9007199254740992), by norm_num⟩
  | 1 => ⟨((839526597/4294967296), (34652659/2147483648)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((-683814675/2147483648), (-28225427/1073741824)), (233/4294967296), by norm_num⟩
  | 3 => ⟨((371322371/1073741824), (15326861/536870912)), (255/4294967296), by norm_num⟩
  | 4 => ⟨((-302451033/1073741824), (-49936393/2147483648)), (105/2147483648), by norm_num⟩
  | 5 => ⟨((788331731/4294967296), (130158071/8589934592)), (69/2147483648), by norm_num⟩
  | 6 => ⟨((-214038407/2147483648), (-70677927/8589934592)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((796980335/17179869184), (131586005/34359738368)), (283/34359738368), by norm_num⟩
  | 8 => ⟨((-1298319435/68719476736), (-107179977/68719476736)), (29/8589934592), by norm_num⟩
  | 9 => ⟨((235002781/34359738368), (155201205/274877906944)), (169/137438953472), by norm_num⟩
  | 10 => ⟨((-306264699/137438953472), (-50566051/274877906944)), (111/274877906944), by norm_num⟩
  | 11 => ⟨((362850893/549755813888), (59908755/1099511627776)), (265/2199023255552), by norm_num⟩
  | 12 => ⟨((-1576270985/8796093022208), (-16265709/1099511627776)), (145/4398046511104), by norm_num⟩
  | 13 => ⟨((790098929/17592186044416), (130449847/35184372088832)), (293/35184372088832), by norm_num⟩
  | 14 => ⟨((-1470982049/140737488355328), (-60716885/70368744177664)), (137/70368744177664), by norm_num⟩
  | 15 => ⟨((1278027073/562949953421312), (52752393/281474976710656)), (15/35184372088832), by norm_num⟩
  | 16 => ⟨((-130122987/281474976710656), (-85936195/2251799813685248)), (197/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (-1992492083709/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777624058272625/633825300114114700748351602688), (-1177574285551/158456325028528675187087900672)), (92665/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888453723629127/39614081257132168796771975168), (-5297771776877/39614081257132168796771975168)), (52139/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888147824627509/2475880078570760549798248448), (-703408262795/309485009821345068724781056)), (110829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769813552584501/154742504910672534362390528), (-5625448007553/154742504910672534362390528)), (27717/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774130904019193/4835703278458516698824704), (-2635963144533/4835703278458516698824704)), (103981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257657965772703/604462909807314587353088), (-2305502427499/302231454903657293676544)), (5689/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885953593847499/75557863725914323419136), (-7489264136119/75557863725914323419136)), (18499/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648079855476019/2361183241434822606848), (-5613782904841/4722366482869645213696)), (55531/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404887375619491/147573952589676412928), (-7713810321311/590295810358705651712)), (38205/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821099158220627/73786976294838206464), (-9634555120499/73786976294838206464)), (191191/73786976294838206464), by norm_num⟩
  | 7 => ⟨((7109302647859/36028797018963968), (-10828282777695/9223372036854775808)), (107659/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795613106430355/576460752303423488), (-5407526406969/576460752303423488)), (215603/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192161846640325/144115188075855872), (-9448300848547/144115188075855872)), (188975/144115188075855872), by norm_num⟩
  | 4 => ⟨((744000312187231/18014398509481984), (-1767842990497/4503599627370496)), (142053/18014398509481984), by norm_num⟩
  | 3 => ⟨((742348553667469/4503599627370496), (-17626517185483/9007199254740992)), (89065/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109391769593855/2251799813685248), (-8774399242823/1125899906842624)), (89489/562949953421312), by norm_num⟩
  | 1 => ⟨((1101124932298655/1125899906842624), (-26129427738143/1125899906842624)), (541187/1125899906842624), by norm_num⟩
  | 0 => ⟨((134537847490659/140737488355328), (-51486939452291/1125899906842624)), (549735/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((134537847490659/140737488355328), (-51486939452291/1125899906842624)), (2097072603465843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2053071968683015/2251799813685248), (-196875532986755/2251799813685248)), (4405263/2251799813685248), by norm_num⟩
  | 2 => ⟨((1854669543767399/2251799813685248), (-359001395806255/2251799813685248)), (550205/140737488355328), by norm_num⟩
  | 3 => ⟨((1470342565207409/2251799813685248), (-73921863627185/281474976710656)), (4327109/562949953421312), by norm_num⟩
  | 4 => ⟨((804770905935679/2251799813685248), (-193073046600225/562949953421312)), (31694741/2251799813685248), by norm_num⟩
  | 5 => ⟨((22746688916731/2251799813685248), (-1104038251925663/4503599627370496)), (88790499/4503599627370496), by norm_num⟩
  | 6 => ⟨((-540381434838533/9007199254740992), (-89220061272231/18014398509481984)), (90654143/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-2000109037/33554432)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1011638701/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-430764555357021/9007199254740992), (599712050733667/18014398509481984)), (96267897/9007199254740992), by norm_num⟩
  | 1 => ⟨((676979877/4294967296), (-235623489/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-557803809/2147483648), (388288291/2147483648)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((612810119/2147483648), (-26661143/134217728)), (281/4294967296), by norm_num⟩
  | 4 => ⟨((-1009861091/4294967296), (43935389/268435456)), (233/4294967296), by norm_num⟩
  | 5 => ⟨((665667483/4294967296), (-463372399/4294967296)), (155/4294967296), by norm_num⟩
  | 6 => ⟨((-731310477/8589934592), (127266653/2147483648)), (43/2147483648), by norm_num⟩
  | 7 => ⟨((688651437/17179869184), (-479371573/17179869184)), (41/4294967296), by norm_num⟩
  | 8 => ⟨((-1134841397/68719476736), (789965251/68719476736)), (17/4294967296), by norm_num⟩
  | 9 => ⟨((25973973/4294967296), (-289288511/68719476736)), (201/137438953472), by norm_num⟩
  | 10 => ⟨((-1095756515/549755813888), (47672387/34359738368)), (267/549755813888), by norm_num⟩
  | 11 => ⟨((328312247/549755813888), (-228538779/549755813888)), (161/1099511627776), by norm_num⟩
  | 12 => ⟨((-360687869/2199023255552), (251075511/2199023255552)), (89/2199023255552), by norm_num⟩
  | 13 => ⟨((365774885/8796093022208), (-509233185/17592186044416)), (91/8796093022208), by norm_num⟩
  | 14 => ⟨((-172219193/17592186044416), (239764215/35184372088832)), (173/70368744177664), by norm_num⟩
  | 15 => ⟨((1210893579/562949953421312), (-421452661/281474976710656)), (307/562949953421312), by norm_num⟩
  | 16 => ⟨((-997726925/2251799813685248), (694519609/2251799813685248)), (255/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (825037634865/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444394420265471/158456325028528675187087900672), (3900606102319/633825300114114700748351602688)), (92585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888401766682243/39614081257132168796771975168), (4387092794237/39614081257132168796771975168)), (104183/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888092911579621/2475880078570760549798248448), (4659933162571/2475880078570760549798248448)), (110723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769758966802825/154742504910672534362390528), (2329205803551/77371252455336267181195264)), (110755/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548210981303461/9671406556917033397649408), (4365644748401/9671406556917033397649408)), (25967/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257613839494667/604462909807314587353088), (238645225339/37778931862957161709568)), (45459/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885882538805933/75557863725914323419136), (1550436986019/18889465931478580854784)), (73903/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324026746970269/1180591620717411303424), (36317677913/36893488147419103232)), (110911/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809738965161441/295147905179352825856), (6387610336633/590295810358705651712)), (152593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821011073900117/73786976294838206464), (1994516381065/18446744073709551616)), (190879/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819884278075217/9223372036854775808), (4483232576231/4611686018427387904)), (13433/576460752303423488), by norm_num⟩
  | 6 => ⟨((49722855516229/36028797018963968), (2238850464529/288230376151711744)), (53791/288230376151711744), by norm_num⟩
  | 5 => ⟨((298020379066003/36028797018963968), (977943004831/18014398509481984)), (188535/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487885413077681/36028797018963968), (11710484914817/36028797018963968)), (283335/36028797018963968), by norm_num⟩
  | 3 => ⟨((742281149481431/4503599627370496), (7297364084467/4503599627370496)), (355103/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218541373206731/4503599627370496), (29059628294985/4503599627370496)), (713015/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201954661617797/2251799813685248), (43265941910483/2251799813685248)), (1076569/2251799813685248), by norm_num⟩
  | 0 => ⟨((2152283866576277/2251799813685248), (85244291031391/2251799813685248)), (545365/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152283866576277/2251799813685248), (85244291031391/2251799813685248)), (2080402376415061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((513484727312617/562949953421312), (5092313024163/70368744177664)), (4335269/2251799813685248), by norm_num⟩
  | 2 => ⟨((465417818879041/562949953421312), (18579448838827/140737488355328)), (4268065/1125899906842624), by norm_num⟩
  | 3 => ⟨((187486125667791/281474976710656), (122884196038933/562949953421312)), (16368253/2251799813685248), by norm_num⟩
  | 4 => ⟨((55734822817195/140737488355328), (654810089063769/2251799813685248)), (3618901/281474976710656), by norm_num⟩
  | 5 => ⟨((162738528751977/2251799813685248), (259317717826099/1125899906842624)), (39768181/2251799813685248), by norm_num⟩
  | 6 => ⟨((-430764555357021/9007199254740992), (599712050733667/18014398509481984)), (96267897/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1011638701/16777216)), (1/16777216), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile008Terms3
