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
namespace Reinmann.XiBand97.Tile063Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨63,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80667/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80667/2560))
  have he : value ((69/80), (80667/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2862621597/1073741824), (-104582924085/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-626215217551245/9007199254740992), (13859783547477/18014398509481984)), (6379939/18014398509481984), by norm_num⟩
  | 1 => ⟨((29535794409/137438953472), (-1307409037/549755813888)), (151/137438953472), by norm_num⟩
  | 2 => ⟨((-22824098603/68719476736), (1010314209/274877906944)), (469/274877906944), by norm_num⟩
  | 3 => ⟨((47033505161/137438953472), (-65060919/17179869184)), (485/274877906944), by norm_num⟩
  | 4 => ⟨((-4543205037/17179869184), (804424251/274877906944)), (377/274877906944), by norm_num⟩
  | 5 => ⟨((11234591715/68719476736), (-248650951/137438953472)), (117/137438953472), by norm_num⟩
  | 6 => ⟨((-92604266499/1099511627776), (1024787527/1099511627776)), (121/274877906944), by norm_num⟩
  | 7 => ⟨((40891959873/1099511627776), (-905046215/2199023255552)), (429/2199023255552), by norm_num⟩
  | 8 => ⟨((-126398783969/8796093022208), (174846017/1099511627776)), (665/8796093022208), by norm_num⟩
  | 9 => ⟨((43411556367/8796093022208), (-960811487/17592186044416)), (459/17592186044416), by norm_num⟩
  | 10 => ⟨((-53674785479/35184372088832), (593981819/35184372088832)), (285/35184372088832), by norm_num⟩
  | 11 => ⟨((120662574975/281474976710656), (-333822367/70368744177664)), (643/281474976710656), by norm_num⟩
  | 12 => ⟨((-124324380593/1125899906842624), (85988259/70368744177664)), (665/1125899906842624), by norm_num⟩
  | 13 => ⟨((59121836677/2251799813685248), (-20445643/70368744177664)), (635/4503599627370496), by norm_num⟩
  | 14 => ⟨((-104427489765/18014398509481984), (1155626981/18014398509481984)), (563/18014398509481984), by norm_num⟩
  | 15 => ⟨((43038640555/36028797018963968), (-476278941/36028797018963968)), (233/36028797018963968), by norm_num⟩
  | 16 => ⟨((-133034265091/576460752303423488), (736099213/288230376151711744)), (723/576460752303423488), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (2038930337951/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777845369933579/633825300114114700748351602688), (1205306453147/158456325028528675187087900672)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472175651203581/9903520314283042199192993792), (2711298371115/19807040628566084398385987584)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888412145176219/2475880078570760549798248448), (1439984701875/618970019642690137449562112)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770077742959875/154742504910672534362390528), (5758172544061/154742504910672534362390528)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548509348238393/9671406556917033397649408), (2698205262249/4835703278458516698824704)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628937212603439/302231454903657293676544), (294998965253/37778931862957161709568)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886305081303221/75557863725914323419136), (3833228518983/37778931862957161709568)), (4627/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296423099886469/4722366482869645213696), (2873383614075/2361183241434822606848)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((202488911761113/73786976294838206464), (987101130887/73786976294838206464)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910775422863207/36893488147419103232), (4931760379551/36893488147419103232)), (5977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910244433848469/4611686018427387904), (5543083346859/4611686018427387904)), (1683/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397933163769057/288230376151711744), (2768326754375/288230376151711744)), (6741/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192603918349363/144115188075855872), (9674687546847/144115188075855872)), (5909/144115188075855872), by norm_num⟩
  | 4 => ⟨((744330801809929/18014398509481984), (7241573383123/18014398509481984)), (4441/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485519611670447/9007199254740992), (18053447736675/9007199254740992)), (11139/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110208704064523/2251799813685248), (8988921918189/1125899906842624)), (11193/2251799813685248), by norm_num⟩
  | 1 => ⟨((551168221778607/562949953421312), (3347274151501/140737488355328)), (16925/1125899906842624), by norm_num⟩
  | 0 => ⟨((539335223783021/562949953421312), (26402363007941/562949953421312)), (34395/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539335223783021/562949953421312), (26402363007941/562949953421312)), (131206516746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030945635849457/1125899906842624), (25294831760349/281474976710656)), (17283/281474976710656), by norm_num⟩
  | 2 => ⟨((1869813899902247/2251799813685248), (370584933945083/2251799813685248)), (139029/1125899906842624), by norm_num⟩
  | 3 => ⟨((1491638291551109/2251799813685248), (615440907645201/2251799813685248)), (553301/2251799813685248), by norm_num⟩
  | 4 => ⟨((819885173983065/2251799813685248), (50960081933757/140737488355328)), (1035483/2251799813685248), by norm_num⟩
  | 5 => ⟨((6570416334795/4503599627370496), (1187499254980639/4503599627370496)), (3007853/4503599627370496), by norm_num⟩
  | 6 => ⟨((-626215217551245/9007199254740992), (13859783547477/18014398509481984)), (6379939/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-104582924085/1073741824)), (1/536870912), by norm_num⟩, -16, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1451894239/536870912), (-53043456779/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-95444183661991/9007199254740992), (1190184670683069/18014398509481984)), (6387189/18014398509481984), by norm_num⟩
  | 1 => ⟨((18265666859/549755813888), (-113886021449/549755813888)), (613/549755813888), by norm_num⟩
  | 2 => ⟨((-14317973197/274877906944), (44636120191/137438953472)), (483/274877906944), by norm_num⟩
  | 3 => ⟨((7482320357/137438953472), (-93304197787/274877906944)), (507/274877906944), by norm_num⟩
  | 4 => ⟨((-11730386101/274877906944), (73138693121/274877906944)), (399/274877906944), by norm_num⟩
  | 5 => ⟨((3678055777/137438953472), (-91730379697/549755813888)), (251/274877906944), by norm_num⟩
  | 6 => ⟨((-3844174205/274877906944), (47936679161/549755813888)), (527/1099511627776), by norm_num⟩
  | 7 => ⟨((3443824567/549755813888), (-85888674423/2199023255552)), (237/1099511627776), by norm_num⟩
  | 8 => ⟨((-10798092011/4398046511104), (67325860467/4398046511104)), (373/4398046511104), by norm_num⟩
  | 9 => ⟨((15047713353/17592186044416), (-23455538453/4398046511104)), (261/8796093022208), by norm_num⟩
  | 10 => ⟨((-18872807273/70368744177664), (58835764121/35184372088832)), (657/70368744177664), by norm_num⟩
  | 11 => ⟨((1344899501/17592186044416), (-67083344761/140737488355328)), (47/17592186044416), by norm_num⟩
  | 12 => ⟨((-2811283071/140737488355328), (70113146495/562949953421312)), (395/562949953421312), by norm_num⟩
  | 13 => ⟨((5424468805/1125899906842624), (-33821440815/1125899906842624)), (383/2251799813685248), by norm_num⟩
  | 14 => ⟨((-9719080321/9007199254740992), (30299123443/4503599627370496)), (345/9007199254740992), by norm_num⟩
  | 15 => ⟨((8126432035/36028797018963968), (-50668120695/36028797018963968)), (579/72057594037927936), by norm_num⟩
  | 16 => ⟨((-12740190321/288230376151711744), (39717399843/144115188075855872)), (455/288230376151711744), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (2253293385991/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222224373290031/79228162514264337593543950336), (665971022317/158456325028528675187087900672)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944323206318773/19807040628566084398385987584), (2996166455985/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236044136861505/309485009821345068724781056), (3182548513987/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1770019427553681/154742504910672534362390528), (795390196375/38685626227668133590597632)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774227728862843/4835703278458516698824704), (1490832075127/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314457012620857/151115727451828646838272), (1303953733787/302231454903657293676544)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886231182395361/75557863725914323419136), (2117942143475/37778931862957161709568)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648184475861933/2361183241434822606848), (3175194432405/4722366482869645213696)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619838911089771/590295810358705651712), (1090775250687/147573952589676412928)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821463468159007/73786976294838206464), (5449692179543/73786976294838206464)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820394824094941/9223372036854775808), (1531288843231/2305843009213693952)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795821959872205/576460752303423488), (6117977115081/1152921504606846976)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192532230353901/144115188075855872), (668145532877/18014398509481984)), (5871/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488565941571397/36028797018963968), (8001639511713/36028797018963968)), (8819/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485420714678477/9007199254740992), (2493479373547/2251799813685248)), (11043/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220281289407523/4503599627370496), (2482957442971/562949953421312)), (173/35184372088832), by norm_num⟩
  | 1 => ⟨((2204621618663215/2251799813685248), (29585819949199/2251799813685248)), (33367/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157842357799991/2251799813685248), (29168782554289/1125899906842624)), (67337/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157842357799991/2251799813685248), (29168782554289/1125899906842624)), (256870278365325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((516573491717079/562949953421312), (111806802964591/2251799813685248)), (132545/2251799813685248), by norm_num⟩
  | 2 => ⟨((472629712736343/562949953421312), (205192061049581/2251799813685248)), (256415/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568504323695501/2251799813685248), (43067711561325/281474976710656)), (477283/2251799813685248), by norm_num⟩
  | 4 => ⟨((1039833479582339/2251799813685248), (479985060022223/2251799813685248)), (810965/2251799813685248), by norm_num⟩
  | 5 => ⟨((188930650549985/1125899906842624), (886587754519123/4503599627370496)), (547349/1125899906842624), by norm_num⟩
  | 6 => ⟨((-95444183661991/9007199254740992), (1190184670683069/18014398509481984)), (6387189/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-53043456779/536870912)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-53763441863/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1075249444330941/18014398509481984), (440417119995329/18014398509481984)), (3184773/18014398509481984), by norm_num⟩
  | 1 => ⟨((-52142343371/274877906944), (-21357258837/274877906944)), (39/68719476736), by norm_num⟩
  | 2 => ⟨((82855587037/274877906944), (16968629563/137438953472)), (125/137438953472), by norm_num⟩
  | 3 => ⟨((-21943292979/68719476736), (-17975739393/137438953472)), (267/274877906944), by norm_num⟩
  | 4 => ⟨((34868483151/137438953472), (7140983429/68719476736)), (107/137438953472), by norm_num⟩
  | 5 => ⟨((-88651133149/549755813888), (-18155543791/274877906944)), (137/274877906944), by norm_num⟩
  | 6 => ⟨((93912691089/1099511627776), (38466196991/1099511627776)), (293/1099511627776), by norm_num⟩
  | 7 => ⟨((-85274167895/2199023255552), (-17463949241/1099511627776)), (67/549755813888), by norm_num⟩
  | 8 => ⟨((67751473977/4398046511104), (27750685389/4398046511104)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((-23924203487/4398046511104), (-39196965331/17592186044416)), (305/17592186044416), by norm_num⟩
  | 10 => ⟨((7603240653/4398046511104), (12457006581/17592186044416)), (49/8796093022208), by norm_num⟩
  | 11 => ⟨((-8786730211/17592186044416), (-14396013629/70368744177664)), (57/35184372088832), by norm_num⟩
  | 12 => ⟨((37232935471/281474976710656), (30500870837/562949953421312)), (243/562949953421312), by norm_num⟩
  | 13 => ⟨((-72817398885/2251799813685248), (-7456416107/562949953421312)), (15/140737488355328), by norm_num⟩
  | 14 => ⟨((33059659063/4503599627370496), (13541081011/4503599627370496)), (55/2251799813685248), by norm_num⟩
  | 15 => ⟨((-56034867261/36028797018963968), (-22951618333/36028797018963968)), (47/9007199254740992), by norm_num⟩
  | 16 => ⟨((44520456133/144115188075855872), (18235369639/144115188075855872)), (301/288230376151711744), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (506391220685/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777742073498789/633825300114114700748351602688), (598628530605/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888587097864971/39614081257132168796771975168), (673298469195/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472072589125095/618970019642690137449562112), (5587341615/19342813113834066795298816)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884978503896843/77371252455336267181195264), (178738740777/38685626227668133590597632)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548397277475765/9671406556917033397649408), (670031565893/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257777480734563/604462909807314587353088), (293019509967/302231454903657293676544)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886149639598681/75557863725914323419136), (475933134705/37778931862957161709568)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296308347893307/4722366482869645213696), (713508693613/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619756478668435/590295810358705651712), (30638734675/18446744073709551616)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821361772280271/73786976294838206464), (612298874129/36893488147419103232)), (2963/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910141130840363/4611686018427387904), (1376365225677/9223372036854775808)), (1667/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49735426843353/36028797018963968), (687366532739/576460752303423488)), (6669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192438334480609/144115188075855872), (600528924567/72057594037927936)), (5837/144115188075855872), by norm_num⟩
  | 4 => ⟨((744215122344849/18014398509481984), (1797926090093/36028797018963968)), (8757/36028797018963968), by norm_num⟩
  | 3 => ⟨((371315015272737/2251799813685248), (2241015975067/9007199254740992)), (10951/9007199254740992), by norm_num⟩
  | 2 => ⟨((554996681712669/1125899906842624), (557864392019/562949953421312)), (21915/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204246085939587/2251799813685248), (6646783402267/2251799813685248)), (32907/2251799813685248), by norm_num⟩
  | 0 => ⟨((269669156572503/281474976710656), (6552210555075/1125899906842624)), (16489/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269669156572503/281474976710656), (6552210555075/1125899906842624)), (62900545360374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2066791773531741/2251799813685248), (3138696580991/281474976710656)), (31787/562949953421312), by norm_num⟩
  | 2 => ⟨((1852250013307/2199023255552), (46093136583667/2251799813685248)), (236239/2251799813685248), by norm_num⟩
  | 3 => ⟨((399165316141287/562949953421312), (38824515672995/1125899906842624)), (407643/2251799813685248), by norm_num⟩
  | 4 => ⟨((282362780012347/562949953421312), (13764456305981/281474976710656)), (606201/2251799813685248), by norm_num⟩
  | 5 => ⟨((561121982703867/2251799813685248), (220925934849861/4503599627370496)), (1334803/4503599627370496), by norm_num⟩
  | 6 => ⟨((1075249444330941/18014398509481984), (440417119995329/18014398509481984)), (3184773/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-53763441863/536870912)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-54454031465/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((43713907722905/1125899906842624), (-877002672522699/18014398509481984)), (4298235/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8588234911/68719476736), (43074992385/274877906944)), (213/274877906944), by norm_num⟩
  | 2 => ⟨((55288923467/274877906944), (-69326525823/274877906944)), (345/274877906944), by norm_num⟩
  | 3 => ⟨((-59322726377/274877906944), (74384492665/274877906944)), (93/68719476736), by norm_num⟩
  | 4 => ⟨((23869061225/137438953472), (-1870581603/8589934592)), (301/274877906944), by norm_num⟩
  | 5 => ⟨((-3841577207/34359738368), (19267743681/137438953472)), (195/274877906944), by norm_num⟩
  | 6 => ⟨((32974826669/549755813888), (-20673491445/274877906944)), (211/549755813888), by norm_num⟩
  | 7 => ⟨((-60652498511/2199023255552), (19012971951/549755813888)), (195/1099511627776), by norm_num⟩
  | 8 => ⟨((24404107647/2199023255552), (-15300098943/1099511627776)), (79/1099511627776), by norm_num⟩
  | 9 => ⟨((-34912796503/8796093022208), (10944248579/2199023255552)), (57/2199023255552), by norm_num⟩
  | 10 => ⟨((44951982657/35184372088832), (-14091270869/8796093022208)), (295/35184372088832), by norm_num⟩
  | 11 => ⟨((-822129831/2199023255552), (16493836779/35184372088832)), (347/140737488355328), by norm_num⟩
  | 12 => ⟨((14113780469/140737488355328), (-70788816623/562949953421312)), (375/562949953421312), by norm_num⟩
  | 13 => ⟨((-55914469845/2251799813685248), (35055447769/1125899906842624)), (187/1125899906842624), by norm_num⟩
  | 14 => ⟨((51423352927/9007199254740992), (-32239752387/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 15 => ⟨((-5517512919/4503599627370496), (55347071765/36028797018963968)), (299/36028797018963968), by norm_num⟩
  | 16 => ⟨((35520377897/144115188075855872), (-44538837821/144115188075855872)), (121/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-1169188590453/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777687024981405/633825300114114700748351602688), (-691035808231/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888525137483945/39614081257132168796771975168), (-1554459213493/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944112240416953/1237940039285380274899124224), (-12899573491/19342813113834066795298816)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769891084096327/154742504910672534362390528), (-1650619733831/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387083855757385/2417851639229258349412352), (-1546897701589/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257723307173729/604462909807314587353088), (-1352977447423/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471515378053265/18889465931478580854784), (-2197542571021/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296242169049819/4722366482869645213696), (-102952651015/295147905179352825856)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101229084226613/36893488147419103232), (-565868316019/147573952589676412928)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113827978511955/4611686018427387904), (-353389472871/9223372036854775808)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820153603608765/9223372036854775808), (-1588723845693/4611686018427387904)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591404655080289/1152921504606846976), (-1586815045609/576460752303423488)), (3341/576460752303423488), by norm_num⟩
  | 5 => ⟨((596162534188135/72057594037927936), (-86644922219/4503599627370496)), (2925/72057594037927936), by norm_num⟩
  | 4 => ⟨((744129786800049/18014398509481984), (-1037598390123/9007199254740992)), (2195/9007199254740992), by norm_num⟩
  | 3 => ⟨((742522689529521/4503599627370496), (-2586520375579/4503599627370496)), (5493/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219553364013281/4503599627370496), (-5150680874357/2251799813685248)), (11001/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101793075903105/1125899906842624), (-15340710350677/2251799813685248)), (33081/2251799813685248), by norm_num⟩
  | 0 => ⟨((134749653937643/140737488355328), (-30238883549559/2251799813685248)), (66479/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((134749653937643/140737488355328), (-30238883549559/2251799813685248)), (253597268111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1031929593868375/1125899906842624), (-14476168153137/562949953421312)), (2017/35184372088832), by norm_num⟩
  | 2 => ⟨((945057764422115/1125899906842624), (-13267952357265/281474976710656)), (60817/562949953421312), by norm_num⟩
  | 3 => ⟨((1581521688966439/2251799813685248), (-89094821427807/1125899906842624)), (107831/562949953421312), by norm_num⟩
  | 4 => ⟨((548330115501871/1125899906842624), (-125149128804719/1125899906842624)), (674133/2251799813685248), by norm_num⟩
  | 5 => ⟨((506268113876933/2251799813685248), (-121898999787451/1125899906842624)), (1612985/4503599627370496), by norm_num⟩
  | 6 => ⟨((43713907722905/1125899906842624), (-877002672522699/18014398509481984)), (4298235/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-54454031465/536870912)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-3017330773/1073741824), (-13779383009/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-578465049534859/18014398509481984), (-917271394063943/18014398509481984)), (1540473/4503599627370496), by norm_num⟩
  | 1 => ⟨((28758163075/274877906944), (45601787619/274877906944)), (77/68719476736), by norm_num⟩
  | 2 => ⟨((-46848435777/274877906944), (-2321484787/8589934592)), (63/34359738368), by norm_num⟩
  | 3 => ⟨((25439454403/137438953472), (80678629841/274877906944)), (275/137438953472), by norm_num⟩
  | 4 => ⟨((-5180262395/34359738368), (-8214336393/34359738368)), (225/137438953472), by norm_num⟩
  | 5 => ⟨((3375558995/34359738368), (42820961543/274877906944)), (295/274877906944), by norm_num⟩
  | 6 => ⟨((-29327725535/549755813888), (-23252471093/274877906944)), (161/274877906944), by norm_num⟩
  | 7 => ⟨((6825182931/274877906944), (43290740325/1099511627776)), (301/1099511627776), by norm_num⟩
  | 8 => ⟨((-22237104879/2199023255552), (-70522705591/4398046511104)), (493/4398046511104), by norm_num⟩
  | 9 => ⟨((32200281965/8796093022208), (12764987941/2199023255552)), (359/8796093022208), by norm_num⟩
  | 10 => ⟨((-41964650877/35184372088832), (-66543300829/35184372088832)), (235/17592186044416), by norm_num⟩
  | 11 => ⟨((24859069771/70368744177664), (39418999647/70368744177664)), (559/140737488355328), by norm_num⟩
  | 12 => ⟨((-3374718715/35184372088832), (-21405151047/140737488355328)), (305/281474976710656), by norm_num⟩
  | 13 => ⟨((27065007661/1125899906842624), (42916952937/1125899906842624)), (77/281474976710656), by norm_num⟩
  | 14 => ⟨((-50388804435/9007199254740992), (-39950735939/4503599627370496)), (575/9007199254740992), by norm_num⟩
  | 15 => ⟨((10944772619/9007199254740992), (69420455709/36028797018963968)), (501/36028797018963968), by norm_num⟩
  | 16 => ⟨((-35659125779/144115188075855872), (-56544636603/144115188075855872)), (205/72057594037927936), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-2779042197033/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777630173574597/633825300114114700748351602688), (-3284859856157/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888460935203673/39614081257132168796771975168), (-3694564764085/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888155934696357/2475880078570760549798248448), (-981087316161/618970019642690137449562112)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769822165819133/154742504910672534362390528), (-1961541615119/77371252455336267181195264)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548270417097119/9671406556917033397649408), (-3676545835143/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314416508082583/151115727451828646838272), (-803908359807/151115727451828646838272)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885967701457825/75557863725914323419136), (-2611442572691/37778931862957161709568)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296171165078561/4722366482869645213696), (-3914960683327/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404891667284941/147573952589676412928), (-5379492875391/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910561369394705/36893488147419103232), (-419937666559/4611686018427387904)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910005459102621/4611686018427387904), (-7551509238581/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198907410586063/144115188075855872), (-7542307217601/1152921504606846976)), (3357/576460752303423488), by norm_num⟩
  | 5 => ⟨((596097428913075/72057594037927936), (-6589178809651/144115188075855872)), (2941/72057594037927936), by norm_num⟩
  | 4 => ⟨((744029128848637/18014398509481984), (-4931559423311/18014398509481984)), (8837/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484783285292625/9007199254740992), (-1536603880157/1125899906842624)), (5535/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109499017067051/2251799813685248), (-6119433670209/1125899906842624)), (11107/2251799813685248), by norm_num⟩
  | 1 => ⟨((550669003300945/562949953421312), (-36447744930451/2251799813685248)), (16753/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153869859002977/2251799813685248), (-71825817095703/2251799813685248)), (16939/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153869859002977/2251799813685248), (-71825817095703/2251799813685248)), (64617159129905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((514476952320213/562949953421312), (-34351069220383/562949953421312)), (66971/1125899906842624), by norm_num⟩
  | 2 => ⟨((1872326567650697/2251799813685248), (-31393258484235/281474976710656)), (261165/2251799813685248), by norm_num⟩
  | 3 => ⟨((1528791506065609/2251799813685248), (-417645878095803/2251799813685248)), (123141/562949953421312), by norm_num⟩
  | 4 => ⟨((3751817241479/8796093022208), (-141774030510117/562949953421312)), (425769/1125899906842624), by norm_num⟩
  | 5 => ⟨((533702340386027/4503599627370496), (-241884778034467/1125899906842624)), (2310645/4503599627370496), by norm_num⟩
  | 6 => ⟨((-578465049534859/18014398509481984), (-917271394063943/18014398509481984)), (1540473/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-13779383009/134217728)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-3052282179/1073741824), (-111511977579/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1032547990087821/18014398509481984), (94514012732551/9007199254740992)), (5640057/18014398509481984), by norm_num⟩
  | 1 => ⟨((3245458347/17179869184), (-2376577511/68719476736)), (569/549755813888), by norm_num⟩
  | 2 => ⟨((-85572010137/274877906944), (15665623551/274877906944)), (471/274877906944), by norm_num⟩
  | 3 => ⟨((94010461903/274877906944), (-17210446543/274877906944)), (519/274877906944), by norm_num⟩
  | 4 => ⟨((-77460786533/274877906944), (14180706049/274877906944)), (429/274877906944), by norm_num⟩
  | 5 => ⟨((51059623185/274877906944), (-18694917513/549755813888)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((-28047364743/274877906944), (5134616529/274877906944)), (313/549755813888), by norm_num⟩
  | 7 => ⟨((52822593551/1099511627776), (-2417551207/274877906944)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((-10880915699/549755813888), (15935708787/4398046511104)), (489/4398046511104), by norm_num⟩
  | 9 => ⟨((31877087197/4398046511104), (-2917860917/2199023255552)), (45/1099511627776), by norm_num⟩
  | 10 => ⟨((-21012335833/8796093022208), (480839679/1099511627776)), (119/8796093022208), by norm_num⟩
  | 11 => ⟨((100731972479/140737488355328), (-18440950001/140737488355328)), (573/140737488355328), by norm_num⟩
  | 12 => ⟨((-27666345707/140737488355328), (10129727143/281474976710656)), (79/70368744177664), by norm_num⟩
  | 13 => ⟨((56113084387/1125899906842624), (-80254635/8796093022208)), (643/2251799813685248), by norm_num⟩
  | 14 => ⟨((-6604984721/562949953421312), (19346738081/9007199254740992)), (19/281474976710656), by norm_num⟩
  | 15 => ⟨((92880862477/36028797018963968), (-17003651361/36028797018963968)), (67/4503599627370496), by norm_num⟩
  | 16 => ⟨((-76530042675/144115188075855872), (14010315253/144115188075855872)), (443/144115188075855872), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (3856418476623/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888787348270565/316912650057057350374175801344), (4558085839745/633825300114114700748351602688)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888398247419479/39614081257132168796771975168), (5126565298193/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888088953867993/2475880078570760549798248448), (2722696833691/1237940039285380274899124224)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769754763567467/154742504910672534362390528), (2721807188819/77371252455336267181195264)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548206780129691/9671406556917033397649408), (1275374628325/2417851639229258349412352)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257609903083775/604462909807314587353088), (34858764283/4722366482869645213696)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117867228403991/4722366482869645213696), (1811770416123/18889465931478580854784)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648050699227197/2361183241434822606848), (5432213869479/4722366482869645213696)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404867388338937/147573952589676412928), (7464263200385/590295810358705651712)), (4775/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910499783609111/36893488147419103232), (9322786844111/73786976294838206464)), (2987/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819869912180723/9223372036854775808), (5238885738615/4611686018427387904)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795557619434971/576460752303423488), (2616206734855/288230376151711744)), (421/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192065408558149/144115188075855872), (9142174877353/144115188075855872)), (369/9007199254740992), by norm_num⟩
  | 4 => ⟨((371964322968109/9007199254740992), (13684199708677/36028797018963968)), (8875/36028797018963968), by norm_num⟩
  | 3 => ⟨((742260125741633/4503599627370496), (8527234174141/4503599627370496)), (11127/9007199254740992), by norm_num⟩
  | 2 => ⟨((277304590451963/562949953421312), (16978453006347/2251799813685248)), (11179/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100873382801033/1125899906842624), (12639094693121/562949953421312)), (33/2199023255552), by norm_num⟩
  | 0 => ⟨((2151667165295901/2251799813685248), (24900854478795/562949953421312)), (68615/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2151667165295901/2251799813685248), (24900854478795/562949953421312)), (261745461470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1025790729992007/1125899906842624), (190348540378105/2251799813685248)), (137199/2251799813685248), by norm_num⟩
  | 2 => ⟨((1853074991287535/2251799813685248), (173423735982831/1125899906842624)), (68299/562949953421312), by norm_num⟩
  | 3 => ⟨((1471526791319601/2251799813685248), (570862802443337/2251799813685248)), (533805/2251799813685248), by norm_num⟩
  | 4 => ⟨((408452551416505/1125899906842624), (746105317939757/2251799813685248)), (484163/1125899906842624), by norm_num⟩
  | 5 => ⟨((24571633966769/1125899906842624), (541342296745591/2251799813685248)), (672131/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1032547990087821/18014398509481984), (94514012732551/9007199254740992)), (5640057/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-111511977579/1073741824)), (1/536870912), by norm_num⟩, -17, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile063Terms3
