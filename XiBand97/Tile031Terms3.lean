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
namespace Reinmann.XiBand97.Tile031Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63483/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63483/2560))
  have he : value ((69/80), (63483/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-321501017/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((48833941092615/2251799813685248), (-74376311168647/1125899906842624)), (363551059/18014398509481984), by norm_num⟩
  | 1 => ⟨((-71977513/1073741824), (877000181/4294967296)), (135/2147483648), by norm_num⟩
  | 2 => ⟨((444971097/4294967296), (-338855599/1073741824)), (105/1073741824), by norm_num⟩
  | 3 => ⟨((-229237425/2147483648), (174569507/536870912)), (435/4294967296), by norm_num⟩
  | 4 => ⟨((177145653/2147483648), (-539601757/2147483648)), (169/2147483648), by norm_num⟩
  | 5 => ⟨((-438051787/8589934592), (1334345551/8589934592)), (105/2147483648), by norm_num⟩
  | 6 => ⟨((451345557/17179869184), (-687419791/8589934592)), (435/17179869184), by norm_num⟩
  | 7 => ⟨((-398608079/34359738368), (1214196433/34359738368)), (193/17179869184), by norm_num⟩
  | 8 => ⟨((19251789/4294967296), (-234570795/17179869184)), (75/17179869184), by norm_num⟩
  | 9 => ⟨((-423168691/274877906944), (644505143/137438953472)), (415/274877906944), by norm_num⟩
  | 10 => ⟨((130803239/274877906944), (-1593754207/1099511627776)), (129/274877906944), by norm_num⟩
  | 11 => ⟨((-36756215/274877906944), (447851083/1099511627776)), (73/549755813888), by norm_num⟩
  | 12 => ⟨((302973389/8796093022208), (-461442237/4398046511104)), (303/8796093022208), by norm_num⟩
  | 13 => ⟨((-72038739/8796093022208), (877746181/35184372088832)), (145/17592186044416), by norm_num⟩
  | 14 => ⟨((508970973/281474976710656), (-775185917/140737488355328)), (515/281474976710656), by norm_num⟩
  | 15 => ⟨((-419533569/1125899906842624), (1277937375/1125899906842624)), (427/1125899906842624), by norm_num⟩
  | 16 => ⟨((162099509/2251799813685248), (-493769835/2251799813685248)), (83/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-1632943500887/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888927918780193/316912650057057350374175801344), (-1930617542637/633825300114114700748351602688)), (46195/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472178738340061/9903520314283042199192993792), (-2171444065457/39614081257132168796771975168)), (207903/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888426032489749/2475880078570760549798248448), (-1153266001327/1237940039285380274899124224)), (220925/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442523123049509/38685626227668133590597632), (-2305826595841/154742504910672534362390528)), (220957/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387131022673301/2417851639229258349412352), (-1080481610973/4835703278458516698824704)), (207181/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628944119527117/302231454903657293676544), (-1890093926091/604462909807314587353088)), (90659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58947788785477/2361183241434822606848), (-1534999565955/37778931862957161709568)), (18419/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648221358128383/2361183241434822606848), (-2301271964439/4722366482869645213696)), (55271/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809970347523011/295147905179352825856), (-3162255718523/590295810358705651712)), (304081/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910795616861297/36893488147419103232), (-3949832015443/73786976294838206464)), (380237/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820539295259777/9223372036854775808), (-2219728310441/4611686018427387904)), (213977/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591789307191083/1152921504606846976), (-4434331518149/1152921504606846976)), (107047/288230376151711744), by norm_num⟩
  | 5 => ⟨((596330235980393/72057594037927936), (-968570436287/36028797018963968)), (374929/144115188075855872), by norm_num⟩
  | 4 => ⟨((372190087779035/9007199254740992), (-5799924446023/36028797018963968)), (562921/36028797018963968), by norm_num⟩
  | 3 => ⟨((742833645517529/4503599627370496), (-3614912652739/4503599627370496)), (704579/9007199254740992), by norm_num⟩
  | 2 => ⟨((138799066462333/281474976710656), (-14399575724971/4503599627370496)), (705973/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205403581906737/2251799813685248), (-2681219433079/281474976710656)), (2124915/2251799813685248), by norm_num⟩
  | 0 => ⟨((269938749530659/281474976710656), (-42304541387871/2251799813685248)), (4277977/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((269938749530659/281474976710656), (-42304541387871/2251799813685248)), (16319187172896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070207893850025/2251799813685248), (-10142673369371/281474976710656)), (8366031/2251799813685248), by norm_num⟩
  | 2 => ⟨((1900336243513037/2251799813685248), (-74597901097257/1125899906842624)), (7992831/1125899906842624), by norm_num⟩
  | 3 => ⟨((199230546006167/281474976710656), (-251818290921901/2251799813685248)), (29099503/2251799813685248), by norm_num⟩
  | 4 => ⟨((549988369939971/1125899906842624), (-356478548686639/2251799813685248)), (47702169/2251799813685248), by norm_num⟩
  | 5 => ⟨((480891714273201/2251799813685248), (-696541689786767/4503599627370496)), (61707153/2251799813685248), by norm_num⟩
  | 6 => ⟨((48833941092615/2251799813685248), (-74376311168647/1125899906842624)), (363551059/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-321501017/4194304)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-326124469/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-852099694202809/18014398509481984), (-426293333526133/9007199254740992)), (442966309/18014398509481984), by norm_num⟩
  | 1 => ⟨((4976529/33554432), (637359753/4294967296)), (333/4294967296), by norm_num⟩
  | 2 => ⟨((-998648185/4294967296), (-999218909/4294967296)), (131/1073741824), by norm_num⟩
  | 3 => ⟨((1043751869/4294967296), (522174185/2147483648)), (275/2147483648), by norm_num⟩
  | 4 => ⟨((-818169487/4294967296), (-204659267/1073741824)), (433/4294967296), by norm_num⟩
  | 5 => ⟨((1026146277/8589934592), (256683179/2147483648)), (273/4294967296), by norm_num⟩
  | 6 => ⟨((-1072491905/17179869184), (-1073104831/17179869184)), (573/17179869184), by norm_num⟩
  | 7 => ⟨((960797761/34359738368), (480673427/17179869184)), (515/34359738368), by norm_num⟩
  | 8 => ⟨((-753143955/68719476736), (-753574375/68719476736)), (203/34359738368), by norm_num⟩
  | 9 => ⟨((524773003/137438953472), (1050145819/274877906944)), (71/34359738368), by norm_num⟩
  | 10 => ⟨((-329084543/274877906944), (-164636307/137438953472)), (179/274877906944), by norm_num⟩
  | 11 => ⟨((750431041/2199023255552), (375429955/1099511627776)), (205/1099511627776), by norm_num⟩
  | 12 => ⟨((-784324063/8796093022208), (-784772301/8796093022208)), (431/8796093022208), by norm_num⟩
  | 13 => ⟨((756690327/35184372088832), (189280693/8796093022208)), (209/17592186044416), by norm_num⟩
  | 14 => ⟨((-2647989/549755813888), (-42392037/8796093022208)), (47/17592186044416), by norm_num⟩
  | 15 => ⟨((566801353/562949953421312), (567125277/562949953421312)), (79/140737488355328), by norm_num⟩
  | 16 => ⟨((-444300591/2251799813685248), (-889109013/4503599627370496)), (497/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-767208570161/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777791732328109/633825300114114700748351602688), (-3628031246889/633825300114114700748351602688)), (185115/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888642574303225/39614081257132168796771975168), (-4080570030809/39614081257132168796771975168)), (52075/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888348778267789/2475880078570760549798248448), (-541801069179/309485009821345068724781056)), (221373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770014843040617/154742504910672534362390528), (-1083265559165/38685626227668133590597632)), (27679/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96778179709327/604462909807314587353088), (-253800989331/604462909807314587353088)), (207657/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314455939193653/151115727451828646838272), (-3551784332185/604462909807314587353088)), (181763/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886223672940827/75557863725914323419136), (-5768970253159/75557863725914323419136)), (73871/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296362854541997/4722366482869645213696), (-2162192187145/2361183241434822606848)), (110859/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809914886374729/295147905179352825856), (-185694456697/18446744073709551616)), (38129/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821450915009715/73786976294838206464), (-7422072894513/73786976294838206464)), (381545/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113773696921581/576460752303423488), (-8341992766577/9223372036854775808)), (429589/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397906578017435/288230376151711744), (-260381318337/36028797018963968)), (430029/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192514653695071/144115188075855872), (-7279674152311/144115188075855872)), (188385/72057594037927936), by norm_num⟩
  | 4 => ⟨((744267626048871/18014398509481984), (-2724383698537/9007199254740992)), (283073/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485374819561309/9007199254740992), (-6791762569669/4503599627370496)), (709419/9007199254740992), by norm_num⟩
  | 2 => ⟨((555041759312499/1125899906842624), (-6763032909795/1125899906842624)), (356015/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102197283250063/1125899906842624), (-20145907450137/1125899906842624)), (2149185/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157168428873513/2251799813685248), (-79443576321631/2251799813685248)), (543873/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157168428873513/2251799813685248), (-79443576321631/2251799813685248)), (2074710847021007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2063711134740953/2251799813685248), (-4756561109371/70368744177664)), (2160819/562949953421312), by norm_num⟩
  | 2 => ⟨((940522277193105/1125899906842624), (-139496139077049/1125899906842624)), (17011121/2251799813685248), by norm_num⟩
  | 3 => ⟨((768383562181097/1125899906842624), (-233056643111937/1125899906842624)), (32635805/2251799813685248), by norm_num⟩
  | 4 => ⟨((238075292694043/562949953421312), (-159052232384055/562949953421312)), (29028165/1125899906842624), by norm_num⟩
  | 5 => ⟨((445968344777765/4503599627370496), (-1076228010631293/4503599627370496)), (163821079/4503599627370496), by norm_num⟩
  | 6 => ⟨((-852099694202809/18014398509481984), (-426293333526133/9007199254740992)), (442966309/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-326124469/4194304)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1322204471/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-139992916450093/2251799813685248), (309605574137047/18014398509481984)), (407122003/18014398509481984), by norm_num⟩
  | 1 => ⟨((424294495/2147483648), (-234590335/4294967296)), (155/2147483648), by norm_num⟩
  | 2 => ⟨((-1348430745/4294967296), (93192589/1073741824)), (495/4294967296), by norm_num⟩
  | 3 => ⟨((1428461831/4294967296), (-394894753/4294967296)), (527/4294967296), by norm_num⟩
  | 4 => ⟨((-283733037/1073741824), (78437299/1073741824)), (421/4294967296), by norm_num⟩
  | 5 => ⟨((180343773/1073741824), (-199422367/4294967296)), (537/8589934592), by norm_num⟩
  | 6 => ⟨((-1528379249/17179869184), (211258339/8589934592)), (571/17179869184), by norm_num⟩
  | 7 => ⟨((173473983/4294967296), (-191825821/17179869184)), (521/34359738368), by norm_num⟩
  | 8 => ⟨((-68913707/4294967296), (304816393/68719476736)), (13/2147483648), by norm_num⟩
  | 9 => ⟨((1557414901/274877906944), (-430543513/274877906944)), (295/137438953472), by norm_num⟩
  | 10 => ⟨((-494954839/274877906944), (68414523/137438953472)), (47/68719476736), by norm_num⟩
  | 11 => ⟨((571997499/1099511627776), (-316254599/2199023255552)), (109/549755813888), by norm_num⟩
  | 12 => ⟨((-605946281/4398046511104), (335024713/8796093022208)), (29/549755813888), by norm_num⟩
  | 13 => ⟨((1185064553/35184372088832), (-20475511/2199023255552)), (455/35184372088832), by norm_num⟩
  | 14 => ⟨((-134507105/17592186044416), (148736631/70368744177664)), (415/140737488355328), by norm_num⟩
  | 15 => ⟨((455968875/281474976710656), (-7878217/17592186044416)), (353/562949953421312), by norm_num⟩
  | 16 => ⟨((-1449093629/4503599627370496), (400598363/4503599627370496)), (563/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (3740945882777/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888865887017461/316912650057057350374175801344), (4422345501853/633825300114114700748351602688)), (185271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888574949959097/39614081257132168796771975168), (310871121721/2475880078570760549798248448)), (208487/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888276694912505/2475880078570760549798248448), (330208064865/154742504910672534362390528)), (110791/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769942498448021/154742504910672534362390528), (660208046707/19342813113834066795298816)), (221655/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96773923436233/604462909807314587353088), (4949792119077/9671406556917033397649408)), (25985/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257763891919313/604462909807314587353088), (4329300405899/604462909807314587353088)), (45493/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471531468428699/18889465931478580854784), (7031799857859/75557863725914323419136)), (147925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648144525869605/2361183241434822606848), (2635475943527/2361183241434822606848)), (222015/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809863779134453/295147905179352825856), (7242851708359/590295810358705651712)), (152739/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821322045429067/73786976294838206464), (9046507648279/73786976294838206464)), (382159/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820232661114009/9223372036854775808), (5083811894195/4611686018427387904)), (430357/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24866842781471/18014398509481984), (10155511206941/1152921504606846976)), (107723/288230376151711744), by norm_num⟩
  | 5 => ⟨((18630979890067/2251799813685248), (8872458116287/144115188075855872)), (188817/72057594037927936), by norm_num⟩
  | 4 => ⟨((744166565236011/18014398509481984), (13281489961899/36028797018963968)), (567659/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485114835777807/9007199254740992), (4138584368243/2251799813685248)), (711691/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109812610370829/2251799813685248), (4120797582423/562949953421312)), (714875/2251799813685248), by norm_num⟩
  | 1 => ⟨((137720483108177/140737488355328), (3068426119373/140737488355328)), (540147/562949953421312), by norm_num⟩
  | 0 => ⟨((1077610677707619/1125899906842624), (48388261038207/1125899906842624)), (274083/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077610677707619/1125899906842624), (48388261038207/1125899906842624)), (1045543671191167787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2058625890028005/2251799813685248), (92625830153415/1125899906842624)), (8771429/2251799813685248), by norm_num⟩
  | 2 => ⟨((933391670054275/1125899906842624), (169359577063905/1125899906842624)), (4370285/562949953421312), by norm_num⟩
  | 3 => ⟨((748323486184649/1125899906842624), (561608780726047/2251799813685248)), (8560863/562949953421312), by norm_num⟩
  | 4 => ⟨((427335441991159/1125899906842624), (746540679345787/2251799813685248)), (3912525/140737488355328), by norm_num⟩
  | 5 => ⟨((19222327508511/562949953421312), (566699205202447/2251799813685248)), (178055769/4503599627370496), by norm_num⟩
  | 6 => ⟨((-139992916450093/2251799813685248), (309605574137047/18014398509481984)), (407122003/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1322204471/16777216)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-83699259/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-319454579844063/18014398509481984), (537650982544775/9007199254740992)), (97936579/9007199254740992), by norm_num⟩
  | 1 => ⟨((245162159/4294967296), (-1650459051/8589934592)), (303/8589934592), by norm_num⟩
  | 2 => ⟨((-394573273/4294967296), (1328155685/4294967296)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((211680395/2147483648), (-356264019/1073741824)), (133/2147483648), by norm_num⟩
  | 4 => ⟨((-340686453/4294967296), (573384819/2147483648)), (27/536870912), by norm_num⟩
  | 5 => ⟨((438650955/8589934592), (-738261813/4294967296)), (35/1073741824), by norm_num⟩
  | 6 => ⟨((-235327159/8589934592), (1584248735/17179869184)), (303/17179869184), by norm_num⟩
  | 7 => ⟨((216425401/17179869184), (-1456999987/34359738368)), (35/4294967296), by norm_num⟩
  | 8 => ⟨((-174161623/34359738368), (1172475509/68719476736)), (227/68719476736), by norm_num⟩
  | 9 => ⟨((249157617/137438953472), (-209669615/34359738368)), (41/34359738368), by norm_num⟩
  | 10 => ⟨((-80200743/137438953472), (134980091/68719476736)), (213/549755813888), by norm_num⟩
  | 11 => ⟨((375499975/2199023255552), (-157994237/274877906944)), (251/2199023255552), by norm_num⟩
  | 12 => ⟨((-402895931/8796093022208), (1356170213/8796093022208)), (17/549755813888), by norm_num⟩
  | 13 => ⟨((199518765/17592186044416), (-335795655/8796093022208)), (271/35184372088832), by norm_num⟩
  | 14 => ⟨((-45873295/17592186044416), (617648295/70368744177664)), (251/140737488355328), by norm_num⟩
  | 15 => ⟨((315008939/562949953421312), (-132542211/70368744177664)), (217/562949953421312), by norm_num⟩
  | 16 => ⟨((-253493665/2251799813685248), (426636919/1125899906842624)), (11/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (2422304558767/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444420912731655/158456325028528675187087900672), (2863351904401/633825300114114700748351602688)), (46241/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236065144779691/4951760157141521099596496896), (1610247699165/19807040628566084398385987584)), (104061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944110002881103/1237940039285380274899124224), (3420807087395/2475880078570760549798248448)), (55293/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442471582838371/38685626227668133590597632), (3419717109713/154742504910672534362390528)), (110609/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548330672558571/9671406556917033397649408), (200301694247/604462909807314587353088)), (51861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257718856019767/604462909807314587353088), (2803066508231/604462909807314587353088)), (45391/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886053727515879/75557863725914323419136), (4552814305707/75557863725914323419136)), (147567/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296235848501165/4722366482869645213696), (1706357027925/2361183241434822606848)), (110717/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619655874702917/590295810358705651712), (4689401607463/590295810358705651712)), (76151/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821234643748627/73786976294838206464), (1464283739951/18446744073709551616)), (190479/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910068678637609/4611686018427387904), (6582933712519/9223372036854775808)), (53607/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591386404350331/1152921504606846976), (6575012798911/1152921504606846976)), (214601/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192306850592759/144115188075855872), (5744236138415/144115188075855872)), (187971/144115188075855872), by norm_num⟩
  | 4 => ⟨((23253558851217/562949953421312), (8598581476109/36028797018963968)), (70587/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484997816048301/9007199254740992), (10717186114433/9007199254740992)), (353621/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109717485940797/2251799813685248), (21341495847257/4503599627370496)), (709305/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101675453956757/1125899906842624), (15890455706023/1125899906842624)), (1069133/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155296392632441/2251799813685248), (62641631038731/2251799813685248)), (67471/70368744177664), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155296392632441/2251799813685248), (62641631038731/2251799813685248)), (257381439477419831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2061186140058889/2251799813685248), (1873657915019/35184372088832)), (2126605/1125899906842624), by norm_num⟩
  | 2 => ⟨((1880322080713309/2251799813685248), (54881720155447/562949953421312)), (8239345/2251799813685248), by norm_num⟩
  | 3 => ⟨((1548725181833575/2251799813685248), (91655847565711/562949953421312)), (7683357/1125899906842624), by norm_num⟩
  | 4 => ⟨((1005478801799961/2251799813685248), (126076677264667/562949953421312)), (26141413/2251799813685248), by norm_num⟩
  | 5 => ⟨((336025591382017/2251799813685248), (900736739531267/4503599627370496)), (70109123/4503599627370496), by norm_num⟩
  | 6 => ⟨((-319454579844063/18014398509481984), (537650982544775/9007199254740992)), (97936579/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-83699259/1048576)), (1/16777216), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1355505615/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((685102369976659/18014398509481984), (840620849464205/18014398509481984)), (66131391/4503599627370496), by norm_num⟩
  | 1 => ⟨((-266090591/2147483648), (-326493249/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((866948833/4294967296), (265936631/1073741824)), (85/1073741824), by norm_num⟩
  | 3 => ⟨((-941534331/4294967296), (-288815739/1073741824)), (371/4294967296), by norm_num⟩
  | 4 => ⟨((191725609/1073741824), (940989559/4294967296)), (19/268435456), by norm_num⟩
  | 5 => ⟨((-249864217/2147483648), (-613166965/4294967296)), (25/536870912), by norm_num⟩
  | 6 => ⟨((67840145/1073741824), (665919055/8589934592)), (219/8589934592), by norm_num⟩
  | 7 => ⟨((-252605419/8589934592), (-619893877/17179869184)), (103/8589934592), by norm_num⟩
  | 8 => ⟨((823012841/68719476736), (1009837047/68719476736)), (169/34359738368), by norm_num⟩
  | 9 => ⟨((-595878953/137438953472), (-365571843/68719476736)), (123/68719476736), by norm_num⟩
  | 10 => ⟨((388286231/274877906944), (952854685/549755813888)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((-230013459/549755813888), (-564453191/1099511627776)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((124901009/1099511627776), (613014329/4398046511104)), (105/2199023255552), by norm_num⟩
  | 13 => ⟨((-500848671/17592186044416), (-76817687/2199023255552)), (53/4398046511104), by norm_num⟩
  | 14 => ⟨((932464755/140737488355328), (1144134583/140737488355328)), (397/140737488355328), by norm_num⟩
  | 15 => ⟨((-101268673/70368744177664), (-248513395/140737488355328)), (347/562949953421312), by norm_num⟩
  | 16 => ⟨((329943113/1125899906842624), (101210079/281474976710656)), (71/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (144423536715/1267650600228229401496703205376)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777634962776583/633825300114114700748351602688), (682841129309/316912650057057350374175801344)), (184669/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944233291475569/19807040628566084398385987584), (1536021443613/39614081257132168796771975168)), (207771/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888162286137897/2475880078570760549798248448), (1631555206055/2475880078570760549798248448)), (27597/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769828911320559/154742504910672534362390528), (1631029459093/154742504910672534362390528)), (220799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774138579666291/4835703278458516698824704), (1528531743649/9671406556917033397649408)), (12939/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257672349708041/604462909807314587353088), (668453581227/302231454903657293676544)), (181169/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885978749937241/75557863725914323419136), (542857057755/18889465931478580854784)), (294445/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81011258467151/295147905179352825856), (813828278907/2361183241434822606848)), (110437/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202447514172351/73786976294838206464), (2236542554967/590295810358705651712)), (151883/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455285301545893/18446744073709551616), (2793452190901/73786976294838206464)), (379803/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820033974825333/9223372036854775808), (784893977001/2305843009213693952)), (427411/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591285185451805/1152921504606846976), (3135758065579/1152921504606846976)), (213789/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192220711240957/144115188075855872), (342437412397/18014398509481984)), (187159/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488103394828009/36028797018963968), (4100686071143/36028797018963968)), (561853/36028797018963968), by norm_num⟩
  | 3 => ⟨((742425389383369/4503599627370496), (1277726638389/2251799813685248)), (702977/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219166027134825/4503599627370496), (5088547847163/2251799813685248)), (351985/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203009785467827/2251799813685248), (7577161775411/1125899906842624)), (2116905/2251799813685248), by norm_num⟩
  | 0 => ⟨((269357520622519/281474976710656), (29866197334009/2251799813685248)), (1063485/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269357520622519/281474976710656), (29866197334009/2251799813685248)), (4056873323680686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1030848815392081/1125899906842624), (28580461959079/1125899906842624)), (2063615/562949953421312), by norm_num⟩
  | 2 => ⟨((943096656226905/1125899906842624), (6541908204899/140737488355328)), (15534271/2251799813685248), by norm_num⟩
  | 3 => ⟨((787540986164043/1125899906842624), (175352049421451/2251799813685248)), (6867089/562949953421312), by norm_num⟩
  | 4 => ⟨((68004903883607/140737488355328), (122654709435515/1125899906842624)), (1334531/70368744177664), by norm_num⟩
  | 5 => ⟨((499039933279877/2251799813685248), (474137876041933/4503599627370496)), (12643735/562949953421312), by norm_num⟩
  | 6 => ⟨((685102369976659/18014398509481984), (840620849464205/18014398509481984)), (66131391/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1355505615/16777216)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-85700449/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((524226414538293/9007199254740992), (-51318784126337/18014398509481984)), (137312629/18014398509481984), by norm_num⟩
  | 1 => ⟨((-411931215/2147483648), (40325723/4294967296)), (109/4294967296), by norm_num⟩
  | 2 => ⟨((1357658085/4294967296), (-33226751/2147483648)), (91/2147483648), by norm_num⟩
  | 3 => ⟨((-93221241/268435456), (36503317/2147483648)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((1228968011/4294967296), (-60154489/4294967296)), (167/4294967296), by norm_num⟩
  | 5 => ⟨((-1620191231/8589934592), (79303753/8589934592)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((444990499/4294967296), (-43562039/8589934592)), (123/8589934592), by norm_num⟩
  | 7 => ⟨((-419033169/8589934592), (10255241/4294967296)), (233/34359738368), by norm_num⟩
  | 8 => ⟨((690532483/34359738368), (-67599203/68719476736)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((-2023006591/274877906944), (24755105/68719476736)), (143/137438953472), by norm_num⟩
  | 10 => ⟨((1333499941/549755813888), (-32635515/274877906944)), (95/274877906944), by norm_num⟩
  | 11 => ⟨((-399545297/549755813888), (9778303/274877906944)), (115/1099511627776), by norm_num⟩
  | 12 => ⟨((1755781493/8796093022208), (-85940511/8796093022208)), (255/8796093022208), by norm_num⟩
  | 13 => ⟨((-890272211/17592186044416), (43576293/17592186044416)), (261/35184372088832), by norm_num⟩
  | 14 => ⟨((209585141/17592186044416), (-82068773/140737488355328)), (31/17592186044416), by norm_num⟩
  | 15 => ⟨((-1473617993/562949953421312), (36064705/281474976710656)), (219/562949953421312), by norm_num⟩
  | 16 => ⟨((1214201127/2251799813685248), (-14857923/562949953421312)), (91/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-31854145055/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111099115184459/39614081257132168796771975168), (-75299881687/633825300114114700748351602688)), (184415/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888411390952917/39614081257132168796771975168), (-21172933145/9903520314283042199192993792)), (207469/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051867481613/1237940039285380274899124224), (-89958892385/2475880078570760549798248448)), (220437/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769770461642903/154742504910672534362390528), (-2810299261/4835703278458516698824704)), (110219/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548222470516459/9671406556917033397649408), (-84277843065/9671406556917033397649408)), (103331/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257624604656091/604462909807314587353088), (-73711993137/604462909807314587353088)), (180831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885901365893679/75557863725914323419136), (-59861836013/37778931862957161709568)), (293853/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648061136849433/2361183241434822606848), (-44870879551/2361183241434822606848)), (220393/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404875209869923/147573952589676412928), (-61656056275/295147905179352825856)), (75761/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821042542216637/73786976294838206464), (-154016037189/73786976294838206464)), (378811/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909961782928429/4611686018427387904), (-169040597/9007199254740992)), (426171/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591175509880933/1152921504606846976), (-172884740599/1152921504606846976)), (213091/576460752303423488), by norm_num⟩
  | 5 => ⟨((9313480999995/1125899906842624), (-151035066915/144115188075855872)), (186461/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487962320270433/36028797018963968), (-226075320381/36028797018963968)), (279705/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484677293850093/9007199254740992), (-70440222899/2251799813685248)), (699311/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109413791650247/2251799813685248), (-280514955733/2251799813685248)), (699387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101261632265611/1125899906842624), (-835342767539/2251799813685248)), (2098567/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153970687364149/2251799813685248), (-51438809881/70368744177664)), (4198891/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153970687364149/2251799813685248), (-51438809881/70368744177664)), (16017498024947356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060390530442821/2251799813685248), (-1574529856563/1125899906842624)), (8039081/2251799813685248), by norm_num⟩
  | 2 => ⟨((1885247167870473/2251799813685248), (-5762761656957/2251799813685248)), (14733959/2251799813685248), by norm_num⟩
  | 3 => ⟨((394586993584159/562949953421312), (-4824687357581/1125899906842624)), (6186621/562949953421312), by norm_num⟩
  | 4 => ⟨((1106265842336715/2251799813685248), (-27054040848091/4503599627370496)), (69806119/4503599627370496), by norm_num⟩
  | 5 => ⟨((67925728022245/281474976710656), (-53164515079063/9007199254740992)), (34713741/2251799813685248), by norm_num⟩
  | 6 => ⟨((524226414538293/9007199254740992), (-51318784126337/18014398509481984)), (137312629/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-85700449/1048576)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile031Terms3
