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
namespace Reinmann.XiBand97.Tile058Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨58,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78877/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78877/2560))
  have he : value ((69/80), (78877/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2862621597/1073741824), (-51131114973/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((342915170466939/9007199254740992), (-1048050968142979/18014398509481984)), (1258633/4503599627370496), by norm_num⟩
  | 1 => ⟨((-32347575373/274877906944), (24715957915/137438953472)), (239/274877906944), by norm_num⟩
  | 2 => ⟨((49993864371/274877906944), (-76398075191/274877906944)), (93/68719476736), by norm_num⟩
  | 3 => ⟨((-51511052393/274877906944), (39358282295/137438953472)), (385/274877906944), by norm_num⟩
  | 4 => ⟨((39805712441/274877906944), (-60829060733/274877906944)), (299/274877906944), by norm_num⟩
  | 5 => ⟨((-49216458817/549755813888), (37605041825/274877906944)), (93/137438953472), by norm_num⟩
  | 6 => ⟨((6338756817/137438953472), (-38746260247/549755813888)), (193/549755813888), by norm_num⟩
  | 7 => ⟨((-22392418769/1099511627776), (4277369119/137438953472)), (343/2199023255552), by norm_num⟩
  | 8 => ⟨((8651989631/1099511627776), (-26443059071/2199023255552)), (267/4398046511104), by norm_num⟩
  | 9 => ⟨((-47544297343/17592186044416), (9081846465/2199023255552)), (369/17592186044416), by norm_num⟩
  | 10 => ⟨((29392288301/35184372088832), (-44915796765/35184372088832)), (115/17592186044416), by norm_num⟩
  | 11 => ⟨((-8259346449/35184372088832), (50486048955/140737488355328)), (261/140737488355328), by norm_num⟩
  | 12 => ⟨((8509996837/140737488355328), (-52018173541/562949953421312)), (135/281474976710656), by norm_num⟩
  | 13 => ⟨((-16187545539/1125899906842624), (49473963927/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 14 => ⟨((14296111565/4503599627370496), (-43693177953/9007199254740992)), (231/9007199254740992), by norm_num⟩
  | 15 => ⟨((-47135880283/72057594037927936), (72030649587/72057594037927936)), (383/72057594037927936), by norm_num⟩
  | 16 => ⟨((18212375879/144115188075855872), (-27831224477/144115188075855872)), (149/144115188075855872), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (-645667908135/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777856586432137/633825300114114700748351602688), (-190842149381/79228162514264337593543950336)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944357918399291/19807040628566084398385987584), (-1717184138355/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472106756505965/618970019642690137449562112), (-1824012146303/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55315423356265/4835703278458516698824704), (-1823454415073/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548525145414591/9671406556917033397649408), (-854448077537/4835703278458516698824704)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314472306836071/151115727451828646838272), (-1494692035897/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886330969620211/75557863725914323419136), (-2427764921887/75557863725914323419136)), (4603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81027757480753/295147905179352825856), (-1819853309887/4722366482869645213696)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619942798521371/590295810358705651712), (-2500722462391/590295810358705651712)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910797061637967/36893488147419103232), (-3123541123381/73786976294838206464)), (5937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820542903115523/9223372036854775808), (-3510739004401/9223372036854775808)), (3341/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591793360414641/1152921504606846976), (-1753343721593/576460752303423488)), (6685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192664518173639/144115188075855872), (-1531899766551/72057594037927936)), (1463/36028797018963968), by norm_num⟩
  | 4 => ⟨((744383708117995/18014398509481984), (-286663149149/2251799813685248)), (549/2251799813685248), by norm_num⟩
  | 3 => ⟨((371419464316893/2251799813685248), (-5717391181925/9007199254740992)), (687/562949953421312), by norm_num⟩
  | 2 => ⟨((277601421148691/562949953421312), (-11387301866961/4503599627370496)), (11009/2251799813685248), by norm_num⟩
  | 1 => ⟨((551363966318393/562949953421312), (-8481361230965/1125899906842624)), (33113/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079832606757731/1125899906842624), (-33455338870851/2251799813685248)), (33287/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079832606757731/1125899906842624), (-33455338870851/2251799813685248)), (126979832175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2070803339813053/2251799813685248), (-16043240417429/562949953421312)), (129679/2251799813685248), by norm_num⟩
  | 2 => ⟨((951263135633747/1125899906842624), (-29507415033901/562949953421312)), (245903/2251799813685248), by norm_num⟩
  | 3 => ⟨((1601241455957977/2251799813685248), (-49861121719621/562949953421312)), (220651/1125899906842624), by norm_num⟩
  | 4 => ⟨((1120968250193233/2251799813685248), (-283647577028119/2251799813685248)), (176447/562949953421312), by norm_num⟩
  | 5 => ⟨((2040232340689/8796093022208), (-141202573230697/1125899906842624)), (440253/1125899906842624), by norm_num⟩
  | 6 => ⟨((342915170466939/9007199254740992), (-1048050968142979/18014398509481984)), (1258633/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-51131114973/536870912)), (1/536870912), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1451894239/536870912), (-51866422953/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-856396657209387/18014398509481984), (-26508450241541/562949953421312)), (1730509/4503599627370496), by norm_num⟩
  | 1 => ⟨((10243327199/68719476736), (2536532361/17179869184)), (333/274877906944), by norm_num⟩
  | 2 => ⟨((-64235786369/274877906944), (-15906565093/68719476736)), (131/68719476736), by norm_num⟩
  | 3 => ⟨((8392122359/34359738368), (66499923793/274877906944)), (275/137438953472), by norm_num⟩
  | 4 => ⟨((-6578362779/34359738368), (-52127531603/274877906944)), (433/274877906944), by norm_num⟩
  | 5 => ⟨((16501134755/137438953472), (65378229533/549755813888)), (545/549755813888), by norm_num⟩
  | 6 => ⟨((-34492808387/549755813888), (-68331020183/1099511627776)), (143/274877906944), by norm_num⟩
  | 7 => ⟨((61801143537/2199023255552), (61214719587/2199023255552)), (515/2199023255552), by norm_num⟩
  | 8 => ⟨((-48444282025/4398046511104), (-47984599799/4398046511104)), (203/2199023255552), by norm_num⟩
  | 9 => ⟨((67509673815/17592186044416), (66869082277/17592186044416)), (71/2199023255552), by norm_num⟩
  | 10 => ⟨((-42335238353/35184372088832), (-41933524141/35184372088832)), (179/17592186044416), by norm_num⟩
  | 11 => ⟨((48269779995/140737488355328), (47811753599/140737488355328)), (205/70368744177664), by norm_num⟩
  | 12 => ⟨((-50449871993/562949953421312), (-49971158955/562949953421312)), (215/281474976710656), by norm_num⟩
  | 13 => ⟨((48672394409/2251799813685248), (48210547651/2251799813685248)), (417/2251799813685248), by norm_num⟩
  | 14 => ⟨((-10900857939/2251799813685248), (-21594841901/4503599627370496)), (375/9007199254740992), by norm_num⟩
  | 15 => ⟨((9114553871/9007199254740992), (18056133833/18014398509481984)), (315/36028797018963968), by norm_num⟩
  | 16 => ⟨((-57157261887/288230376151711744), (-14153725799/72057594037927936)), (31/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (-3075415974281/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777791702013599/633825300114114700748351602688), (-3635812243849/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888642538544767/39614081257132168796771975168), (-4089321512603/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888348738053387/2475880078570760549798248448), (-135740763357/77371252455336267181195264)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885007400165155/77371252455336267181195264), (-4342355212981/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774225416329313/4835703278458516698824704), (-2034762458073/4835703278458516698824704)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628911858386559/302231454903657293676544), (-1779700852545/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886223602980143/75557863725914323419136), (-5781342713481/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648181398869137/2361183241434822606848), (-4333658670987/4722366482869645213696)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619829687612737/590295810358705651712), (-2977483284915/295147905179352825856)), (4767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910725399029327/36893488147419103232), (-232437204307/2305843009213693952)), (5963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910189502362189/4611686018427387904), (-4179941602731/4611686018427387904)), (6713/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591626148027041/1152921504606846976), (-8350071494651/1152921504606846976)), (105/18014398509481984), by norm_num⟩
  | 5 => ⟨((596257244970395/72057594037927936), (-7295286032991/144115188075855872)), (23/562949953421312), by norm_num⟩
  | 4 => ⟨((1488534966176187/36028797018963968), (-10920905109649/36028797018963968)), (8847/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485374391974283/9007199254740992), (-13612654948739/9007199254740992)), (5543/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220165972807879/4503599627370496), (-27110142203951/4503599627370496)), (22253/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102196225578235/1125899906842624), (-20189104412581/1125899906842624)), (2099/140737488355328), by norm_num⟩
  | 0 => ⟨((134822634392445/140737488355328), (-79613880836117/2251799813685248)), (67991/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((134822634392445/140737488355328), (-79613880836117/2251799813685248)), (259365090377043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063687075704057/2251799813685248), (-152535806542623/2251799813685248)), (33769/562949953421312), by norm_num⟩
  | 2 => ⟨((940478178479499/1125899906842624), (-279586285273675/2251799813685248)), (265885/2251799813685248), by norm_num⟩
  | 3 => ⟨((1536472427453065/2251799813685248), (-233541897200627/1125899906842624)), (127555/562949953421312), by norm_num⟩
  | 4 => ⟨((951496769965861/2251799813685248), (-637411342736701/2251799813685248)), (907945/2251799813685248), by norm_num⟩
  | 5 => ⟨((443248001330387/4503599627370496), (-538675622999539/2251799813685248)), (2562647/4503599627370496), by norm_num⟩
  | 6 => ⟨((-856396657209387/18014398509481984), (-26508450241541/562949953421312)), (1730509/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-51866422953/536870912)), (1/536870912), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-105140863149/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1002135129655175/18014398509481984), (294046675304267/9007199254740992)), (3305781/9007199254740992), by norm_num⟩
  | 1 => ⟨((48596792409/274877906944), (-14259279827/137438953472)), (161/137438953472), by norm_num⟩
  | 2 => ⟨((-77221611129/274877906944), (5664594859/34359738368)), (257/137438953472), by norm_num⟩
  | 3 => ⟨((81804812345/274877906944), (-48006366371/274877906944)), (547/274877906944), by norm_num⟩
  | 4 => ⟨((-64995024303/274877906944), (9535426033/68719476736)), (437/274877906944), by norm_num⟩
  | 5 => ⟨((10327884297/68719476736), (-48486555565/549755813888)), (557/549755813888), by norm_num⟩
  | 6 => ⟨((-21881714833/274877906944), (3210268409/68719476736)), (297/549755813888), by norm_num⟩
  | 7 => ⟨((79475734445/2199023255552), (-23319784717/1099511627776)), (541/2199023255552), by norm_num⟩
  | 8 => ⟨((-7893067571/549755813888), (37055765571/4398046511104)), (27/274877906944), by norm_num⟩
  | 9 => ⟨((44594833115/8796093022208), (-6542512095/2199023255552)), (153/4398046511104), by norm_num⟩
  | 10 => ⟨((-28344956039/17592186044416), (16633964499/17592186044416)), (391/35184372088832), by norm_num⟩
  | 11 => ⟨((65514033535/140737488355328), (-19223139851/70368744177664)), (227/70368744177664), by norm_num⟩
  | 12 => ⟨((-2168824221/17592186044416), (20364057745/281474976710656)), (483/562949953421312), by norm_num⟩
  | 13 => ⟨((4241624691/140737488355328), (-39826505673/2251799813685248)), (237/1125899906842624), by norm_num⟩
  | 14 => ⟨((-481432557/70368744177664), (36163079687/9007199254740992)), (433/9007199254740992), by norm_num⟩
  | 15 => ⟨((13056158565/9007199254740992), (-30647523711/36028797018963968)), (369/36028797018963968), by norm_num⟩
  | 16 => ⟨((-41493174737/144115188075855872), (12174935015/72057594037927936)), (147/72057594037927936), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (1700497993771/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888866797091511/316912650057057350374175801344), (2010237487787/316912650057057350374175801344)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888577096770497/39614081257132168796771975168), (282621710069/2475880078570760549798248448)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888279109216709/2475880078570760549798248448), (4803224064639/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884972531285455/77371252455336267181195264), (4801711352829/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548385337892903/9671406556917033397649408), (4499997610007/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257766293365199/604462909807314587353088), (3935891657057/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943065036837525/37778931862957161709568), (3196406675141/37778931862957161709568)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648146230899017/2361183241434822606848), (2395988436865/2361183241434822606848)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619732669142905/590295810358705651712), (3292345733969/295147905179352825856)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821329066035509/73786976294838206464), (2056113234945/18446744073709551616)), (5967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820241426609611/9223372036854775808), (2310924977189/2305843009213693952)), (6719/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591487785095561/1152921504606846976), (9232696876415/1152921504606846976)), (6727/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192392542434855/144115188075855872), (2016560941743/36028797018963968)), (5895/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488350292466101/36028797018963968), (3018666168045/9007199254740992)), (8859/36028797018963968), by norm_num⟩
  | 3 => ⟨((371285124931741/2251799813685248), (15050173906557/9007199254740992)), (11103/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219689104508825/4503599627370496), (14985578011927/2251799813685248)), (2787/562949953421312), by norm_num⟩
  | 1 => ⟨((275456833894783/281474976710656), (11158682660141/562949953421312)), (16835/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077799032431223/1125899906842624), (87987300399083/2251799813685248)), (34125/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077799032431223/1125899906842624), (87987300399083/2251799813685248)), (130176548484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060068228096769/2251799813685248), (168456585989615/2251799813685248)), (136003/2251799813685248), by norm_num⟩
  | 2 => ⟨((1872059610908077/2251799813685248), (308226387178629/2251799813685248)), (67299/562949953421312), by norm_num⟩
  | 3 => ⟨((189271025576871/281474976710656), (128123771692851/562949953421312)), (521295/2251799813685248), by norm_num⟩
  | 4 => ⟨((225381284513447/562949953421312), (689229798043777/2251799813685248)), (58647/140737488355328), by norm_num⟩
  | 5 => ⟨((299946609799871/4503599627370496), (68984594573629/281474976710656)), (662887/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1002135129655175/18014398509481984), (294046675304267/9007199254740992)), (3305781/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-105140863149/1073741824)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-6655712125/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((242248684115905/18014398509481984), (1095281301368817/18014398509481984)), (331237/1125899906842624), by norm_num⟩
  | 1 => ⟨((-23796644071/549755813888), (-107591995313/549755813888)), (523/549755813888), by norm_num⟩
  | 2 => ⟨((9574805289/137438953472), (43290659083/137438953472)), (423/274877906944), by norm_num⟩
  | 3 => ⟨((-20546739515/274877906944), (-23224542661/68719476736)), (57/34359738368), by norm_num⟩
  | 4 => ⟨((2066793847/34359738368), (74756918915/274877906944)), (369/274877906944), by norm_num⟩
  | 5 => ⟨((-21288808797/549755813888), (-96253295615/549755813888)), (477/549755813888), by norm_num⟩
  | 6 => ⟨((22842010659/1099511627776), (103275802107/1099511627776)), (257/549755813888), by norm_num⟩
  | 7 => ⟨((-21007313115/2199023255552), (-94980566485/2199023255552)), (237/1099511627776), by norm_num⟩
  | 8 => ⟨((16904983083/4398046511104), (76432662323/4398046511104)), (383/4398046511104), by norm_num⟩
  | 9 => ⟨((-24184462829/17592186044416), (-13668180499/2199023255552)), (275/8796093022208), by norm_num⟩
  | 10 => ⟨((3892339137/8796093022208), (70393881245/35184372088832)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((-9111968255/70368744177664), (-10299507389/17592186044416)), (419/140737488355328), by norm_num⟩
  | 12 => ⟨((19553529555/562949953421312), (44203780457/281474976710656)), (113/140737488355328), by norm_num⟩
  | 13 => ⟨((-19366271869/2251799813685248), (-43780455471/1125899906842624)), (225/1125899906842624), by norm_num⟩
  | 14 => ⟨((17810749811/9007199254740992), (80527914125/9007199254740992)), (13/281474976710656), by norm_num⟩
  | 15 => ⟨((-1911019733/4503599627370496), (-69122494935/36028797018963968)), (359/36028797018963968), by norm_num⟩
  | 16 => ⟨((12302670439/144115188075855872), (111248363951/288230376151711744)), (145/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (1762597275991/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222210715087527/79228162514264337593543950336), (1041763358919/316912650057057350374175801344)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888523599258579/39614081257132168796771975168), (2343406001929/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944111375469579/1237940039285380274899124224), (2489163894581/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884944623431973/77371252455336267181195264), (2488371169613/154742504910672534362390528)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548333586674919/9671406556917033397649408), (2332006030561/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628860793261697/302231454903657293676544), (509915926593/151115727451828646838272)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943029251469049/37778931862957161709568), (1656438182765/37778931862957161709568)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648119862879701/2361183241434822606848), (1241639024095/2361183241434822606848)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1619661685742411/590295810358705651712), (3412267548263/590295810358705651712)), (2377/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910621313028513/36893488147419103232), (2130988680693/36893488147419103232)), (743/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455036830841571/2305843009213693952), (4790112740917/9223372036854775808)), (3345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795698800002347/576460752303423488), (1196088568969/288230376151711744)), (3347/576460752303423488), by norm_num⟩
  | 5 => ⟨((298079506507057/36028797018963968), (1044960083641/36028797018963968)), (2931/72057594037927936), by norm_num⟩
  | 4 => ⟨((186030909759501/4503599627370496), (6256842700905/36028797018963968)), (8801/36028797018963968), by norm_num⟩
  | 3 => ⟨((742513496406533/4503599627370496), (7798495550783/9007199254740992)), (11017/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219507597456007/4503599627370496), (15529510544711/4503599627370496)), (345/70368744177664), by norm_num⟩
  | 1 => ⟨((2203495213539271/2251799813685248), (23126237908027/2251799813685248)), (33237/2251799813685248), by norm_num⟩
  | 0 => ⟨((269465575777157/281474976710656), (45584391235419/2251799813685248)), (16737/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((269465575777157/281474976710656), (45584391235419/2251799813685248)), (63846590282249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((515706437678869/562949953421312), (87278978573859/2251799813685248)), (130895/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886327741879677/2251799813685248), (79954409536809/1125899906842624)), (15623/140737488355328), by norm_num⟩
  | 3 => ⟨((784408431401787/1125899906842624), (133955265364431/1125899906842624)), (454299/2251799813685248), by norm_num⟩
  | 4 => ⟨((530555665299343/1125899906842624), (186651831026771/1125899906842624)), (370559/1125899906842624), by norm_num⟩
  | 5 => ⟨((876278278225521/4503599627370496), (175911172543673/1125899906842624)), (944197/2251799813685248), by norm_num⟩
  | 6 => ⟨((242248684115905/18014398509481984), (1095281301368817/18014398509481984)), (331237/1125899906842624), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-6655712125/67108864)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-3017330773/1073741824), (-53894474499/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1073108657265451/18014398509481984), (78176776607985/9007199254740992)), (2423703/18014398509481984), by norm_num⟩
  | 1 => ⟨((-53349176043/274877906944), (-7773055579/274877906944)), (243/549755813888), by norm_num⟩
  | 2 => ⟨((43454191443/137438953472), (791417671/17179869184)), (25/34359738368), by norm_num⟩
  | 3 => ⟨((-94385300469/274877906944), (-429752529/8589934592)), (219/274877906944), by norm_num⟩
  | 4 => ⟨((38439552587/137438953472), (1400175227/34359738368)), (181/274877906944), by norm_num⟩
  | 5 => ⟨((-100191818565/549755813888), (-14598099391/549755813888)), (119/274877906944), by norm_num⟩
  | 6 => ⟨((27202884767/274877906944), (247718839/17179869184)), (65/274877906944), by norm_num⟩
  | 7 => ⟨((-50645499819/1099511627776), (-14758251735/2199023255552)), (61/549755813888), by norm_num⟩
  | 8 => ⟨((82503963813/4398046511104), (12020952221/4398046511104)), (201/4398046511104), by norm_num⟩
  | 9 => ⟨((-119469279499/17592186044416), (-2175856823/2199023255552)), (147/8796093022208), by norm_num⟩
  | 10 => ⟨((77848489187/35184372088832), (2835660633/8796093022208)), (193/35184372088832), by norm_num⟩
  | 11 => ⟨((-92231961131/140737488355328), (-13438336133/140737488355328)), (115/70368744177664), by norm_num⟩
  | 12 => ⟨((12520859719/70368744177664), (14594465477/562949953421312)), (63/140737488355328), by norm_num⟩
  | 13 => ⟨((-25104104433/562949953421312), (-14630823829/2251799813685248)), (255/2251799813685248), by norm_num⟩
  | 14 => ⟨((93476109421/9007199254740992), (13619610419/9007199254740992)), (239/9007199254740992), by norm_num⟩
  | 15 => ⟨((-81214450265/36028797018963968), (-2958267037/9007199254740992)), (105/18014398509481984), by norm_num⟩
  | 16 => ⟨((66151129811/144115188075855872), (1204789949/18014398509481984)), (173/144115188075855872), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (94233153591/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222204492112891/79228162514264337593543950336), (222769343827/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472116932927081/9903520314283042199192993792), (62638779063/9903520314283042199192993792)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472040894508469/618970019642690137449562112), (266138555679/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884915141686141/77371252455336267181195264), (266052816279/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387069632680829/2417851639229258349412352), (124666728105/4835703278458516698824704)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628836817342333/302231454903657293676544), (109037879551/302231454903657293676544)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885980997242323/75557863725914323419136), (177101274325/37778931862957161709568)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296181960094019/4722366482869645213696), (265502764907/4722366482869645213696)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619582848006743/590295810358705651712), (364824113411/590295810358705651712)), (4737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910572481279757/36893488147419103232), (113916791251/18446744073709551616)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455009666173427/2305843009213693952), (512126963941/9223372036854775808)), (3331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795645226929859/576460752303423488), (511504461783/1152921504606846976)), (3331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192225970044255/144115188075855872), (446867110365/144115188075855872)), (2915/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488112576160437/36028797018963968), (334452313591/18014398509481984)), (4373/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484864507714365/9007199254740992), (208423360249/2251799813685248)), (10935/9007199254740992), by norm_num⟩
  | 2 => ⟨((554800049816563/1125899906842624), (1660097694059/4503599627370496)), (21873/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101538840405173/1125899906842624), (309000408141/281474976710656)), (4103/281474976710656), by norm_num⟩
  | 0 => ⟨((538765404769311/562949953421312), (1217977399567/562949953421312)), (32853/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538765404769311/562949953421312), (1217977399567/562949953421312)), (125324253562545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062468794202443/2251799813685248), (9325220939297/2251799813685248)), (31513/562949953421312), by norm_num⟩
  | 2 => ⟨((944509041492417/1125899906842624), (17082315283495/2251799813685248)), (14497/140737488355328), by norm_num⟩
  | 3 => ⟨((1584553604926709/2251799813685248), (1791278373951/140737488355328)), (196343/1125899906842624), by norm_num⟩
  | 4 => ⟨((278664725213285/562949953421312), (40335757558855/2251799813685248)), (562651/2251799813685248), by norm_num⟩
  | 5 => ⟨((1102085082672207/4503599627370496), (79866089183213/4503599627370496)), (577191/2251799813685248), by norm_num⟩
  | 6 => ⟨((1073108657265451/18014398509481984), (78176776607985/9007199254740992)), (2423703/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-53894474499/536870912)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-3052282179/1073741824), (-109037527805/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((275519322824347/9007199254740992), (-893444658189439/18014398509481984)), (2144483/9007199254740992), by norm_num⟩
  | 1 => ⟨((-27711997725/274877906944), (1404117509/8589934592)), (109/137438953472), by norm_num⟩
  | 2 => ⟨((45667111867/274877906944), (-37021938003/137438953472)), (361/274877906944), by norm_num⟩
  | 3 => ⟨((-50170450285/274877906944), (81345512081/274877906944)), (399/274877906944), by norm_num⟩
  | 4 => ⟨((41338404909/274877906944), (-4189086525/17179869184)), (331/274877906944), by norm_num⟩
  | 5 => ⟨((-851528993/8589934592), (44180946573/274877906944)), (55/68719476736), by norm_num⟩
  | 6 => ⟨((7484001727/137438953472), (-24268865415/274877906944)), (243/549755813888), by norm_num⟩
  | 7 => ⟨((-14094885027/549755813888), (45706412189/1099511627776)), (115/549755813888), by norm_num⟩
  | 8 => ⟨((23227220847/2199023255552), (-75320439153/4398046511104)), (381/4398046511104), by norm_num⟩
  | 9 => ⟨((-4252951709/1099511627776), (27582653347/4398046511104)), (281/8796093022208), by norm_num⟩
  | 10 => ⟨((22427256051/17592186044416), (-72726340611/35184372088832)), (93/8796093022208), by norm_num⟩
  | 11 => ⟨((-26878755381/70368744177664), (43580755367/70368744177664)), (225/70368744177664), by norm_num⟩
  | 12 => ⟨((14764665483/140737488355328), (-11969588349/70368744177664)), (249/281474976710656), by norm_num⟩
  | 13 => ⟨((-29945802347/1125899906842624), (48553612987/1125899906842624)), (127/562949953421312), by norm_num⟩
  | 14 => ⟨((14099497051/2251799813685248), (-45721367903/4503599627370496)), (241/4503599627370496), by norm_num⟩
  | 15 => ⟨((-24783809159/18014398509481984), (80368090613/36028797018963968)), (425/36028797018963968), by norm_num⟩
  | 16 => ⟨((40841695953/144115188075855872), (-66220028973/144115188075855872)), (11/4503599627370496), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (-663124557691/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222198065915297/79228162514264337593543950336), (-391889349499/158456325028528675187087900672)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888409839600447/39614081257132168796771975168), (-1763071209147/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888101990317263/2475880078570760549798248448), (-1872720225295/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769768608762903/154742504910672534362390528), (-468027436603/38685626227668133590597632)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548220618542831/9671406556917033397649408), (-1754454523185/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257622869393251/604462909807314587353088), (-191812455913/75557863725914323419136)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885898331107277/75557863725914323419136), (-2492347458255/75557863725914323419136)), (4603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296119809736889/4722366482869645213696), (-1868198578065/4722366482869645213696)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619497146687469/590295810358705651712), (-2567048476901/590295810358705651712)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821037469742245/73786976294838206464), (-3206225855639/73786976294838206464)), (2969/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819917232927483/9223372036854775808), (-3603453497435/9223372036854775808)), (3341/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198896049482341/144115188075855872), (-1799510198213/576460752303423488)), (6685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((9313425524299/1125899906842624), (-3144162662539/144115188075855872)), (5853/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487949923206449/36028797018963968), (-588287654373/4503599627370496)), (4393/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484658757094721/9007199254740992), (-2932758133393/4503599627370496)), (5497/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218781446712761/4503599627370496), (-11679109551607/4503599627370496)), (11011/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101215802352299/1125899906842624), (-2173675968603/281474976710656)), (33123/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076849378423903/1125899906842624), (-34265081717351/2251799813685248)), (66605/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076849378423903/1125899906842624), (-34265081717351/2251799813685248)), (254077919966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32177345783859/35184372088832), (-16386151080005/562949953421312)), (129435/2251799813685248), by norm_num⟩
  | 2 => ⟨((940720138112477/1125899906842624), (-119885691985445/2251799813685248)), (244281/2251799813685248), by norm_num⟩
  | 3 => ⟨((1565612055047173/2251799813685248), (-200335543216315/2251799813685248)), (434219/2251799813685248), by norm_num⟩
  | 4 => ⟨((1070702094555845/2251799813685248), (-278575155400317/2251799813685248)), (681063/2251799813685248), by norm_num⟩
  | 5 => ⟨((118660510093345/562949953421312), (-132458933767383/1125899906842624)), (1632371/4503599627370496), by norm_num⟩
  | 6 => ⟨((275519322824347/9007199254740992), (-893444658189439/18014398509481984)), (2144483/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-109037527805/1073741824)), (1/536870912), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile058Terms3
