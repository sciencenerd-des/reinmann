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
namespace Reinmann.XiBand97.Tile012Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25387/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25387/1280))
  have he : value ((69/80), (25387/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-922585791/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((470362726069823/2251799813685248), (-286422833669483/562949953421312)), (21089229/1125899906842624), by norm_num⟩
  | 1 => ⟨((-310927007/2147483648), (1514687955/4294967296)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((431036357/8589934592), (-1049901685/8589934592)), (43/8589934592), by norm_num⟩
  | 3 => ⟨((-398362181/34359738368), (485157595/17179869184)), (21/17179869184), by norm_num⟩
  | 4 => ⟨((552247245/274877906944), (-336285619/68719476736)), (61/274877906944), by norm_num⟩
  | 5 => ⟨((-612461793/2199023255552), (186476343/274877906944)), (35/1099511627776), by norm_num⟩
  | 6 => ⟨((566034887/17592186044416), (-689362941/8796093022208)), (67/17592186044416), by norm_num⟩
  | 7 => ⟨((-448394841/140737488355328), (1092182809/140737488355328)), (55/140737488355328), by norm_num⟩
  | 8 => ⟨((77700905/281474976710656), (-757043435/1125899906842624)), (79/2251799813685248), by norm_num⟩
  | 9 => ⟨((-382991383/18014398509481984), (233218899/4503599627370496)), (25/9007199254740992), by norm_num⟩
  | 10 => ⟨((106187759/72057594037927936), (-1034592143/288230376151711744)), (57/288230376151711744), by norm_num⟩
  | 11 => ⟨((-428239975/4611686018427387904), (1043090367/4611686018427387904)), (15/1152921504606846976), by norm_num⟩
  | 12 => ⟨((395777775/73786976294838206464), (-241005049/18446744073709551616)), (57/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-337639691/1180591620717411303424), (205602425/295147905179352825856)), (25/590295810358705651712), by norm_num⟩
  | 14 => ⟨((534934857/37778931862957161709568), (-651486817/18889465931478580854784)), (81/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-395507827/604462909807314587353088), (240840667/151115727451828646838272)), (31/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((274145135/9671406556917033397649408), (-667752117/9671406556917033397649408)), (89/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-769341310781/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890523324484689/316912650057057350374175801344), (-1825388962393/633825300114114700748351602688)), (2887/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((473076026072935/9903520314283042199192993792), (-513362454489/9903520314283042199192993792)), (12993/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473059721510577/618970019642690137449562112), (-1090828515353/1237940039285380274899124224)), (6903/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886952324546743/77371252455336267181195264), (-545376736921/38685626227668133590597632)), (863/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1552097247684923/9671406556917033397649408), (-2045003295931/9671406556917033397649408)), (25895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630507005718529/302231454903657293676544), (-1789218411567/604462909807314587353088)), (11331/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59106476063295/2361183241434822606848), (-2907180897807/75557863725914323419136)), (36833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325062499334091/1180591620717411303424), (-2129027363/4611686018427387904)), (27631/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812586867449917/295147905179352825856), (-2997245320691/590295810358705651712)), (38003/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828129576881525/73786976294838206464), (-3745918807631/73786976294838206464)), (47519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456972716797179/2305843009213693952), (-4213281569627/9223372036854775808)), (53481/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599135800885305/1152921504606846976), (-4212185126855/1152921504606846976)), (13377/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199082943572383/144115188075855872), (-921107094007/36028797018963968)), (46851/144115188075855872), by norm_num⟩
  | 4 => ⟨((374595661100969/9007199254740992), (-5524175065413/36028797018963968)), (70337/36028797018963968), by norm_num⟩
  | 3 => ⟨((374418799451469/2251799813685248), (-6900900084705/9007199254740992)), (88029/9007199254740992), by norm_num⟩
  | 2 => ⟨((561185264257295/1125899906842624), (-6894420721661/2251799813685248)), (88191/2251799813685248), by norm_num⟩
  | 1 => ⟨((560297057861871/562949953421312), (-10325428355375/1125899906842624)), (132691/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115241593417593/1125899906842624), (-5146505029427/281474976710656)), (133501/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115241593417593/1125899906842624), (-5146505029427/281474976710656)), (509265901805686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1104307780743175/1125899906842624), (-40782285776329/1125899906842624)), (269357/562949953421312), by norm_num⟩
  | 2 => ⟨((270413131836905/281474976710656), (-40000176947867/562949953421312)), (1095793/1125899906842624), by norm_num⟩
  | 3 => ⟨((516729829278107/562949953421312), (-76856374580125/562949953421312)), (2261181/1125899906842624), by norm_num⟩
  | 4 => ⟨((927623539411759/1125899906842624), (-70546202329997/281474976710656)), (2384237/562949953421312), by norm_num⟩
  | 5 => ⟨((693540482163827/1125899906842624), (-464981425078363/1125899906842624)), (640481/70368744177664), by norm_num⟩
  | 6 => ⟨((470362726069823/2251799813685248), (-286422833669483/562949953421312)), (21089229/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-922585791/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-1462263883/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-855295716245707/2251799813685248), (-349816004661119/4503599627370496)), (146417465/4503599627370496), by norm_num⟩
  | 1 => ⟨((448054497/1073741824), (183254319/2147483648)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-984476353/4294967296), (-201325447/4294967296)), (87/4294967296), by norm_num⟩
  | 3 => ⟨((1442077093/17179869184), (147452407/8589934592)), (65/8589934592), by norm_num⟩
  | 4 => ⟨((-49508863/2147483648), (-323986053/68719476736)), (145/68719476736), by norm_num⟩
  | 5 => ⟨((174051345/34359738368), (284748047/274877906944)), (65/137438953472), by norm_num⟩
  | 6 => ⟨((-127476631/137438953472), (-104275901/549755813888)), (97/1099511627776), by norm_num⟩
  | 7 => ⟨((1280433311/8796093022208), (130924327/4398046511104)), (31/2199023255552), by norm_num⟩
  | 8 => ⟨((-1406699771/70368744177664), (-287670149/70368744177664)), (139/70368744177664), by norm_num⟩
  | 9 => ⟨((686852291/281474976710656), (35115329/70368744177664)), (69/281474976710656), by norm_num⟩
  | 10 => ⟨((-301833747/1125899906842624), (-246900045/4503599627370496)), (31/1125899906842624), by norm_num⟩
  | 11 => ⟨((482324747/18014398509481984), (98635427/18014398509481984)), (101/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1413034385/576460752303423488), (-288965579/576460752303423488)), (75/288230376151711744), by norm_num⟩
  | 13 => ⟨((477654443/2305843009213693952), (195360699/4611686018427387904)), (103/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-1199444665/73786976294838206464), (-122643237/36893488147419103232)), (131/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1405572959/1180591620717411303424), (287439717/1180591620717411303424)), (39/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-772089863/9444732965739290427392), (-315784805/18889465931478580854784)), (87/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-957378500619/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890248580971843/316912650057057350374175801344), (-4540460636031/633825300114114700748351602688)), (11581/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891685424758885/39614081257132168796771975168), (-2553776767733/19807040628566084398385987584)), (52129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945790454584261/1237940039285380274899124224), (-2713123506981/1237940039285380274899124224)), (55403/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773245963789487/154742504910672534362390528), (-5425652051413/154742504910672534362390528)), (27711/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551478977753409/9671406556917033397649408), (-5085916451369/9671406556917033397649408)), (51977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630236136533401/302231454903657293676544), (-4449544324261/604462909807314587353088)), (11375/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890525499428575/75557863725914323419136), (-7229322981559/75557863725914323419136)), (73975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649793731727223/2361183241434822606848), (-5420953534055/4722366482869645213696)), (27757/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624260748405765/590295810358705651712), (-1863030582197/147573952589676412928)), (2387/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1826985342100439/73786976294838206464), (-4656309092557/36893488147419103232)), (95559/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826599478936261/9223372036854775808), (-10473207686471/9223372036854775808)), (107613/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199729907778181/144115188075855872), (-10468844191889/1152921504606846976)), (107749/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197942684567237/144115188075855872), (-9155324548487/144115188075855872)), (94435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496660696876181/36028797018963968), (-6861572820865/18014398509481984)), (17745/4503599627370496), by norm_num⟩
  | 3 => ⟨((186937821486429/1125899906842624), (-17136680942139/9007199254740992)), (44497/2251799813685248), by norm_num⟩
  | 2 => ⟨((560083844482799/1125899906842624), (-17110746382087/2251799813685248)), (89399/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117214580272291/1125899906842624), (-25601081402279/1125899906842624)), (16889/70368744177664), by norm_num⟩
  | 0 => ⟨((1108182967966087/1125899906842624), (-50940806391353/1125899906842624)), (548579/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108182967966087/1125899906842624), (-50940806391353/1125899906842624)), (2092662815574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((544220013380647/562949953421312), (-100278423817733/1125899906842624)), (564767/562949953421312), by norm_num⟩
  | 2 => ⟨((260823791358779/281474976710656), (-48471027326859/281474976710656)), (298139/140737488355328), by norm_num⟩
  | 3 => ⟨((933363390468099/1125899906842624), (-359318537404259/1125899906842624)), (2620847/562949953421312), by norm_num⟩
  | 4 => ⟨((659079375381361/1125899906842624), (-595745263484697/1125899906842624)), (3009079/281474976710656), by norm_num⟩
  | 5 => ⟨((141172769631897/2251799813685248), (-1394949635425385/2251799813685248)), (53658291/2251799813685248), by norm_num⟩
  | 6 => ⟨((-855295716245707/2251799813685248), (-349816004661119/4503599627370496)), (146417465/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1462263883/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-922585791/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-969329097238203/4503599627370496), (-957261824321273/4503599627370496)), (61111595/2251799813685248), by norm_num⟩
  | 1 => ⟨((80095259/268435456), (632785163/2147483648)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-888284847/4294967296), (-877226503/4294967296)), (117/4294967296), by norm_num⟩
  | 3 => ⟨((205237379/2147483648), (202682359/2147483648)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((-284519421/8589934592), (-561954823/17179869184)), (39/8589934592), by norm_num⟩
  | 5 => ⟨((315542135/34359738368), (311613921/34359738368)), (11/8589934592), by norm_num⟩
  | 6 => ⟨((-291622855/137438953472), (-575984829/274877906944)), (83/274877906944), by norm_num⟩
  | 7 => ⟨((115507177/274877906944), (456276869/1099511627776)), (133/2199023255552), by norm_num⟩
  | 8 => ⟨((-640507793/8796093022208), (-632534051/8796093022208)), (47/4398046511104), by norm_num⟩
  | 9 => ⟨((789273193/70368744177664), (24357733/2199023255552)), (59/35184372088832), by norm_num⟩
  | 10 => ⟨((-437665991/281474976710656), (-432217445/281474976710656)), (133/562949953421312), by norm_num⟩
  | 11 => ⟨((441261015/2251799813685248), (217883857/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 12 => ⟨((-815623543/36028797018963968), (-402734883/18014398509481984)), (1/281474976710656), by norm_num⟩
  | 13 => ⟨((43488243/18014398509481984), (343574829/144115188075855872)), (111/288230376151711744), by norm_num⟩
  | 14 => ⟨((-551200055/2305843009213693952), (-8505283/36028797018963968)), (45/1152921504606846976), by norm_num⟩
  | 15 => ⟨((407533615/18446744073709551616), (804920379/36893488147419103232)), (135/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-35310097/18446744073709551616), (-557928291/295147905179352825856)), (3/9223372036854775808), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-769341310781/2535301200456458802993406410752)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890058959691883/316912650057057350374175801344), (-911796155841/158456325028528675187087900672)), (5785/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891259055858615/39614081257132168796771975168), (-2051314873033/19807040628566084398385987584)), (13019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891128230584577/2475880078570760549798248448), (-2179255153677/1237940039285380274899124224)), (3459/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772793665872069/154742504910672534362390528), (-4357909701697/154742504910672534362390528)), (55359/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775527676425137/4835703278458516698824704), (-2042451084033/4835703278458516698824704)), (12979/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157512750699929/75557863725914323419136), (-1786825590889/302231454903657293676544)), (22721/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889924572747213/75557863725914323419136), (-1451496609045/18889465931478580854784)), (73873/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649568715749963/2361183241434822606848), (-4353442604361/4722366482869645213696)), (55431/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623643031648787/590295810358705651712), (-1496070423455/147573952589676412928)), (76259/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913107405711507/36893488147419103232), (-7477799024655/73786976294838206464)), (23847/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456433713025373/2305843009213693952), (-2102253244157/2305843009213693952)), (107399/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596977409383617/1152921504606846976), (-8404623686439/1152921504606846976)), (107509/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37412240074331/4503599627370496), (-7349106909411/144115188075855872)), (47097/72057594037927936), by norm_num⟩
  | 4 => ⟨((373885106860029/9007199254740992), (-11013780584757/36028797018963968)), (141537/36028797018963968), by norm_num⟩
  | 3 => ⟨((747056567365187/4503599627370496), (-13749931327691/9007199254740992)), (88677/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118794581965259/2251799813685248), (-13723980246893/2251799813685248)), (44501/562949953421312), by norm_num⟩
  | 1 => ⟨((557597838617425/562949953421312), (-2565132495595/140737488355328)), (134317/562949953421312), by norm_num⟩
  | 0 => ⟨((1104307780743175/1125899906842624), (-20391142888165/562949953421312)), (543795/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104307780743175/1125899906842624), (-20391142888165/562949953421312)), (2074413303855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((270413131836905/281474976710656), (-10000044236967/140737488355328)), (69133/70368744177664), by norm_num⟩
  | 2 => ⟨((516729829278107/562949953421312), (-76856374580127/562949953421312)), (2282507/1125899906842624), by norm_num⟩
  | 3 => ⟨((463811769705879/562949953421312), (-282184809319995/1125899906842624)), (4813447/1125899906842624), by norm_num⟩
  | 4 => ⟨((346770241081911/562949953421312), (-232490712539187/562949953421312)), (5172173/562949953421312), by norm_num⟩
  | 5 => ⟨((470362726069793/2251799813685248), (-1145691334677951/2251799813685248)), (10644065/562949953421312), by norm_num⟩
  | 6 => ⟨((-969329097238203/4503599627370496), (-957261824321273/4503599627370496)), (61111595/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-922585791/33554432)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-535544467/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((983535642213303/4503599627370496), (-135931303121291/1125899906842624)), (105232613/4503599627370496), by norm_num⟩
  | 1 => ⟨((-754804397/2147483648), (417276369/2147483648)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((1214810813/4294967296), (-83947551/536870912)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((-1303441719/8589934592), (180144495/2147483648)), (73/4294967296), by norm_num⟩
  | 4 => ⟨((262226065/4294967296), (-72482845/2147483648)), (119/17179869184), by norm_num⟩
  | 5 => ⟨((-675258513/34359738368), (93325311/8589934592)), (155/68719476736), by norm_num⟩
  | 6 => ⟨((362262217/68719476736), (-400536783/137438953472)), (85/137438953472), by norm_num⟩
  | 7 => ⟨((-1332659535/1099511627776), (368365191/549755813888)), (159/1099511627776), by norm_num⟩
  | 8 => ⟨((536208195/2199023255552), (-74107613/549755813888)), (65/2199023255552), by norm_num⟩
  | 9 => ⟨((-383552799/8796093022208), (424076807/17592186044416)), (95/17592186044416), by norm_num⟩
  | 10 => ⟨((493843533/70368744177664), (-546020233/140737488355328)), (31/35184372088832), by norm_num⟩
  | 11 => ⟨((-1156088007/1125899906842624), (639116847/1125899906842624)), (147/1125899906842624), by norm_num⟩
  | 12 => ⟨((1240434579/9007199254740992), (-685745923/9007199254740992)), (5/281474976710656), by norm_num⟩
  | 13 => ⟨((-1228555347/72057594037927936), (679178761/72057594037927936)), (161/72057594037927936), by norm_num⟩
  | 14 => ⟨((282469079/144115188075855872), (-624626313/576460752303423488)), (75/288230376151711744), by norm_num⟩
  | 15 => ⟨((-30307763/144115188075855872), (33509909/288230376151711744)), (131/4611686018427387904), by norm_num⟩
  | 16 => ⟨((780455405/36893488147419103232), (-26966059/2305843009213693952)), (107/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-328916724063/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889913809129485/316912650057057350374175801344), (-779393694151/633825300114114700748351602688)), (92277/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472733226334397/9903520314283042199192993792), (-876709902213/39614081257132168796771975168)), (12977/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472695560596757/618970019642690137449562112), (-465686163855/1237940039285380274899124224)), (110311/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443112073134013/38685626227668133590597632), (-465611961909/77371252455336267181195264)), (110317/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775366109204435/4835703278458516698824704), (-436432390733/4835703278458516698824704)), (103429/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259819915766527/604462909807314587353088), (-763599072693/604462909807314587353088)), (22627/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236183425028405/9444732965739290427392), (-620276524431/37778931862957161709568)), (147087/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162349452761059/590295810358705651712), (-930156349423/4722366482869645213696)), (110327/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405793695349111/147573952589676412928), (-1278545163375/590295810358705651712)), (151717/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912816051671893/36893488147419103232), (-1597551979461/73786976294838206464)), (189673/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825082884106079/9223372036854775808), (-1796380856581/9223372036854775808)), (53355/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596329910253571/1152921504606846976), (-1795300067101/1152921504606846976)), (213467/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196630142096983/144115188075855872), (-1569672510051/144115188075855872)), (186837/144115188075855872), by norm_num⟩
  | 4 => ⟨((747354072448165/18014398509481984), (-1176040382503/18014398509481984)), (35045/4503599627370496), by norm_num⟩
  | 3 => ⟨((186636287065261/1125899906842624), (-2935856670825/9007199254740992)), (87659/2251799813685248), by norm_num⟩
  | 2 => ⟨((2235595897235099/4503599627370496), (-5858999323511/4503599627370496)), (701829/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227532005876013/2251799813685248), (-547298736299/140737488355328)), (263535/562949953421312), by norm_num⟩
  | 0 => ⟨((2203416235570613/2251799813685248), (-17387077048329/2251799813685248)), (2113889/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203416235570613/2251799813685248), (-17387077048329/2251799813685248)), (8063846596724700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155938004445751/2251799813685248), (-34026974888773/2251799813685248)), (4169583/2251799813685248), by norm_num⟩
  | 2 => ⟨((2063642964952737/2251799813685248), (-32578405901441/1125899906842624)), (2027543/562949953421312), by norm_num⟩
  | 3 => ⟨((472330716391701/562949953421312), (-119424822294227/2251799813685248)), (15334341/2251799813685248), by norm_num⟩
  | 4 => ⟨((197357608154511/281474976710656), (-100200757680795/1125899906842624)), (27358403/2251799813685248), by norm_num⟩
  | 5 => ⟨((1089191343523955/2251799813685248), (-281025078708573/2251799813685248)), (5404319/281474976710656), by norm_num⟩
  | 6 => ⟨((983535642213303/4503599627370496), (-135931303121291/1125899906842624)), (105232613/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-535544467/16777216)), (1/16777216), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1192424837/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-267648040319687/2251799813685248), (398629878396339/2251799813685248)), (42898547/2251799813685248), by norm_num⟩
  | 1 => ⟨((114336231/536870912), (-681160793/2147483648)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-409726049/2147483648), (1220476301/4294967296)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((7647193/67108864), (-728933323/4294967296)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((-438461775/8589934592), (40814787/536870912)), (19/2147483648), by norm_num⟩
  | 5 => ⟨((314247215/17179869184), (-468033799/17179869184)), (55/17179869184), by norm_num⟩
  | 6 => ⟨((-187685141/34359738368), (1118138655/137438953472)), (133/137438953472), by norm_num⟩
  | 7 => ⟨((768655151/549755813888), (-1144820299/549755813888)), (69/274877906944), by norm_num⟩
  | 8 => ⟨((-688622573/2199023255552), (512810653/1099511627776)), (125/2199023255552), by norm_num⟩
  | 9 => ⟨((548376007/8796093022208), (-408370375/4398046511104)), (101/8796093022208), by norm_num⟩
  | 10 => ⟨((-786046323/70368744177664), (585361189/35184372088832)), (147/70368744177664), by norm_num⟩
  | 11 => ⟨((16004613/8796093022208), (-762782875/281474976710656)), (49/140737488355328), by norm_num⟩
  | 12 => ⟨((-611763561/2251799813685248), (28473405/70368744177664)), (119/2251799813685248), by norm_num⟩
  | 13 => ⟨((674543479/18014398509481984), (-1004652171/18014398509481984)), (133/18014398509481984), by norm_num⟩
  | 14 => ⟨((-690639809/144115188075855872), (514312869/72057594037927936)), (69/72057594037927936), by norm_num⟩
  | 15 => ⟨((329989445/576460752303423488), (-491479975/576460752303423488)), (67/576460752303423488), by norm_num⟩
  | 16 => ⟨((-591261713/9223372036854775808), (880613899/9223372036854775808)), (61/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (352044219981/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222447417129433/79228162514264337593543950336), (3335919363063/633825300114114700748351602688)), (46265/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890653298600667/39614081257132168796771975168), (3752384676181/39614081257132168796771975168)), (26029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472621197378617/618970019642690137449562112), (3986278678219/2475880078570760549798248448)), (13831/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886075211422767/77371252455336267181195264), (996392475077/38685626227668133590597632)), (27669/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775226261464807/4835703278458516698824704), (3735718768053/9671406556917033397649408)), (25947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259574739830473/604462909807314587353088), (1634000489695/302231454903657293676544)), (45421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944534080191753/37778931862957161709568), (5309089974665/75557863725914323419136)), (73837/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40577983356659/147573952589676412928), (1990291233521/2361183241434822606848)), (27701/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811380445967787/295147905179352825856), (2735647138761/295147905179352825856)), (9527/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456278244525899/18446744073709551616), (6836108420799/73786976294838206464)), (2979/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1824496446373681/9223372036854775808), (1921621204865/2305843009213693952)), (107325/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595740449507837/1152921504606846976), (3840657294725/576460752303423488)), (53713/576460752303423488), by norm_num⟩
  | 5 => ⟨((299027742234863/36028797018963968), (6715335427299/144115188075855872)), (94111/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493922609849479/36028797018963968), (5030688824687/18014398509481984)), (141391/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492096553958093/9007199254740992), (6278193447499/4503599627370496)), (177135/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116786536407079/2251799813685248), (12525903097975/2251799813685248)), (177731/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112204941057061/1125899906842624), (18712711786127/1125899906842624)), (33511/140737488355328), by norm_num⟩
  | 0 => ⟨((1098411599848701/1125899906842624), (37121254278359/1125899906842624)), (135539/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098411599848701/1125899906842624), (37121254278359/1125899906842624)), (517040253759288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((133796313490973/140737488355328), (9053739158445/140737488355328)), (546795/562949953421312), by norm_num⟩
  | 2 => ⟨((253230088432951/281474976710656), (17214417236869/140737488355328)), (555003/281474976710656), by norm_num⟩
  | 3 => ⟨((894433086451445/1125899906842624), (247792308938077/1125899906842624)), (4537571/1125899906842624), by norm_num⟩
  | 4 => ⟨((656017034268603/1125899906842624), (393700431691027/1125899906842624)), (18413463/2251799813685248), by norm_num⟩
  | 5 => ⟨((122283658459953/562949953421312), (458787123115585/1125899906842624)), (34335085/2251799813685248), by norm_num⟩
  | 6 => ⟨((-267648040319687/2251799813685248), (398629878396339/2251799813685248)), (42898547/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1192424837/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1295012881/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((65714565970599/562949953421312), (-656101484392527/4503599627370496)), (25295895/2251799813685248), by norm_num⟩
  | 1 => ⟨((-487803043/2147483648), (152196233/536870912)), (3/134217728), by norm_num⟩
  | 2 => ⟨((237305223/1073741824), (-592320389/2147483648)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-615699523/4294967296), (24012547/134217728)), (1/67108864), by norm_num⟩
  | 4 => ⟨((599047975/8589934592), (-747620143/8589934592)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-233138707/8589934592), (1163841299/34359738368)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((302444651/34359738368), (-754910199/68719476736)), (17/17179869184), by norm_num⟩
  | 7 => ⟨((-672605847/274877906944), (419710691/137438953472)), (77/274877906944), by norm_num⟩
  | 8 => ⟨((81801909/137438953472), (-816719293/1099511627776)), (77/1099511627776), by norm_num⟩
  | 9 => ⟨((-141492591/1099511627776), (706338827/4398046511104)), (17/1099511627776), by norm_num⟩
  | 10 => ⟨((220265495/8796093022208), (-549788757/17592186044416)), (27/8796093022208), by norm_num⟩
  | 11 => ⟨((-623442709/140737488355328), (778065107/140737488355328)), (39/70368744177664), by norm_num⟩
  | 12 => ⟨((808775663/1125899906842624), (-126170399/140737488355328)), (103/1125899906842624), by norm_num⟩
  | 13 => ⟨((-242123811/2251799813685248), (604347717/4503599627370496)), (63/4503599627370496), by norm_num⟩
  | 14 => ⟨((538458493/36028797018963968), (-42000227/2251799813685248)), (71/36028797018963968), by norm_num⟩
  | 15 => ⟨((-279411159/144115188075855872), (697417967/288230376151711744)), (75/288230376151711744), by norm_num⟩
  | 16 => ⟨((271854505/1152921504606846976), (-339278175/1152921504606846976)), (37/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1138868701/9903520314283042199192993792)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779379147583179/633825300114114700748351602688), (-690520752773/316912650057057350374175801344)), (46169/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472607101068881/9903520314283042199192993792), (-776720636813/19807040628566084398385987584)), (6493/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118140390160523/154742504910672534362390528), (-1650248675891/2475880078570760549798248448)), (55195/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885956164681351/77371252455336267181195264), (-1649930744143/154742504910672534362390528)), (27601/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775114895939963/4835703278458516698824704), (-386618087179/2417851639229258349412352)), (51757/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259380331511517/604462909807314587353088), (-338206417397/151115727451828646838272)), (22647/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236094143610461/9444732965739290427392), (-549427208551/18889465931478580854784)), (73613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162282499692837/590295810358705651712), (-1647728044335/4722366482869645213696)), (13805/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811219200815355/295147905179352825856), (-8846589231/2305843009213693952)), (75943/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824711784695185/73786976294838206464), (-353695042827/9223372036854775808)), (94953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912023870169579/4611686018427387904), (-3181402594525/9223372036854775808)), (106855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398823758768889/288230376151711744), (-3179088104517/1152921504606846976)), (106897/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195724928750319/144115188075855872), (-347387543691/18014398509481984)), (46791/72057594037927936), by norm_num⟩
  | 4 => ⟨((746675465210825/18014398509481984), (-4163452184897/36028797018963968)), (70233/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491394839651485/9007199254740992), (-2597614850763/4503599627370496)), (175747/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232208173210679/4503599627370496), (-5181624509165/2251799813685248)), (175993/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222458415187903/2251799813685248), (-3869252260047/562949953421312)), (264609/1125899906842624), by norm_num⟩
  | 0 => ⟨((2193301161023413/2251799813685248), (-7670881765619/562949953421312)), (531701/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193301161023413/2251799813685248), (-7670881765619/562949953421312)), (2028278355125045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2135904122064173/2251799813685248), (-59772822718449/2251799813685248)), (1050267/1125899906842624), by norm_num⟩
  | 2 => ⟨((506096678822287/562949953421312), (-113392867035375/2251799813685248)), (4096363/2251799813685248), by norm_num⟩
  | 3 => ⟨((907115189795401/1125899906842624), (-101941128265431/1125899906842624)), (7777887/2251799813685248), by norm_num⟩
  | 4 => ⟨((721614744781289/1125899906842624), (-328527768241051/2251799813685248)), (13941429/2251799813685248), by norm_num⟩
  | 5 => ⟨((877067691823547/2251799813685248), (-421121771468393/2251799813685248)), (21938743/2251799813685248), by norm_num⟩
  | 6 => ⟨((65714565970599/562949953421312), (-656101484392527/4503599627370496)), (25295895/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1295012881/33554432)), (1/33554432), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-1383878687/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1379041631057335/9007199254740992), (586456828915473/9007199254740992)), (264750025/9007199254740992), by norm_num⟩
  | 1 => ⟨((683697809/2147483648), (-290752099/2147483648)), (265/4294967296), by norm_num⟩
  | 2 => ⟨((-710854813/2147483648), (604601993/4294967296)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((985454019/4294967296), (-419078167/4294967296)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((-256149253/2147483648), (435724275/8589934592)), (205/8589934592), by norm_num⟩
  | 5 => ⟨((213058959/4294967296), (-362425263/17179869184)), (173/17179869184), by norm_num⟩
  | 6 => ⟨((-590724867/34359738368), (251214049/34359738368)), (121/34359738368), by norm_num⟩
  | 7 => ⟨((1403860375/274877906944), (-149252837/68719476736)), (145/137438953472), by norm_num⟩
  | 8 => ⟨((-1459622791/1099511627776), (620725099/1099511627776)), (19/68719476736), by norm_num⟩
  | 9 => ⟨((168622237/549755813888), (-573671803/4398046511104)), (71/1099511627776), by norm_num⟩
  | 10 => ⟨((-561024135/8796093022208), (477166791/17592186044416)), (239/17592186044416), by norm_num⟩
  | 11 => ⟨((848448649/70368744177664), (-90203677/17592186044416)), (183/70368744177664), by norm_num⟩
  | 12 => ⟨((-588099789/281474976710656), (500195395/562949953421312)), (1/2199023255552), by norm_num⟩
  | 13 => ⟨((1505131239/4503599627370496), (-640078205/4503599627370496)), (331/4503599627370496), by norm_num⟩
  | 14 => ⟨((-894237835/18014398509481984), (380287203/18014398509481984)), (199/18014398509481984), by norm_num⟩
  | 15 => ⟨((991741495/144115188075855872), (-105438001/36028797018963968)), (223/144115188075855872), by norm_num⟩
  | 16 => ⟨((-128891779/144115188075855872), (438504319/1152921504606846976)), (117/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (3568502499789/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889596488447281/316912650057057350374175801344), (2112548188683/316912650057057350374175801344)), (11577/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472554626237165/9903520314283042199192993792), (148514357937/1237940039285380274899124224)), (26055/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890022634801719/2475880078570760549798248448), (5048561425001/2475880078570760549798248448)), (27691/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885844029286733/77371252455336267181195264), (5047518797791/154742504910672534362390528)), (110799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550018833958411/9671406556917033397649408), (2365470575999/4835703278458516698824704)), (103911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314798759932207/151115727451828646838272), (4138465866091/604462909807314587353088)), (90959/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944225365725673/37778931862957161709568), (6722930372097/75557863725914323419136)), (73939/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298032031935389/4722366482869645213696), (5040380869979/4722366482869645213696)), (110969/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622123077866341/590295810358705651712), (6927571536037/590295810358705651712)), (152681/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228039353322195/9223372036854775808), (8655036736353/73786976294838206464)), (190999/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823597312912457/9223372036854775808), (9730829170899/9223372036854775808)), (107539/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398709950858635/288230376151711744), (4861610795435/576460752303423488)), (215333/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195321206925103/144115188075855872), (8499262252767/144115188075855872)), (5897/4503599627370496), by norm_num⟩
  | 4 => ⟨((186591823235725/4503599627370496), (12731784847973/36028797018963968)), (283629/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490605635351033/9007199254740992), (15884801884837/9007199254740992)), (177771/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115286840726809/2251799813685248), (15839929812981/2251799813685248)), (178527/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109933650130187/1125899906842624), (23647791274167/1125899906842624)), (67421/140737488355328), by norm_num⟩
  | 0 => ⟨((546891598440907/562949953421312), (23423817839601/562949953421312)), (1093933/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546891598440907/562949953421312), (23423817839601/562949953421312)), (4173023228171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132579167734489/140737488355328), (22755644799389/281474976710656)), (2216493/1125899906842624), by norm_num⟩
  | 2 => ⟨((123973939555887/140737488355328), (171492300112541/1125899906842624)), (1133599/281474976710656), by norm_num⟩
  | 3 => ⟨((827671961435/1099511627776), (151065478693029/562949953421312)), (9369909/1125899906842624), by norm_num⟩
  | 4 => ⟨((278459169462615/562949953421312), (227433085556143/562949953421312)), (9567703/562949953421312), by norm_num⟩
  | 5 => ⟨((366834749630435/4503599627370496), (1799970394594181/4503599627370496)), (34391881/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1379041631057335/9007199254740992), (586456828915473/9007199254740992)), (264750025/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1383878687/33554432)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile012Terms0
