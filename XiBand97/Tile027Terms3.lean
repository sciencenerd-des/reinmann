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
namespace Reinmann.XiBand97.Tile027Terms3
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
  | 0 => ⟨((-22364231/8388608), (-1231612799/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-507958308030979/18014398509481984), (1144881011465059/18014398509481984)), (27901107/1125899906842624), by norm_num⟩
  | 1 => ⟨((374345945/4294967296), (-421866871/2147483648)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((-144639901/1073741824), (163001051/536870912)), (513/4294967296), by norm_num⟩
  | 3 => ⟨((596117433/4294967296), (-1343581783/4294967296)), (531/4294967296), by norm_num⟩
  | 4 => ⟨((-460656073/4294967296), (1038267083/4294967296)), (103/1073741824), by norm_num⟩
  | 5 => ⟨((569562991/8589934592), (-1283731053/8589934592)), (1/16777216), by norm_num⟩
  | 6 => ⟨((-586847795/17179869184), (1322689061/17179869184)), (529/17179869184), by norm_num⟩
  | 7 => ⟨((518277557/34359738368), (-73008715/2147483648)), (469/34359738368), by norm_num⟩
  | 8 => ⟨((-400504483/68719476736), (451346075/34359738368)), (91/17179869184), by norm_num⟩
  | 9 => ⟨((550211715/274877906944), (-155014431/34359738368)), (251/137438953472), by norm_num⟩
  | 10 => ⟨((-170072777/274877906944), (766649899/549755813888)), (39/68719476736), by norm_num⟩
  | 11 => ⟨((191164427/1099511627776), (-430863161/1099511627776)), (11/68719476736), by norm_num⟩
  | 12 => ⟨((-393931573/8796093022208), (221969387/2199023255552)), (91/2199023255552), by norm_num⟩
  | 13 => ⟨((187332187/17592186044416), (-211112861/8796093022208)), (87/8796093022208), by norm_num⟩
  | 14 => ⟨((-165443355/70368744177664), (2913209/549755813888)), (309/140737488355328), by norm_num⟩
  | 15 => ⟨((545485263/1125899906842624), (-1229462555/1125899906842624)), (1/2199023255552), by norm_num⟩
  | 16 => ⟨((-210764763/2251799813685248), (475040119/2251799813685248)), (397/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (1295043672891/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444463201813485/158456325028528675187087900672), (3062241935507/633825300114114700748351602688)), (185003/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888711378539903/39614081257132168796771975168), (861055539341/9903520314283042199192993792)), (208167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944211006094437/1237940039285380274899124224), (3658490351565/2475880078570760549798248448)), (221223/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770088222371925/154742504910672534362390528), (3657370610823/154742504910672534362390528)), (110637/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774259911413731/4835703278458516698824704), (3427595619269/9671406556917033397649408)), (103749/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257884240012007/604462909807314587353088), (1498978642007/302231454903657293676544)), (90807/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471580561743239/18889465931478580854784), (4869452377657/75557863725914323419136)), (36903/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296437037399023/4722366482869645213696), (228133784165/295147905179352825856)), (221507/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404983045894543/147573952589676412928), (1253944582003/147573952589676412928)), (304715/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910789770762979/36893488147419103232), (97890291041/1152921504606846976)), (381109/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910262348303009/4611686018427387904), (880197825445/1152921504606846976)), (107261/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591772906494565/1152921504606846976), (7033442217291/1152921504606846976)), (429415/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149080512464109/18014398509481984), (3072557191853/72057594037927936)), (94039/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488731763588375/36028797018963968), (9199402386407/36028797018963968)), (565069/36028797018963968), by norm_num⟩
  | 3 => ⟨((742812268648867/4503599627370496), (11467340170823/9007199254740992)), (707803/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220678624335745/4503599627370496), (11419587341479/2251799813685248)), (710007/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205192035004593/2251799813685248), (34020811261431/2251799813685248)), (2141075/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079440989679987/1125899906842624), (67094689059959/2251799813685248)), (2163285/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079440989679987/1125899906842624), (67094689059959/2251799813685248)), (8252277378562545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516949783369601/562949953421312), (128652213435659/2251799813685248)), (8553909/2251799813685248), by norm_num⟩
  | 2 => ⟨((1891483354118215/2251799813685248), (236279383136603/2251799813685248)), (16687315/2251799813685248), by norm_num⟩
  | 3 => ⟨((1564029497918397/2251799813685248), (396943384938635/2251799813685248)), (31536239/2251799813685248), by norm_num⟩
  | 4 => ⟨((254088330321737/562949953421312), (275704420648105/1125899906842624)), (54926473/2251799813685248), by norm_num⟩
  | 5 => ⟨((647413112836565/4503599627370496), (995516926207057/4503599627370496)), (152965015/4503599627370496), by norm_num⟩
  | 6 => ⟨((-507958308030979/18014398509481984), (1144881011465059/18014398509481984)), (27901107/1125899906842624), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1231612799/16777216)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-9760347/131072)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((359014313293071/9007199254740992), (121025101031421/2251799813685248)), (300912935/18014398509481984), by norm_num⟩
  | 1 => ⟨((-268384767/2147483648), (-723788269/4294967296)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((210379721/1073741824), (1134716965/4294967296)), (179/2147483648), by norm_num⟩
  | 3 => ⟨((-109940733/536870912), (-74122885/268435456)), (47/536870912), by norm_num⟩
  | 4 => ⟨((689437065/4294967296), (929647509/4294967296)), (297/4294967296), by norm_num⟩
  | 5 => ⟨((-216172593/2147483648), (-1165961755/8589934592)), (375/8589934592), by norm_num⟩
  | 6 => ⟨((903743887/17179869184), (1218622113/17179869184)), (197/8589934592), by norm_num⟩
  | 7 => ⟨((-809623923/34359738368), (-545854655/17179869184)), (355/34359738368), by norm_num⟩
  | 8 => ⟨((317321391/34359738368), (855762057/68719476736)), (35/8589934592), by norm_num⟩
  | 9 => ⟨((-884408343/274877906944), (-1192549769/274877906944)), (49/34359738368), by norm_num⟩
  | 10 => ⟨((554611449/549755813888), (186961645/137438953472)), (31/68719476736), by norm_num⟩
  | 11 => ⟨((-158089181/549755813888), (-213169875/549755813888)), (285/2199023255552), by norm_num⟩
  | 12 => ⟨((330458475/4398046511104), (891190547/8796093022208)), (75/2199023255552), by norm_num⟩
  | 13 => ⟨((-637631161/35184372088832), (-53736977/2199023255552)), (291/35184372088832), by norm_num⟩
  | 14 => ⟨((17850793/4398046511104), (385124527/70368744177664)), (131/70368744177664), by norm_num⟩
  | 15 => ⟨((-477619697/562949953421312), (-644029721/562949953421312)), (221/562949953421312), by norm_num⟩
  | 16 => ⟨((748786899/4503599627370496), (252418933/1125899906842624)), (349/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1214927208677/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777797686184135/633825300114114700748351602688), (1436308862807/633825300114114700748351602688)), (184683/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236081199666901/4951760157141521099596496896), (403867702361/9903520314283042199192993792)), (207787/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236044584555403/309485009821345068724781056), (428991107873/618970019642690137449562112)), (220795/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770023231376939/154742504910672534362390528), (107214514369/9671406556917033397649408)), (110409/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387114814944583/2417851639229258349412352), (1607652475809/9671406556917033397649408)), (207043/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831613027427/604462909807314587353088), (351532732307/151115727451828646838272)), (45297/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886237413088727/75557863725914323419136), (1141951972861/37778931862957161709568)), (294477/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296374010640727/4722366482869645213696), (1712002033043/4722366482869645213696)), (55225/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619846493306889/590295810358705651712), (2352499170087/590295810358705651712)), (75951/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821473883708879/73786976294838206464), (2938370281697/73786976294838206464)), (23741/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910203914274475/4611686018427387904), (825642652133/2305843009213693952)), (213739/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591658529176959/1152921504606846976), (3298704935625/1152921504606846976)), (213827/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192546814099517/144115188075855872), (2882023807969/144115188075855872)), (187197/72057594037927936), by norm_num⟩
  | 4 => ⟨((186073925678649/4503599627370496), (4314364348171/36028797018963968)), (561985/36028797018963968), by norm_num⟩
  | 3 => ⟨((185682349414681/1125899906842624), (5377813471495/9007199254740992)), (351587/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110188044547727/2251799813685248), (10710332460125/4503599627370496)), (1408431/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102405008366717/1125899906842624), (997045071235/140737488355328)), (1058941/1125899906842624), by norm_num⟩
  | 0 => ⟨((269800197045517/281474976710656), (15728536932943/1125899906842624)), (4256851/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269800197045517/281474976710656), (15728536932943/1125899906842624)), (16238597878462981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034218892160817/1125899906842624), (30152324113045/1125899906842624)), (4139757/1125899906842624), by norm_num⟩
  | 2 => ⟨((949195881230595/1125899906842624), (110788190142825/2251799813685248)), (1956763/281474976710656), by norm_num⟩
  | 3 => ⟨((1594998471390499/2251799813685248), (93400570631063/1125899906842624)), (27934911/2251799813685248), by norm_num⟩
  | 4 => ⟨((557137770887105/1125899906842624), (33078821322873/281474976710656)), (22104281/1125899906842624), by norm_num⟩
  | 5 => ⟨((1040572645036105/4503599627370496), (523796779117399/4503599627370496)), (54142875/2251799813685248), by norm_num⟩
  | 6 => ⟨((359014313293071/9007199254740992), (121025101031421/2251799813685248)), (300912935/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-9760347/131072)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-633141057/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((18100171905835/281474976710656), (-45311775623185/9007199254740992)), (78026857/9007199254740992), by norm_num⟩
  | 1 => ⟨((-109717027/536870912), (137332213/8589934592)), (239/8589934592), by norm_num⟩
  | 2 => ⟨((1394746471/4294967296), (-109112291/4294967296)), (3/67108864), by norm_num⟩
  | 3 => ⟨((-1477526455/4294967296), (115588245/4294967296)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((293478663/1073741824), (-22421/1048576)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((-746152791/4294967296), (116744429/8589934592)), (53/2147483648), by norm_num⟩
  | 6 => ⟨((1580875823/17179869184), (-7729585/1073741824)), (227/17179869184), by norm_num⟩
  | 7 => ⟨((-1435459561/34359738368), (112297313/34359738368)), (13/2147483648), by norm_num⟩
  | 8 => ⟨((1140491939/68719476736), (-44610863/34359738368)), (167/68719476736), by norm_num⟩
  | 9 => ⟨((-1610908789/274877906944), (63011433/137438953472)), (119/137438953472), by norm_num⟩
  | 10 => ⟨((1023910969/549755813888), (-40050745/274877906944)), (153/549755813888), by norm_num⟩
  | 11 => ⟨((-1183288791/2199023255552), (92569763/2199023255552)), (179/2199023255552), by norm_num⟩
  | 12 => ⟨((1253518491/8796093022208), (-98063897/8796093022208)), (3/137438953472), by norm_num⟩
  | 13 => ⟨((-1225768997/35184372088832), (95893029/35184372088832)), (95/17592186044416), by norm_num⟩
  | 14 => ⟨((556508551/70368744177664), (-87072345/140737488355328)), (87/70368744177664), by norm_num⟩
  | 15 => ⟨((-1886521741/1125899906842624), (2306005/17592186044416)), (297/1125899906842624), by norm_num⟩
  | 16 => ⟨((1498866911/4503599627370496), (-229019/8796093022208)), (119/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-101697372053/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444435564507843/158456325028528675187087900672), (-30055294165/158456325028528675187087900672)), (23053/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944293657756665/19807040628566084398385987584), (-67608490485/19807040628566084398385987584)), (207479/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145300633627/1237940039285380274899124224), (-143627899079/2475880078570760549798248448)), (6889/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1769957267746469/154742504910672534362390528), (-71791381193/77371252455336267181195264)), (110225/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548397537302997/9671406556917033397649408), (-134560902073/9671406556917033397649408)), (206675/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257777724189643/604462909807314587353088), (-29423218561/151115727451828646838272)), (180843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886150065380043/75557863725914323419136), (-95580563939/37778931862957161709568)), (293873/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648154346796495/2361183241434822606848), (-17911540649/590295810358705651712)), (220409/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202469624598235/73786976294838206464), (-49224860207/147573952589676412928)), (303069/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821362483991785/73786976294838206464), (-245933198687/73786976294838206464)), (94711/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820283150273363/9223372036854775808), (-276412337869/9223372036854775808)), (426213/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99470916076197/72057594037927936), (-276084581745/1152921504606846976)), (213115/576460752303423488), by norm_num⟩
  | 5 => ⟨((596219665462279/72057594037927936), (-241205808223/144115188075855872)), (186485/72057594037927936), by norm_num⟩
  | 4 => ⟨((372107996114301/9007199254740992), (-361073620779/36028797018963968)), (279747/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485262662752467/9007199254740992), (-450058557775/9007199254740992)), (174859/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219993203155697/4503599627370496), (-448139225561/2251799813685248)), (1399083/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204258955417679/2251799813685248), (-1334861980869/2251799813685248)), (524795/562949953421312), by norm_num⟩
  | 0 => ⟨((2157391448016851/2251799813685248), (-1315872985135/1125899906842624)), (4200707/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157391448016851/2251799813685248), (-1315872985135/1125899906842624)), (16024425515181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066938146811645/2251799813685248), (-5042816164303/2251799813685248)), (8058999/2251799813685248), by norm_num⟩
  | 2 => ⟨((1897241418524893/2251799813685248), (-9257651620725/2251799813685248)), (14830887/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598472152887361/2251799813685248), (-7799982923157/1125899906842624)), (12556655/1125899906842624), by norm_num⟩
  | 4 => ⟨((567295069724849/1125899906842624), (-1384232228359/140737488355328)), (18001021/1125899906842624), by norm_num⟩
  | 5 => ⟨((1142911776977057/4503599627370496), (-44637324578065/4503599627370496)), (73976249/4503599627370496), by norm_num⟩
  | 6 => ⟨((18100171905835/281474976710656), (-45311775623185/9007199254740992)), (78026857/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-633141057/8388608)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-641273733/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((280260523307597/9007199254740992), (-485834771555673/9007199254740992)), (18581593/1125899906842624), by norm_num⟩
  | 1 => ⟨((-26885385/268435456), (93212235/536870912)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((692325727/4294967296), (-1200154439/4294967296)), (373/4294967296), by norm_num⟩
  | 3 => ⟨((-742836849/4294967296), (1287716037/4294967296)), (201/2147483648), by norm_num⟩
  | 4 => ⟨((298887447/2147483648), (-1036249505/4294967296)), (325/4294967296), by norm_num⟩
  | 5 => ⟨((-384832631/4294967296), (41694481/268435456)), (421/8589934592), by norm_num⟩
  | 6 => ⟨((103227371/2147483648), (-715783237/8589934592)), (227/8589934592), by norm_num⟩
  | 7 => ⟨((-189872051/8589934592), (1316581347/34359738368)), (105/8589934592), by norm_num⟩
  | 8 => ⟨((611174555/68719476736), (-66217373/4294967296)), (85/17179869184), by norm_num⟩
  | 9 => ⟨((-437176667/137438953472), (757850671/137438953472)), (245/137438953472), by norm_num⟩
  | 10 => ⟨((281443481/274877906944), (-487885441/274877906944)), (317/549755813888), by norm_num⟩
  | 11 => ⟨((-329429679/1099511627776), (571070055/1099511627776)), (373/2199023255552), by norm_num⟩
  | 12 => ⟨((176732205/2199023255552), (-1225469063/8796093022208)), (201/4398046511104), by norm_num⟩
  | 13 => ⟨((-700158797/35184372088832), (1213733151/35184372088832)), (25/2199023255552), by norm_num⟩
  | 14 => ⟨((643921207/140737488355328), (-1116244657/140737488355328)), (185/70368744177664), by norm_num⟩
  | 15 => ⟨((-276360321/281474976710656), (958147451/562949953421312)), (319/562949953421312), by norm_num⟩
  | 16 => ⟨((222392389/1125899906842624), (-771039417/2251799813685248)), (129/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-341141757273/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888843326922671/316912650057057350374175801344), (-201628010983/79228162514264337593543950336)), (92359/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472131174944717/9903520314283042199192993792), (-907109154247/19807040628566084398385987584)), (207829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888223988589069/2475880078570760549798248448), (-963530639317/1237940039285380274899124224)), (220841/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884945280654381/77371252455336267181195264), (-481611926721/38685626227668133590597632)), (55217/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387083725123033/2417851639229258349412352), (-28209266699/151115727451828646838272)), (51773/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628861408780251/302231454903657293676544), (-1579067575253/604462909807314587353088)), (90617/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943030327960339/37778931862957161709568), (-2564764139891/75557863725914323419136)), (294559/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296241473809417/4722366482869645213696), (-1922505648301/4722366482869645213696)), (110483/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809832152817201/295147905179352825856), (-1320855914515/295147905179352825856)), (9497/18446744073709551616), by norm_num⟩
  | 8 => ⟨((910623112432019/36893488147419103232), (-1649770846507/36893488147419103232)), (379993/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227518977070447/1152921504606846976), (-3708415375565/9223372036854775808)), (427649/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397850661889247/288230376151711744), (-3703959107961/1152921504606846976)), (427845/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596161532237623/72057594037927936), (-1617978905509/72057594037927936)), (187293/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488256074907561/36028797018963968), (-4843941106701/36028797018963968)), (281161/18014398509481984), by norm_num⟩
  | 3 => ⟨((46407504601555/281474976710656), (-6037472714941/9007199254740992)), (703679/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219540341120529/4503599627370496), (-3005684671115/1125899906842624)), (44053/140737488355328), by norm_num⟩
  | 1 => ⟨((2203560275228957/2251799813685248), (-279752024493/35184372088832)), (2120419/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155917674579487/2251799813685248), (-17645781857033/1125899906842624)), (4264491/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155917674579487/2251799813685248), (-17645781857033/1125899906842624)), (16267742165572356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063565107721583/2251799813685248), (-16894420523595/562949953421312)), (259359/70368744177664), by norm_num⟩
  | 2 => ⟨((944518732268471/1125899906842624), (-123857321581745/2251799813685248)), (15709563/2251799813685248), by norm_num⟩
  | 3 => ⟨((394475774969067/562949953421312), (-207808100261101/2251799813685248)), (14042855/1125899906842624), by norm_num⟩
  | 4 => ⟨((1086505990095525/2251799813685248), (-291234632482497/2251799813685248)), (44544785/2251799813685248), by norm_num⟩
  | 5 => ⟨((973157248435045/4503599627370496), (-562089348782105/4503599627370496)), (54508541/2251799813685248), by norm_num⟩
  | 6 => ⟨((280260523307597/9007199254740992), (-485834771555673/9007199254740992)), (18581593/1125899906842624), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-641273733/8388608)), (1/8388608), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1298174793/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-430503975974631/18014398509481984), (-995326577848467/18014398509481984)), (48356719/2251799813685248), by norm_num⟩
  | 1 => ⟨((334411505/4294967296), (193290119/1073741824)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-544772483/4294967296), (-1259515735/4294967296)), (247/2147483648), by norm_num⟩
  | 3 => ⟨((591640447/4294967296), (1367874619/4294967296)), (269/2147483648), by norm_num⟩
  | 4 => ⟨((-481905423/4294967296), (-557083445/2147483648)), (55/536870912), by norm_num⟩
  | 5 => ⟨((157009439/2147483648), (1452025315/8589934592)), (575/8589934592), by norm_num⟩
  | 6 => ⟨((-170517303/4294967296), (-788473109/8589934592)), (157/4294967296), by norm_num⟩
  | 7 => ⟨((634927811/34359738368), (1467955147/34359738368)), (293/17179869184), by norm_num⟩
  | 8 => ⟨((-258582013/34359738368), (-37365153/2147483648)), (479/68719476736), by norm_num⟩
  | 9 => ⟨((187218925/68719476736), (216425379/34359738368)), (349/137438953472), by norm_num⟩
  | 10 => ⟨((-487981865/549755813888), (-1128215645/549755813888)), (57/68719476736), by norm_num⟩
  | 11 => ⟨((578142555/2199023255552), (668333725/1099511627776)), (271/1099511627776), by norm_num⟩
  | 12 => ⟨((-627881419/8796093022208), (-181457983/1099511627776)), (295/4398046511104), by norm_num⟩
  | 13 => ⟨((78680703/4398046511104), (1455280311/35184372088832)), (593/35184372088832), by norm_num⟩
  | 14 => ⟨((-585941317/140737488355328), (-1354698213/140737488355328)), (277/70368744177664), by norm_num⟩
  | 15 => ⟨((127270225/140737488355328), (588498341/281474976710656)), (483/562949953421312), by norm_num⟩
  | 16 => ⟨((-51832335/281474976710656), (-239673051/562949953421312)), (395/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-2577899337481/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777630981409849/633825300114114700748351602688), (-3047106681655/633825300114114700748351602688)), (185001/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888461887855695/39614081257132168796771975168), (-856789832729/9903520314283042199192993792)), (208165/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888157006042079/2475880078570760549798248448), (-3640312653415/2475880078570760549798248448)), (55305/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221227912953973/19342813113834066795298816), (-909784620325/38685626227668133590597632)), (110635/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548271554356659/9671406556917033397649408), (-1705222608397/4835703278458516698824704)), (103747/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257667097924029/604462909807314587353088), (-372861619957/75557863725914323419136)), (181611/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942984782536851/37778931862957161709568), (-605608093305/9444732965739290427392)), (147609/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648086339083905/2361183241434822606848), (-1815802678491/2361183241434822606848)), (221501/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809784468426535/295147905179352825856), (-2495069584253/295147905179352825856)), (304707/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56910182930559/2305843009213693952), (-6232700175579/73786976294838206464)), (190549/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820014807270739/9223372036854775808), (-3502477222525/4611686018427387904)), (429031/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591263653474765/1152921504606846976), (-54659542395/9007199254740992)), (53675/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192199218609591/144115188075855872), (-6112280845203/144115188075855872)), (376141/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488065871095239/36028797018963968), (-9149274790123/36028797018963968)), (565045/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484794669523311/9007199254740992), (-11403153062193/9007199254740992)), (707767/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219026369526331/4503599627370496), (-709570253063/140737488355328)), (1419925/4503599627370496), by norm_num⟩
  | 1 => ⟨((550683077446953/562949953421312), (-33810146693109/2251799813685248)), (267613/281474976710656), by norm_num⟩
  | 0 => ⟨((2154036887031731/2251799813685248), (-4164305946509/140737488355328)), (4326091/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154036887031731/2251799813685248), (-4164305946509/140737488355328)), (16502727517134856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058546888961219/2251799813685248), (-31868085477761/562949953421312)), (8532555/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874663134104727/2251799813685248), (-116532469393951/1125899906842624)), (16566597/2251799813685248), by norm_num⟩
  | 3 => ⟨((1536567584583159/2251799813685248), (-388061359577967/2251799813685248)), (15506655/1125899906842624), by norm_num⟩
  | 4 => ⟨((490818124630859/1125899906842624), (-264802626917759/1125899906842624)), (53014585/2251799813685248), by norm_num⟩
  | 5 => ⟨((606739548358375/4503599627370496), (-923491887342461/4503599627370496)), (71158939/2251799813685248), by norm_num⟩
  | 6 => ⟨((-430503975974631/18014398509481984), (-995326577848467/18014398509481984)), (48356719/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1298174793/16777216)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1313212267/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1012716575371951/18014398509481984), (-276210228575585/18014398509481984)), (184061329/18014398509481984), by norm_num⟩
  | 1 => ⟨((1591562569/8589934592), (27130361/536870912)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-1311382647/4294967296), (-22354311/268435456)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((1440701091/4294967296), (98234883/1073741824)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-593539471/2147483648), (-323766149/4294967296)), (111/2147483648), by norm_num⟩
  | 5 => ⟨((195620927/1073741824), (106708041/2147483648)), (147/4294967296), by norm_num⟩
  | 6 => ⟨((-859646217/8589934592), (-117230765/4294967296)), (163/8589934592), by norm_num⟩
  | 7 => ⟨((1619002111/34359738368), (55196211/4294967296)), (309/34359738368), by norm_num⟩
  | 8 => ⟨((-1333991711/68719476736), (-181917707/34359738368)), (1/268435456), by norm_num⟩
  | 9 => ⟨((488513229/68719476736), (133238019/68719476736)), (189/137438953472), by norm_num⟩
  | 10 => ⟨((-161005991/68719476736), (-87826155/137438953472)), (251/549755813888), by norm_num⟩
  | 11 => ⟨((385926895/549755813888), (105258429/549755813888)), (303/2199023255552), by norm_num⟩
  | 12 => ⟨((-847968059/4398046511104), (-231276407/4398046511104)), (21/549755813888), by norm_num⟩
  | 13 => ⟨((859927505/17592186044416), (234538249/17592186044416)), (43/4398046511104), by norm_num⟩
  | 14 => ⟨((-809765935/70368744177664), (-862723/274877906944)), (163/70368744177664), by norm_num⟩
  | 15 => ⟨((1423390091/562949953421312), (388218097/562949953421312)), (289/562949953421312), by norm_num⟩
  | 16 => ⟨((-146601923/281474976710656), (-319875879/2251799813685248)), (15/140737488355328), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-936358613355/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222196916131495/79228162514264337593543950336), (-4426908503161/633825300114114700748351602688)), (92637/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((7376558567415/154742504910672534362390528), (-4979029444339/39614081257132168796771975168)), (26061/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888089792626043/2475880078570760549798248448), (-2644341276147/1237940039285380274899124224)), (13849/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769755654358999/154742504910672534362390528), (-1321738682211/38685626227668133590597632)), (110829/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774103835241947/4835703278458516698824704), (-2477342388089/4835703278458516698824704)), (103941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314402684331599/151115727451828646838272), (-4333514492739/604462909807314587353088)), (90987/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942938556730013/37778931862957161709568), (-1759630569887/18889465931478580854784)), (147927/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296102583018879/4722366482869645213696), (-5275884050797/4722366482869645213696)), (111009/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202433916085137/73786976294838206464), (-7249455497779/590295810358705651712)), (152741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910501002910037/36893488147419103232), (-1131811989745/9223372036854775808)), (95541/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819872956730271/9223372036854775808), (-10176244908187/9223372036854775808)), (107591/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795559329450825/576460752303423488), (-10163676284107/1152921504606846976)), (107725/576460752303423488), by norm_num⟩
  | 5 => ⟨((298017205559685/36028797018963968), (-554943185567/9007199254740992)), (188821/144115188075855872), by norm_num⟩
  | 4 => ⟨((743931625771309/18014398509481984), (-6645209850829/18014398509481984)), (70959/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484529162494269/9007199254740992), (-16563723628653/9007199254740992)), (355855/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109229450812555/2251799813685248), (-32979857537747/4503599627370496)), (357449/2251799813685248), by norm_num⟩
  | 1 => ⟨((2201790823909155/2251799813685248), (-49101908488039/2251799813685248)), (1080345/2251799813685248), by norm_num⟩
  | 0 => ⟨((1075898928766533/1125899906842624), (-48369442301103/1125899906842624)), (1096415/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1075898928766533/1125899906842624), (-48369442301103/1125899906842624)), (4182491306785201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2052080997523215/2251799813685248), (-11555341385259/140737488355328)), (2189653/1125899906842624), by norm_num⟩
  | 2 => ⟨((1854895697606651/2251799813685248), (-336974842363469/2251799813685248)), (8700917/2251799813685248), by norm_num⟩
  | 3 => ⟨((1477522994892135/2251799813685248), (-277579375174887/1125899906842624)), (16938703/2251799813685248), by norm_num⟩
  | 4 => ⟨((416305426208541/1125899906842624), (-91067133773645/281474976710656)), (15290433/1125899906842624), by norm_num⟩
  | 5 => ⟨((36076601466849/1125899906842624), (-1077516513397185/4503599627370496)), (84805507/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1012716575371951/18014398509481984), (-276210228575585/18014398509481984)), (184061329/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1313212267/16777216)), (1/16777216), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile027Terms3
