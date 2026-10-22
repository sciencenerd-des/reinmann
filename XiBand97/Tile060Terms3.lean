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
namespace Reinmann.XiBand97.Tile060Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨60,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79593/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79593/2560))
  have he : value ((69/80), (79593/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2862621597/1073741824), (-103190507601/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-352239790690247/18014398509481984), (-1201957244757639/18014398509481984)), (1704479/4503599627370496), by norm_num⟩
  | 1 => ⟨((8306794333/137438953472), (56690992289/274877906944)), (81/68719476736), by norm_num⟩
  | 2 => ⟨((-25676653935/274877906944), (-10952141493/34359738368)), (503/274877906944), by norm_num⟩
  | 3 => ⟨((26455875791/274877906944), (45138045747/137438953472)), (65/34359738368), by norm_num⟩
  | 4 => ⟨((-20444058803/274877906944), (-69761807833/274877906944)), (403/274877906944), by norm_num⟩
  | 5 => ⟨((789918171/17179869184), (43127341927/274877906944)), (125/137438953472), by norm_num⟩
  | 6 => ⟨((-26044486413/1099511627776), (-88872296531/1099511627776)), (517/1099511627776), by norm_num⟩
  | 7 => ⟨((23001318051/2199023255552), (78488011859/2199023255552)), (229/1099511627776), by norm_num⟩
  | 8 => ⟨((-17774512645/4398046511104), (-7581555523/549755813888)), (89/1099511627776), by norm_num⟩
  | 9 => ⟨((24418565855/17592186044416), (20831031097/4398046511104)), (491/17592186044416), by norm_num⟩
  | 10 => ⟨((-30191529483/70368744177664), (-103023362349/70368744177664)), (609/70368744177664), by norm_num⟩
  | 11 => ⟨((4241968153/35184372088832), (7237490607/17592186044416)), (43/17592186044416), by norm_num⟩
  | 12 => ⟨((-8741402431/281474976710656), (-29828520963/281474976710656)), (89/140737488355328), by norm_num⟩
  | 13 => ⟨((16627720625/2251799813685248), (56739215149/2251799813685248)), (85/562949953421312), by norm_num⟩
  | 14 => ⟨((-14684854387/9007199254740992), (-50109520799/9007199254740992)), (301/9007199254740992), by norm_num⟩
  | 15 => ⟨((6052201111/18014398509481984), (20652087481/18014398509481984)), (249/36028797018963968), by norm_num⟩
  | 16 => ⟨((-9353805285/144115188075855872), (-31918239577/144115188075855872)), (387/288230376151711744), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (-604369343057/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777853455216129/633825300114114700748351602688), (-2858166385431/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118044508933519/2475880078570760549798248448), (-803672913327/9903520314283042199192993792)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944211435921607/1237940039285380274899124224), (-3414680680911/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885044567692403/77371252455336267181195264), (-1706817867311/77371252455336267181195264)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193565091928011/1208925819614629174706176), (-1599586813043/4835703278458516698824704)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257885095128883/604462909807314587353088), (-1399083737731/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886323742542287/75557863725914323419136), (-1136235710627/18889465931478580854784)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324109562929767/1180591620717411303424), (-851722162061/1180591620717411303424)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809967001802797/295147905179352825856), (-4681518557837/590295810358705651712)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821582041703353/73786976294838206464), (-2923735587405/36893488147419103232)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820527818288291/9223372036854775808), (-821540343983/1152921504606846976)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795888206761387/576460752303423488), (-820590887689/144115188075855872)), (6707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18635118760395/2251799813685248), (-2867800533657/72057594037927936)), (5875/144115188075855872), by norm_num⟩
  | 4 => ⟨((46523058643735/1125899906842624), (-1073294523119/4503599627370496)), (1103/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485633679545243/9007199254740992), (-5351585831121/4503599627370496)), (11051/9007199254740992), by norm_num⟩
  | 2 => ⟨((277587673089561/562949953421312), (-21317245933243/4503599627370496)), (11083/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205237270914693/2251799813685248), (-15876952791813/1125899906842624)), (16705/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159016269095401/2251799813685248), (-3914039208575/140737488355328)), (67467/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159016269095401/2251799813685248), (-3914039208575/140737488355328)), (257366189009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2068314144962669/2251799813685248), (-120088462966673/2251799813685248)), (16641/281474976710656), by norm_num⟩
  | 2 => ⟨((1893375306900573/2251799813685248), (-110303173972779/1125899906842624)), (258761/2251799813685248), by norm_num⟩
  | 3 => ⟨((24537336690465/35184372088832), (-370983787463817/2251799813685248)), (60731/281474976710656), by norm_num⟩
  | 4 => ⟨((1034059221584123/2251799813685248), (-16170094773755/70368744177664)), (418871/1125899906842624), by norm_num⟩
  | 5 => ⟨((22246959318937/140737488355328), (-475234731274287/2251799813685248)), (577209/1125899906842624), by norm_num⟩
  | 6 => ⟨((-352239790690247/18014398509481984), (-1201957244757639/18014398509481984)), (1704479/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-103190507601/1073741824)), (1/536870912), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1451894239/536870912), (-104674472967/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1199807248005795/18014398509481984), (115933113221833/18014398509481984)), (6313949/18014398509481984), by norm_num⟩
  | 1 => ⟨((114806783641/549755813888), (-11093371763/549755813888)), (607/549755813888), by norm_num⟩
  | 2 => ⟨((-44997000757/137438953472), (4347900375/137438953472)), (239/137438953472), by norm_num⟩
  | 3 => ⟨((5878659817/17179869184), (-4544272159/137438953472)), (501/274877906944), by norm_num⟩
  | 4 => ⟨((-73730015415/274877906944), (7124269535/274877906944)), (197/137438953472), by norm_num⟩
  | 5 => ⟨((46236007375/274877906944), (-69806581/4294967296)), (31/34359738368), by norm_num⟩
  | 6 => ⟨((-12081061141/137438953472), (4669400127/549755813888)), (65/137438953472), by norm_num⟩
  | 7 => ⟨((86583079611/2199023255552), (-1045776935/274877906944)), (117/549755813888), by norm_num⟩
  | 8 => ⟨((-33935093165/2199023255552), (3279027531/2199023255552)), (369/4398046511104), by norm_num⟩
  | 9 => ⟨((94580700743/17592186044416), (-9138997207/17592186044416)), (129/4398046511104), by norm_num⟩
  | 10 => ⟨((-7413931003/4398046511104), (11462109153/70368744177664)), (649/70368744177664), by norm_num⟩
  | 11 => ⟨((33812854949/70368744177664), (-6534432173/140737488355328)), (93/35184372088832), by norm_num⟩
  | 12 => ⟨((-70680007411/562949953421312), (3414779047/281474976710656)), (391/562949953421312), by norm_num⟩
  | 13 => ⟨((68189770591/2251799813685248), (-3294467677/1125899906842624)), (379/2251799813685248), by norm_num⟩
  | 14 => ⟨((-15272045091/2251799813685248), (737841739/1125899906842624)), (681/18014398509481984), by norm_num⟩
  | 15 => ⟨((102155539303/72057594037927936), (-4935463477/36028797018963968)), (571/72057594037927936), by norm_num⟩
  | 16 => ⟨((-80077025653/288230376151711744), (7737558593/288230376151711744)), (225/144115188075855872), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (991699499979/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777786995945857/633825300114114700748351602688), (2344810077333/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888636987375219/39614081257132168796771975168), (1318640266177/9903520314283042199192993792)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888342495187709/2475880078570760549798248448), (5602672133445/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885004085018269/77371252455336267181195264), (5600929810681/154742504910672534362390528)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548444205458739/9671406556917033397649408), (5249020926941/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628908753529633/302231454903657293676544), (4591043042765/604462909807314587353088)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886212742550263/75557863725914323419136), (3728488379497/37778931862957161709568)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296353979794883/4722366482869645213696), (2794849487401/2361183241434822606848)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619816471464671/590295810358705651712), (7680908502253/590295810358705651712)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910716321670315/36893488147419103232), (4796873875957/36893488147419103232)), (747/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820356337536231/9223372036854775808), (5391406795739/4611686018427387904)), (6729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591600683447453/1152921504606846976), (10770131358595/1152921504606846976)), (3369/576460752303423488), by norm_num⟩
  | 5 => ⟨((596244535161905/72057594037927936), (9409609194829/144115188075855872)), (2953/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488490582885189/36028797018963968), (7042965871845/18014398509481984)), (8879/36028797018963968), by norm_num⟩
  | 3 => ⟨((371327004699335/2251799813685248), (17557637385535/9007199254740992)), (11133/9007199254740992), by norm_num⟩
  | 2 => ⟨((138750046537095/281474976710656), (4370776038995/562949953421312)), (5593/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102032051595059/1125899906842624), (1627424264245/70368744177664)), (16911/1125899906842624), by norm_num⟩
  | 0 => ⟨((269523451080275/281474976710656), (25668449695653/562949953421312)), (34351/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269523451080275/281474976710656), (25668449695653/562949953421312)), (131038670066451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((514988395783979/562949953421312), (98314233495285/1125899906842624)), (34459/562949953421312), by norm_num⟩
  | 2 => ⟨((1867282333486847/2251799813685248), (359752685529233/2251799813685248)), (138129/1125899906842624), by norm_num⟩
  | 3 => ⟨((1490950171415135/2251799813685248), (149160646970167/562949953421312)), (68305/281474976710656), by norm_num⟩
  | 4 => ⟨((414546183151705/1125899906842624), (197522968797659/562949953421312)), (1013185/2251799813685248), by norm_num⟩
  | 5 => ⟨((56087561813041/4503599627370496), (581809393905977/2251799813685248)), (1457087/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1199807248005795/18014398509481984), (115933113221833/18014398509481984)), (6313949/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-104674472967/1073741824)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-26523817845/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-21884071454753/2251799813685248), (1148685423333527/18014398509481984)), (1537251/4503599627370496), by norm_num⟩
  | 1 => ⟨((16979677029/549755813888), (-111406985763/549755813888)), (299/274877906944), by norm_num⟩
  | 2 => ⟨((-13490581905/274877906944), (44257174729/137438953472)), (477/274877906944), by norm_num⟩
  | 3 => ⟨((7145632583/137438953472), (-11720973639/34359738368)), (507/274877906944), by norm_num⟩
  | 4 => ⟨((-2838650625/68719476736), (37249885169/137438953472)), (405/274877906944), by norm_num⟩
  | 5 => ⟨((14434215187/549755813888), (-94705712193/549755813888)), (517/549755813888), by norm_num⟩
  | 6 => ⟨((-477840759/34359738368), (50163308565/549755813888)), (275/549755813888), by norm_num⟩
  | 7 => ⟨((13884376269/2199023255552), (-91098111387/2199023255552)), (501/2199023255552), by norm_num⟩
  | 8 => ⟨((-2757830949/1099511627776), (36189337729/2199023255552)), (25/274877906944), by norm_num⟩
  | 9 => ⟨((15581395931/17592186044416), (-51116294839/8796093022208)), (71/2199023255552), by norm_num⟩
  | 10 => ⟨((-2475925751/8796093022208), (32490067321/17592186044416)), (363/35184372088832), by norm_num⟩
  | 11 => ⟨((2861318297/35184372088832), (-75094678471/140737488355328)), (421/140737488355328), by norm_num⟩
  | 12 => ⟨((-12124564765/562949953421312), (39775821759/281474976710656)), (7/8796093022208), by norm_num⟩
  | 13 => ⟨((2964039961/562949953421312), (-77790586275/2251799813685248)), (55/281474976710656), by norm_num⟩
  | 14 => ⟨((-10765575487/9007199254740992), (70635048765/9007199254740992)), (401/9007199254740992), by norm_num⟩
  | 15 => ⟨((4561810455/18014398509481984), (-14965465819/9007199254740992)), (341/36028797018963968), by norm_num⟩
  | 16 => ⟨((-7248839595/144115188075855872), (47561055969/144115188075855872)), (17/9007199254740992), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (2243154080557/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777738493470257/633825300114114700748351602688), (2651736397299/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944291437665223/19807040628566084398385987584), (1491247377717/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888285607802601/2475880078570760549798248448), (49500226711/38685626227668133590597632)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((110621997776167/9671406556917033397649408), (1583508997649/77371252455336267181195264)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548392236480043/9671406556917033397649408), (742005240047/2417851639229258349412352)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314443189331939/151115727451828646838272), (2595960363923/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886141378687175/75557863725914323419136), (4216452808157/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81018852539645/295147905179352825856), (395075699079/590295810358705651712)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809873213026995/295147905179352825856), (2171508322761/295147905179352825856)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910673981684473/36893488147419103232), (2712274880951/36893488147419103232)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455066255167823/2305843009213693952), (3048409726003/4611686018427387904)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591514290496637/1152921504606846976), (6089578018799/1152921504606846976)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192419000496081/144115188075855872), (5320244257295/144115188075855872)), (5871/144115188075855872), by norm_num⟩
  | 4 => ⟨((744198243859041/18014398509481984), (7964118598125/36028797018963968)), (4409/18014398509481984), by norm_num⟩
  | 3 => ⟨((742604790146503/4503599627370496), (2481692827987/2251799813685248)), (5521/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109930532311513/2251799813685248), (9884319105409/2251799813685248)), (22143/4503599627370496), by norm_num⟩
  | 1 => ⟨((550999093659399/562949953421312), (29441486964029/2251799813685248)), (8341/562949953421312), by norm_num⟩
  | 0 => ⟨((269576517692845/281474976710656), (58041823029497/2251799813685248)), (33665/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269576517692845/281474976710656), (58041823029497/2251799813685248)), (128421787742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257994019249811/281474976710656), (111176579287333/2251799813685248)), (16555/281474976710656), by norm_num⟩
  | 2 => ⟨((117892869417129/140737488355328), (203804209325997/2251799813685248)), (127931/1125899906842624), by norm_num⟩
  | 3 => ⟨((1561656751056123/2251799813685248), (21340318877999/140737488355328)), (14843/70368744177664), by norm_num⟩
  | 4 => ⟨((515629106169559/1125899906842624), (118398635057977/562949953421312)), (401425/1125899906842624), by norm_num⟩
  | 5 => ⟨((46585053147219/281474976710656), (867569587607029/4503599627370496)), (67067/140737488355328), by norm_num⟩
  | 6 => ⟨((-21884071454753/2251799813685248), (1148685423333527/18014398509481984)), (1537251/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-26523817845/268435456)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-26864515393/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((63042790513149/1125899906842624), (61349515400073/2251799813685248)), (3229773/18014398509481984), by norm_num⟩
  | 1 => ⟨((-24771351845/137438953472), (-24106014647/274877906944)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((79735905603/274877906944), (38797133891/274877906944)), (65/68719476736), by norm_num⟩
  | 3 => ⟨((-85553326307/274877906944), (-41627718785/274877906944)), (281/274877906944), by norm_num⟩
  | 4 => ⟨((68846383447/274877906944), (16749307205/137438953472)), (57/68719476736), by norm_num⟩
  | 5 => ⟨((-88643183723/549755813888), (-43131152037/549755813888)), (37/68719476736), by norm_num⟩
  | 6 => ⟨((47555233521/549755813888), (361546413/8589934592)), (5/17179869184), by norm_num⟩
  | 7 => ⟨((-87471080873/2199023255552), (-42560841449/2199023255552)), (37/274877906944), by norm_num⟩
  | 8 => ⟨((17597409225/1099511627776), (34249515907/4398046511104)), (15/274877906944), by norm_num⟩
  | 9 => ⟨((-50350111231/8796093022208), (-12249437641/4398046511104)), (173/8796093022208), by norm_num⟩
  | 10 => ⟨((64828302329/35184372088832), (31543534953/35184372088832)), (225/35184372088832), by norm_num⟩
  | 11 => ⟨((-37940773661/70368744177664), (-9230429281/35184372088832)), (265/140737488355328), by norm_num⟩
  | 12 => ⟨((40708879705/281474976710656), (39615474221/562949953421312)), (143/281474976710656), by norm_num⟩
  | 13 => ⟨((-10079756057/281474976710656), (-39236089927/2251799813685248)), (143/1125899906842624), by norm_num⟩
  | 14 => ⟨((18540276053/2251799813685248), (9021150095/2251799813685248)), (265/9007199254740992), by norm_num⟩
  | 15 => ⟨((-15914359033/9007199254740992), (-7743456521/9007199254740992)), (229/36028797018963968), by norm_num⟩
  | 16 => ⟨((6403293195/18014398509481984), (6231306249/36028797018963968)), (93/72057594037927936), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (589882929413/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777687788951493/633825300114114700748351602688), (348643692059/316912650057057350374175801344)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472131509621143/9903520314283042199192993792), (196065321927/9903520314283042199192993792)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944112747052101/1237940039285380274899124224), (833041788319/2475880078570760549798248448)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769892160238811/154742504910672534362390528), (416388311751/77371252455336267181195264)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548336498658057/9671406556917033397649408), (780446465329/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314431078757419/151115727451828646838272), (341304585627/302231454903657293676544)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943031637435037/37778931862957161709568), (1108712400303/75557863725914323419136)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296243600186651/4722366482869645213696), (51942063627/295147905179352825856)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809833746272007/295147905179352825856), (1141976346319/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821250602552573/73786976294838206464), (713173889799/36893488147419103232)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((14219978767291/72057594037927936), (1603099108583/9223372036854775808)), (6669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591408787540695/1152921504606846976), (1601173684025/1152921504606846976)), (6671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596164596693061/72057594037927936), (699431983607/72057594037927936)), (2919/72057594037927936), by norm_num⟩
  | 4 => ⟨((744133387817575/18014398509481984), (523494416759/9007199254740992)), (1095/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485056148725977/9007199254740992), (1304966222093/4503599627370496)), (10955/9007199254740992), by norm_num⟩
  | 2 => ⟨((554895042921095/1125899906842624), (5197315233631/4503599627370496)), (10963/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101819709534827/1125899906842624), (3869920200883/1125899906842624)), (32929/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156152534232153/2251799813685248), (15256595265993/2251799813685248)), (33011/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156152534232153/2251799813685248), (15256595265993/2251799813685248)), (125926975730514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2064464593577065/2251799813685248), (29217114546865/2251799813685248)), (127331/2251799813685248), by norm_num⟩
  | 2 => ⟨((1892335363229801/2251799813685248), (26786439070609/1125899906842624)), (236781/2251799813685248), by norm_num⟩
  | 3 => ⟨((1588979203174347/2251799813685248), (45020810109543/1125899906842624)), (409233/2251799813685248), by norm_num⟩
  | 4 => ⟨((1117660370808029/2251799813685248), (127075471876959/2251799813685248)), (305139/1125899906842624), by norm_num⟩
  | 5 => ⟨((547569336061033/2251799813685248), (63072755471175/1125899906842624)), (168673/562949953421312), by norm_num⟩
  | 6 => ⟨((63042790513149/1125899906842624), (61349515400073/2251799813685248)), (3229773/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-26864515393/268435456)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-3017330773/1073741824), (-27191848757/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((781118749594807/18014398509481984), (-376119037982915/9007199254740992)), (3856033/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4854126537/34359738368), (37397220933/274877906944)), (193/274877906944), by norm_num⟩
  | 2 => ⟨((63260851461/274877906944), (-60921878027/274877906944)), (317/274877906944), by norm_num⟩
  | 3 => ⟨((-68703320379/274877906944), (66163119963/274877906944)), (173/137438953472), by norm_num⟩
  | 4 => ⟨((55960512569/274877906944), (-6736432253/34359738368)), (71/68719476736), by norm_num⟩
  | 5 => ⟨((-36464950453/274877906944), (35116714563/274877906944)), (187/274877906944), by norm_num⟩
  | 6 => ⟨((19801054805/274877906944), (-595904407/8589934592)), (51/137438953472), by norm_num⟩
  | 7 => ⟨((-4608124865/137438953472), (4437746481/137438953472)), (191/1099511627776), by norm_num⟩
  | 8 => ⟨((30027431339/2199023255552), (-57834425785/4398046511104)), (313/4398046511104), by norm_num⟩
  | 9 => ⟨((-43481008929/8796093022208), (5234170623/1099511627776)), (57/2199023255552), by norm_num⟩
  | 10 => ⟨((7083266233/4398046511104), (-13642746549/8796093022208)), (299/35184372088832), by norm_num⟩
  | 11 => ⟨((-67135898739/140737488355328), (32326825673/70368744177664)), (89/35184372088832), by norm_num⟩
  | 12 => ⟨((18227936605/140737488355328), (-35107972937/281474976710656)), (195/281474976710656), by norm_num⟩
  | 13 => ⟨((-18273346815/562949953421312), (17597717705/562949953421312)), (197/1125899906842624), by norm_num⟩
  | 14 => ⟨((34020758855/4503599627370496), (-16381446609/2251799813685248)), (369/9007199254740992), by norm_num⟩
  | 15 => ⟨((-59116222211/36028797018963968), (56930490117/36028797018963968)), (323/36028797018963968), by norm_num⟩
  | 16 => ⟨((12037897433/36028797018963968), (-46371258189/144115188075855872)), (265/144115188075855872), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-998537094989/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444408804007009/158456325028528675187087900672), (-295070584185/158456325028528675187087900672)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236058360200491/4951760157141521099596496896), (-331874274973/9903520314283042199192993792)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118010163875325/154742504910672534362390528), (-705030794541/1237940039285380274899124224)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769829268028409/154742504910672534362390528), (-22025113177/2417851639229258349412352)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548277515870227/9671406556917033397649408), (-1321024250371/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257672683781059/604462909807314587353088), (-577706953163/302231454903657293676544)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942989667101337/37778931862957161709568), (-1876643744549/75557863725914323419136)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296180609850159/4722366482869645213696), (-10989784529/36893488147419103232)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619580824347293/590295810358705651712), (-483229650059/147573952589676412928)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821142182797937/73786976294838206464), (-2414224617079/73786976294838206464)), (5933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227504399267797/1152921504606846976), (-2713360267085/9223372036854775808)), (1669/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591286555189117/1152921504606846976), (-2710061081877/1152921504606846976)), (6679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37256939952719/4503599627370496), (-1183798574289/72057594037927936)), (5847/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488105781909533/36028797018963968), (-3543996319985/36028797018963968)), (4387/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484854348209799/9007199254740992), (-552134509357/1125899906842624)), (10977/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219174911711455/4503599627370496), (-8795512420075/4503599627370496)), (21979/4503599627370496), by norm_num⟩
  | 1 => ⟨((550756859486533/562949953421312), (-13097081936151/2251799813685248)), (33037/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154912542126847/2251799813685248), (-25811883065291/2251799813685248)), (66345/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154912542126847/2251799813685248), (-25811883065291/2251799813685248)), (253086098677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1030949061877221/1125899906842624), (-49402571414443/2251799813685248)), (128503/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886927618013225/2251799813685248), (-90472579923859/2251799813685248)), (240971/2251799813685248), by norm_num⟩
  | 3 => ⟨((1577542784360279/2251799813685248), (-151625565197867/2251799813685248)), (423215/2251799813685248), by norm_num⟩
  | 4 => ⟨((1094968970812009/2251799813685248), (-106224281061193/1125899906842624)), (649979/2251799813685248), by norm_num⟩
  | 5 => ⟨((1024800382770189/4503599627370496), (-413224269766559/4503599627370496)), (754769/2251799813685248), by norm_num⟩
  | 6 => ⟨((781118749594807/18014398509481984), (-376119037982915/9007199254740992)), (3856033/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-27191848757/268435456)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-3052282179/1073741824), (-110027307715/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47345347824609/2251799813685248), (-978992186263573/18014398509481984)), (2908997/9007199254740992), by norm_num⟩
  | 1 => ⟨((38096323925/549755813888), (98467972993/549755813888)), (587/549755813888), by norm_num⟩
  | 2 => ⟨((-31389817213/274877906944), (-40566796939/137438953472)), (485/274877906944), by norm_num⟩
  | 3 => ⟨((34485238929/274877906944), (89134363259/274877906944)), (535/274877906944), by norm_num⟩
  | 4 => ⟨((-28414430449/274877906944), (-73443080115/274877906944)), (443/274877906944), by norm_num⟩
  | 5 => ⟨((2341233185/34359738368), (96822564399/549755813888)), (293/274877906944), by norm_num⟩
  | 6 => ⟨((-10288430191/274877906944), (-53185229535/549755813888)), (81/137438953472), by norm_num⟩
  | 7 => ⟨((19376564295/1099511627776), (25041405747/549755813888)), (307/1099511627776), by norm_num⟩
  | 8 => ⟨((-15965498735/2199023255552), (-41266194119/2199023255552)), (127/1099511627776), by norm_num⟩
  | 9 => ⟨((5846631035/2199023255552), (7555924661/1099511627776)), (187/4398046511104), by norm_num⟩
  | 10 => ⟨((-30831267371/35184372088832), (-79689904175/35184372088832)), (495/35184372088832), by norm_num⟩
  | 11 => ⟨((18475423205/70368744177664), (47753622551/70368744177664)), (595/140737488355328), by norm_num⟩
  | 12 => ⟨((-20297326971/281474976710656), (-52462716563/281474976710656)), (329/281474976710656), by norm_num⟩
  | 13 => ⟨((20583593389/1125899906842624), (13300658103/281474976710656)), (21/70368744177664), by norm_num⟩
  | 14 => ⟨((-9691452275/2251799813685248), (-50099199221/4503599627370496)), (159/2251799813685248), by norm_num⟩
  | 15 => ⟨((17035437703/18014398509481984), (88063353467/36028797018963968)), (561/36028797018963968), by norm_num⟩
  | 16 => ⟨((-28073011805/144115188075855872), (-72560611725/144115188075855872)), (29/9007199254740992), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (-631750558155/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444395264656779/158456325028528675187087900672), (-746696265157/158456325028528675187087900672)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888405749412477/39614081257132168796771975168), (-3359305664989/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59003043453649/77371252455336267181195264), (-3568227026787/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442440930900335/38685626227668133590597632), (-1783531436601/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548215735771921/9671406556917033397649408), (-3342884985527/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157202286791783/75557863725914323419136), (-730947104029/151115727451828646838272)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885890329828543/75557863725914323419136), (-2374419932185/37778931862957161709568)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296113313452083/4722366482869645213696), (-889901053083/1180591620717411303424)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619487410573709/590295810358705651712), (-2445583044631/295147905179352825856)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821024096083299/73786976294838206464), (-6109026620315/73786976294838206464)), (5955/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909950268039619/4611686018427387904), (-6865880620793/9223372036854775808)), (419/576460752303423488), by norm_num⟩
  | 6 => ⟨((795574819840351/576460752303423488), (-6857421384567/1152921504606846976)), (3355/576460752303423488), by norm_num⟩
  | 5 => ⟨((298024936400507/36028797018963968), (-374421186585/9007199254740992)), (5877/144115188075855872), by norm_num⟩
  | 4 => ⟨((371979309608813/9007199254740992), (-4483564390847/18014398509481984)), (2207/9007199254740992), by norm_num⟩
  | 3 => ⟨((742304942663993/4503599627370496), (-5587881687589/4503599627370496)), (11057/9007199254740992), by norm_num⟩
  | 2 => ⟨((69333119050167/140737488355328), (-11126175495277/2251799813685248)), (22181/4503599627370496), by norm_num⟩
  | 1 => ⟨((68818435975309/70368744177664), (-16565759927765/1125899906842624)), (1045/70368744177664), by norm_num⟩
  | 0 => ⟨((134561366040145/140737488355328), (-65280594680761/2251799813685248)), (67557/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((134561366040145/140737488355328), (-65280594680761/2251799813685248)), (257709511763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028303957315377/1125899906842624), (-124831643633971/2251799813685248)), (133103/2251799813685248), by norm_num⟩
  | 2 => ⟨((467853886217895/562949953421312), (-228021820353411/2251799813685248)), (257889/2251799813685248), by norm_num⟩
  | 3 => ⟨((766098782418669/1125899906842624), (-379006674204241/2251799813685248)), (480881/2251799813685248), by norm_num⟩
  | 4 => ⟨((978765210480729/2251799813685248), (-515776846364023/2251799813685248)), (204073/562949953421312), by norm_num⟩
  | 5 => ⟨((614580015325367/4503599627370496), (-896748335308519/4503599627370496)), (1083563/2251799813685248), by norm_num⟩
  | 6 => ⟨((-47345347824609/2251799813685248), (-978992186263573/18014398509481984)), (2908997/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-110027307715/1073741824)), (1/536870912), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile060Terms3
