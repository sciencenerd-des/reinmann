/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile056Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨56,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78161/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78161/2560))
  have he : value ((69/80), (78161/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-715655399/268435456), (-3166686009/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((310612185507919/4503599627370496), (-158414692238145/18014398509481984)), (10990541/18014398509481984), by norm_num⟩
  | 1 => ⟨((-29300398313/137438953472), (1867929607/68719476736)), (261/137438953472), by norm_num⟩
  | 2 => ⟨((22642193771/68719476736), (-1443462429/34359738368)), (51/17179869184), by norm_num⟩
  | 3 => ⟨((-11664663697/34359738368), (2974535765/68719476736)), (53/17179869184), by norm_num⟩
  | 4 => ⟨((18027985345/68719476736), (-1149302041/34359738368)), (83/34359738368), by norm_num⟩
  | 5 => ⟨((-5572526805/34359738368), (88813535/4294967296)), (207/137438953472), by norm_num⟩
  | 6 => ⟨((11483277951/137438953472), (-732070419/68719476736)), (215/274877906944), by norm_num⟩
  | 7 => ⟨((-20283028371/549755813888), (2586126565/549755813888)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((3918481361/274877906944), (-1998456751/1099511627776)), (75/549755813888), by norm_num⟩
  | 9 => ⟨((-21532786203/4398046511104), (1372736591/2199023255552)), (13/274877906944), by norm_num⟩
  | 10 => ⟨((26623502517/17592186044416), (-106079677/549755813888)), (259/17592186044416), by norm_num⟩
  | 11 => ⟨((-29925227831/70368744177664), (1907763113/35184372088832)), (293/70368744177664), by norm_num⟩
  | 12 => ⟨((1927086451/17592186044416), (-491414731/35184372088832)), (153/140737488355328), by norm_num⟩
  | 13 => ⟨((-1832832625/70368744177664), (934759259/281474976710656)), (293/1125899906842624), by norm_num⟩
  | 14 => ⟨((3237350545/562949953421312), (-825537301/1125899906842624)), (261/4503599627370496), by norm_num⟩
  | 15 => ⟨((-10673907169/9007199254740992), (680472225/4503599627370496)), (217/18014398509481984), by norm_num⟩
  | 16 => ⟨((16496750101/72057594037927936), (-262921067/9007199254740992)), (169/72057594037927936), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (-165194256673/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777857816128911/633825300114114700748351602688), (-97654000181/316912650057057350374175801344)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472179321864683/9903520314283042199192993792), (-219671095925/39614081257132168796771975168)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888428657464975/2475880078570760549798248448), (-116668552967/1237940039285380274899124224)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770095280099613/154742504910672534362390528), (-233265780433/154742504910672534362390528)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387131719329719/2417851639229258349412352), (-27326364581/1208925819614629174706176)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628945425080243/302231454903657293676544), (-5975276071/18889465931478580854784)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886333807861469/75557863725914323419136), (-310572458549/75557863725914323419136)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296446424182511/4722366482869645213696), (-116402628795/2361183241434822606848)), (13779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404986563123315/147573952589676412928), (-159952863483/295147905179352825856)), (18945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910799434000081/36893488147419103232), (-199790073387/36893488147419103232)), (11841/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820548827297211/9223372036854775808), (-449112790629/9223372036854775808)), (6661/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591800015885565/1152921504606846976), (-56074348095/144115188075855872)), (13323/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192671162119865/144115188075855872), (-24496155407/9007199254740992)), (23317/144115188075855872), by norm_num⟩
  | 4 => ⟨((372194754314581/9007199254740992), (-586745842543/36028797018963968)), (17489/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485695207151103/9007199254740992), (-731403521611/9007199254740992)), (43729/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110427281824471/2251799813685248), (-1456738741127/4503599627370496)), (21869/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102770857769343/1125899906842624), (-2170000318413/2251799813685248)), (131265/2251799813685248), by norm_num⟩
  | 0 => ⟨((16874375669093/17592186044416), (-4279945742289/2251799813685248)), (262741/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((16874375669093/17592186044416), (-4279945742289/2251799813685248)), (1002277382857512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071781172588955/2251799813685248), (-4105311990015/1125899906842624)), (505041/2251799813685248), by norm_num⟩
  | 2 => ⟨((1906124064253911/2251799813685248), (-15108462194243/2251799813685248)), (933015/2251799813685248), by norm_num⟩
  | 3 => ⟨((1613411929700869/2251799813685248), (-25578298023913/2251799813685248)), (1592095/2251799813685248), by norm_num⟩
  | 4 => ⟨((288929303323835/562949953421312), (-36653641165097/2251799813685248)), (2317639/2251799813685248), by norm_num⟩
  | 5 => ⟨((592565457900423/2251799813685248), (-75248685548341/4503599627370496)), (4908937/4503599627370496), by norm_num⟩
  | 6 => ⟨((310612185507919/4503599627370496), (-158414692238145/18014398509481984)), (10990541/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-3166686009/33554432)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-725947119/268435456), (-25697804711/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((26122250044443/4503599627370496), (-1200858015488587/18014398509481984)), (23824145/18014398509481984), by norm_num⟩
  | 1 => ⟨((-624894439/34359738368), (897713509/4294967296)), (143/34359738368), by norm_num⟩
  | 2 => ⟨((1959352899/68719476736), (-2814775515/8589934592)), (225/34359738368), by norm_num⟩
  | 3 => ⟨((-2047846561/68719476736), (23535232923/68719476736)), (473/68719476736), by norm_num⟩
  | 4 => ⟨((802626381/34359738368), (-18448646675/68719476736)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((-503326075/34359738368), (2892281247/17179869184)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((1052117331/137438953472), (-6045820747/68719476736)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-1885090175/549755813888), (21664726837/549755813888)), (443/549755813888), by norm_num⟩
  | 8 => ⟨((1477672335/1099511627776), (-8491203211/549755813888)), (349/1099511627776), by norm_num⟩
  | 9 => ⟨((-2059214693/4398046511104), (23665883159/4398046511104)), (61/549755813888), by norm_num⟩
  | 10 => ⟨((80708197/549755813888), (-29681695903/17592186044416)), (615/17592186044416), by norm_num⟩
  | 11 => ⟨((-1472349585/35184372088832), (8460616893/17592186044416)), (11/1099511627776), by norm_num⟩
  | 12 => ⟨((1538847869/140737488355328), (-17685476887/140737488355328)), (369/140737488355328), by norm_num⟩
  | 13 => ⟨((-23197349/8796093022208), (17062372457/562949953421312)), (179/281474976710656), by norm_num⟩
  | 14 => ⟨((2660028475/4503599627370496), (-30570840085/4503599627370496)), (161/1125899906842624), by norm_num⟩
  | 15 => ⟨((-2224134373/18014398509481984), (12780625635/9007199254740992)), (541/18014398509481984), by norm_num⟩
  | 16 => ⟨((1743440115/72057594037927936), (-20036788877/72057594037927936)), (213/36028797018963968), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (-483269890845/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888897995658103/316912650057057350374175801344), (-2285321531679/633825300114114700748351602688)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944323799053783/19807040628566084398385987584), (-2570384958481/39614081257132168796771975168)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888354428085033/2475880078570760549798248448), (-2730280660577/2475880078570760549798248448)), (13815/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770020843484569/154742504910672534362390528), (-2729433510843/154742504910672534362390528)), (13817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548456872997003/9671406556917033397649408), (-2557944154919/9671406556917033397649408)), (3239/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257829376599861/604462909807314587353088), (-559325437771/151115727451828646838272)), (11339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471558375424771/18889465931478580854784), (-227120612529/4722366482869645213696)), (9215/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296370834846467/4722366482869645213696), (-42562082795/73786976294838206464)), (13827/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202480216684993/73786976294838206464), (-467883681543/73786976294838206464)), (19019/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910733672610673/36893488147419103232), (-2337624344197/36893488147419103232)), (23783/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910199832421063/4611686018427387904), (-2627362679849/4611686018427387904)), (13385/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198956169740041/144115188075855872), (-2624284987889/576460752303423488)), (26787/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596268829481091/72057594037927936), (-1146395672963/36028797018963968)), (11729/72057594037927936), by norm_num⟩
  | 4 => ⟨((744287710072395/18014398509481984), (-6864563862557/36028797018963968)), (17613/18014398509481984), by norm_num⟩
  | 3 => ⟨((371358722411537/2251799813685248), (-8556586221595/9007199254740992)), (11025/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220316577105445/4503599627370496), (-4260253265977/1125899906842624)), (44203/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204691746497397/2251799813685248), (-25381807073497/2251799813685248)), (133125/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158050514661591/2251799813685248), (-50048866707371/2251799813685248)), (33541/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158050514661591/2251799813685248), (-50048866707371/2251799813685248)), (127948762060069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1033545945444129/1125899906842624), (-47965179630825/1125899906842624)), (263121/1125899906842624), by norm_num⟩
  | 2 => ⟨((236681022089287/281474976710656), (-2751921853169/35184372088832)), (505495/1125899906842624), by norm_num⟩
  | 3 => ⟨((1578349312254909/2251799813685248), (-148094767818721/1125899906842624)), (1858351/2251799813685248), by norm_num⟩
  | 4 => ⟨((133418737750769/281474976710656), (-415215017808685/2251799813685248)), (6043/4398046511104), by norm_num⟩
  | 5 => ⟨((53669974148167/281474976710656), (-196811326600247/1125899906842624)), (8148291/4503599627370496), by norm_num⟩
  | 6 => ⟨((26122250044443/4503599627370496), (-1200858015488587/18014398509481984)), (23824145/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-25697804711/268435456)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-735800759/268435456), (-13023306865/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-544105458295921/9007199254740992), (-407339671686009/18014398509481984)), (25869611/18014398509481984), by norm_num⟩
  | 1 => ⟨((13192721831/68719476736), (2469153221/34359738368)), (315/68719476736), by norm_num⟩
  | 2 => ⟨((-10481795037/34359738368), (-1961775463/17179869184)), (251/34359738368), by norm_num⟩
  | 3 => ⟨((22207805911/68719476736), (4156418683/34359738368)), (267/34359738368), by norm_num⟩
  | 4 => ⟨((-4411100165/17179869184), (-3302330579/34359738368)), (213/34359738368), by norm_num⟩
  | 5 => ⟨((22429942041/137438953472), (8395987477/137438953472)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((-5940296935/68719476736), (-4447150027/137438953472)), (579/274877906944), by norm_num⟩
  | 7 => ⟨((10787761959/274877906944), (2019040311/137438953472)), (33/34359738368), by norm_num⟩
  | 8 => ⟨((-4285511027/274877906944), (-3208309397/549755813888)), (421/1099511627776), by norm_num⟩
  | 9 => ⟨((6053148771/1099511627776), (9063271083/4398046511104)), (597/4398046511104), by norm_num⟩
  | 10 => ⟨((-7694893055/4398046511104), (-1440178169/2199023255552)), (381/8796093022208), by norm_num⟩
  | 11 => ⟨((4446324427/8796093022208), (6657401813/35184372088832)), (221/17592186044416), by norm_num⟩
  | 12 => ⟨((-18840877835/140737488355328), (-7052527111/140737488355328)), (235/70368744177664), by norm_num⟩
  | 13 => ⟨((18423791991/562949953421312), (6896403323/562949953421312)), (461/562949953421312), by norm_num⟩
  | 14 => ⟨((-2091135811/281474976710656), (-6262040285/2251799813685248)), (105/562949953421312), by norm_num⟩
  | 15 => ⟨((14177583305/9007199254740992), (5306960297/9007199254740992)), (179/4503599627370496), by norm_num⟩
  | 16 => ⟨((-2816070183/9007199254740992), (-4216451375/36028797018963968)), (571/72057594037927936), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-453214061473/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777732410400315/633825300114114700748351602688), (-2143061384847/316912650057057350374175801344)), (11579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944287850267439/19807040628566084398385987584), (-2410363045251/19807040628566084398385987584)), (13029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888277539011333/2475880078570760549798248448), (-5120587227257/2475880078570760549798248448)), (1731/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442485848732237/38685626227668133590597632), (-2559487046785/77371252455336267181195264)), (3463/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387095917759893/2417851639229258349412352), (-4797324733571/9671406556917033397649408)), (12991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628882365763901/302231454903657293676544), (-2097973098391/302231454903657293676544)), (2843/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886127342134087/75557863725914323419136), (-3407600966313/37778931862957161709568)), (2311/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296290243990065/4722366482869645213696), (-5108593276895/4722366482869645213696)), (6937/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619729345175285/590295810358705651712), (-7019754603333/590295810358705651712)), (19089/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821324500036709/73786976294838206464), (-8767855249723/73786976294838206464)), (2985/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820235725791121/9223372036854775808), (-4927220475873/4611686018427387904)), (13445/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795740690425815/576460752303423488), (-9842704774657/1152921504606846976)), (13461/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192386149649803/144115188075855872), (-537448497593/9007199254740992)), (11797/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488339130841161/36028797018963968), (-6436206858989/18014398509481984)), (4433/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485123808703433/9007199254740992), (-16044474477001/9007199254740992)), (22229/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109823778260491/2251799813685248), (-15975550921999/2251799813685248)), (89299/4503599627370496), by norm_num⟩
  | 1 => ⟨((550893028096369/562949953421312), (-47583018197855/2251799813685248)), (134915/2251799813685248), by norm_num⟩
  | 0 => ⟨((538838265997823/562949953421312), (-93797397690915/2251799813685248)), (68429/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((538838265997823/562949953421312), (-93797397690915/2251799813685248)), (261035921336936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1029565072894881/1125899906842624), (-22444991255313/281474976710656)), (546789/2251799813685248), by norm_num⟩
  | 2 => ⟨((467156889707809/562949953421312), (-328392659666595/2251799813685248)), (271803/562949953421312), by norm_num⟩
  | 3 => ⟨((751382781483275/1125899906842624), (-545024979788599/2251799813685248)), (265191/281474976710656), by norm_num⟩
  | 4 => ⟨((435485449622377/1125899906842624), (-181864472499981/562949953421312)), (3858643/2251799813685248), by norm_num⟩
  | 5 => ⟨((203743977785175/4503599627370496), (-281372548645431/1125899906842624)), (10956155/4503599627370496), by norm_num⟩
  | 6 => ⟨((-544105458295921/9007199254740992), (-407339671686009/18014398509481984)), (25869611/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-13023306865/134217728)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-745252095/268435456), (-13190590803/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-707622281521233/18014398509481984), (870400057892167/18014398509481984)), (12854377/9007199254740992), by norm_num⟩
  | 1 => ⟨((1086115005/8589934592), (-2671918587/17179869184)), (317/68719476736), by norm_num⟩
  | 2 => ⟨((-6992138665/34359738368), (17201148291/68719476736)), (1/134217728), by norm_num⟩
  | 3 => ⟨((7502275371/34359738368), (-18456120131/68719476736)), (551/68719476736), by norm_num⟩
  | 4 => ⟨((-12074446411/68719476736), (14851989727/68719476736)), (223/34359738368), by norm_num⟩
  | 5 => ⟨((3886614365/34359738368), (-9561342137/68719476736)), (289/68719476736), by norm_num⟩
  | 6 => ⟨((-1042544085/17179869184), (10258924353/137438953472)), (39/17179869184), by norm_num⟩
  | 7 => ⟨((15340891207/549755813888), (-9434915311/274877906944)), (9/8589934592), by norm_num⟩
  | 8 => ⟨((-12345105959/1099511627776), (7592455201/549755813888)), (465/1099511627776), by norm_num⟩
  | 9 => ⟨((8830525139/2199023255552), (-5430926777/1099511627776)), (167/1099511627776), by norm_num⟩
  | 10 => ⟨((-2842436389/2199023255552), (13985183127/8796093022208)), (27/549755813888), by norm_num⟩
  | 11 => ⟨((13308290583/35184372088832), (-16369661045/35184372088832)), (127/8796093022208), by norm_num⟩
  | 12 => ⟨((-7139622471/70368744177664), (17563968733/140737488355328)), (547/140737488355328), by norm_num⟩
  | 13 => ⟨((1767812167/70368744177664), (-17395764413/562949953421312)), (17/17592186044416), by norm_num⟩
  | 14 => ⟨((-13006555079/2251799813685248), (1999814483/281474976710656)), (251/1125899906842624), by norm_num⟩
  | 15 => ⟨((11164396189/9007199254740992), (-13732596253/9007199254740992)), (433/9007199254740992), by norm_num⟩
  | 16 => ⟨((-280756289/1125899906842624), (11050880523/36028797018963968)), (175/18014398509481984), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (2935311627421/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888840795198591/316912650057057350374175801344), (1734883028647/316912650057057350374175801344)), (11569/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472129682029525/9903520314283042199192993792), (3902542548143/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944108636425409/1237940039285380274899124224), (4145276389177/2475880078570760549798248448)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884941714434751/77371252455336267181195264), (4143954906739/154742504910672534362390528)), (6919/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774163885731279/4835703278458516698824704), (1941777058451/4835703278458516698824704)), (12977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628858068858171/302231454903657293676544), (849176692279/151115727451828646838272)), (11359/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235756121678953/9444732965739290427392), (5517018834197/75557863725914323419136)), (577/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296231988568731/4722366482869645213696), (1033866070813/1180591620717411303424)), (13855/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809825044816469/295147905179352825856), (2841264117785/295147905179352825856)), (4765/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821226697118099/73786976294838206464), (887195152469/9223372036854775808)), (745/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820127435737697/9223372036854775808), (7977063583215/9223372036854775808)), (26841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591375258760755/1152921504606846976), (3983728250317/576460752303423488)), (26867/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192295725152737/144115188075855872), (1740182176387/36028797018963968)), (11769/72057594037927936), by norm_num⟩
  | 4 => ⟨((744104171111831/18014398509481984), (10419532160307/36028797018963968)), (35367/36028797018963968), by norm_num⟩
  | 3 => ⟨((742484385010723/4503599627370496), (12986752345433/9007199254740992)), (5539/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219362672256911/4503599627370496), (25860790696089/4503599627370496)), (44467/2251799813685248), by norm_num⟩
  | 1 => ⟨((17212556654667/17592186044416), (38510360717507/2251799813685248)), (134185/2251799813685248), by norm_num⟩
  | 0 => ⟨((269358764700853/281474976710656), (75903167391079/2251799813685248)), (271517/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((269358764700853/281474976710656), (75903167391079/2251799813685248)), (1035755166060637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059554275095565/2251799813685248), (145271765499495/2251799813685248)), (134491/562949953421312), by norm_num⟩
  | 2 => ⟨((1874349531677789/2251799813685248), (132869309192947/1125899906842624)), (1053485/2251799813685248), by norm_num⟩
  | 3 => ⟨((1528807815276025/2251799813685248), (110597543328051/562949953421312)), (2002445/2251799813685248), by norm_num⟩
  | 4 => ⟨((951036702992281/2251799813685248), (300350657394427/1125899906842624)), (438229/281474976710656), by norm_num⟩
  | 5 => ⟨((482839315951163/4503599627370496), (507406559346819/2251799813685248)), (4831809/2251799813685248), by norm_num⟩
  | 6 => ⟨((-707622281521233/18014398509481984), (870400057892167/18014398509481984)), (12854377/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-13190590803/134217728)), (1/134217728), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-754332693/268435456), (-13351312871/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((533995825170825/18014398509481984), (943852257925951/18014398509481984)), (18046729/18014398509481984), by norm_num⟩
  | 1 => ⟨((-51850377/536870912), (-5865405605/34359738368)), (113/34359738368), by norm_num⟩
  | 2 => ⟨((10811746163/68719476736), (597189303/2147483648)), (185/34359738368), by norm_num⟩
  | 3 => ⟨((-1467738031/8589934592), (-20754137607/68719476736)), (101/17179869184), by norm_num⟩
  | 4 => ⟨((9564064395/68719476736), (4226186493/17179869184)), (331/68719476736), by norm_num⟩
  | 5 => ⟨((-6232129019/68719476736), (-11015458865/68719476736)), (217/68719476736), by norm_num⟩
  | 6 => ⟨((1692073165/34359738368), (5981571399/68719476736)), (119/68719476736), by norm_num⟩
  | 7 => ⟨((-6300500253/274877906944), (-11136306895/274877906944)), (7/8589934592), by norm_num⟩
  | 8 => ⟨((10263819031/1099511627776), (9070790735/549755813888)), (367/1099511627776), by norm_num⟩
  | 9 => ⟨((-7431225167/2199023255552), (-6567447087/1099511627776)), (267/2199023255552), by norm_num⟩
  | 10 => ⟨((2421164899/2199023255552), (8558950647/4398046511104)), (175/4398046511104), by norm_num⟩
  | 11 => ⟨((-1434252541/4398046511104), (-10140322717/17592186044416)), (417/35184372088832), by norm_num⟩
  | 12 => ⟨((6230577651/70368744177664), (2753179195/17592186044416)), (57/17592186044416), by norm_num⟩
  | 13 => ⟨((-6246099531/281474976710656), (-172502377/4398046511104)), (115/140737488355328), by norm_num⟩
  | 14 => ⟨((5814398645/1125899906842624), (20554217959/2251799813685248)), (431/2251799813685248), by norm_num⟩
  | 15 => ⟨((-10103398451/9007199254740992), (-4464508425/2251799813685248)), (47/1125899906842624), by norm_num⟩
  | 16 => ⟨((8229461879/36028797018963968), (14545799443/36028797018963968)), (77/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (687734854677/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777634545171225/633825300114114700748351602688), (1625821024397/633825300114114700748351602688)), (5773/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236058261310547/4951760157141521099596496896), (1828606436913/39614081257132168796771975168)), (12991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888161732311567/2475880078570760549798248448), (1942337646883/2475880078570760549798248448)), (3451/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769828323135197/154742504910672534362390528), (1941711691183/154742504910672534362390528)), (13805/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774138285716871/4835703278458516698824704), (454922476191/2417851639229258349412352)), (12945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257671798856871/604462909807314587353088), (1591564167315/604462909807314587353088)), (177/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((942988893277401/37778931862957161709568), (2585046486291/75557863725914323419136)), (4603/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648089676647255/2361183241434822606848), (1937695890133/4722366482869645213696)), (3453/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202447367637751/73786976294838206464), (2662563483767/590295810358705651712)), (18995/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455284898978533/18446744073709551616), (3325553937785/73786976294838206464)), (23751/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820031964401195/9223372036854775808), (3737607316325/9223372036854775808)), (13365/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198910365879499/144115188075855872), (1866530710419/576460752303423488)), (13371/576460752303423488), by norm_num⟩
  | 5 => ⟨((596109228477961/72057594037927936), (3261321730435/144115188075855872)), (23413/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488099459101939/36028797018963968), (4881786343529/36028797018963968)), (35147/36028797018963968), by norm_num⟩
  | 3 => ⟨((371211223418135/2251799813685248), (6084429408245/9007199254740992)), (43983/9007199254740992), by norm_num⟩
  | 2 => ⟨((554787844728817/1125899906842624), (12115607582459/4503599627370496)), (88113/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101490340873267/1125899906842624), (9020419683349/1125899906842624)), (33135/562949953421312), by norm_num⟩
  | 0 => ⟨((2154773811778729/2251799813685248), (35554714605797/2251799813685248)), (33321/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154773811778729/2251799813685248), (35554714605797/2251799813685248)), (127109528661632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2061367095772197/2251799813685248), (34022725933375/1125899906842624)), (518583/2251799813685248), by norm_num⟩
  | 2 => ⟨((942491444891347/1125899906842624), (124581816414233/2251799813685248)), (980797/2251799813685248), by norm_num⟩
  | 3 => ⟨((1571027692733849/2251799813685248), (407373080267/4398046511104)), (875289/1125899906842624), by norm_num⟩
  | 4 => ⟨((269187391663789/562949953421312), (291035753604659/2251799813685248)), (2766973/2251799813685248), by norm_num⟩
  | 5 => ⟨((954514529119729/4503599627370496), (278330799807745/2251799813685248)), (3361423/2251799813685248), by norm_num⟩
  | 6 => ⟨((533995825170825/18014398509481984), (943852257925951/18014398509481984)), (18046729/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-13351312871/134217728)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-763070545/268435456), (-13505968487/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((65302514465065/1125899906842624), (-12621803404387/2251799813685248)), (8978977/18014398509481984), by norm_num⟩
  | 1 => ⟨((-6568189533/34359738368), (2539026183/137438953472)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((10823840603/34359738368), (-261506753/8589934592)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((-11891204297/34359738368), (2298356259/68719476736)), (211/68719476736), by norm_num⟩
  | 4 => ⟨((612366711/2147483648), (-946875911/34359738368)), (11/4294967296), by norm_num⟩
  | 5 => ⟨((-25833738005/137438953472), (624149707/34359738368)), (117/68719476736), by norm_num⟩
  | 6 => ⟨((28381262035/274877906944), (-342849269/34359738368)), (259/274877906944), by norm_num⟩
  | 7 => ⟨((-26725717063/549755813888), (2582800595/549755813888)), (123/274877906944), by norm_num⟩
  | 8 => ⟨((5505225223/274877906944), (-2128122355/1099511627776)), (205/1099511627776), by norm_num⟩
  | 9 => ⟨((-8064144109/1099511627776), (1558654247/2199023255552)), (19/274877906944), by norm_num⟩
  | 10 => ⟨((10631241379/4398046511104), (-2054828051/8796093022208)), (101/4398046511104), by norm_num⟩
  | 11 => ⟨((-25482790741/35184372088832), (2462682925/35184372088832)), (61/8796093022208), by norm_num⟩
  | 12 => ⟨((13997853529/70368744177664), (-2705533725/140737488355328)), (135/70368744177664), by norm_num⟩
  | 13 => ⟨((-14195274371/281474976710656), (2743691629/562949953421312)), (69/140737488355328), by norm_num⟩
  | 14 => ⟨((13367231027/1125899906842624), (-322955715/281474976710656)), (131/1125899906842624), by norm_num⟩
  | 15 => ⟨((-23496646835/9007199254740992), (1135369975/4503599627370496)), (29/1125899906842624), by norm_num⟩
  | 16 => ⟨((19360278717/36028797018963968), (-935498555/18014398509481984)), (193/36028797018963968), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (-62747999679/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888792917090645/316912650057057350374175801344), (-148329736797/633825300114114700748351602688)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472102845152957/9903520314283042199192993792), (-20853788311/4951760157141521099596496896)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051861667031/1237940039285380274899124224), (-88602919805/1237940039285380274899124224)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442442612323179/38685626227668133590597632), (-177148091199/154742504910672534362390528)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548222458172737/9671406556917033397649408), (-166015004437/9671406556917033397649408)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257624593090663/604462909807314587353088), (-72600913897/302231454903657293676544)), (1413/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885901345667695/75557863725914323419136), (-235838094279/75557863725914323419136)), (18369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296122257277825/4722366482869645213696), (-44194529481/1180591620717411303424)), (13777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619500814869971/590295810358705651712), (-121453397779/295147905179352825856)), (37/1152921504606846976), by norm_num⟩
  | 8 => ⟨((910521254206757/36893488147419103232), (-151694513985/36893488147419103232)), (185/576460752303423488), by norm_num⟩
  | 7 => ⟨((1819923523655463/9223372036854775808), (-340976853389/9223372036854775808)), (26641/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591175462476099/1152921504606846976), (-170278803229/576460752303423488)), (13321/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192125520683639/144115188075855872), (-4648702327/2251799813685248)), (23313/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487962237667205/36028797018963968), (-13916726479/1125899906842624)), (34973/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484677170341395/9007199254740992), (-555027652467/9007199254740992)), (43721/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218827275906547/4503599627370496), (-552573326075/2251799813685248)), (87457/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202522653848499/2251799813685248), (-1645502659485/2251799813685248)), (65613/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153968875677511/2251799813685248), (-3242460549129/2251799813685248)), (131313/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153968875677511/2251799813685248), (-3242460549129/2251799813685248)), (500919346335982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515095899693233/562949953421312), (-193849356107/70368744177664)), (503189/2251799813685248), by norm_num⟩
  | 2 => ⟨((1885221798517861/2251799813685248), (-709484087401/140737488355328)), (923603/2251799813685248), by norm_num⟩
  | 3 => ⟨((789131508468117/1125899906842624), (-9503756837645/1125899906842624)), (777903/1125899906842624), by norm_num⟩
  | 4 => ⟨((1106027653930995/2251799813685248), (-6661084101549/562949953421312)), (2207163/2251799813685248), by norm_num⟩
  | 5 => ⟨((1085875612181275/4503599627370496), (-52348122078693/4503599627370496)), (4440879/4503599627370496), by norm_num⟩
  | 6 => ⟨((65302514465065/1125899906842624), (-12621803404387/2251799813685248)), (8978977/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-13505968487/134217728)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile056Terms3
