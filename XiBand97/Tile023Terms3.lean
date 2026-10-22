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
namespace Reinmann.XiBand97.Tile023Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28967/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28967/1280))
  have he : value ((69/80), (28967/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-586797723/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((209768505422441/4503599627370496), (-29059626189169/562949953421312)), (296328235/18014398509481984), by norm_num⟩
  | 1 => ⟨((-618365627/4294967296), (685306841/4294967296)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((477848601/2147483648), (-529578135/2147483648)), (343/4294967296), by norm_num⟩
  | 3 => ⟨((-61543763/268435456), (545649499/2147483648)), (89/1073741824), by norm_num⟩
  | 4 => ⟨((760937537/4294967296), (-843312883/4294967296)), (277/4294967296), by norm_num⟩
  | 5 => ⟨((-940836093/8589934592), (1042686369/8589934592)), (345/8589934592), by norm_num⟩
  | 6 => ⟨((484694051/8589934592), (-1074329277/17179869184)), (179/8589934592), by norm_num⟩
  | 7 => ⟨((-6688437/268435456), (474399629/17179869184)), (159/17179869184), by norm_num⟩
  | 8 => ⟨((661575767/68719476736), (-733194697/68719476736)), (31/8589934592), by norm_num⟩
  | 9 => ⟨((-454435285/137438953472), (3934611/1073741824)), (343/274877906944), by norm_num⟩
  | 10 => ⟨((561871503/549755813888), (-311348471/274877906944)), (107/274877906944), by norm_num⟩
  | 11 => ⟨((-631552243/2199023255552), (43745061/137438953472)), (121/1099511627776), by norm_num⟩
  | 12 => ⟨((650718265/8796093022208), (-721161817/8796093022208)), (251/8796093022208), by norm_num⟩
  | 13 => ⟨((-618891625/35184372088832), (342944891/17592186044416)), (241/35184372088832), by norm_num⟩
  | 14 => ⟨((546577225/140737488355328), (-605746981/140737488355328)), (107/70368744177664), by norm_num⟩
  | 15 => ⟨((-450531575/562949953421312), (998607805/1125899906842624)), (355/1125899906842624), by norm_num⟩
  | 16 => ⟨((10879783/70368744177664), (-192921195/1125899906842624)), (69/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-1089896848241/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777856946082609/633825300114114700748351602688), (-322144332265/158456325028528675187087900672)), (184653/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472179065268035/9903520314283042199192993792), (-362329058055/9903520314283042199192993792)), (25969/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888427503167175/2475880078570760549798248448), (-1539479902199/2475880078570760549798248448)), (55189/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221261756769421/19342813113834066795298816), (-1539009216039/154742504910672534362390528)), (220777/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193565706491739/1208925819614629174706176), (-360580308267/2417851639229258349412352)), (207001/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257889701956377/604462909807314587353088), (-1261531393769/604462909807314587353088)), (181149/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886331799692853/75557863725914323419136), (-512263019071/18889465931478580854784)), (294409/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296444793659655/4722366482869645213696), (-767985072135/2361183241434822606848)), (55211/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619943808658211/590295810358705651712), (-263828637133/73786976294838206464)), (303721/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910797755446563/36893488147419103232), (-2636293137123/73786976294838206464)), (379743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820544635659731/9223372036854775808), (-2963091587067/9223372036854775808)), (53417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591795306814069/1152921504606846976), (-1479836300171/576460752303423488)), (427493/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298166615297495/36028797018963968), (-2585872320261/144115188075855872)), (187117/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488770808922145/36028797018963968), (-3871138939713/36028797018963968)), (70213/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485682931156097/9007199254740992), (-4825530884697/9007199254740992)), (21961/281474976710656), by norm_num⟩
  | 2 => ⟨((2220824001100989/4503599627370496), (-9610998775445/4503599627370496)), (87961/281474976710656), by norm_num⟩
  | 1 => ⟨((2205480971348333/2251799813685248), (-14316743375341/2251799813685248)), (2115769/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079869873758367/1125899906842624), (-28236874856245/2251799813685248)), (4250493/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079869873758367/1125899906842624), (-28236874856245/2251799813685248)), (16214344033248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071089280476279/2251799813685248), (-54164940064439/2251799813685248)), (4130021/1125899906842624), by norm_num⟩
  | 2 => ⟨((118973635581431/140737488355328), (-24909058536937/562949953421312)), (15591697/2251799813685248), by norm_num⟩
  | 3 => ⟨((1604797391637289/2251799813685248), (-10528542493127/140737488355328)), (6935233/562949953421312), by norm_num⟩
  | 4 => ⟨((565546945986711/1125899906842624), (-240109124131217/2251799813685248)), (21845513/1125899906842624), by norm_num⟩
  | 5 => ⟨((542553113977339/2251799813685248), (-120608396031189/1125899906842624)), (53210119/2251799813685248), by norm_num⟩
  | 6 => ⟨((209768505422441/4503599627370496), (-29059626189169/562949953421312)), (296328235/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-586797723/8388608)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-297618181/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1264404974427/70368744177664), (-145140244879211/2251799813685248)), (209536883/9007199254740992), by norm_num⟩
  | 1 => ⟨((120987991/2147483648), (868008419/4294967296)), (315/4294967296), by norm_num⟩
  | 2 => ⟨((-189678573/2147483648), (-170102211/536870912)), (31/268435456), by norm_num⟩
  | 3 => ⟨((49561339/536870912), (1422278663/4294967296)), (65/536870912), by norm_num⟩
  | 4 => ⟨((-310798583/4294967296), (-557443315/2147483648)), (205/2147483648), by norm_num⟩
  | 5 => ⟨((24362679/536870912), (174786029/1073741824)), (129/2147483648), by norm_num⟩
  | 6 => ⟨((-25463013/1073741824), (-730720777/8589934592)), (271/8589934592), by norm_num⟩
  | 7 => ⟨((5702795/536870912), (163655055/4294967296)), (61/4294967296), by norm_num⟩
  | 8 => ⟨((-71524323/17179869184), (-1026278957/68719476736)), (385/68719476736), by norm_num⟩
  | 9 => ⟨((398691735/274877906944), (178771763/34359738368)), (539/274877906944), by norm_num⟩
  | 10 => ⟨((-125009563/274877906944), (-448430263/274877906944)), (339/549755813888), by norm_num⟩
  | 11 => ⟨((17816671/137438953472), (1022582179/2199023255552)), (97/549755813888), by norm_num⟩
  | 12 => ⟨((-297941701/8796093022208), (-267191709/2199023255552)), (51/1099511627776), by norm_num⟩
  | 13 => ⟨((287444455/35184372088832), (32222233/1099511627776)), (395/35184372088832), by norm_num⟩
  | 14 => ⟨((-257508693/140737488355328), (-923726859/140737488355328)), (355/140737488355328), by norm_num⟩
  | 15 => ⟨((430622409/1125899906842624), (772357393/562949953421312)), (149/281474976710656), by norm_num⟩
  | 16 => ⟨((-168776759/2251799813685248), (-1210861069/4503599627370496)), (469/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1200138741539/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777794473524759/633825300114114700748351602688), (-354706417545/79228162514264337593543950336)), (184959/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888645807755909/39614081257132168796771975168), (-3191607824039/39614081257132168796771975168)), (208115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236044051829499/309485009821345068724781056), (-3390147566781/2475880078570760549798248448)), (55291/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221252338135143/19342813113834066795298816), (-1694547636393/77371252455336267181195264)), (221211/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548454735589883/9671406556917033397649408), (-397019893429/1208925819614629174706176)), (207435/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157228421729837/75557863725914323419136), (-2778022023635/604462909807314587353088)), (45389/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886229998981817/75557863725914323419136), (-4512191917063/75557863725914323419136)), (295121/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324091997717495/1180591620717411303424), (-211394545975/295147905179352825856)), (221423/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202479683872487/73786976294838206464), (-4647706060647/590295810358705651712)), (304589/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227682686238639/9223372036854775808), (-2902587357687/36893488147419103232)), (47617/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820392354131555/9223372036854775808), (-3262348487815/4611686018427387904)), (107207/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795820572474239/576460752303423488), (-6517048714915/1152921504606846976)), (107293/288230376151711744), by norm_num⟩
  | 5 => ⟨((596264730221213/72057594037927936), (-711727948229/18014398509481984)), (375913/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488561105198267/36028797018963968), (-8523572908159/36028797018963968)), (141161/9007199254740992), by norm_num⟩
  | 3 => ⟨((23209585656529/140737488355328), (-5312244681273/4503599627370496)), (176791/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220263284202397/4503599627370496), (-21159278265619/4503599627370496)), (88651/281474976710656), by norm_num⟩
  | 1 => ⟨((1102292918397867/1125899906842624), (-31515469202655/2251799813685248)), (534469/562949953421312), by norm_num⟩
  | 0 => ⟨((1078868074683083/1125899906842624), (-31070975466919/1125899906842624)), (2158477/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078868074683083/1125899906842624), (-31070975466919/1125899906842624)), (8233936314109420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032943434834547/1125899906842624), (-119092232894929/2251799813685248)), (4255757/1125899906842624), by norm_num⟩
  | 2 => ⟨((1889024758099497/2251799813685248), (-109259748012217/1125899906842624)), (16517881/2251799813685248), by norm_num⟩
  | 3 => ⟨((1563488790243857/2251799813685248), (-366630049091281/2251799813685248)), (30919415/2251799813685248), by norm_num⟩
  | 4 => ⟨((1025881426173891/2251799813685248), (-254561692578991/1125899906842624)), (26502421/1125899906842624), by norm_num⟩
  | 5 => ⟨((352263142768307/2251799813685248), (-463895787973767/2251799813685248)), (72264585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1264404974427/70368744177664), (-145140244879211/2251799813685248)), (209536883/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-297618181/4194304)), (1/8388608), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-75414475/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-548529204228693/9007199254740992), (-95718182039305/4503599627370496)), (25770307/1125899906842624), by norm_num⟩
  | 1 => ⟨((415624461/2147483648), (9065793/134217728)), (157/2147483648), by norm_num⟩
  | 2 => ⟨((-660438455/2147483648), (-460985251/4294967296)), (501/4294967296), by norm_num⟩
  | 3 => ⟨((1399272641/4294967296), (244172657/2147483648)), (533/4294967296), by norm_num⟩
  | 4 => ⟨((-69483809/268435456), (-96999231/1073741824)), (425/4294967296), by norm_num⟩
  | 5 => ⟨((706634513/4294967296), (123307511/2147483648)), (271/4294967296), by norm_num⟩
  | 6 => ⟨((-1497148347/17179869184), (-522503877/17179869184)), (9/268435456), by norm_num⟩
  | 7 => ⟨((1359433725/34359738368), (118610389/8589934592)), (525/34359738368), by norm_num⟩
  | 8 => ⟨((-1080088389/68719476736), (-376950201/68719476736)), (419/68719476736), by norm_num⟩
  | 9 => ⟨((1525590685/274877906944), (133107559/68719476736)), (297/137438953472), by norm_num⟩
  | 10 => ⟨((-121210233/68719476736), (-169209195/274877906944)), (379/549755813888), by norm_num⟩
  | 11 => ⟨((280154651/549755813888), (195547611/1099511627776)), (55/274877906944), by norm_num⟩
  | 12 => ⟨((-1187128749/8796093022208), (-414307223/8796093022208)), (117/2199023255552), by norm_num⟩
  | 13 => ⟨((72553059/2199023255552), (405135587/35184372088832)), (115/8796093022208), by norm_num⟩
  | 14 => ⟨((-1054068695/140737488355328), (-11495917/4398046511104)), (419/140737488355328), by norm_num⟩
  | 15 => ⟨((446651607/281474976710656), (311762287/562949953421312)), (357/562949953421312), by norm_num⟩
  | 16 => ⟨((-709741425/2251799813685248), (-495398665/4503599627370496)), (569/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-1827440080983/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777732251236623/633825300114114700748351602688), (-2160301612287/316912650057057350374175801344)), (185251/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888575512803957/39614081257132168796771975168), (-4859506817911/39614081257132168796771975168)), (104231/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888277327886643/2475880078570760549798248448), (-5161780162263/2475880078570760549798248448)), (221555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884971585350139/77371252455336267181195264), (-5160153987557/154742504910672534362390528)), (221627/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548383446913973/9671406556917033397649408), (-604489628501/1208925819614629174706176)), (207851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314441130379975/151115727451828646838272), (-132178143691/18889465931478580854784)), (181945/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235765871855071/9444732965739290427392), (-6870026853965/75557863725914323419136)), (295803/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648144972885569/2361183241434822606848), (-2574844617221/2361183241434822606848)), (221977/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404932224552513/147573952589676412928), (-7076224602685/590295810358705651712)), (305421/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821323886050779/73786976294838206464), (-8838387334867/73786976294838206464)), (2985/576460752303423488), by norm_num⟩
  | 7 => ⟨((56882342474907/288230376151711744), (-2483428338083/2305843009213693952)), (215129/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591480519656237/1152921504606846976), (-9921881930165/1152921504606846976)), (215391/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192385289984441/144115188075855872), (-270885900649/4503599627370496)), (377523/144115188075855872), by norm_num⟩
  | 4 => ⟨((744168814935403/18014398509481984), (-6487979350923/18014398509481984)), (567465/36028797018963968), by norm_num⟩
  | 3 => ⟨((742560782067615/4503599627370496), (-16173530673017/9007199254740992)), (88925/1125899906842624), by norm_num⟩
  | 2 => ⟨((138727623074223/281474976710656), (-8052022287823/1125899906842624)), (357255/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203561009859785/2251799813685248), (-23982843289945/1125899906842624)), (2159127/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155320116049433/2251799813685248), (-94551485529083/2251799813685248)), (4380927/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155320116049433/2251799813685248), (-94551485529083/2251799813685248)), (16711910256392668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257375499758771/281474976710656), (-181000742183803/2251799813685248)), (547147/140737488355328), by norm_num⟩
  | 2 => ⟨((1868166153061889/2251799813685248), (-331007445284575/2251799813685248)), (17416993/2251799813685248), by norm_num⟩
  | 3 => ⟨((1501234179906879/2251799813685248), (-34326813929793/140737488355328)), (34019891/2251799813685248), by norm_num⟩
  | 4 => ⟨((433442513736581/1125899906842624), (-183080524460553/562949953421312)), (30978125/1125899906842624), by norm_num⟩
  | 5 => ⟨((47782665794999/1125899906842624), (-281925177384301/1125899906842624)), (176002997/4503599627370496), by norm_num⟩
  | 6 => ⟨((-548529204228693/9007199254740992), (-95718182039305/4503599627370496)), (25770307/1125899906842624), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-75414475/1048576)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1222130743/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-466665726985679/9007199254740992), (622268384008429/18014398509481984)), (410554803/18014398509481984), by norm_num⟩
  | 1 => ⟨((716275705/4294967296), (-477553525/4294967296)), (317/4294967296), by norm_num⟩
  | 2 => ⟨((-288200319/1073741824), (192148187/1073741824)), (513/4294967296), by norm_num⟩
  | 3 => ⟨((1236908053/4294967296), (-824668205/4294967296)), (553/4294967296), by norm_num⟩
  | 4 => ⟨((-497681679/2147483648), (663626137/4294967296)), (447/4294967296), by norm_num⟩
  | 5 => ⟨((320395105/2147483648), (-213613013/2147483648)), (289/4294967296), by norm_num⟩
  | 6 => ⟨((-171885343/2147483648), (229197921/4294967296)), (39/1073741824), by norm_num⟩
  | 7 => ⟨((632317229/17179869184), (-421576941/17179869184)), (9/536870912), by norm_num⟩
  | 8 => ⟨((-1017675321/68719476736), (84812739/8589934592)), (465/68719476736), by norm_num⟩
  | 9 => ⟨((363974499/68719476736), (-60667039/17179869184)), (335/137438953472), by norm_num⟩
  | 10 => ⟨((-937270973/549755813888), (624894929/549755813888)), (433/549755813888), by norm_num⟩
  | 11 => ⟨((1097075955/2199023255552), (-365719851/1099511627776)), (509/2199023255552), by norm_num⟩
  | 12 => ⟨((-588558545/4398046511104), (784804525/8796093022208)), (137/2199023255552), by norm_num⟩
  | 13 => ⟨((1165844229/35184372088832), (-97161089/4398046511104)), (545/35184372088832), by norm_num⟩
  | 14 => ⟨((-536101115/70368744177664), (178713989/35184372088832)), (503/140737488355328), by norm_num⟩
  | 15 => ⟨((460171445/281474976710656), (-613608681/562949953421312)), (217/281474976710656), by norm_num⟩
  | 16 => ⟨((-370308685/1125899906842624), (493782537/2251799813685248)), (351/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (207893146113/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777679755021347/633825300114114700748351602688), (3931933224037/633825300114114700748351602688)), (185175/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472129140884471/9903520314283042199192993792), (4422350259125/39614081257132168796771975168)), (52093/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888214838570849/2475880078570760549798248448), (2348707521227/1237940039285380274899124224)), (221453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769880843547931/154742504910672534362390528), (2347958435177/77371252455336267181195264)), (110759/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548325187378881/9671406556917033397649408), (2200415373077/4835703278458516698824704)), (103871/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257713716452543/604462909807314587353088), (1924568065801/302231454903657293676544)), (45461/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943022369423955/37778931862957161709568), (6251864683161/75557863725914323419136)), (295625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648114275215863/2361183241434822606848), (4686290838309/4722366482869645213696)), (27729/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809822468366783/295147905179352825856), (1609853654225/147573952589676412928)), (305203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910609809436849/36893488147419103232), (2010729791189/18446744073709551616)), (95445/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820118598411475/9223372036854775808), (2259890062245/2305843009213693952)), (429883/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198920666395391/144115188075855872), (4514332398625/576460752303423488)), (53795/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192285815526277/144115188075855872), (3943918557613/72057594037927936)), (188551/72057594037927936), by norm_num⟩
  | 4 => ⟨((744095520376437/18014398509481984), (11807298498627/36028797018963968)), (566727/36028797018963968), by norm_num⟩
  | 3 => ⟨((742471449209001/4503599627370496), (14716395015149/9007199254740992)), (710291/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219298274693289/4503599627370496), (29304893332161/4503599627370496)), (1426243/4503599627370496), by norm_num⟩
  | 1 => ⟨((34423114036813/35184372088832), (43638604216235/2251799813685248)), (538391/562949953421312), by norm_num⟩
  | 0 => ⟨((16831956618957/17592186044416), (86008295200981/2251799813685248)), (4364185/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((16831956618957/17592186044416), (86008295200981/2251799813685248)), (16648044594771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058101094147545/2251799813685248), (164583058641865/2251799813685248)), (4342283/1125899906842624), by norm_num⟩
  | 2 => ⟨((1869034940389107/2251799813685248), (150425704367839/1125899906842624)), (17144551/2251799813685248), by norm_num⟩
  | 3 => ⟨((377784474620787/562949953421312), (124856079873285/562949953421312)), (33041773/2251799813685248), by norm_num⟩
  | 4 => ⟨((451663839069667/1125899906842624), (670307379922121/2251799813685248)), (59003951/2251799813685248), by norm_num⟩
  | 5 => ⟨((162842588531183/2251799813685248), (1075596872270363/4503599627370496)), (164935955/4503599627370496), by norm_num⟩
  | 6 => ⟨((-466665726985679/9007199254740992), (622268384008429/18014398509481984)), (410554803/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1222130743/16777216)), (1/8388608), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-309255479/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-25764069781095/4503599627370496), (1079531413732157/18014398509481984)), (45310597/2251799813685248), by norm_num⟩
  | 1 => ⟨((20013291/1073741824), (-1677140027/8589934592)), (565/8589934592), by norm_num⟩
  | 2 => ⟨((-32602617/1073741824), (1366071029/4294967296)), (231/2147483648), by norm_num⟩
  | 3 => ⟨((141629965/4294967296), (-1483597097/4294967296)), (503/4294967296), by norm_num⟩
  | 4 => ⟨((-115361025/4294967296), (604212821/2147483648)), (103/1073741824), by norm_num⟩
  | 5 => ⟨((75171471/4294967296), (-98429185/536870912)), (539/8589934592), by norm_num⟩
  | 6 => ⟨((-163277273/17179869184), (1710356197/17179869184)), (587/17179869184), by norm_num⟩
  | 7 => ⟨((151992319/34359738368), (-1592144459/34359738368)), (549/34359738368), by norm_num⟩
  | 8 => ⟨((-30950353/17179869184), (162105011/8589934592)), (449/68719476736), by norm_num⟩
  | 9 => ⟨((44817439/68719476736), (-938940045/137438953472)), (653/274877906944), by norm_num⟩
  | 10 => ⟨((-58407817/274877906944), (305915731/137438953472)), (427/549755813888), by norm_num⟩
  | 11 => ⟨((8649923/137438953472), (-1449749795/2199023255552)), (127/549755813888), by norm_num⟩
  | 12 => ⟨((-37576379/2199023255552), (787237465/4398046511104)), (277/4398046511104), by norm_num⟩
  | 13 => ⟨((37669991/8796093022208), (-1578397329/35184372088832)), (557/35184372088832), by norm_num⟩
  | 14 => ⟨((-140265677/140737488355328), (367326491/35184372088832)), (65/17592186044416), by norm_num⟩
  | 15 => ⟨((121866431/562949953421312), (-1276570847/562949953421312)), (453/562949953421312), by norm_num⟩
  | 16 => ⟨((-99263149/2251799813685248), (259949441/562949953421312)), (371/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (1085057140455/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777632432947643/633825300114114700748351602688), (641275013067/158456325028528675187087900672)), (184905/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888463599606693/39614081257132168796771975168), (2885036427397/39614081257132168796771975168)), (208051/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888158931071393/2475880078570760549798248448), (1496324465/1208925819614629174706176)), (221093/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884912674047687/77371252455336267181195264), (3063484414487/154742504910672534362390528)), (221135/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548273597830789/9671406556917033397649408), (1435483595907/4835703278458516698824704)), (207359/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257669012630241/604462909807314587353088), (1255523647301/302231454903657293676544)), (181485/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471493228427293/18889465931478580854784), (254905370923/4722366482869645213696)), (73749/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296175396966241/4722366482869645213696), (382143153033/590295810358705651712)), (221321/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404893252902347/147573952589676412928), (2100391362177/295147905179352825856)), (304437/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821131450980305/73786976294838206464), (5246793587987/73786976294838206464)), (380727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820021795400591/9223372036854775808), (5896893730601/9223372036854775808)), (214283/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591271503620913/1152921504606846976), (1472428751655/288230376151711744)), (428877/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192207054400557/144115188075855872), (5145435000411/144115188075855872)), (187809/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488079551484487/36028797018963968), (7702047294417/36028797018963968)), (282065/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484815125752663/9007199254740992), (9599433545659/9007199254740992)), (88299/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219077285467019/4503599627370496), (9557362053583/2251799813685248)), (1416485/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101416735099303/1125899906842624), (1778909054589/140737488355328)), (2134013/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077168513929301/1125899906842624), (56091806521493/2251799813685248)), (1076341/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077168513929301/1125899906842624), (56091806521493/2251799813685248)), (4105915071727561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((257461926158819/281474976710656), (107328062658437/2251799813685248)), (4226265/1125899906842624), by norm_num⟩
  | 2 => ⟨((939432057908401/1125899906842624), (196343490749027/2251799813685248)), (16268615/2251799813685248), by norm_num⟩
  | 3 => ⟨((1550572825401515/2251799813685248), (163825725937341/1125899906842624)), (14992787/1125899906842624), by norm_num⟩
  | 4 => ⟨((510018830048431/1125899906842624), (451236770153893/2251799813685248)), (12505471/562949953421312), by norm_num⟩
  | 5 => ⟨((92910368873707/562949953421312), (817618860042733/4503599627370496)), (130732617/4503599627370496), by norm_num⟩
  | 6 => ⟨((-25764069781095/4503599627370496), (1079531413732157/18014398509481984)), (45310597/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-309255479/4194304)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1251351023/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((722333444369861/18014398509481984), (761656974987877/18014398509481984)), (15343777/1125899906842624), by norm_num⟩
  | 1 => ⟨((-567601489/4294967296), (-598501477/4294967296)), (195/4294967296), by norm_num⟩
  | 2 => ⟨((233840239/1073741824), (61642601/268435456)), (323/4294967296), by norm_num⟩
  | 3 => ⟨((-1027599041/4294967296), (-1083541103/4294967296)), (357/4294967296), by norm_num⟩
  | 4 => ⟨((846699701/4294967296), (446396839/2147483648)), (37/536870912), by norm_num⟩
  | 5 => ⟨((-279058409/2147483648), (-36781279/268435456)), (197/4294967296), by norm_num⟩
  | 6 => ⟨((613153995/8589934592), (323266921/4294967296)), (109/4294967296), by norm_num⟩
  | 7 => ⟨((-577387297/17179869184), (-152205005/4294967296)), (207/17179869184), by norm_num⟩
  | 8 => ⟨((475743585/34359738368), (1003285733/68719476736)), (343/68719476736), by norm_num⟩
  | 9 => ⟨((-348438499/68719476736), (-367407345/68719476736)), (253/137438953472), by norm_num⟩
  | 10 => ⟨((114839645/68719476736), (484365869/274877906944)), (21/34359738368), by norm_num⟩
  | 11 => ⟨((-68816861/137438953472), (-580505777/1099511627776)), (203/1099511627776), by norm_num⟩
  | 12 => ⟨((604824393/4398046511104), (159437695/1099511627776)), (225/4398046511104), by norm_num⟩
  | 13 => ⟨((-613354625/17592186044416), (-323372697/8796093022208)), (115/8796093022208), by norm_num⟩
  | 14 => ⟨((18049257/2199023255552), (19031851/2199023255552)), (109/35184372088832), by norm_num⟩
  | 15 => ⟨((-253812935/140737488355328), (-267630405/140737488355328)), (193/281474976710656), by norm_num⟩
  | 16 => ⟨((209131507/562949953421312), (882066155/2251799813685248)), (5/35184372088832), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1057577986413/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444396251870249/158456325028528675187087900672), (1250002112981/633825300114114700748351602688)), (92323/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944205202894881/19807040628566084398385987584), (702954589207/19807040628566084398385987584)), (1623/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((118006414190715/154742504910672534362390528), (1493345598487/2475880078570760549798248448)), (110373/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769769284998445/154742504910672534362390528), (746429422985/77371252455336267181195264)), (220767/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387055323611833/2417851639229258349412352), (1399038212051/9671406556917033397649408)), (206991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628811751351113/302231454903657293676544), (1223641725447/604462909807314587353088)), (181139/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885899438695511/75557863725914323419136), (1987449494771/75557863725914323419136)), (36799/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296120708994297/4722366482869645213696), (186217546583/590295810358705651712)), (220831/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619498494423071/590295810358705651712), (1023509012183/295147905179352825856)), (303701/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910519660505519/36893488147419103232), (2556711758741/73786976294838206464)), (189857/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819919544215279/9223372036854775808), (1436734972121/4611686018427387904)), (106825/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591170992215245/1152921504606846976), (179370976531/72057594037927936)), (427453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298030264667939/36028797018963968), (2507223275397/144115188075855872)), (374193/144115188075855872), by norm_num⟩
  | 4 => ⟨((743977223835681/18014398509481984), (1876454191737/18014398509481984)), (561635/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484665522309005/9007199254740992), (1169324020827/2251799813685248)), (702649/9007199254740992), by norm_num⟩
  | 2 => ⟨((2166795199991/4398046511104), (9313201803741/4503599627370496)), (1407121/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202465056912491/2251799813685248), (3466693212191/562949953421312)), (2115267/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076899000078453/1125899906842624), (6831022974661/562949953421312)), (4249027/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076899000078453/1125899906842624), (6831022974661/562949953421312)), (16208751687056731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029864908792933/1125899906842624), (26134905123333/1125899906842624)), (8231325/2251799813685248), by norm_num⟩
  | 2 => ⟨((1882829353933727/2251799813685248), (95622786777317/2251799813685248)), (3860147/562949953421312), by norm_num⟩
  | 3 => ⟨((1570256217801463/2251799813685248), (79954438558473/1125899906842624)), (3391561/281474976710656), by norm_num⟩
  | 4 => ⟨((1083637064775257/2251799813685248), (223019743627737/2251799813685248)), (1302949/70368744177664), by norm_num⟩
  | 5 => ⟨((998784594680793/4503599627370496), (107324131968985/1125899906842624)), (96776331/4503599627370496), by norm_num⟩
  | 6 => ⟨((722333444369861/18014398509481984), (761656974987877/18014398509481984)), (15343777/1125899906842624), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1251351023/16777216)), (1/8388608), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile023Terms3
