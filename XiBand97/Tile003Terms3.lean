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
namespace Reinmann.XiBand97.Tile003Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9919/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9919/640))
  have he : value ((69/80), (9919/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-803734817/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-888273675893589/18014398509481984), (441515559272601/9007199254740992)), (230008911/18014398509481984), by norm_num⟩
  | 1 => ⟨((163655975/1073741824), (-650760335/4294967296)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-1011735133/4294967296), (1005763911/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((1042438749/4294967296), (-259071579/1073741824)), (69/1073741824), by norm_num⟩
  | 4 => ⟨((-805555607/4294967296), (800801249/4294967296)), (215/4294967296), by norm_num⟩
  | 5 => ⟨((124500329/1073741824), (-990124263/8589934592)), (67/2147483648), by norm_num⟩
  | 6 => ⟨((-513114403/8589934592), (255043011/4294967296)), (279/17179869184), by norm_num⟩
  | 7 => ⟨((56644943/2147483648), (-225242507/8589934592)), (249/34359738368), by norm_num⟩
  | 8 => ⟨((-350183847/34359738368), (696234151/68719476736)), (195/68719476736), by norm_num⟩
  | 9 => ⟨((962162789/274877906944), (-956484141/274877906944)), (135/137438953472), by norm_num⟩
  | 10 => ⟨((-297408603/274877906944), (591306617/549755813888)), (169/549755813888), by norm_num⟩
  | 11 => ⟨((334291861/1099511627776), (-332318883/1099511627776)), (191/2199023255552), by norm_num⟩
  | 12 => ⟨((-172218389/2199023255552), (342403925/4398046511104)), (199/8796093022208), by norm_num⟩
  | 13 => ⟨((655180741/35184372088832), (-20353559/1099511627776)), (191/35184372088832), by norm_num⟩
  | 14 => ⟨((-578626139/140737488355328), (143802777/35184372088832)), (85/70368744177664), by norm_num⟩
  | 15 => ⟨((953897579/1125899906842624), (-948267709/1125899906842624)), (141/562949953421312), by norm_num⟩
  | 16 => ⟨((-368567239/2251799813685248), (11449749/70368744177664)), (55/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (3073061741925/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888925378336517/316912650057057350374175801344), (3633259145251/633825300114114700748351602688)), (46279/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888708959493903/39614081257132168796771975168), (4086462614173/39614081257132168796771975168)), (104151/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888419291701581/2475880078570760549798248448), (4340684628847/2475880078570760549798248448)), (3459/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770085333038325/154742504910672534362390528), (271209712337/9671406556917033397649408)), (110717/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774258467412491/4835703278458516698824704), (2033366902109/4835703278458516698824704)), (103829/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257881533922967/604462909807314587353088), (222311292407/37778931862957161709568)), (90883/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886317514141555/75557863725914323419136), (1444362062121/18889465931478580854784)), (4617/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648216597309633/2361183241434822606848), (2165386261287/2361183241434822606848)), (27715/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809963212017303/295147905179352825856), (5951054428945/590295810358705651712)), (76259/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821571629663841/73786976294838206464), (1858296175149/18446744073709551616)), (190775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820514818032063/9223372036854775808), (8354592392043/9223372036854775808)), (214797/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397940452138629/288230376151711744), (4172462527345/576460752303423488)), (215017/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596316510533123/72057594037927936), (455684055063/9007199254740992)), (47097/36028797018963968), by norm_num⟩
  | 4 => ⟨((744356209648817/18014398509481984), (5457358128277/18014398509481984)), (141539/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485595607375089/9007199254740992), (6802740731711/4503599627370496)), (354717/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110303300793677/2251799813685248), (1693592075083/281474976710656)), (712047/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205048892782825/2251799813685248), (20181683069865/1125899906842624)), (16791/35184372088832), by norm_num⟩
  | 0 => ⟨((2158457049066457/2251799813685248), (79600635020959/2251799813685248)), (1087791/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158457049066457/2251799813685248), (79600635020959/2251799813685248)), (4149593357566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066169711575999/2251799813685248), (76300988536795/1125899906842624)), (4324611/2251799813685248), by norm_num⟩
  | 2 => ⟨((1885500606147907/2251799813685248), (280044061678867/2251799813685248)), (8522361/2251799813685248), by norm_num⟩
  | 3 => ⟨((1543959564332965/2251799813685248), (468978854012315/2251799813685248)), (16391825/2251799813685248), by norm_num⟩
  | 4 => ⟨((480475652771991/1125899906842624), (643116126683753/2251799813685248)), (7326525/562949953421312), by norm_num⟩
  | 5 => ⟨((113204792035131/1125899906842624), (1097794355958721/4503599627370496)), (41752345/2251799813685248), by norm_num⟩
  | 6 => ⟨((-888273675893589/18014398509481984), (441515559272601/9007199254740992)), (230008911/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-803734817/16777216)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1630586385/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-119649079816991/18014398509481984), (149930296898401/2251799813685248)), (25168121/2251799813685248), by norm_num⟩
  | 1 => ⟨((89444875/4294967296), (-1793310465/8589934592)), (303/8589934592), by norm_num⟩
  | 2 => ⟨((-1095523/33554432), (1405728647/4294967296)), (239/4294967296), by norm_num⟩
  | 3 => ⟨((146560257/4294967296), (-734609007/2147483648)), (63/1073741824), by norm_num⟩
  | 4 => ⟨((-57442355/2147483648), (575840573/2147483648)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((144088137/8589934592), (-1444435829/8589934592)), (63/2147483648), by norm_num⟩
  | 6 => ⟨((-588265/67108864), (1509673395/17179869184)), (265/17179869184), by norm_num⟩
  | 7 => ⟨((67456055/17179869184), (-1352449199/34359738368)), (239/34359738368), by norm_num⟩
  | 8 => ⟨((-105754035/68719476736), (132518645/8589934592)), (189/68719476736), by norm_num⟩
  | 9 => ⟨((147373851/274877906944), (-738687013/137438953472)), (265/274877906944), by norm_num⟩
  | 10 => ⟨((-184835943/1099511627776), (1852919085/1099511627776)), (167/549755813888), by norm_num⟩
  | 11 => ⟨((13171637/274877906944), (-1056330377/2199023255552)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((-27533061/2199023255552), (552019631/4398046511104)), (101/4398046511104), by norm_num⟩
  | 13 => ⟨((26563001/8796093022208), (-133142643/4398046511104)), (197/35184372088832), by norm_num⟩
  | 14 => ⟨((-95186441/140737488355328), (1908425083/281474976710656)), (355/281474976710656), by norm_num⟩
  | 15 => ⟨((159176819/1125899906842624), (-797847441/562949953421312)), (299/1125899906842624), by norm_num⟩
  | 16 => ⟨((-124774499/4503599627370496), (625411509/2251799813685248)), (59/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (2175649764391/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777795244122165/633825300114114700748351602688), (2572092399151/633825300114114700748351602688)), (92453/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888646716734931/39614081257132168796771975168), (723231363485/9903520314283042199192993792)), (104027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888353436883507/2475880078570760549798248448), (1536442631661/1237940039285380274899124224)), (110547/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770019790769375/154742504910672534362390528), (767982907859/38685626227668133590597632)), (110569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774227910386217/4835703278458516698824704), (1439461518399/4835703278458516698824704)), (103681/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314457097665077/151115727451828646838272), (314755650187/75557863725914323419136)), (11343/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886231777346151/75557863725914323419136), (4089925973083/75557863725914323419136)), (36875/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296369434785217/4722366482869645213696), (766446265023/1180591620717411303424)), (110663/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619839635093849/590295810358705651712), (2106379769919/295147905179352825856)), (152221/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455366115677465/18446744073709551616), (5261909915179/73786976294838206464)), (95183/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820396065852577/9223372036854775808), (369631186547/576460752303423488)), (107143/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591645314756227/1152921504606846976), (5907168875949/1152921504606846976)), (107221/576460752303423488), by norm_num⟩
  | 5 => ⟨((74533351431993/9007199254740992), (1290246495181/36028797018963968)), (187813/144115188075855872), by norm_num⟩
  | 4 => ⟨((744284186517679/18014398509481984), (3862964670061/18014398509481984)), (141035/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485424350871171/9007199254740992), (2407563403783/2251799813685248)), (88301/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220290341476847/4503599627370496), (19179247867407/4503599627370496)), (708261/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102319803981447/1125899906842624), (28566473638257/2251799813685248)), (1067041/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078947877150475/1125899906842624), (1760245099379/70368744177664)), (538193/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078947877150475/1125899906842624), (1760245099379/70368744177664)), (2053043367625999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2066498643543797/2251799813685248), (26989435941111/562949953421312)), (2116849/1125899906842624), by norm_num⟩
  | 2 => ⟨((236408768635157/281474976710656), (198147748031083/2251799813685248)), (2044141/562949953421312), by norm_num⟩
  | 3 => ⟨((1571027861915673/2251799813685248), (41605710094801/281474976710656)), (15173871/2251799813685248), by norm_num⟩
  | 4 => ⟨((261717569362641/562949953421312), (464437233729019/2251799813685248)), (1603669/140737488355328), by norm_num⟩
  | 5 => ⟨((390903058249651/2251799813685248), (431837264376141/2251799813685248)), (17220977/1125899906842624), by norm_num⟩
  | 6 => ⟨((-119649079816991/18014398509481984), (149930296898401/2251799813685248)), (25168121/2251799813685248), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1630586385/33554432)), (1/16777216), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-1652719141/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((154347916210075/4503599627370496), (984355692443207/18014398509481984)), (75549975/9007199254740992), by norm_num⟩
  | 1 => ⟨((-467802035/4294967296), (-186463319/1073741824)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((92918753/536870912), (592590465/2147483648)), (187/4294967296), by norm_num⟩
  | 3 => ⟨((-787468797/4294967296), (-1255522931/4294967296)), (25/536870912), by norm_num⟩
  | 4 => ⟨((625654557/4294967296), (997529865/4294967296)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-99418193/1073741824), (-1268081443/8589934592)), (207/8589934592), by norm_num⟩
  | 6 => ⟨((421275159/8589934592), (83958981/1073741824)), (111/8589934592), by norm_num⟩
  | 7 => ⟨((-765048647/34359738368), (-1219776737/34359738368)), (51/8589934592), by norm_num⟩
  | 8 => ⟨((303920723/34359738368), (969129033/68719476736)), (41/17179869184), by norm_num⟩
  | 9 => ⟨((-53659801/17179869184), (-171108013/34359738368)), (117/137438953472), by norm_num⟩
  | 10 => ⟨((545707955/549755813888), (435032381/274877906944)), (151/549755813888), by norm_num⟩
  | 11 => ⟨((-630650639/2199023255552), (-1005495509/2199023255552)), (177/2199023255552), by norm_num⟩
  | 12 => ⟨((41755035/549755813888), (1065172951/8796093022208)), (95/4398046511104), by norm_num⟩
  | 13 => ⟨((-653291071/35184372088832), (-260398229/8796093022208)), (47/8796093022208), by norm_num⟩
  | 14 => ⟨((148299585/35184372088832), (945782387/140737488355328)), (173/140737488355328), by norm_num⟩
  | 15 => ⟨((-502724335/562949953421312), (-801532623/562949953421312)), (37/140737488355328), by norm_num⟩
  | 16 => ⟨((798842499/4503599627370496), (1273656911/4503599627370496)), (237/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (82277331967/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777740966510863/633825300114114700748351602688), (778110777995/316912650057057350374175801344)), (46177/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944292896103385/19807040628566084398385987584), (1750335782207/39614081257132168796771975168)), (25977/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472072222036139/618970019642690137449562112), (232401497881/309485009821345068724781056)), (55207/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884977724160115/77371252455336267181195264), (464656879359/38685626227668133590597632)), (110427/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774197859369071/4835703278458516698824704), (1741842551275/9671406556917033397649408)), (103539/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157222002524923/75557863725914323419136), (380872941399/151115727451828646838272)), (45305/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471536771305937/18889465931478580854784), (618627834411/18889465931478580854784)), (147267/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296306273926597/4722366482869645213696), (1854866662871/4722366482869645213696)), (110473/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619753370276313/590295810358705651712), (637197601945/147573952589676412928)), (1187/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1821357502393741/73786976294838206464), (1591756536823/36893488147419103232)), (189975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910138465272287/4611686018427387904), (3578052327743/9223372036854775808)), (106899/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397881917500807/288230376151711744), (1786903604201/576460752303423488)), (213893/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596216178080041/72057594037927936), (1561156022653/72057594037927936)), (93631/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488419806576511/36028797018963968), (584243220503/4503599627370496)), (281107/36028797018963968), by norm_num⟩
  | 3 => ⟨((185655556463049/1125899906842624), (5825804605683/9007199254740992)), (351759/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109973935061877/2251799813685248), (11601871829941/4503599627370496)), (704645/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102084435354519/1125899906842624), (4319742960343/562949953421312)), (1059801/2251799813685248), by norm_num⟩
  | 0 => ⟨((539281021030523/562949953421312), (17032817066077/1125899906842624)), (2131011/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539281021030523/562949953421312), (17032817066077/1125899906842624)), (8129161843306731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065913594360479/2251799813685248), (32633362602113/1125899906842624)), (4147305/2251799813685248), by norm_num⟩
  | 2 => ⟨((946740293704573/1125899906842624), (29939476422225/562949953421312)), (7850303/2251799813685248), by norm_num⟩
  | 3 => ⟨((792905025841571/1125899906842624), (201402689735193/2251799813685248)), (14037245/2251799813685248), by norm_num⟩
  | 4 => ⟨((274694764333585/562949953421312), (35459014593241/281474976710656)), (22282215/2251799813685248), by norm_num⟩
  | 5 => ⟨((250209974299015/1125899906842624), (17302436207685/140737488355328)), (54719029/4503599627370496), by norm_num⟩
  | 6 => ⟨((154347916210075/4503599627370496), (984355692443207/18014398509481984)), (75549975/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1652719141/33554432)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1673948263/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((521293439208125/9007199254740992), (103482530428767/4503599627370496)), (97613575/18014398509481984), by norm_num⟩
  | 1 => ⟨((-400061333/2147483648), (-158833225/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((1287747753/4294967296), (127816107/1073741824)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((-1381700037/4294967296), (-548565569/4294967296)), (17/536870912), by norm_num⟩
  | 4 => ⟨((277970053/1073741824), (55180139/536870912)), (111/4294967296), by norm_num⟩
  | 5 => ⟨((-715800867/4294967296), (-284188825/4294967296)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((384012351/4294967296), (152461423/4294967296)), (79/8589934592), by norm_num⟩
  | 7 => ⟨((-353168021/8589934592), (-560862159/34359738368)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((1136804005/68719476736), (451336411/68719476736)), (121/68719476736), by norm_num⟩
  | 9 => ⟨((-813162429/137438953472), (-322843525/137438953472)), (11/17179869184), by norm_num⟩
  | 10 => ⟨((523493777/274877906944), (415677287/549755813888)), (115/549755813888), by norm_num⟩
  | 11 => ⟨((-612749623/1099511627776), (-486550389/2199023255552)), (137/2199023255552), by norm_num⟩
  | 12 => ⟨((657454983/4398046511104), (130512107/2199023255552)), (149/8796093022208), by norm_num⟩
  | 13 => ⟨((-325579377/8796093022208), (-517048943/35184372088832)), (75/17592186044416), by norm_num⟩
  | 14 => ⟨((299428453/35184372088832), (475518955/140737488355328)), (35/35184372088832), by norm_num⟩
  | 15 => ⟨((-257019469/140737488355328), (-408169725/562949953421312)), (61/281474976710656), by norm_num⟩
  | 16 => ⟨((827313755/2251799813685248), (328461915/2251799813685248)), (25/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (246152350325/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444421967028025/158456325028528675187087900672), (581942347857/633825300114114700748351602688)), (46129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944263065922121/19807040628566084398385987584), (163632271955/9903520314283042199192993792)), (51897/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888225599097457/2475880078570760549798248448), (695240340169/2475880078570760549798248448)), (110285/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884946135873601/77371252455336267181195264), (695019043103/154742504910672534362390528)), (55145/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548336610113627/9671406556917033397649408), (651345323865/9671406556917033397649408)), (103403/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724419463127/604462909807314587353088), (569692240879/604462909807314587353088)), (45241/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886063457516293/75557863725914323419136), (231327414501/18889465931478580854784)), (147043/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296243748481391/4722366482869645213696), (21674914875/147573952589676412928)), (110291/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404916928700459/147573952589676412928), (7445868171/4611686018427387904)), (9479/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821250907857677/73786976294838206464), (1190401990071/73786976294838206464)), (189601/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820157663395729/9223372036854775808), (334478809193/2305843009213693952)), (213329/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795704607877093/576460752303423488), (1336308370951/1152921504606846976)), (213365/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298082405207351/36028797018963968), (1167464691457/144115188075855872)), (186735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488267521930405/36028797018963968), (1747593238173/36028797018963968)), (280185/36028797018963968), by norm_num⟩
  | 3 => ⟨((92816079044669/562949953421312), (2178199423085/9007199254740992)), (350375/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109791474799711/2251799813685248), (1084395107221/1125899906842624)), (701183/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203644938866623/2251799813685248), (6459526828899/2251799813685248)), (1052873/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078084457223379/1125899906842624), (12732886832781/2251799813685248)), (527553/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078084457223379/1125899906842624), (12732886832781/2251799813685248)), (2012454988719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2064527331855099/2251799813685248), (24384276624555/2251799813685248)), (2032527/1125899906842624), by norm_num⟩
  | 2 => ⟨((1892565442598407/2251799813685248), (44712682941847/2251799813685248)), (3771001/1125899906842624), by norm_num⟩
  | 3 => ⟨((1589752654186081/2251799813685248), (2348723398593/70368744177664)), (12977137/2251799813685248), by norm_num⟩
  | 4 => ⟨((1119844041430669/2251799813685248), (26530878875961/562949953421312)), (4797449/562949953421312), by norm_num⟩
  | 5 => ⟨((275954476288671/1125899906842624), (52776355060693/1125899906842624)), (10447673/1125899906842624), by norm_num⟩
  | 6 => ⟨((521293439208125/9007199254740992), (103482530428767/4503599627370496)), (97613575/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1673948263/33554432)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-1694344653/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1055901107805979/18014398509481984), (-247146617092163/18014398509481984)), (20906915/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1640428421/8589934592), (383962411/8589934592)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((334042135/1073741824), (-312746651/4294967296)), (109/4294967296), by norm_num⟩
  | 3 => ⟨((-90695127/268435456), (339652927/4294967296)), (15/536870912), by norm_num⟩
  | 4 => ⟨((1181973917/4294967296), (-138327753/2147483648)), (25/1073741824), by norm_num⟩
  | 5 => ⟨((-1540394051/8589934592), (360548139/8589934592)), (33/2147483648), by norm_num⟩
  | 6 => ⟨((418229377/4294967296), (-391566881/17179869184)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((-1557293355/34359738368), (91125907/8589934592)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((634226511/34359738368), (-148448501/34359738368)), (57/34359738368), by norm_num⟩
  | 9 => ⟨((-1793725/268435456), (214959799/137438953472)), (21/34359738368), by norm_num⟩
  | 10 => ⟨((1196877663/549755813888), (-280143911/549755813888)), (111/549755813888), by norm_num⟩
  | 11 => ⟨((-709007813/1099511627776), (165951983/1099511627776)), (133/2199023255552), by norm_num⟩
  | 12 => ⟨((1540010601/8796093022208), (-90114597/2199023255552)), (147/8796093022208), by norm_num⟩
  | 13 => ⟨((-1543847141/35184372088832), (361356377/35184372088832)), (149/35184372088832), by norm_num⟩
  | 14 => ⟨((718571861/70368744177664), (-84095283/35184372088832)), (141/140737488355328), by norm_num⟩
  | 15 => ⟨((-1248627463/562949953421312), (292256587/562949953421312)), (31/140737488355328), by norm_num⟩
  | 16 => ⟨((254259301/562949953421312), (-59512511/562949953421312)), (103/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (-299500544147/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817948134033/316912650057057350374175801344), (-354013089617/633825300114114700748351602688)), (92235/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888467683789585/39614081257132168796771975168), (-398168739325/39614081257132168796771975168)), (103767/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888163524145477/2475880078570760549798248448), (-422933103599/2475880078570760549798248448)), (6891/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221228778267705/19342813113834066795298816), (-26424803113/9671406556917033397649408)), (110259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774139236760755/4835703278458516698824704), (-396227339033/9671406556917033397649408)), (103371/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673581088445/604462909807314587353088), (-346554283777/604462909807314587353088)), (90453/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942990451754783/37778931862957161709568), (-562879663323/75557863725914323419136)), (146991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296181883992711/4722366482869645213696), (-210961364383/2361183241434822606848)), (110249/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619582733953283/590295810358705651712), (-289879437065/295147905179352825856)), (9475/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821144805895329/73786976294838206464), (-724121761013/73786976294838206464)), (189513/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227504808637673/1152921504606846976), (-813844625369/9223372036854775808)), (53305/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49727819817001/36028797018963968), (-812855360957/1152921504606846976)), (106621/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192225750733885/144115188075855872), (-88767142393/18014398509481984)), (186613/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488112193275209/36028797018963968), (-531493575413/18014398509481984)), (279969/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484863935193985/9007199254740992), (-331215136739/2251799813685248)), (350051/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219198774259767/4503599627370496), (-659534292515/1125899906842624)), (700375/4503599627370496), by norm_num⟩
  | 1 => ⟨((275384356196557/281474976710656), (-3928372428331/2251799813685248)), (525629/1125899906842624), by norm_num⟩
  | 0 => ⟨((269381652321621/281474976710656), (-7742167294775/2251799813685248)), (263171/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269381652321621/281474976710656), (-7742167294775/2251799813685248)), (1003917695165538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1031218318232005/1125899906842624), (-3704765948983/562949953421312)), (252769/140737488355328), by norm_num⟩
  | 2 => ⟨((236112533679011/281474976710656), (-13572867314883/1125899906842624)), (1865409/562949953421312), by norm_num⟩
  | 3 => ⟨((1584158287638371/2251799813685248), (-45541868459595/2251799813685248)), (396817/70368744177664), by norm_num⟩
  | 4 => ⟨((556773165019241/1125899906842624), (-8009762670325/281474976710656)), (9190057/1125899906842624), by norm_num⟩
  | 5 => ⟨((1097681435584917/4503599627370496), (-63375024879659/2251799813685248)), (4806127/562949953421312), by norm_num⟩
  | 6 => ⟨((1055901107805979/18014398509481984), (-247146617092163/18014398509481984)), (20906915/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-1694344653/33554432)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-428492795/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((360042188967447/9007199254740992), (-763783634975881/18014398509481984)), (7685079/1125899906842624), by norm_num⟩
  | 1 => ⟨((-282917099/2147483648), (300086291/2147483648)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((932448605/4294967296), (-989035461/4294967296)), (163/4294967296), by norm_num⟩
  | 3 => ⟨((-128049937/536870912), (1086566511/4294967296)), (181/4294967296), by norm_num⟩
  | 4 => ⟨((422031703/2147483648), (-895286491/4294967296)), (151/4294967296), by norm_num⟩
  | 5 => ⟨((-278189529/2147483648), (590143645/4294967296)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((305622435/4294967296), (-162084765/2147483648)), (113/8589934592), by norm_num⟩
  | 7 => ⟨((-17987173/536870912), (4769687/134217728)), (27/4294967296), by norm_num⟩
  | 8 => ⟨((474262303/34359738368), (-62880441/4294967296)), (45/17179869184), by norm_num⟩
  | 9 => ⟨((-86838399/17179869184), (368433201/68719476736)), (133/137438953472), by norm_num⟩
  | 10 => ⟨((457928315/274877906944), (-971436581/549755813888)), (177/549755813888), by norm_num⟩
  | 11 => ⟨((-548820735/1099511627776), (145531659/274877906944)), (27/274877906944), by norm_num⟩
  | 12 => ⟨((150735301/1099511627776), (-159882869/1099511627776)), (15/549755813888), by norm_num⟩
  | 13 => ⟨((-152861219/4398046511104), (648551205/17592186044416)), (123/17592186044416), by norm_num⟩
  | 14 => ⟨((575777875/70368744177664), (-305359853/35184372088832)), (117/70368744177664), by norm_num⟩
  | 15 => ⟨((-506045319/281474976710656), (536755339/281474976710656)), (13/35184372088832), by norm_num⟩
  | 16 => ⟨((833921409/2251799813685248), (-884529017/2251799813685248)), (173/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1061419051085/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444396250344767/158456325028528675187087900672), (-39204439107/19807040628566084398385987584)), (23081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888410398594541/39614081257132168796771975168), (-352753839457/9903520314283042199192993792)), (103873/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051309479859/1237940039285380274899124224), (-1498769341279/2475880078570760549798248448)), (55187/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769769276404729/154742504910672534362390528), (-1498280820193/154742504910672534362390528)), (6899/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774110642928909/4835703278458516698824704), (-702059717265/4835703278458516698824704)), (12937/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257623494654019/604462909807314587353088), (-614042958803/302231454903657293676544)), (90571/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885899424620069/75557863725914323419136), (-997333894245/37778931862957161709568)), (73599/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324030174391589/1180591620717411303424), (-1495151016023/4722366482869645213696)), (6901/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619498477295771/590295810358705651712), (-1027226331165/295147905179352825856)), (37963/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910519648742361/36893488147419103232), (-2565997567087/73786976294838206464)), (189859/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909959757421463/4611686018427387904), (-180244136915/576460752303423488)), (213653/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795585479610077/576460752303423488), (-2880359025193/1152921504606846976)), (106865/576460752303423488), by norm_num⟩
  | 5 => ⟨((596060512868789/72057594037927936), (-2516329319217/144115188075855872)), (46775/36028797018963968), by norm_num⟩
  | 4 => ⟨((371988597543335/9007199254740992), (-1883269317309/18014398509481984)), (140411/18014398509481984), by norm_num⟩
  | 3 => ⟨((742332718167449/4503599627370496), (-1173570895443/2251799813685248)), (351331/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218798070807811/4503599627370496), (-4673513146805/2251799813685248)), (703577/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202464631791693/2251799813685248), (-13917134849597/2251799813685248)), (528833/1125899906842624), by norm_num⟩
  | 0 => ⟨((1076898369469201/1125899906842624), (-27423326134453/2251799813685248)), (531153/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076898369469201/1125899906842624), (-27423326134453/2251799813685248)), (2026187898875999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059724992273989/2251799813685248), (-6557451292991/281474976710656)), (4116039/2251799813685248), by norm_num⟩
  | 2 => ⟨((1882811699030217/2251799813685248), (-95969783684729/2251799813685248)), (7721677/2251799813685248), by norm_num⟩
  | 3 => ⟨((1570197169897617/2251799813685248), (-160487651146297/2251799813685248)), (6785467/1125899906842624), by norm_num⟩
  | 4 => ⟨((541736181732595/1125899906842624), (-111909262138635/1125899906842624)), (1303791/140737488355328), by norm_num⟩
  | 5 => ⟨((998150567162517/4503599627370496), (-215384319700349/2251799813685248)), (12110733/1125899906842624), by norm_num⟩
  | 6 => ⟨((360042188967447/9007199254740992), (-763783634975881/18014398509481984)), (7685079/1125899906842624), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-428492795/8388608)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile003Terms3
