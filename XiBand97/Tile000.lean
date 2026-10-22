/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile000Gamma
import XiBand97.Tile000Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile000
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-380242491/4398046511104), (875813407/4398046511104)), (347/2199023255552), by norm_num⟩
  | 1 => ⟨((-1005469853/4398046511104), (589061211/4398046511104)), (725/2199023255552), by norm_num⟩
  | 2 => ⟨((-43325357/274877906944), (-126684257/8796093022208)), (3131/8796093022208), by norm_num⟩
  | 3 => ⟨((-51859077/1099511627776), (-174451951/4398046511104)), (2315/8796093022208), by norm_num⟩
  | 4 => ⟨((-170951835/35184372088832), (-594557455/35184372088832)), (10465/70368744177664), by norm_num⟩
  | 5 => ⟨((158079667/140737488355328), (-1057251301/281474976710656)), (19179/281474976710656), by norm_num⟩
  | 6 => ⟨((4644033/8796093022208), (-134638395/281474976710656)), (29627/1125899906842624), by norm_num⟩
  | 7 => ⟨((478054579/4503599627370496), (-109119687/4503599627370496)), (19847/2251799813685248), by norm_num⟩
  | 8 => ⟨((1003724485/72057594037927936), (255773749/72057594037927936)), (189369/72057594037927936), by norm_num⟩
  | 9 => ⟨((187871981/144115188075855872), (611438981/576460752303423488)), (52247/72057594037927936), by norm_num⟩
  | 10 => ⟨((48499311/576460752303423488), (723039065/4611686018427387904)), (944499/4611686018427387904), by norm_num⟩
  | 11 => ⟨((164017533/73786976294838206464), (634718487/36893488147419103232)), (5637431/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-195120061/590295810358705651712), (28349521/18446744073709551616)), (28006563/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-318904141/4722366482869645213696), (270631641/2361183241434822606848)), (391200341/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-147788067/18889465931478580854784), (33543633/4722366482869645213696)), (760377947/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-26933393/37778931862957161709568), (1644229/4722366482869645213696)), (1512776935/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-2102191/37778931862957161709568), (396107/37778931862957161709568)), (377854041/9444732965739290427392), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile000Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-186024563/134217728), (926954651/268435456)), (13813/67108864), by norm_num⟩
  | 1 => ⟨((2966429/134217728), (580862223/67108864)), (14359/67108864), by norm_num⟩
  | 2 => ⟨((44466813/33554432), (-460410699/134217728)), (29303/134217728), by norm_num⟩
  | 3 => ⟨((-88772463/134217728), (58273331/67108864)), (233029/1073741824), by norm_num⟩
  | 4 => ⟨((28069153/134217728), (-19820797/134217728)), (455977/2147483648), by norm_num⟩
  | 5 => ⟨((-6487235/134217728), (3881165/268435456)), (1780675/8589934592), by norm_num⟩
  | 6 => ⟨((145169/16777216), (114919/268435456)), (27991855/137438953472), by norm_num⟩
  | 7 => ⟨((-1311311/1073741824), (-558757/1073741824)), (110831803/549755813888), by norm_num⟩
  | 8 => ⟨((35655/268435456), (275087/2147483648)), (882337239/4398046511104), by norm_num⟩
  | 9 => ⟨((-21071/2147483648), (-183935/8589934592)), (1761108909/8796093022208), by norm_num⟩
  | 10 => ⟨((2287/17179869184), (47819/17179869184)), (1759812013/8796093022208), by norm_num⟩
  | 11 => ⟨((7079/68719476736), (-19935/68719476736)), (1759388973/8796093022208), by norm_num⟩
  | 12 => ⟨((-5907/274877906944), (3253/137438953472)), (1759263661/8796093022208), by norm_num⟩
  | 13 => ⟨((785/274877906944), (-45/34359738368)), (1759229677/8796093022208), by norm_num⟩
  | 14 => ⟨((-325/1099511627776), (25/4398046511104)), (1759221143/8796093022208), by norm_num⟩
  | 15 => ⟨((55/2199023255552), (23/2199023255552)), (879609575/4398046511104), by norm_num⟩
  | 16 => ⟨((-15/8796093022208), (-1/549755813888)), (1759218715/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile000Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (18227/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (18227/1280))
  have he : value ((69/80), (18227/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logpi : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negativeHalfLogPi : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piArg : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66258563/134217728), (-1093926473/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piPower : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-200730098788889/1125899906842624), (-1314528652993909/2251799813685248)), (28982889/1125899906842624), by norm_num⟩
  | 1 => ⟨((219136947/2147483648), (717535131/2147483648)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((-501705225/17179869184), (-821383909/8589934592)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((382877977/68719476736), (313420903/17179869184)), (31/34359738368), by norm_num⟩
  | 4 => ⟨((-438291863/549755813888), (-1435129099/549755813888)), (37/274877906944), by norm_num⟩
  | 5 => ⟨((100345159/1099511627776), (164283517/549755813888)), (35/2199023255552), by norm_num⟩
  | 6 => ⟨((-76578735/8796093022208), (-1002988009/35184372088832)), (55/35184372088832), by norm_num⟩
  | 7 => ⟨((400740419/562949953421312), (328042957/140737488355328)), (37/281474976710656), by norm_num⟩
  | 8 => ⟨((-229369767/4503599627370496), (-1502082307/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 9 => ⟨((58348095/18014398509481984), (1528425341/144115188075855872)), (91/144115188075855872), by norm_num⟩
  | 10 => ⟨((-106868493/576460752303423488), (-1399707333/2305843009213693952)), (43/1152921504606846976), by norm_num⟩
  | 11 => ⟨((355885259/36893488147419103232), (1165299503/36893488147419103232)), (37/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-271594995/590295810358705651712), (-27790691/18446744073709551616)), (59/590295810358705651712), by norm_num⟩
  | 13 => ⟨((382649733/18889465931478580854784), (1252936253/18889465931478580854784)), (85/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-500606383/604462909807314587353088), (-1639169799/604462909807314587353088)), (57/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((152815757/4835703278458516698824704), (1000750217/9671406556917033397649408)), (9/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((-43733191/38685626227668133590597632), (-572794341/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2432239140429/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55662655842691/19807040628566084398385987584), (-2885938841055/633825300114114700748351602688)), (23121/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473120515665719/9903520314283042199192993792), (-101454007309/1237940039285380274899124224)), (813/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((946213879542107/1237940039285380274899124224), (-3449261410889/2475880078570760549798248448)), (27647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774093288459603/154742504910672534362390528), (-1724532327525/77371252455336267181195264)), (27653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552273848842125/9671406556917033397649408), (-1616644501035/4835703278458516698824704)), (25931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261168289237059/604462909807314587353088), (-353614837309/75557863725914323419136)), (2837/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891657470128399/75557863725914323419136), (-4596600534791/75557863725914323419136)), (36893/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300437267333327/4722366482869645213696), (-1723553476933/2361183241434822606848)), (865/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1625430569783817/590295810358705651712), (-592401711997/73786976294838206464)), (9519/147573952589676412928), by norm_num⟩
  | 8 => ⟨((457112407173789/18446744073709551616), (-5923179110101/73786976294838206464)), (47621/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828249562174799/9223372036854775808), (-6662423485835/9223372036854775808)), (6701/1152921504606846976), by norm_num⟩
  | 6 => ⟨((799746396177437/576460752303423488), (-6660981096155/1152921504606846976)), (53651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199393395497007/144115188075855872), (-2913367113683/72057594037927936)), (23497/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498844493182941/36028797018963968), (-8736849022939/36028797018963968)), (70587/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498245812605861/9007199254740992), (-10915361059841/9007199254740992)), (22101/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122931108601175/2251799813685248), (-10906793433945/2251799813685248)), (88661/2251799813685248), by norm_num⟩
  | 1 => ⟨((280352483141137/281474976710656), (-4084677666079/281474976710656)), (261/2199023255552), by norm_num⟩
  | 0 => ⟨((1116773215537053/1125899906842624), (-1018473181585/35184372088832)), (269833/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116773215537053/1125899906842624), (-1018473181585/35184372088832)), (1029331211570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106777098783989/1125899906842624), (-64653907539703/1125899906842624)), (275457/562949953421312), by norm_num⟩
  | 2 => ⟨((542133191064909/562949953421312), (-63555795481421/562949953421312)), (573193/562949953421312), by norm_num⟩
  | 3 => ⟨((1029821766404897/1125899906842624), (-122411258782803/562949953421312)), (308355/140737488355328), by norm_num⟩
  | 4 => ⟨((888706713068413/1125899906842624), (-223930702865177/562949953421312)), (5585477/1125899906842624), by norm_num⟩
  | 5 => ⟨((261666147909387/562949953421312), (-176755249457737/281474976710656)), (13261163/1125899906842624), by norm_num⟩
  | 6 => ⟨((-200730098788889/1125899906842624), (-1314528652993909/2251799813685248)), (28982889/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1093926473/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piGamma : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((579063039/4398046511104), (65829753/4398046511104)), (281/2199023255552), by norm_num⟩
  | 1 => ⟨((95849513/2199023255552), (888524401/8796093022208)), (2937/8796093022208), by norm_num⟩
  | 2 => ⟨((-117962321/4398046511104), (301802253/8796093022208)), (981/2199023255552), by norm_num⟩
  | 3 => ⟨((-1498761027/140737488355328), (-36006383/17592186044416)), (57353/140737488355328), by norm_num⟩
  | 4 => ⟨((-129677849/281474976710656), (-1026447625/562949953421312)), (79935/281474976710656), by norm_num⟩
  | 5 => ⟨((107528259/562949953421312), (-312574543/2251799813685248)), (722231/4503599627370496), by norm_num⟩
  | 6 => ⟨((604528461/36028797018963968), (478331623/36028797018963968)), (2747503/36028797018963968), by norm_num⟩
  | 7 => ⟨((-498769571/576460752303423488), (616497619/576460752303423488)), (4520189/144115188075855872), by norm_num⟩
  | 8 => ⟨((-221928123/9223372036854775808), (-219022697/2305843009213693952)), (6568297/576460752303423488), by norm_num⟩
  | 9 => ⟨((875961955/73786976294838206464), (307886463/147573952589676412928)), (275212405/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-408099887/1180591620717411303424), (662360935/590295810358705651712)), (1338132275/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-46470277/590295810358705651712), (-1649385/36893488147419103232)), (1624836201/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((52174771/9444732965739290427392), (-40861825/9444732965739290427392)), (1189463583/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((1630133/9444732965739290427392), (10749653/18889465931478580854784)), (166687999/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-906957/18889465931478580854784), (-12137/18889465931478580854784)), (1087959161/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((46403/37778931862957161709568), (-129541/37778931862957161709568)), (1034201749/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((7901/37778931862957161709568), (3339/18889465931478580854784)), (2046335223/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-257474457/1099511627776), (954183331/2199023255552)), (33865/1099511627776), by norm_num⟩
  | 1 => ⟨((-147300059/274877906944), (1264943625/1099511627776)), (35109/549755813888), by norm_num⟩
  | 2 => ⟨((-1602738665/2199023255552), (-211638811/1099511627776)), (178561/2199023255552), by norm_num⟩
  | 3 => ⟨((250223861/8796093022208), (-12133003/68719476736)), (47671/549755813888), by norm_num⟩
  | 4 => ⟨((1391248685/70368744177664), (32216401/35184372088832)), (3048323/35184372088832), by norm_num⟩
  | 5 => ⟨((70850363/281474976710656), (1187075157/2251799813685248)), (188438913/2251799813685248), by norm_num⟩
  | 6 => ⟨((1040493257/9007199254740992), (68509991/2251799813685248)), (721178339/9007199254740992), by norm_num⟩
  | 7 => ⟨((-2253805/9007199254740992), (218926197/18014398509481984)), (694835983/9007199254740992), by norm_num⟩
  | 8 => ⟨((-874679/9007199254740992), (1548027/9007199254740992)), (1356168183/18014398509481984), by norm_num⟩
  | 9 => ⟨((-172981/18014398509481984), (474939/9007199254740992)), (1338309879/18014398509481984), by norm_num⟩
  | 10 => ⟨((-12167/4503599627370496), (3809/9007199254740992)), (665027719/9007199254740992), by norm_num⟩
  | 11 => ⟨((-1125/18014398509481984), (741/9007199254740992)), (663337197/9007199254740992), by norm_num⟩
  | 12 => ⟨((-121/9007199254740992), (1/2251799813685248)), (662714067/9007199254740992), by norm_num⟩
  | 13 => ⟨((-11/18014398509481984), (-33/18014398509481984)), (1325009767/18014398509481984), by norm_num⟩
  | 14 => ⟨((1/4503599627370496), (1/18014398509481984)), (1324880627/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1/18014398509481984), (-1/18014398509481984)), (1324843683/18014398509481984), by norm_num⟩
  | 16 => ⟨(0, 0), (1324833821/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-263653825105/1125899906842624), (122135465305/281474976710656)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-603341039293/1125899906842624), (1295302269915/1125899906842624)), (1/4194304), by norm_num⟩
  | 2 => ⟨((-205150541661/281474976710656), (-216718141997/1125899906842624)), (1/4194304), by norm_num⟩
  | 3 => ⟨((32028630987/1125899906842624), (-49696777203/281474976710656)), (1/2097152), by norm_num⟩
  | 4 => ⟨((11129995001/562949953421312), (515457011/562949953421312)), (1/2097152), by norm_num⟩
  | 5 => ⟨((141697867/562949953421312), (593544663/1125899906842624)), (1/2097152), by norm_num⟩
  | 6 => ⟨((130063375/1125899906842624), (34252379/1125899906842624)), (1/2097152), by norm_num⟩
  | 7 => ⟨((-141451/562949953421312), (6842337/562949953421312)), (1/2097152), by norm_num⟩
  | 8 => ⟨((-27337/281474976710656), (48233/281474976710656)), (1/2097152), by norm_num⟩
  | 9 => ⟨((-2725/281474976710656), (59613/1125899906842624)), (1/2097152), by norm_num⟩
  | 10 => ⟨((-1541/562949953421312), (197/562949953421312)), (1/2097152), by norm_num⟩
  | 11 => ⟨((-57/1125899906842624), (49/562949953421312)), (1/2097152), by norm_num⟩
  | 12 => ⟨((-13/1125899906842624), 0), (1/2097152), by norm_num⟩
  | 13 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 14 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 15 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 16 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨0,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(2225339/1073741824)) (L:=(291056106662065755/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile000
