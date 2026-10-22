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
namespace Reinmann.XiBand97.Tile037Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33621/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33621/1280))
  have he : value ((69/80), (33621/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-340537961/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1104637284352257/18014398509481984), (147595444359265/4503599627370496)), (14806747/1125899906842624), by norm_num⟩
  | 1 => ⟨((-814075647/4294967296), (-217544453/2147483648)), (11/268435456), by norm_num⟩
  | 2 => ⟨((1258171193/4294967296), (168109785/1073741824)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((-324088381/1073741824), (-86605747/536870912)), (285/4294967296), by norm_num⟩
  | 4 => ⟨((15652671/67108864), (535404081/4294967296)), (111/2147483648), by norm_num⟩
  | 5 => ⟨((-1238606607/8589934592), (-330991349/4294967296)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((638097601/8589934592), (42629513/1073741824)), (9/536870912), by norm_num⟩
  | 7 => ⟨((-1127078157/34359738368), (-37648467/2147483648)), (1/134217728), by norm_num⟩
  | 8 => ⟨((108870201/8589934592), (465492039/68719476736)), (199/68719476736), by norm_num⟩
  | 9 => ⟨((-149565517/34359738368), (-319745701/137438953472)), (275/274877906944), by norm_num⟩
  | 10 => ⟨((184925345/137438953472), (197669507/274877906944)), (43/137438953472), by norm_num⟩
  | 11 => ⟨((-415717885/1099511627776), (-444367155/2199023255552)), (195/2199023255552), by norm_num⟩
  | 12 => ⟨((428333877/4398046511104), (114463145/2199023255552)), (203/8796093022208), by norm_num⟩
  | 13 => ⟨((-407384061/17592186044416), (-108864751/8796093022208)), (195/35184372088832), by norm_num⟩
  | 14 => ⟨((359783265/70368744177664), (384577791/140737488355328)), (87/70368744177664), by norm_num⟩
  | 15 => ⟨((-1186245703/1125899906842624), (-633998015/1125899906842624)), (289/1125899906842624), by norm_num⟩
  | 16 => ⟨((916683957/4503599627370496), (489928695/4503599627370496)), (225/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (639363744247/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777857530162477/633825300114114700748351602688), (755915229215/633825300114114700748351602688)), (184549/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888716950104959/39614081257132168796771975168), (850209411523/39614081257132168796771975168)), (51907/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((461042060075/604462909807314587353088), (451550986325/1237940039285380274899124224)), (27577/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770094877150865/154742504910672534362390528), (902825896113/154742504910672534362390528)), (55157/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193565809318991/1208925819614629174706176), (846106064409/9671406556917033397649408)), (51713/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628945236379953/302231454903657293676544), (740049726119/604462909807314587353088)), (90505/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886333147797789/75557863725914323419136), (601015780941/37778931862957161709568)), (294165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296445888244261/4722366482869645213696), (225260841487/1180591620717411303424)), (110323/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809972724611247/295147905179352825856), (619077330299/295147905179352825856)), (303423/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113849860283619/4611686018427387904), (96657768691/4611686018427387904)), (379333/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820547449522369/9223372036854775808), (1738233925997/9223372036854775808)), (53353/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591798468024113/1152921504606846976), (1736228787491/1152921504606846976)), (106729/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192669616926351/144115188075855872), (1516947497553/144115188075855872)), (373657/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488776319167289/36028797018963968), (283865446901/4503599627370496)), (560695/36028797018963968), by norm_num⟩
  | 3 => ⟨((742845585996173/4503599627370496), (707700216239/2251799813685248)), (350619/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110422258790443/2251799813685248), (2819055021513/2251799813685248)), (1403589/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205521748470815/2251799813685248), (8398677083761/2251799813685248)), (2108191/2251799813685248), by norm_num⟩
  | 0 => ⟨((539965201659241/562949953421312), (8282422031215/1125899906842624)), (2113869/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539965201659241/562949953421312), (8282422031215/1125899906842624)), (8063770298484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129472108311925/140737488355328), (31777032079901/2251799813685248)), (255389/70368744177664), by norm_num⟩
  | 2 => ⟨((1905287078729639/2251799813685248), (58466857514083/2251799813685248)), (15267221/2251799813685248), by norm_num⟩
  | 3 => ⟨((1610578550058217/2251799813685248), (98939654829441/2251799813685248)), (3328567/281474976710656), by norm_num⟩
  | 4 => ⟨((573801941652321/1125899906842624), (141531307401321/2251799813685248)), (20215815/1125899906842624), by norm_num⟩
  | 5 => ⟨((575967523453421/2251799813685248), (288519213823227/4503599627370496)), (11573373/562949953421312), by norm_num⟩
  | 6 => ⟨((1104637284352257/18014398509481984), (147595444359265/4503599627370496)), (14806747/1125899906842624), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-340537961/4194304)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1381740721/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((234934118302721/4503599627370496), (-754899512924067/18014398509481984)), (258989193/18014398509481984), by norm_num⟩
  | 1 => ⟨((-702509469/4294967296), (564332737/4294967296)), (195/4294967296), by norm_num⟩
  | 2 => ⟨((275339297/1073741824), (-110591377/536870912)), (77/1073741824), by norm_num⟩
  | 3 => ⟨((-1151099697/4294967296), (924689661/4294967296)), (81/1073741824), by norm_num⟩
  | 4 => ⟨((451158305/2147483648), (-724839771/4294967296)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-282920851/2147483648), (227273091/2147483648)), (81/2147483648), by norm_num⟩
  | 6 => ⟨((1182795589/17179869184), (-950151283/17179869184)), (341/17179869184), by norm_num⟩
  | 7 => ⟨((-529806961/17179869184), (851198243/34359738368)), (77/8589934592), by norm_num⟩
  | 8 => ⟨((830603331/68719476736), (-41701987/4294967296)), (243/68719476736), by norm_num⟩
  | 9 => ⟨((-1157489751/274877906944), (929822855/274877906944)), (341/274877906944), by norm_num⟩
  | 10 => ⟨((181465121/137438953472), (-583090837/549755813888)), (27/68719476736), by norm_num⟩
  | 11 => ⟨((-103451425/274877906944), (83103543/274877906944)), (31/274877906944), by norm_num⟩
  | 12 => ⟨((216247563/2199023255552), (-347427571/4398046511104)), (261/8796093022208), by norm_num⟩
  | 13 => ⟨((-104314305/4398046511104), (83796703/4398046511104)), (127/17592186044416), by norm_num⟩
  | 14 => ⟨((747604343/140737488355328), (-600557891/140737488355328)), (115/70368744177664), by norm_num⟩
  | 15 => ⟨((-312547879/281474976710656), (502145545/562949953421312)), (97/281474976710656), by norm_num⟩
  | 16 => ⟨((979992067/4503599627370496), (-393618613/2251799813685248)), (153/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-881550059449/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798210159745/633825300114114700748351602688), (-65136523939/39614081257132168796771975168)), (92303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888650215404817/39614081257132168796771975168), (-586092236083/19807040628566084398385987584)), (207695/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944178685766667/1237940039285380274899124224), (-311275653173/618970019642690137449562112)), (220691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770023969604637/154742504910672534362390528), (-1244716498453/154742504910672534362390528)), (55177/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774229998831271/4835703278458516698824704), (-36453488653/302231454903657293676544)), (206933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257832304429113/604462909807314587353088), (-127535973587/75557863725914323419136)), (181085/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886238622312595/75557863725914323419136), (-1657199502927/75557863725914323419136)), (36787/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296374992452071/4722366482869645213696), (-155278486155/590295810358705651712)), (220753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809923982414751/295147905179352825856), (-426743129133/147573952589676412928)), (9487/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821475905113311/73786976294838206464), (-1066040349083/36893488147419103232)), (379553/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820410352398801/9223372036854775808), (-2396344842047/9223372036854775808)), (427099/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591661364517671/1152921504606846976), (-2393540573665/1152921504606846976)), (213613/576460752303423488), by norm_num⟩
  | 5 => ⟨((149068705557461/18014398509481984), (-2091197540885/144115188075855872)), (373967/144115188075855872), by norm_num⟩
  | 4 => ⟨((93037271710853/2251799813685248), (-195656639087/2251799813685248)), (280619/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485466185913295/9007199254740992), (-3902149469063/9007199254740992)), (702053/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110197243845225/2251799813685248), (-7771446132521/4503599627370496)), (351407/1125899906842624), by norm_num⟩
  | 1 => ⟨((275605822643787/281474976710656), (-11575376167601/2251799813685248)), (132017/140737488355328), by norm_num⟩
  | 0 => ⟨((1079255056050837/1125899906842624), (-22825606283533/2251799813685248)), (33125/17592186044416), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079255056050837/1125899906842624), (-22825606283533/2251799813685248)), (126361846990936989/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((2068853930722523/2251799813685248), (-21879965385211/1125899906842624)), (4107321/1125899906842624), by norm_num⟩
  | 2 => ⟨((949960478086043/1125899906842624), (-20102343075153/562949953421312)), (15413775/2251799813685248), by norm_num⟩
  | 3 => ⟨((1600157327773777/2251799813685248), (-135688306374405/2251799813685248)), (6777771/562949953421312), by norm_num⟩
  | 4 => ⟨((282228924357737/562949953421312), (-192843641267453/2251799813685248)), (41798261/2251799813685248), by norm_num⟩
  | 5 => ⟨((549454695932245/2251799813685248), (-386720369108265/4503599627370496)), (49069409/2251799813685248), by norm_num⟩
  | 6 => ⟨((234934118302721/4503599627370496), (-754899512924067/18014398509481984)), (258989193/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1381740721/16777216)), (1/8388608), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-350123943/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-257933159431081/18014398509481984), (-1132960353586803/18014398509481984)), (200081543/9007199254740992), by norm_num⟩
  | 1 => ⟨((390875561/8589934592), (1716904159/8589934592)), (609/8589934592), by norm_num⟩
  | 2 => ⟨((-310555893/4294967296), (-1364103459/4294967296)), (243/2147483648), by norm_num⟩
  | 3 => ⟨((164493891/2147483648), (1445064741/4294967296)), (517/4294967296), by norm_num⟩
  | 4 => ⟨((-65346305/1073741824), (-143515423/536870912)), (413/4294967296), by norm_num⟩
  | 5 => ⟨((41534815/1073741824), (1459519167/8589934592)), (527/8589934592), by norm_num⟩
  | 6 => ⟨((-175999837/8589934592), (-1546143493/17179869184)), (35/1073741824), by norm_num⟩
  | 7 => ⟨((159810559/17179869184), (1403922071/34359738368)), (511/34359738368), by norm_num⟩
  | 8 => ⟨((-15871455/4294967296), (-1115434979/68719476736)), (51/8589934592), by norm_num⟩
  | 9 => ⟨((179343425/137438953472), (1575516625/274877906944)), (579/274877906944), by norm_num⟩
  | 10 => ⟨((-227985223/549755813888), (-1001415329/549755813888)), (185/274877906944), by norm_num⟩
  | 11 => ⟨((263472477/2199023255552), (1157291571/2199023255552)), (215/1099511627776), by norm_num⟩
  | 12 => ⟨((-279109905/8796093022208), (-1225978303/8796093022208)), (457/8796093022208), by norm_num⟩
  | 13 => ⟨((136465585/17592186044416), (599419237/17592186044416)), (7/549755813888), by norm_num⟩
  | 14 => ⟨((-61956425/35184372088832), (-272140943/35184372088832)), (409/140737488355328), by norm_num⟩
  | 15 => ⟨((210027577/562949953421312), (922537137/562949953421312)), (87/140737488355328), by norm_num⟩
  | 16 => ⟨((-333739473/4503599627370496), (-1465936341/4503599627370496)), (555/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-1168862095535/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777738168731567/633825300114114700748351602688), (-2763532107895/633825300114114700748351602688)), (11559/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944291246154431/19807040628566084398385987584), (-48566163791/618970019642690137449562112)), (104049/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472071294262861/618970019642690137449562112), (-412696943031/309485009821345068724781056)), (27643/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884975753467329/77371252455336267181195264), (-1650268467095/77371252455336267181195264)), (110595/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548391779209003/9671406556917033397649408), (-3093150249719/9671406556917033397649408)), (103707/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257772328862707/604462909807314587353088), (-1352701894557/302231454903657293676544)), (5673/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((117883789332931/4722366482869645213696), (-1098553645581/18889465931478580854784)), (295087/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296301032204657/4722366482869645213696), (-3293853632099/4722366482869645213696)), (221395/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619745514154707/590295810358705651712), (-4526113651623/590295810358705651712)), (76137/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910673355359457/36893488147419103232), (-2826621267371/36893488147419103232)), (380879/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227532932084539/1152921504606846976), (-6353853547047/9223372036854775808)), (107189/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591512533501201/1152921504606846976), (-6346305734185/1152921504606846976)), (429091/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192417246622981/144115188075855872), (-2772268312321/72057594037927936)), (375833/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488393425459641/36028797018963968), (-8299869116059/36028797018963968)), (70563/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485205000925551/9007199254740992), (-5172628527205/4503599627370496)), (353477/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219849665175607/4503599627370496), (-20602009098155/4503599627370496)), (354473/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203973722213577/2251799813685248), (-1917660311623/140737488355328)), (2136827/2251799813685248), by norm_num⟩
  | 0 => ⟨((539136228326283/562949953421312), (-15122051284587/562949953421312)), (4313811/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539136228326283/562949953421312), (-15122051284587/562949953421312)), (16455883034712981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1031847305408591/1125899906842624), (-115858905674725/2251799813685248)), (8494417/2251799813685248), by norm_num⟩
  | 2 => ⟨((58916929122795/70368744177664), (-106180575112849/1125899906842624)), (16443769/2251799813685248), by norm_num⟩
  | 3 => ⟨((194811732747131/281474976710656), (-43408564369/274877906944)), (30636953/2251799813685248), by norm_num⟩
  | 4 => ⟨((1022493047186713/2251799813685248), (-492232947190657/2251799813685248)), (13021161/562949953421312), by norm_num⟩
  | 5 => ⟨((713383802915119/4503599627370496), (-447024431781059/2251799813685248)), (35035959/1125899906842624), by norm_num⟩
  | 6 => ⟨((-257933159431081/18014398509481984), (-1132960353586803/18014398509481984)), (200081543/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-350123943/4194304)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1418485093/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1079692389581871/18014398509481984), (-304285866559313/18014398509481984)), (393662329/18014398509481984), by norm_num⟩
  | 1 => ⟨((6473429/33554432), (233521085/4294967296)), (607/8589934592), by norm_num⟩
  | 2 => ⟨((-1333578503/4294967296), (-46979711/536870912)), (491/4294967296), by norm_num⟩
  | 3 => ⟨((1430874535/4294967296), (403258283/4294967296)), (529/4294967296), by norm_num⟩
  | 4 => ⟨((-575725931/2147483648), (-324509585/4294967296)), (107/1073741824), by norm_num⟩
  | 5 => ⟨((1482552225/8589934592), (417822423/8589934592)), (553/8589934592), by norm_num⟩
  | 6 => ⟨((-397679293/4294967296), (-224153083/8589934592)), (149/4294967296), by norm_num⟩
  | 7 => ⟨((1462948871/34359738368), (25768605/2147483648)), (275/17179869184), by norm_num⟩
  | 8 => ⟨((-1177262689/68719476736), (-331783759/68719476736)), (445/68719476736), by norm_num⟩
  | 9 => ⟨((421051379/68719476736), (237326827/137438953472)), (5/2147483648), by norm_num⟩
  | 10 => ⟨((-271062421/137438953472), (-152785117/274877906944)), (207/274877906944), by norm_num⟩
  | 11 => ⟨((1269114581/2199023255552), (357670051/2199023255552)), (487/2199023255552), by norm_num⟩
  | 12 => ⟨((-1361707415/8796093022208), (-47970645/1099511627776)), (131/2199023255552), by norm_num⟩
  | 13 => ⟨((674333397/17592186044416), (23755623/2199023255552)), (521/35184372088832), by norm_num⟩
  | 14 => ⟨((-310085067/35184372088832), (-21847543/8796093022208)), (481/140737488355328), by norm_num⟩
  | 15 => ⟨((532333507/281474976710656), (300051319/562949953421312)), (415/562949953421312), by norm_num⟩
  | 16 => ⟨((-26773679/70368744177664), (-30182123/281474976710656)), (21/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-3734445740141/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777677594489797/633825300114114700748351602688), (-4414404573205/633825300114114700748351602688)), (185269/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888514015479641/39614081257132168796771975168), (-4964992616159/39614081257132168796771975168)), (208485/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944105986519359/1237940039285380274899124224), (-5273808398821/2475880078570760549798248448)), (55395/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884938900108095/77371252455336267181195264), (-5272125506253/154742504910672534362390528)), (221653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96770134094049/604462909807314587353088), (-1235207520603/2417851639229258349412352)), (207877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157213858280465/75557863725914323419136), (-4321439296913/604462909807314587353088)), (90985/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943019877038701/37778931862957161709568), (-877373670453/9444732965739290427392)), (295847/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324056125801437/1180591620717411303424), (-5261312394039/4722366482869645213696)), (55503/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404909717741707/147573952589676412928), (-7229546104927/590295810358705651712)), (152737/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455302821670353/18446744073709551616), (-9029798843137/73786976294838206464)), (382153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820108195517147/9223372036854775808), (-10148721024845/9223372036854775808)), (430349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795676822433733/576460752303423488), (-10136477110859/1152921504606846976)), (107721/288230376151711744), by norm_num⟩
  | 5 => ⟨((149034268801023/18014398509481984), (-8855656033793/144115188075855872)), (188813/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488170674382505/36028797018963968), (-3313998397703/9007199254740992)), (567645/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484912443876959/9007199254740992), (-2065244578947/1125899906842624)), (355835/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109611235090145/2251799813685248), (-16450049517489/2251799813685248)), (714849/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101464341002459/1125899906842624), (-24495817325831/1125899906842624)), (1080243/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154043541647307/2251799813685248), (-48277672689175/1125899906842624)), (4385029/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154043541647307/2251799813685248), (-48277672689175/1125899906842624)), (16727558144576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028195449801781/1125899906842624), (-184727271811411/2251799813685248)), (4382691/1125899906842624), by norm_num⟩
  | 2 => ⟨((931392600161165/1125899906842624), (-84348412845787/562949953421312)), (8723803/1125899906842624), by norm_num⟩
  | 3 => ⟨((1490422996817675/2251799813685248), (-139553235740495/562949953421312)), (34095265/2251799813685248), by norm_num⟩
  | 4 => ⟨((848103374086009/2251799813685248), (-369470413069365/1125899906842624)), (62038185/2251799813685248), by norm_num⟩
  | 5 => ⟨((19234146342471/562949953421312), (-34788738994993/140737488355328)), (174895377/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1079692389581871/18014398509481984), (-304285866559313/18014398509481984)), (393662329/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1418485093/16777216)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-717884383/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-197351329114137/4503599627370496), (743537434331105/18014398509481984)), (199633537/9007199254740992), by norm_num⟩
  | 1 => ⟨((306601373/2147483648), (-577572999/4294967296)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-124867109/536870912), (470447147/2147483648)), (255/2147483648), by norm_num⟩
  | 3 => ⟨((271219397/1073741824), (-1021841481/4294967296)), (139/1073741824), by norm_num⟩
  | 4 => ⟨((-883658979/4294967296), (208078637/1073741824)), (455/4294967296), by norm_num⟩
  | 5 => ⟨((143952313/1073741824), (-271176115/2147483648)), (149/2147483648), by norm_num⟩
  | 6 => ⟨((-625347377/8589934592), (294505987/4294967296)), (325/8589934592), by norm_num⟩
  | 7 => ⟨((582126321/17179869184), (-274151125/8589934592)), (19/1073741824), by norm_num⟩
  | 8 => ⟨((-237077969/17179869184), (893210831/68719476736)), (497/68719476736), by norm_num⟩
  | 9 => ⟨((343299071/68719476736), (-161675951/34359738368)), (181/68719476736), by norm_num⟩
  | 10 => ⟨((-223700303/137438953472), (421404685/274877906944)), (473/549755813888), by norm_num⟩
  | 11 => ⟨((1060126811/2199023255552), (-998528833/2199023255552)), (563/2199023255552), by norm_num⟩
  | 12 => ⟨((-143916479/1099511627776), (271108611/2199023255552)), (77/1099511627776), by norm_num⟩
  | 13 => ⟨((577100039/17592186044416), (-543568017/17592186044416)), (311/17592186044416), by norm_num⟩
  | 14 => ⟨((-1074427223/140737488355328), (126499791/17592186044416)), (291/70368744177664), by norm_num⟩
  | 15 => ⟨((933490031/562949953421312), (-109906275/70368744177664)), (507/562949953421312), by norm_num⟩
  | 16 => ⟨((-47521885/140737488355328), (179042627/562949953421312)), (415/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (3035323055/9903520314283042199192993792)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888814360478219/316912650057057350374175801344), (1836946831099/316912650057057350374175801344)), (46281/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888459222176993/39614081257132168796771975168), (258257344809/2475880078570760549798248448)), (208311/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236019251029403/309485009821345068724781056), (4389115347751/2475880078570760549798248448)), (27673/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442455029958299/38685626227668133590597632), (548462359771/19342813113834066795298816)), (221445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548268372099859/9671406556917033397649408), (4111963192817/9671406556917033397649408)), (103835/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257664116195677/604462909807314587353088), (899115960751/151115727451828646838272)), (11361/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885964350322191/75557863725914323419136), (5841435015901/75557863725914323419136)), (147753/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648084222124475/2361183241434822606848), (1094652763097/1180591620717411303424)), (27717/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809781295668997/295147905179352825856), (3008293220139/295147905179352825856)), (152529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455279284350789/18446744073709551616), (7514731279303/73786976294838206464)), (190791/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28437561325833/144115188075855872), (2111456632725/2305843009213693952)), (429635/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795625714340585/576460752303423488), (8435528244325/1152921504606846976)), (105/281474976710656), by norm_num⟩
  | 5 => ⟨((298046754048721/36028797018963968), (3684757287733/72057594037927936)), (188411/72057594037927936), by norm_num⟩
  | 4 => ⟨((744022283571671/18014398509481984), (11031158902275/36028797018963968)), (566237/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484762813946703/9007199254740992), (13748573602891/9007199254740992)), (177389/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109473540465611/2251799813685248), (27376312488551/4503599627370496)), (1424403/4503599627370496), by norm_num⟩
  | 1 => ⟨((550643695027639/562949953421312), (20381698488757/1125899906842624)), (2149877/2251799813685248), by norm_num⟩
  | 0 => ⟨((538392377732377/562949953421312), (80328587416435/2251799813685248)), (4353095/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538392377732377/562949953421312), (80328587416435/2251799813685248)), (16605739602095793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056758743961869/2251799813685248), (19206103009769/281474976710656)), (8636977/2251799813685248), by norm_num⟩
  | 2 => ⟨((934063619722593/1125899906842624), (280680867368053/2251799813685248)), (4239107/562949953421312), by norm_num⟩
  | 3 => ⟨((189355066818087/281474976710656), (465714199579069/2251799813685248)), (4045221/281474976710656), by norm_num⟩
  | 4 => ⟨((230687927583749/562949953421312), (19581079730863/70368744177664)), (28463567/1125899906842624), by norm_num⟩
  | 5 => ⟨((101885164104923/1125899906842624), (1027073881906503/4503599627370496)), (156674397/4503599627370496), by norm_num⟩
  | 6 => ⟨((-197351329114137/4503599627370496), (743537434331105/18014398509481984)), (199633537/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-717884383/8388608)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1452400067/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((45947030240577/4503599627370496), (1033493531182487/18014398509481984)), (322631805/18014398509481984), by norm_num⟩
  | 1 => ⟨((-288837273/8589934592), (-1624215165/8589934592)), (509/8589934592), by norm_num⟩
  | 2 => ⟨((237990133/4294967296), (1338287055/4294967296)), (421/4294967296), by norm_num⟩
  | 3 => ⟨((-261458885/4294967296), (-367564651/1073741824)), (465/4294967296), by norm_num⟩
  | 4 => ⟨((107715729/2147483648), (1211433127/4294967296)), (385/4294967296), by norm_num⟩
  | 5 => ⟨((-284010777/8589934592), (-99817149/536870912)), (255/4294967296), by norm_num⟩
  | 6 => ⟨((156008865/8589934592), (219320693/2147483648)), (281/8589934592), by norm_num⟩
  | 7 => ⟨((-293817011/34359738368), (-826108829/17179869184)), (531/34359738368), by norm_num⟩
  | 8 => ⟨((121046617/34359738368), (1361359967/68719476736)), (439/68719476736), by norm_num⟩
  | 9 => ⟨((-44327767/34359738368), (-997071193/137438953472)), (323/137438953472), by norm_num⟩
  | 10 => ⟨((116877671/274877906944), (657236799/274877906944)), (107/137438953472), by norm_num⟩
  | 11 => ⟨((-35019067/274877906944), (-1575378379/2199023255552)), (515/2199023255552), by norm_num⟩
  | 12 => ⟨((307779019/8796093022208), (865365023/4398046511104)), (71/1099511627776), by norm_num⟩
  | 13 => ⟨((-312119827/35184372088832), (-1755139659/35184372088832)), (289/17592186044416), by norm_num⟩
  | 14 => ⟨((4592393/2199023255552), (413189571/35184372088832)), (273/70368744177664), by norm_num⟩
  | 15 => ⟨((-8072415/17592186044416), (-1452592449/562949953421312)), (241/281474976710656), by norm_num⟩
  | 16 => ⟨((26605363/281474976710656), (149609617/281474976710656)), (399/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1816888247083/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444395842796535/158456325028528675187087900672), (2147467304617/633825300114114700748351602688)), (184823/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888408476316853/39614081257132168796771975168), (603827220875/9903520314283042199192993792)), (103977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888100457174525/2475880078570760549798248448), (2565521719097/2475880078570760549798248448)), (220983/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442441745126741/38685626227668133590597632), (2564685166053/154742504910672534362390528)), (110509/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774109495541549/4835703278458516698824704), (2403503860985/9671406556917033397649408)), (103621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314405336123825/151115727451828646838272), (2102177796123/604462909807314587353088)), (181375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117868479014125/4722366482869645213696), (3414374613987/75557863725914323419136)), (294805/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296117644479321/4722366482869645213696), (2559325542895/4722366482869645213696)), (221165/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809746950785049/295147905179352825856), (879177289711/147573952589676412928)), (304203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821033012201497/73786976294838206464), (4392344036827/73786976294838206464)), (380405/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909955833869011/4611686018427387904), (4936520742779/9223372036854775808)), (428165/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591162144271823/1152921504606846976), (4930444639307/1152921504606846976)), (428425/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192112227070213/144115188075855872), (4307312741173/144115188075855872)), (187583/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487939029069277/36028797018963968), (6447339689779/36028797018963968)), (563337/36028797018963968), by norm_num⟩
  | 3 => ⟨((92790154227243/562949953421312), (1004421908891/1125899906842624)), (705203/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218740903644227/4503599627370496), (15999560683237/4503599627370496)), (176689/562949953421312), by norm_num⟩
  | 1 => ⟨((17205867641885/17592186044416), (23822093042075/2251799813685248)), (532015/562949953421312), by norm_num⟩
  | 0 => ⟨((2153459800220671/2251799813685248), (46939538893345/2251799813685248)), (4287471/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153459800220671/2251799813685248), (46939538893345/2251799813685248)), (16355403908736418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058435995369005/2251799813685248), (44889607607829/1125899906842624)), (1047401/281474976710656), by norm_num⟩
  | 2 => ⟨((1878096984396137/2251799813685248), (82069803502401/1125899906842624)), (3996879/562949953421312), by norm_num⟩
  | 3 => ⟨((388612083869219/562949953421312), (273798851089855/2251799813685248)), (7249821/562949953421312), by norm_num⟩
  | 4 => ⟨((259941381398477/562949953421312), (94503553500959/562949953421312)), (5886165/281474976710656), by norm_num⟩
  | 5 => ⟨((6510192400615/35184372088832), (698190213032153/4503599627370496)), (118593643/4503599627370496), by norm_num⟩
  | 6 => ⟨((45947030240577/4503599627370496), (1033493531182487/18014398509481984)), (322631805/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1452400067/16777216)), (1/8388608), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile037Terms3
