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
namespace Reinmann.XiBand97.Tile016Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53459/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53459/2560))
  have he : value ((69/80), (53459/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1082943331/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-90986573744511/9007199254740992), (-1239217473530729/18014398509481984)), (423120811/18014398509481984), by norm_num⟩
  | 1 => ⟨((268214571/8589934592), (1826512251/8589934592)), (313/4294967296), by norm_num⟩
  | 2 => ⟨((-25908207/536870912), (-1411456727/4294967296)), (243/2147483648), by norm_num⟩
  | 3 => ⟨((213555647/4294967296), (181786361/536870912)), (503/4294967296), by norm_num⟩
  | 4 => ⟨((-165027393/4294967296), (-1123818719/4294967296)), (391/4294967296), by norm_num⟩
  | 5 => ⟨((204042671/8589934592), (347377137/2147483648)), (485/8589934592), by norm_num⟩
  | 6 => ⟨((-210234853/17179869184), (-1431676637/17179869184)), (251/8589934592), by norm_num⟩
  | 7 => ⟨((185669959/34359738368), (1264392361/34359738368)), (445/34359738368), by norm_num⟩
  | 8 => ⟨((-143478431/68719476736), (-122134077/8589934592)), (173/34359738368), by norm_num⟩
  | 9 => ⟨((197110187/274877906944), (1342299083/274877906944)), (477/274877906944), by norm_num⟩
  | 10 => ⟨((-121855191/549755813888), (-414910345/274877906944)), (37/68719476736), by norm_num⟩
  | 11 => ⟨((34241779/549755813888), (466365633/1099511627776)), (167/1099511627776), by norm_num⟩
  | 12 => ⟨((-141123723/8796093022208), (-480518657/4398046511104)), (173/4398046511104), by norm_num⟩
  | 13 => ⟨((268442719/70368744177664), (914032965/35184372088832)), (661/70368744177664), by norm_num⟩
  | 14 => ⟨((-118538263/140737488355328), (-807232771/140737488355328)), (293/140737488355328), by norm_num⟩
  | 15 => ⟨((97708481/562949953421312), (166346051/140737488355328)), (485/1125899906842624), by norm_num⟩
  | 16 => ⟨((-151010531/4503599627370496), (-1028365411/4503599627370496)), (377/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-1118031243839/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888927044083485/316912650057057350374175801344), (-2643680851663/633825300114114700748351602688)), (184921/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472178222404851/9903520314283042199192993792), (-743363108921/9903520314283042199192993792)), (104035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472105927892921/618970019642690137449562112), (-1579216931915/1237940039285380274899124224)), (221113/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770090027228965/154742504910672534362390528), (-3157467488995/154742504910672534362390528)), (221157/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548521626855607/9671406556917033397649408), (-2959099358971/9671406556917033397649408)), (51845/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628942965204047/302231454903657293676544), (-10110101303/2361183241434822606848)), (181505/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886325203406415/75557863725914323419136), (-4203879245017/75557863725914323419136)), (36879/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296439437852457/4722366482869645213696), (-1575613880921/2361183241434822606848)), (110675/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619935781374931/590295810358705651712), (-1082551768247/147573952589676412928)), (9515/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821584483814591/73786976294838206464), (-2704332510353/36893488147419103232)), (190393/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820530867450239/9223372036854775808), (-6079123738983/9223372036854775808)), (13395/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591779839056755/1152921504606846976), (-6072100113199/1152921504606846976)), (428961/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596325510121721/72057594037927936), (-5305195479945/144115188075855872)), (375701/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488743847487833/36028797018963968), (-3971016303513/18014398509481984)), (564275/36028797018963968), by norm_num⟩
  | 3 => ⟨((742821304596993/4503599627370496), (-2475003194007/2251799813685248)), (353305/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220723615713579/4503599627370496), (-19717653627431/4503599627370496)), (1417027/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102640727279183/1125899906842624), (-29371291203463/2251799813685248)), (533773/562949953421312), by norm_num⟩
  | 0 => ⟨((2159147435186779/2251799813685248), (-57926256841319/2251799813685248)), (2154287/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159147435186779/2251799813685248), (-57926256841319/2251799813685248)), (8217952732566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517204301125007/562949953421312), (-55542827621171/1125899906842624)), (2121065/562949953421312), by norm_num⟩
  | 2 => ⟨((1895223801377939/2251799813685248), (-102058767987197/1125899906842624)), (16426739/2251799813685248), by norm_num⟩
  | 3 => ⟨((788304818936589/1125899906842624), (-343590411639817/2251799813685248)), (30629129/2251799813685248), by norm_num⟩
  | 4 => ⟨((32857655197557/70368744177664), (-120283328735515/562949953421312)), (816209/35184372088832), by norm_num⟩
  | 5 => ⟨((776309905653575/4503599627370496), (-56164539921695/281474976710656)), (8888209/281474976710656), by norm_num⟩
  | 6 => ⟨((-90986573744511/9007199254740992), (-1239217473530729/18014398509481984)), (423120811/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1082943331/16777216)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1098516957/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-529858213404633/9007199254740992), (-574437993561045/18014398509481984)), (109311571/9007199254740992), by norm_num⟩
  | 1 => ⟨((198050423/1073741824), (214713455/2147483648)), (165/4294967296), by norm_num⟩
  | 2 => ⟨((-1241971911/4294967296), (-168308199/1073741824)), (261/4294967296), by norm_num⟩
  | 3 => ⟨((40564539/134217728), (703639179/4294967296)), (275/4294967296), by norm_num⟩
  | 4 => ⟨((-1017519019/4294967296), (-34472759/268435456)), (217/4294967296), by norm_num⟩
  | 5 => ⟨((1276169999/8589934592), (691770473/8589934592)), (137/4294967296), by norm_num⟩
  | 6 => ⟨((-1333807883/17179869184), (-723014105/17179869184)), (289/17179869184), by norm_num⟩
  | 7 => ⟨((1194899115/34359738368), (647716155/34359738368)), (261/34359738368), by norm_num⟩
  | 8 => ⟨((-117081227/8589934592), (-126931891/17179869184)), (103/34359738368), by norm_num⟩
  | 9 => ⟨((1305271147/274877906944), (353772631/137438953472)), (289/274877906944), by norm_num⟩
  | 10 => ⟨((-409267013/274877906944), (-443700815/549755813888)), (183/549755813888), by norm_num⟩
  | 11 => ⟨((233318973/549755813888), (505898669/2199023255552)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((-487713527/4398046511104), (-264373725/4398046511104)), (111/4398046511104), by norm_num⟩
  | 13 => ⟨((58816267/2199023255552), (255059165/17592186044416)), (27/4398046511104), by norm_num⟩
  | 14 => ⟨((-843054011/140737488355328), (-456992307/140737488355328)), (195/140737488355328), by norm_num⟩
  | 15 => ⟨((176226065/140737488355328), (95526449/140737488355328)), (41/140737488355328), by norm_num⟩
  | 16 => ⟨((-1105111615/4503599627370496), (-599045257/4503599627370496)), (259/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1722612679441/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777789894198477/633825300114114700748351602688), (-4073007569499/633825300114114700748351602688)), (46301/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888640406087679/39614081257132168796771975168), (-4581045274341/39614081257132168796771975168)), (104203/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888346339880581/2475880078570760549798248448), (-608252016513/309485009821345068724781056)), (55373/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770012253328267/154742504910672534362390528), (-2432251997307/77371252455336267181195264)), (110779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548448286844725/9671406556917033397649408), (-4558866304675/9671406556917033397649408)), (103891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257821331334459/604462909807314587353088), (-498425292311/75557863725914323419136)), (90941/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943109715492531/37778931862957161709568), (-6476519241927/75557863725914323419136)), (147845/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162044926294493/590295810358705651712), (-4854757156369/4722366482869645213696)), (110943/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619824610673211/590295810358705651712), (-6671015683413/590295810358705651712)), (152641/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821443823979919/73786976294838206464), (-8332360064861/73786976294838206464)), (190945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820370297187649/9223372036854775808), (-9365097757899/9223372036854775808)), (107505/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591616365870133/1152921504606846976), (-4677048657865/576460752303423488)), (215257/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596252362520991/72057594037927936), (-8172471617373/144115188075855872)), (188627/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488517916381121/36028797018963968), (-12234010263357/36028797018963968)), (283497/36028797018963968), by norm_num⟩
  | 3 => ⟨((371337223676389/2251799813685248), (-7624680035129/4503599627370496)), (177673/4503599627370496), by norm_num⟩
  | 2 => ⟨((138756406251737/281474976710656), (-30369530912405/4503599627370496)), (356811/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204266314408999/2251799813685248), (-45232264716851/2251799813685248)), (538891/1125899906842624), by norm_num⟩
  | 0 => ⟨((134799235474555/140737488355328), (-89182049253843/2251799813685248)), (2185093/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((134799235474555/140737488355328), (-89182049253843/2251799813685248)), (8335468300826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062252607139731/2251799813685248), (-42709558760635/562949953421312)), (4358873/2251799813685248), by norm_num⟩
  | 2 => ⟨((937849822935581/1125899906842624), (-156457778117959/1125899906842624)), (2161329/562949953421312), by norm_num⟩
  | 3 => ⟨((1518932986582463/2251799813685248), (-65162941489315/281474976710656)), (16805465/2251799813685248), by norm_num⟩
  | 4 => ⟨((903899197864607/2251799813685248), (-43955124576051/140737488355328)), (7613271/562949953421312), by norm_num⟩
  | 5 => ⟨((286373767292913/4503599627370496), (-1129222989855275/4503599627370496)), (86941343/4503599627370496), by norm_num⟩
  | 6 => ⟨((-529858213404633/9007199254740992), (-574437993561045/18014398509481984)), (109311571/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1098516957/16777216)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1113427671/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-536903031874043/9007199254740992), (221962392643161/9007199254740992)), (416136775/18014398509481984), by norm_num⟩
  | 1 => ⟨((813630455/4294967296), (-42045619/536870912)), (317/4294967296), by norm_num⟩
  | 2 => ⟨((-323220173/1073741824), (267246481/2147483648)), (253/2147483648), by norm_num⟩
  | 3 => ⟨((342403703/1073741824), (-283107901/2147483648)), (269/2147483648), by norm_num⟩
  | 4 => ⟨((-136022175/536870912), (449866075/4294967296)), (215/2147483648), by norm_num⟩
  | 5 => ⟨((1383314541/8589934592), (-571879441/8589934592)), (549/8589934592), by norm_num⟩
  | 6 => ⟨((-1465416025/17179869184), (18931913/536870912)), (583/17179869184), by norm_num⟩
  | 7 => ⟨((1330620289/34359738368), (-275047491/17179869184)), (133/8589934592), by norm_num⟩
  | 8 => ⟨((-528597863/34359738368), (218528933/34359738368)), (425/68719476736), by norm_num⟩
  | 9 => ⟨((1493255523/274877906944), (-617330411/274877906944)), (301/137438953472), by norm_num⟩
  | 10 => ⟨((-949129287/549755813888), (392381855/549755813888)), (385/549755813888), by norm_num⟩
  | 11 => ⟨((1096866897/2199023255552), (-453458421/2199023255552)), (447/2199023255552), by norm_num⟩
  | 12 => ⟨((-290491837/2199023255552), (480371757/8796093022208)), (119/2199023255552), by norm_num⟩
  | 13 => ⟨((284061137/8796093022208), (-469737631/35184372088832)), (467/35184372088832), by norm_num⟩
  | 14 => ⟨((-1031727525/140737488355328), (426528993/140737488355328)), (213/70368744177664), by norm_num⟩
  | 15 => ⟨((874369497/562949953421312), (-361475227/562949953421312)), (363/562949953421312), by norm_num⟩
  | 16 => ⟨((-173674583/562949953421312), (574393865/4503599627370496)), (579/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (1790815885777/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777732648622523/633825300114114700748351602688), (4234012907577/633825300114114700748351602688)), (92617/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888575981508513/39614081257132168796771975168), (297632328929/2475880078570760549798248448)), (104221/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944138927495527/1237940039285380274899124224), (632291607283/309485009821345068724781056)), (55383/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769943730513275/154742504910672534362390528), (2528369715225/77371252455336267181195264)), (110801/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193548000807773/1208925819614629174706176), (1184750168587/2417851639229258349412352)), (103913/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257765045815119/604462909807314587353088), (518116697801/75557863725914323419136)), (181923/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886127891794977/75557863725914323419136), (6732345691941/75557863725914323419136)), (295763/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20254542035465/73786976294838206464), (1261621361695/1180591620717411303424)), (27743/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619730014036521/590295810358705651712), (433400759759/36893488147419103232)), (76343/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821325418815729/73786976294838206464), (8661260919141/73786976294838206464)), (382013/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910118436455091/4611686018427387904), (1216829681937/1152921504606846976)), (430175/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99467666843877/72057594037927936), (4861522591879/576460752303423488)), (13459/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192387435982339/144115188075855872), (8494635710011/144115188075855872)), (377429/144115188075855872), by norm_num⟩
  | 4 => ⟨((186042672090041/4503599627370496), (12715927112695/36028797018963968)), (141825/9007199254740992), by norm_num⟩
  | 3 => ⟨((185640895892917/1125899906842624), (7924716397859/4503599627370496)), (711153/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219655916399605/4503599627370496), (7890679520195/1125899906842624)), (89275/281474976710656), by norm_num⟩
  | 1 => ⟨((275448590481597/281474976710656), (23502345499543/1125899906842624)), (539471/562949953421312), by norm_num⟩
  | 0 => ⟨((2155402359328229/2251799813685248), (92657732895877/2251799813685248)), (2188593/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155402359328229/2251799813685248), (92657732895877/2251799813685248)), (8348819736960982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2059318882144853/2251799813685248), (177382283167463/2251799813685248)), (4369917/1125899906842624), by norm_num⟩
  | 2 => ⟨((934658968882257/1125899906842624), (324439750696045/2251799813685248)), (17362465/2251799813685248), by norm_num⟩
  | 3 => ⟨((752528794970889/1125899906842624), (538663376747873/2251799813685248)), (16914933/1125899906842624), by norm_num⟩
  | 4 => ⟨((438547002177699/1125899906842624), (720063478707947/2251799813685248)), (30703799/1125899906842624), by norm_num⟩
  | 5 => ⟨((6961167173447/140737488355328), (1121881893926313/4503599627370496)), (43555207/1125899906842624), by norm_num⟩
  | 6 => ⟨((-536903031874043/9007199254740992), (221962392643161/9007199254740992)), (416136775/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1113427671/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-281932403/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-179793470112143/9007199254740992), (1062554834880981/18014398509481984)), (197261069/9007199254740992), by norm_num⟩
  | 1 => ⟨((137980665/2147483648), (-815446871/4294967296)), (305/4294967296), by norm_num⟩
  | 2 => ⟨((-444142627/4294967296), (656205555/2147483648)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((476546655/4294967296), (-704081399/2147483648)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-383486127/4294967296), (1133175297/4294967296)), (107/1073741824), by norm_num⟩
  | 5 => ⟨((493757689/8589934592), (-364755057/2147483648)), (553/8589934592), by norm_num⟩
  | 6 => ⟨((-529781563/17179869184), (782734157/8589934592)), (149/4294967296), by norm_num⟩
  | 7 => ⟨((121807219/8589934592), (-44991501/1073741824)), (275/17179869184), by norm_num⟩
  | 8 => ⟨((-392082313/68719476736), (1158576439/68719476736)), (445/68719476736), by norm_num⟩
  | 9 => ⟨((280458729/137438953472), (-103592047/17179869184)), (5/2147483648), by norm_num⟩
  | 10 => ⟨((-361104729/549755813888), (1067039795/549755813888)), (207/274877906944), by norm_num⟩
  | 11 => ⟨((211336597/1099511627776), (-39030325/68719476736)), (487/2199023255552), by norm_num⟩
  | 12 => ⟨((-226755421/4398046511104), (670046771/4398046511104)), (525/8796093022208), by norm_num⟩
  | 13 => ⟨((449167719/35184372088832), (-663629955/17592186044416)), (261/17592186044416), by norm_num⟩
  | 14 => ⟨((-25818127/8796093022208), (1220652811/140737488355328)), (241/70368744177664), by norm_num⟩
  | 15 => ⟨((354582805/562949953421312), (-1047767953/562949953421312)), (13/17592186044416), by norm_num⟩
  | 16 => ⟨((-285339505/2251799813685248), (421579367/1125899906842624)), (21/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (308900586451/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777683471529471/633825300114114700748351602688), (2921155654961/633825300114114700748351602688)), (184975/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472130236665641/9903520314283042199192993792), (1642754315053/19807040628566084398385987584)), (208135/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59006867744527/77371252455336267181195264), (872466010267/618970019642690137449562112)), (110593/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769886078652535/154742504910672534362390528), (3488752010843/154742504910672534362390528)), (110617/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48385325624327/302231454903657293676544), (3269523902411/9671406556917033397649408)), (207459/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628859309677125/302231454903657293676544), (1429826392087/302231454903657293676544)), (90789/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943026656803875/37778931862957161709568), (4644723106155/75557863725914323419136)), (36895/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324058878110289/1180591620717411303424), (1740803629267/2361183241434822606848)), (110727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809827685516607/295147905179352825856), (4784067389473/590295810358705651712)), (76159/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910616975942619/36893488147419103232), (2987686836351/36893488147419103232)), (381001/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820136493468693/9223372036854775808), (6715823751697/9223372036854775808)), (428909/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397846358493163/288230376151711744), (6707742301765/1152921504606846976)), (429263/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596152940984277/72057594037927936), (2930096997079/72057594037927936)), (94001/36028797018963968), by norm_num⟩
  | 4 => ⟨((744113037662195/18014398509481984), (8772157701845/36028797018963968)), (564805/36028797018963968), by norm_num⟩
  | 3 => ⟨((371248821794911/2251799813685248), (5466763116355/4503599627370496)), (353703/4503599627370496), by norm_num⟩
  | 2 => ⟨((554857169288265/1125899906842624), (2721536105823/562949953421312)), (1419021/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203338400496503/2251799813685248), (16211197115081/1125899906842624)), (534773/562949953421312), by norm_num⟩
  | 0 => ⟨((2155259278561869/2251799813685248), (15976459648845/562949953421312)), (2160315/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155259278561869/2251799813685248), (15976459648845/562949953421312)), (8240947727683639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030522023630731/1125899906842624), (122332057006043/2251799813685248)), (4258013/1125899906842624), by norm_num⟩
  | 2 => ⟨((939900919889731/1125899906842624), (111968993135727/1125899906842624)), (16514513/2251799813685248), by norm_num⟩
  | 3 => ⟨((773493876758499/1125899906842624), (46735841706623/281474976710656)), (7714327/562949953421312), by norm_num⟩
  | 4 => ⟨((1000701663724733/2251799813685248), (128430199400595/562949953421312)), (52645015/2251799813685248), by norm_num⟩
  | 5 => ⟨((655026932154555/4503599627370496), (913191756614215/4503599627370496)), (70811619/2251799813685248), by norm_num⟩
  | 6 => ⟨((-179793470112143/9007199254740992), (1062554834880981/18014398509481984)), (197261069/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-281932403/4194304)), (1/8388608), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-570735273/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((512950989250693/18014398509481984), (238863186851843/4503599627370496)), (291841427/18014398509481984), by norm_num⟩
  | 1 => ⟨((-199227791/2147483648), (-371093427/2147483648)), (57/1073741824), by norm_num⟩
  | 2 => ⟨((40568961/268435456), (604529105/2147483648)), (373/4294967296), by norm_num⟩
  | 3 => ⟨((-352473577/2147483648), (-1313076123/4294967296)), (407/4294967296), by norm_num⟩
  | 4 => ⟨((574196471/4294967296), (1069532193/4294967296)), (167/2147483648), by norm_num⟩
  | 5 => ⟨((-374157507/4294967296), (-696927827/4294967296)), (219/4294967296), by norm_num⟩
  | 6 => ⟨((406347093/8589934592), (756886047/8589934592)), (239/8589934592), by norm_num⟩
  | 7 => ⟨((-189131151/8589934592), (-176143415/4294967296)), (7/536870912), by norm_num⟩
  | 8 => ⟨((154051887/17179869184), (1147784501/68719476736)), (367/68719476736), by norm_num⟩
  | 9 => ⟨((-111536871/34359738368), (-415510301/68719476736)), (267/137438953472), by norm_num⟩
  | 10 => ⟨((581436629/549755813888), (1083018139/549755813888)), (175/274877906944), by norm_num⟩
  | 11 => ⟨((-688864243/2199023255552), (-1283119145/2199023255552)), (417/2199023255552), by norm_num⟩
  | 12 => ⟨((748128735/8796093022208), (696754341/4398046511104)), (455/8796093022208), by norm_num⟩
  | 13 => ⟨((-749992505/35184372088832), (-698490125/17592186044416)), (229/17592186044416), by norm_num⟩
  | 14 => ⟨((698156567/140737488355328), (162553447/17592186044416)), (107/35184372088832), by norm_num⟩
  | 15 => ⟨((-303288199/281474976710656), (-282461239/140737488355328)), (187/281474976710656), by norm_num⟩
  | 16 => ⟨((123517779/562949953421312), (920285985/2251799813685248)), (153/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (1404335151497/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817242522045/316912650057057350374175801344), (1659940309225/633825300114114700748351602688)), (184727/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944233009788425/19807040628566084398385987584), (466745322183/9903520314283042199192993792)), (207839/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472040413141735/618970019642690137449562112), (495774809261/618970019642690137449562112)), (220853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884914119220411/77371252455336267181195264), (991230067921/77371252455336267181195264)), (220881/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548276486778183/9671406556917033397649408), (1857877609681/9671406556917033397649408)), (103553/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257671719533773/604462909807314587353088), (1624964452953/604462909807314587353088)), (181247/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885977647822807/75557863725914323419136), (2639295794939/75557863725914323419136)), (294581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648089620326681/2361183241434822606848), (1978359997835/4722366482869645213696)), (27623/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404894693069609/147573952589676412928), (339804935623/73786976294838206464)), (151965/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821139364007077/73786976294838206464), (1697671629639/36893488147419103232)), (380029/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227503959357065/1152921504606846976), (477005476047/1152921504606846976)), (427695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591282601765801/1152921504606846976), (3811402392649/1152921504606846976)), (427897/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596109066135685/72057594037927936), (1664881377595/72057594037927936)), (374637/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488098892223341/36028797018963968), (4984233565871/36028797018963968)), (562411/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484844045994473/9007199254740992), (6212114141133/9007199254740992)), (351907/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219149268953569/4503599627370496), (12369857181579/4503599627370496)), (1410035/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202976489467319/2251799813685248), (18419424641193/2251799813685248)), (2121097/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077380686303689/1125899906842624), (36300791735853/2251799813685248)), (533317/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077380686303689/1125899906842624), (36300791735853/2251799813685248)), (2034442902685069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1030659740974867/1125899906842624), (69472910826357/2251799813685248)), (8302911/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884808540942565/2251799813685248), (63596179235737/1125899906842624)), (7856729/1125899906842624), by norm_num⟩
  | 3 => ⟨((785221962997019/1125899906842624), (53231473360263/562949953421312)), (28080199/2251799813685248), by norm_num⟩
  | 4 => ⟨((134390092864861/281474976710656), (296996361762817/2251799813685248)), (44477649/2251799813685248), by norm_num⟩
  | 5 => ⟨((237072089282833/1125899906842624), (283601541453257/2251799813685248)), (13551059/562949953421312), by norm_num⟩
  | 6 => ⟨((512950989250693/18014398509481984), (238863186851843/4503599627370496)), (291841427/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-570735273/8388608)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-288673207/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1005881533068765/18014398509481984), (300148786161341/18014398509481984)), (85199085/9007199254740992), by norm_num⟩
  | 1 => ⟨((-790410385/4294967296), (-235853537/4294967296)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((1302531843/4294967296), (388667391/4294967296)), (7/134217728), by norm_num⟩
  | 3 => ⟨((-1430977489/4294967296), (-106748693/1073741824)), (31/536870912), by norm_num⟩
  | 4 => ⟨((1179067091/4294967296), (175913139/2147483648)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((-777202557/4294967296), (-463824807/8589934592)), (137/4294967296), by norm_num⟩
  | 6 => ⟨((106730535/1073741824), (31847727/1073741824)), (19/1073741824), by norm_num⟩
  | 7 => ⟨((-804037559/17179869184), (-479839601/34359738368)), (9/1073741824), by norm_num⟩
  | 8 => ⟨((662494157/34359738368), (197684131/34359738368)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((-121304037/17179869184), (-144785477/68719476736)), (11/8589934592), by norm_num⟩
  | 10 => ⟨((1279354615/549755813888), (190875725/274877906944)), (117/274877906944), by norm_num⟩
  | 11 => ⟨((-1533288765/2199023255552), (-457523819/2199023255552)), (283/2199023255552), by norm_num⟩
  | 12 => ⟨((210561235/1099511627776), (251320645/4398046511104)), (157/4398046511104), by norm_num⟩
  | 13 => ⟨((-854123669/17592186044416), (-7964537/549755813888)), (161/17592186044416), by norm_num⟩
  | 14 => ⟨((1608601301/140737488355328), (479996611/140737488355328)), (305/140737488355328), by norm_num⟩
  | 15 => ⟨((-1413783325/562949953421312), (-105466035/140737488355328)), (135/281474976710656), by norm_num⟩
  | 16 => ⟨((1164899801/2251799813685248), (173799423/1125899906842624)), (7/70368744177664), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (94433659205/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777585739024979/633825300114114700748351602688), (446462672481/633825300114114700748351602688)), (23061/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888411268405869/39614081257132168796771975168), (125537033397/9903520314283042199192993792)), (207555/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051798573547/1237940039285380274899124224), (533377795563/2475880078570760549798248448)), (110267/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769770315276923/154742504910672534362390528), (66650496591/19342813113834066795298816)), (110271/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548222324222037/9671406556917033397649408), (499694117569/9671406556917033397649408)), (103383/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628812233790529/302231454903657293676544), (437047835953/604462909807314587353088)), (2827/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1885901126164247/75557863725914323419136), (177464238805/18889465931478580854784)), (294023/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324030519765245/1180591620717411303424), (66511293923/590295810358705651712)), (220531/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202437568471455/73786976294838206464), (22847913989/18446744073709551616)), (75813/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821042141521937/73786976294838206464), (456590353349/36893488147419103232)), (47387/9223372036854775808), by norm_num⟩
  | 7 => ⟨((7109074474975/36028797018963968), (1026317512637/9223372036854775808)), (13329/288230376151711744), by norm_num⟩
  | 6 => ⟨((198896868489461/144115188075855872), (512527777925/576460752303423488)), (426583/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149015625883887/18014398509481984), (223876499715/36028797018963968)), (93331/36028797018963968), by norm_num⟩
  | 4 => ⟨((743980670487295/18014398509481984), (1340428987107/36028797018963968)), (560113/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484675829552123/9007199254740992), (1670595422495/9007199254740992)), (700365/9007199254740992), by norm_num⟩
  | 2 => ⟨((34669124043195/70368744177664), (3326415129067/4503599627370496)), (1401409/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202516023881075/2251799813685248), (4952846403703/2251799813685248)), (2103837/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076974603047393/1125899906842624), (9759561548315/2251799813685248)), (2107355/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076974603047393/1125899906842624), (9759561548315/2251799813685248)), (8038921360496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515077084694531/562949953421312), (18670931333299/2251799813685248)), (2024915/562949953421312), by norm_num⟩
  | 2 => ⟨((1884946353297421/2251799813685248), (4270792110933/281474976710656)), (3739015/562949953421312), by norm_num⟩
  | 3 => ⟨((1577340665296551/2251799813685248), (28600105449053/1125899906842624)), (12746411/1125899906842624), by norm_num⟩
  | 4 => ⟨((1103442541903811/2251799813685248), (80135203995299/2251799813685248)), (37009561/2251799813685248), by norm_num⟩
  | 5 => ⟨((1075729543099669/4503599627370496), (157073630888777/4503599627370496)), (4863187/281474976710656), by norm_num⟩
  | 6 => ⟨((1005881533068765/18014398509481984), (300148786161341/18014398509481984)), (85199085/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-288673207/4194304)), (1/8388608), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile016Terms3
