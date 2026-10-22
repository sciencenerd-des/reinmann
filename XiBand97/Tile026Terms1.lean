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
namespace Reinmann.XiBand97.Tile026Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30041/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30041/1280))
  have he : value ((69/80), (30041/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-1730329275/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((359076376350945/9007199254740992), (-1305315231073557/9007199254740992)), (197940799/9007199254740992), by norm_num⟩
  | 1 => ⟨((-376210899/4294967296), (683801343/2147483648)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((413309917/4294967296), (-1502465117/4294967296)), (233/4294967296), by norm_num⟩
  | 3 => ⟨((-302711569/4294967296), (1100417761/4294967296)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((166281325/4294967296), (-1208932475/8589934592)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-292285931/17179869184), (1062518459/17179869184)), (171/17179869184), by norm_num⟩
  | 6 => ⟨((428145221/68719476736), (-97274653/4294967296)), (253/68719476736), by norm_num⟩
  | 7 => ⟨((-33597543/17179869184), (977070895/137438953472)), (161/137438953472), by norm_num⟩
  | 8 => ⟨((295285389/549755813888), (-268355523/137438953472)), (179/549755813888), by norm_num⟩
  | 9 => ⟨((-288359251/2199023255552), (1048244179/2199023255552)), (177/2199023255552), by norm_num⟩
  | 10 => ⟨((253436013/8796093022208), (-921291149/8796093022208)), (79/4398046511104), by norm_num⟩
  | 11 => ⟨((-404986063/70368744177664), (1472206223/70368744177664)), (255/70368744177664), by norm_num⟩
  | 12 => ⟨((148307555/140737488355328), (-1078255899/281474976710656)), (189/281474976710656), by norm_num⟩
  | 13 => ⟨((-401064621/2251799813685248), (91121937/140737488355328)), (129/1125899906842624), by norm_num⟩
  | 14 => ⟨((125889863/4503599627370496), (-915270215/9007199254740992)), (41/2251799813685248), by norm_num⟩
  | 15 => ⟨((-147524427/36028797018963968), (536281123/36028797018963968)), (195/72057594037927936), by norm_num⟩
  | 16 => ⟨((324144297/576460752303423488), (-73645629/36028797018963968)), (27/72057594037927936), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1696454241915/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889521850720205/316912650057057350374175801344), (-2008260191677/633825300114114700748351602688)), (46199/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472512755551807/9903520314283042199192993792), (-2258914951603/39614081257132168796771975168)), (12995/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944922631659637/1237940039285380274899124224), (-1199816456691/1237940039285380274899124224)), (110473/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771511338014161/154742504910672534362390528), (-2399110798883/154742504910672534362390528)), (110489/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96865865604699/604462909807314587353088), (-2248611763017/9671406556917033397649408)), (103601/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259051369312103/604462909807314587353088), (-1966980834363/604462909807314587353088)), (22667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944109280730711/37778931862957161709568), (-3195304570895/75557863725914323419136)), (147369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162232379525595/590295810358705651712), (-1197784689039/2361183241434822606848)), (27639/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202735880777193/73786976294838206464), (-205776956013/36893488147419103232)), (152061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824022540382729/73786976294838206464), (-4113325285473/73786976294838206464)), (190147/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823272272184475/9223372036854775808), (-4624448650297/9223372036854775808)), (214011/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594519482305993/1152921504606846976), (-4620648369695/1152921504606846976)), (214133/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298761556483537/36028797018963968), (-4038795565979/144115188075855872)), (187503/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492332690529099/36028797018963968), (-6049658723365/36028797018963968)), (281527/36028797018963968), by norm_num⟩
  | 3 => ⟨((186265215092679/1125899906842624), (-7547157793997/9007199254740992)), (176193/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114830500844581/2251799813685248), (-7524824306473/2251799813685248)), (353105/2251799813685248), by norm_num⟩
  | 1 => ⟨((277329425669183/281474976710656), (-22463084603807/2251799813685248)), (1062917/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092823309442005/1125899906842624), (-44482287698343/2251799813685248)), (1070145/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092823309442005/1125899906842624), (-44482287698343/2251799813685248)), (4082279209617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120558159610753/2251799813685248), (-43175490608553/1125899906842624)), (2119693/1125899906842624), by norm_num⟩
  | 2 => ⟨((996827157780841/1125899906842624), (-40659093383317/562949953421312)), (8309745/2251799813685248), by norm_num⟩
  | 3 => ⟨((876678050146055/1125899906842624), (-287983599600051/2251799813685248)), (15914583/2251799813685248), by norm_num⟩
  | 4 => ⟨((1328414294473813/2251799813685248), (-448474858265895/2251799813685248)), (7213579/562949953421312), by norm_num⟩
  | 5 => ⟨((347178916563383/1125899906842624), (-529141541634221/2251799813685248)), (45537727/2251799813685248), by norm_num⟩
  | 6 => ⟨((359076376350945/9007199254740992), (-1305315231073557/9007199254740992)), (197940799/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1730329275/33554432)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-453325349/8388608)), (3/33554432), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-498158932155753/4503599627370496), (91476465307953/1125899906842624)), (41997989/1125899906842624), by norm_num⟩
  | 1 => ⟨((546957651/2147483648), (-100437329/536870912)), (371/4294967296), by norm_num⟩
  | 2 => ⟨((-629708267/2147483648), (462530993/2147483648)), (215/2147483648), by norm_num⟩
  | 3 => ⟨((120829739/536870912), (-710011313/4294967296)), (83/1073741824), by norm_num⟩
  | 4 => ⟨((-1112883023/8589934592), (817430733/8589934592)), (385/8589934592), by norm_num⟩
  | 5 => ⟨((128125393/2147483648), (-94110191/2147483648)), (357/17179869184), by norm_num⟩
  | 6 => ⟨((-786718987/34359738368), (72232241/4294967296)), (69/8589934592), by norm_num⟩
  | 7 => ⟨((64695979/8589934592), (-760324029/137438953472)), (365/137438953472), by norm_num⟩
  | 8 => ⟨((-1191743975/549755813888), (218838847/137438953472)), (423/549755813888), by norm_num⟩
  | 9 => ⟨((1219596405/2199023255552), (-223953363/549755813888)), (109/549755813888), by norm_num⟩
  | 10 => ⟨((-1123289801/8796093022208), (103134335/1099511627776)), (101/2199023255552), by norm_num⟩
  | 11 => ⟨((940534673/35184372088832), (-345419029/17592186044416)), (85/8796093022208), by norm_num⟩
  | 12 => ⟨((-721887039/140737488355328), (530237805/140737488355328)), (263/140737488355328), by norm_num⟩
  | 13 => ⟨((511448103/562949953421312), (-187833487/281474976710656)), (375/1125899906842624), by norm_num⟩
  | 14 => ⟨((-672944445/4503599627370496), (494288671/4503599627370496)), (249/4503599627370496), by norm_num⟩
  | 15 => ⟨((826406319/36028797018963968), (-75876115/4503599627370496)), (77/9007199254740992), by norm_num⟩
  | 16 => ⟨((-237858859/72057594037927936), (698844845/288230376151711744)), (357/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (3267047682919/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444724434502267/158456325028528675187087900672), (1933473340833/316912650057057350374175801344)), (138871/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889886509417963/39614081257132168796771975168), (4349540256173/39614081257132168796771975168)), (78133/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944835036045959/1237940039285380274899124224), (2310224102235/1237940039285380274899124224)), (41519/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771335701192619/154742504910672534362390528), (288712042399/9671406556917033397649408)), (166123/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549688717018049/9671406556917033397649408), (4329559301355/9671406556917033397649408)), (155791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258906405445293/604462909807314587353088), (1893621617915/302231454903657293676544)), (8523/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943991054713137/37778931862957161709568), (6152168483085/75557863725914323419136)), (221693/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297680922878495/4722366482869645213696), (4612287695749/4722366482869645213696)), (83177/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621640883529717/590295810358705651712), (6338908473975/590295810358705651712)), (28609/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823712954128137/73786976294838206464), (7919156201471/73786976294838206464)), (71573/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822921402567389/9223372036854775808), (8902893630347/9223372036854775808)), (322359/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398541346795695/288230376151711744), (138987505663/18014398509481984)), (322709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194732772035575/144115188075855872), (1943662415371/36028797018963968)), (70691/36028797018963968), by norm_num⟩
  | 4 => ⟨((186481911049719/4503599627370496), (11644683872377/36028797018963968)), (53117/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489512375874501/9007199254740992), (14525620351335/9007199254740992)), (66569/1125899906842624), by norm_num⟩
  | 2 => ⟨((557101178799217/1125899906842624), (14480316908061/2251799813685248)), (534629/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108328805868581/1125899906842624), (21607386214747/1125899906842624)), (807147/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090660666301021/1125899906842624), (10690859034367/281474976710656)), (1635181/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090660666301021/1125899906842624), (10690859034367/281474976710656)), (6237720493796920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054900147275631/1125899906842624), (41424994768679/562949953421312)), (1646109/562949953421312), by norm_num⟩
  | 2 => ⟨((982281100863787/1125899906842624), (155250863124833/1125899906842624)), (6653739/1125899906842624), by norm_num⟩
  | 3 => ⟨((1671149140160053/2251799813685248), (135447199003659/562949953421312)), (26889925/2251799813685248), by norm_num⟩
  | 4 => ⟨((554934842338527/1125899906842624), (402082758469739/1125899906842624)), (52851711/2251799813685248), by norm_num⟩
  | 5 => ⟨((519698540495921/4503599627370496), (1585432103314905/4503599627370496)), (44924081/1125899906842624), by norm_num⟩
  | 6 => ⟨((-498158932155753/4503599627370496), (91476465307953/1125899906842624)), (41997989/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-453325349/8388608)), (3/33554432), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-944179405/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1097031395963255/9007199254740992), (76254490741559/2251799813685248)), (1404305/140737488355328), by norm_num⟩
  | 1 => ⟨((-627175903/2147483648), (-348759237/4294967296)), (105/4294967296), by norm_num⟩
  | 2 => ⟨((1503902133/4294967296), (418144063/4294967296)), (1/33554432), by norm_num⟩
  | 3 => ⟨((-1202066605/4294967296), (-334221891/4294967296)), (13/536870912), by norm_num⟩
  | 4 => ⟨((1441214915/8589934592), (200357273/4294967296)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-1382352973/17179869184), (-192174303/8589934592)), (31/4294967296), by norm_num⟩
  | 6 => ⟨((1104912553/34359738368), (307209235/34359738368)), (101/34359738368), by norm_num⟩
  | 7 => ⟨((-378494941/34359738368), (-420946041/137438953472)), (141/137438953472), by norm_num⟩
  | 8 => ⟨((453795615/137438953472), (126173065/137438953472)), (87/274877906944), by norm_num⟩
  | 9 => ⟨((-15113255/17179869184), (-8404161/34359738368)), (47/549755813888), by norm_num⟩
  | 10 => ⟨((463872035/2199023255552), (128974707/2199023255552)), (23/1099511627776), by norm_num⟩
  | 11 => ⟨((-404478749/8796093022208), (-449844131/35184372088832)), (163/35184372088832), by norm_num⟩
  | 12 => ⟨((1293196907/140737488355328), (359559705/140737488355328)), (33/35184372088832), by norm_num⟩
  | 13 => ⟨((-238534673/140737488355328), (-265288159/562949953421312)), (99/562949953421312), by norm_num⟩
  | 14 => ⟨((81711595/281474976710656), (363504699/4503599627370496)), (69/2251799813685248), by norm_num⟩
  | 15 => ⟨((-835992949/18014398509481984), (-464877973/36028797018963968)), (179/36028797018963968), by norm_num⟩
  | 16 => ⟨((501155885/72057594037927936), (278682173/144115188075855872)), (55/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (353254895761/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889389455701351/316912650057057350374175801344), (418063242697/633825300114114700748351602688)), (46121/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889753303007729/39614081257132168796771975168), (470236262161/39614081257132168796771975168)), (103775/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889529152925027/2475880078570760549798248448), (499520648237/2475880078570760549798248448)), (13783/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771195470755671/154742504910672534362390528), (499402139723/154742504910672534362390528)), (110267/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774778991161925/4835703278458516698824704), (58507953785/1208925819614629174706176)), (103379/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258792743438873/604462909807314587353088), (25589365333/37778931862957161709568)), (90461/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798777971891/75557863725914323419136), (665087659837/75557863725914323419136)), (147005/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297544621391437/4722366482869645213696), (498609480481/4722366482869645213696)), (27565/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621455412331435/590295810358705651712), (171313258311/147573952589676412928)), (151617/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911742013372321/36893488147419103232), (856064097889/73786976294838206464)), (5923/2305843009213693952), by norm_num⟩
  | 7 => ⟨((14239592634385/72057594037927936), (481191048583/4611686018427387904)), (833/36028797018963968), by norm_num⟩
  | 6 => ⟨((1593916830955207/1152921504606846976), (961520335347/1152921504606846976)), (106637/576460752303423488), by norm_num⟩
  | 5 => ⟨((597260443367329/72057594037927936), (420180923827/72057594037927936)), (46661/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491548634821569/36028797018963968), (314652116901/9007199254740992)), (280023/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489148550210363/9007199254740992), (784940683365/4503599627370496)), (350131/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227735282870931/4503599627370496), (48900754609/70368744177664)), (350285/2251799813685248), by norm_num⟩
  | 1 => ⟨((553949530183523/562949953421312), (1167316853281/562949953421312)), (1051633/2251799813685248), by norm_num⟩
  | 0 => ⟨((1090087828945329/1125899906842624), (2309549908183/562949953421312)), (2106413/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1090087828945329/1125899906842624), (2309549908183/562949953421312)), (8035327919966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2110791787991011/2251799813685248), (17888710923245/2251799813685248)), (4096111/2251799813685248), by norm_num⟩
  | 2 => ⟨((989235796893649/1125899906842624), (33537034584557/2251799813685248)), (7744305/2251799813685248), by norm_num⟩
  | 3 => ⟨((434455262291969/562949953421312), (29466238456081/1125899906842624)), (13839249/2251799813685248), by norm_num⟩
  | 4 => ⟨((669808422525605/1125899906842624), (22740498119579/562949953421312)), (22085197/2251799813685248), by norm_num⟩
  | 5 => ⟨((793276203600849/2251799813685248), (216456572458721/4503599627370496)), (56123313/4503599627370496), by norm_num⟩
  | 6 => ⟨((1097031395963255/9007199254740992), (76254490741559/2251799813685248)), (1404305/140737488355328), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-944179405/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-489220215/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-209993362334679/9007199254740992), (-1035237653889429/9007199254740992)), (179233931/9007199254740992), by norm_num⟩
  | 1 => ⟨((124410129/2147483648), (613324387/2147483648)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-309147557/4294967296), (-1524053847/4294967296)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((256067607/4294967296), (1262377179/4294967296)), (7/134217728), by norm_num⟩
  | 4 => ⟨((-159076025/4294967296), (-1568444723/8589934592)), (281/8589934592), by norm_num⟩
  | 5 => ⟨((158115629/8589934592), (1522437/16777216)), (141/8589934592), by norm_num⟩
  | 6 => ⟨((-65483763/8589934592), (-322825713/8589934592)), (235/34359738368), by norm_num⟩
  | 7 => ⟨((185966901/68719476736), (114598823/8589934592)), (169/68719476736), by norm_num⟩
  | 8 => ⟨((-115527597/137438953472), (-1139069509/274877906944)), (53/68719476736), by norm_num⟩
  | 9 => ⟨((255178039/1099511627776), (314497933/274877906944)), (59/274877906944), by norm_num⟩
  | 10 => ⟨((-126818721/2199023255552), (-156299601/549755813888)), (237/4398046511104), by norm_num⟩
  | 11 => ⟨((114593703/8796093022208), (1129861579/17592186044416)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((-47459109/17592186044416), (-467933425/35184372088832)), (181/70368744177664), by norm_num⟩
  | 13 => ⟨((145146407/281474976710656), (1431102621/562949953421312)), (279/562949953421312), by norm_num⟩
  | 14 => ⟨((-206100155/2251799813685248), (-1016044691/2251799813685248)), (25/281474976710656), by norm_num⟩
  | 15 => ⟨((34142643/2251799813685248), (1346547311/18014398509481984)), (267/18014398509481984), by norm_num⟩
  | 16 => ⟨((-169682561/72057594037927936), (-1673022183/144115188075855872)), (167/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1153414745229/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444664832622205/158456325028528675187087900672), (-1364851815863/316912650057057350374175801344)), (92469/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889618579355191/39614081257132168796771975168), (-95948014943/1237940039285380274899124224)), (104045/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944692876275611/1237940039285380274899124224), (-1630759361627/1237940039285380274899124224)), (13821/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771051782090859/154742504910672534362390528), (-1630357961695/77371252455336267181195264)), (55295/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774711484052399/4835703278458516698824704), (-3056068419989/9671406556917033397649408)), (51851/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314668575035395/151115727451828646838272), (-334150919119/75557863725914323419136)), (90763/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887605734644553/75557863725914323419136), (-4342364001451/75557863725914323419136)), (147535/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297399338057569/4722366482869645213696), (-1627687657469/2361183241434822606848)), (110691/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621254834840025/590295810358705651712), (-1118467697061/147573952589676412928)), (152263/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911616043594593/36893488147419103232), (-1397233694501/18446744073709551616)), (190425/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822382753586761/9223372036854775808), (-3141437142569/4611686018427387904)), (26795/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593629641883835/1152921504606846976), (-1569257936161/288230376151711744)), (214525/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194267255735081/144115188075855872), (-5485835601249/144115188075855872)), (187895/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491163521117141/36028797018963968), (-4107816625435/18014398509481984)), (282213/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488659021726257/9007199254740992), (-1280826653575/1125899906842624)), (353417/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226731941549197/4503599627370496), (-1276535566859/281474976710656)), (708791/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214232832932669/2251799813685248), (-7616414087131/562949953421312)), (1068089/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176806578146699/2251799813685248), (-60249197351457/2251799813685248)), (1077931/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176806578146699/2251799813685248), (-60249197351457/2251799813685248)), (4111980442527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2102698865194539/2251799813685248), (-58242676958069/1125899906842624)), (4283493/2251799813685248), by norm_num⟩
  | 2 => ⟨((1957444730755069/2251799813685248), (-217544756867525/2251799813685248)), (8442901/2251799813685248), by norm_num⟩
  | 3 => ⟨((1680550877445445/2251799813685248), (-378214648962797/2251799813685248)), (8154909/1125899906842624), by norm_num⟩
  | 4 => ⟨((1190694179250597/2251799813685248), (-141133540449345/562949953421312)), (29823337/2251799813685248), by norm_num⟩
  | 5 => ⟨((244038968736367/1125899906842624), (-149255616852585/562949953421312)), (46493269/2251799813685248), by norm_num⟩
  | 6 => ⟨((-209993362334679/9007199254740992), (-1035237653889429/9007199254740992)), (179233931/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-489220215/8388608)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-504978759/8388608)), (3/33554432), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-861410096314897/9007199254740992), (239731793167791/4503599627370496)), (266430959/9007199254740992), by norm_num⟩
  | 1 => ⟨((1053558957/4294967296), (-293207125/2147483648)), (41/536870912), by norm_num⟩
  | 2 => ⟨((-1351162685/4294967296), (752061427/4294967296)), (423/4294967296), by norm_num⟩
  | 3 => ⟨((1155221287/4294967296), (-642999825/4294967296)), (91/1073741824), by norm_num⟩
  | 4 => ⟨((-740771025/4294967296), (412315497/4294967296)), (235/4294967296), by norm_num⟩
  | 5 => ⟨((380008033/4294967296), (-105756837/2147483648)), (243/8589934592), by norm_num⟩
  | 6 => ⟨((-649800907/17179869184), (723362483/34359738368)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((238100917/17179869184), (-33131931/4294967296)), (77/17179869184), by norm_num⟩
  | 8 => ⟨((-305358397/68719476736), (679853801/274877906944)), (397/274877906944), by norm_num⟩
  | 9 => ⟨((696203399/549755813888), (-48438627/68719476736)), (57/137438953472), by norm_num⟩
  | 10 => ⟨((-89286323/274877906944), (397576401/2199023255552)), (59/549755813888), by norm_num⟩
  | 11 => ⟨((1332450309/17592186044416), (-741646061/17592186044416)), (443/17592186044416), by norm_num⟩
  | 12 => ⟨((-1139222521/70368744177664), (634094863/70368744177664)), (381/70368744177664), by norm_num⟩
  | 13 => ⟨((899091715/281474976710656), (-31277331/17592186044416)), (151/140737488355328), by norm_num⟩
  | 14 => ⟨((-1317785553/2251799813685248), (183370903/562949953421312)), (445/2251799813685248), by norm_num⟩
  | 15 => ⟨((450673761/4503599627370496), (-501692885/9007199254740992)), (153/4503599627370496), by norm_num⟩
  | 16 => ⟨((-577977687/36028797018963968), (321704211/36028797018963968)), (395/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (3430680453515/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778548089142687/633825300114114700748351602688), (2029554812799/316912650057057350374175801344)), (138899/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944746592766273/19807040628566084398385987584), (2282798604331/19807040628566084398385987584)), (39075/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236156524374209/309485009821345068724781056), (1212462521165/618970019642690137449562112)), (83057/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885458928706411/77371252455336267181195264), (4848616159751/154742504910672534362390528)), (41541/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387324255984571/2417851639229258349412352), (2272133420729/4835703278458516698824704)), (19479/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629281854767573/302231454903657293676544), (3974922944055/604462909807314587353088)), (136407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887425295350151/75557863725914323419136), (3228396541529/37778931862957161709568)), (221761/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324315842725565/1180591620717411303424), (4840445764745/4722366482869645213696)), (20801/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405266711259395/147573952589676412928), (6652121785693/590295810358705651712)), (228953/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911497774858625/36893488147419103232), (4154958689655/36893488147419103232)), (286405/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822114520995811/9223372036854775808), (4670731075405/4611686018427387904)), (80625/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796679377396489/576460752303423488), (2333118265057/288230376151711744)), (80717/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194027250660947/144115188075855872), (254868982565/4503599627370496)), (70731/36028797018963968), by norm_num⟩
  | 4 => ⟨((372699393587255/9007199254740992), (12213513809707/36028797018963968)), (212607/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488191236484273/9007199254740992), (475986939805/281474976710656)), (532971/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112882741176651/2251799813685248), (15178687250823/2251799813685248)), (267577/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106353252028913/1125899906842624), (22636040871931/1125899906842624)), (202051/281474976710656), by norm_num⟩
  | 0 => ⟨((271681354764837/281474976710656), (44745607569149/1125899906842624)), (1638377/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271681354764837/281474976710656), (44745607569149/1125899906842624)), (6249912266257857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65445980137079/70368744177664), (10797182955857/140737488355328)), (3292969/1125899906842624), by norm_num⟩
  | 2 => ⟨((967254783553785/1125899906842624), (160669565335735/1125899906842624)), (6630473/1125899906842624), by norm_num⟩
  | 3 => ⟨((1616071022927389/2251799813685248), (138030392131669/562949953421312)), (26569581/2251799813685248), by norm_num⟩
  | 4 => ⟨((1024446005676625/2251799813685248), (792492887339673/2251799813685248)), (12791539/562949953421312), by norm_num⟩
  | 5 => ⟨((46789754522305/562949953421312), (180270503627403/562949953421312)), (165140401/4503599627370496), by norm_num⟩
  | 6 => ⟨((-861410096314897/9007199254740992), (239731793167791/4503599627370496)), (266430959/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-504978759/8388608)), (3/33554432), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-1039137783/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((289455374960017/4503599627370496), (721209444972551/9007199254740992)), (224607265/9007199254740992), by norm_num⟩
  | 1 => ⟨((-728501633/4294967296), (-226892599/1073741824)), (285/4294967296), by norm_num⟩
  | 2 => ⟨((480639393/2147483648), (37423911/134217728)), (95/1073741824), by norm_num⟩
  | 3 => ⟨((-845623275/4294967296), (-526740515/2147483648)), (337/4294967296), by norm_num⟩
  | 4 => ⟨((557912075/4294967296), (86881151/536870912)), (7/134217728), by norm_num⟩
  | 5 => ⟨((-147236195/2147483648), (-733709883/8589934592)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((259043173/8589934592), (161358537/4294967296)), (53/4294967296), by norm_num⟩
  | 7 => ⟨((-390645591/34359738368), (-973335839/68719476736)), (161/34359738368), by norm_num⟩
  | 8 => ⟨((515468055/137438953472), (321086135/68719476736)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((-37787493/34359738368), (-376606541/274877906944)), (253/549755813888), by norm_num⟩
  | 10 => ⟨((319114753/1099511627776), (397554501/1099511627776)), (269/2199023255552), by norm_num⟩
  | 11 => ⟨((-612481547/8796093022208), (-763032087/8796093022208)), (65/2199023255552), by norm_num⟩
  | 12 => ⟨((538791305/35184372088832), (335614237/17592186044416)), (115/17592186044416), by norm_num⟩
  | 13 => ⟨((-109377011/35184372088832), (-545049361/140737488355328)), (47/35184372088832), by norm_num⟩
  | 14 => ⟨((659776463/1125899906842624), (205488073/281474976710656)), (285/1125899906842624), by norm_num⟩
  | 15 => ⟨((-58039597/562949953421312), (-36152987/281474976710656)), (403/9007199254740992), by norm_num⟩
  | 16 => ⟨((612679295/36028797018963968), (381639221/18014398509481984)), (67/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (582537467467/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778457388234619/633825300114114700748351602688), (1378346937667/633825300114114700748351602688)), (184671/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889391606091235/39614081257132168796771975168), (1550332964245/39614081257132168796771975168)), (207773/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889144866984747/2475880078570760549798248448), (1646846359319/2475880078570760549798248448)), (220779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885405602006913/77371252455336267181195264), (823208155441/77371252455336267181195264)), (220801/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193649719084375/1208925819614629174706176), (771529257933/4835703278458516698824704)), (103513/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258477562944003/604462909807314587353088), (674859797783/302231454903657293676544)), (45293/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58977707751975/2361183241434822606848), (2192438567499/75557863725914323419136)), (294449/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297160557611605/4722366482869645213696), (410895120671/1180591620717411303424)), (220877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405231844855589/147573952589676412928), (2258707619387/590295810358705651712)), (151885/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113926504248291/4611686018427387904), (2821562389145/73786976294838206464)), (189905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455481379282289/2305843009213693952), (3171754170423/9223372036854775808)), (427419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796587316629089/576460752303423488), (3168627648953/1152921504606846976)), (213793/576460752303423488), by norm_num⟩
  | 5 => ⟨((596935812264117/72057594037927936), (692258951459/36028797018963968)), (374327/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490575064580763/36028797018963968), (4146536797517/36028797018963968)), (561867/36028797018963968), by norm_num⟩
  | 3 => ⟨((371983039042393/2251799813685248), (5170913562193/9007199254740992)), (351497/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112652107284681/2251799813685248), (10305143304069/4503599627370496)), (1407975/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212155864711813/2251799813685248), (3841578599379/562949953421312)), (1058475/1125899906842624), by norm_num⟩
  | 0 => ⟨((271613601414035/281474976710656), (30368874916773/2251799813685248)), (531745/281474976710656), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271613601414035/281474976710656), (30368874916773/2251799813685248)), (2028446198583507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1048186078759191/1125899906842624), (58609824457087/2251799813685248)), (8324591/2251799813685248), by norm_num⟩
  | 2 => ⟨((121884200268579/140737488355328), (54564354878329/1125899906842624)), (15933339/2251799813685248), by norm_num⟩
  | 3 => ⟨((841807744208563/1125899906842624), (189019509591505/2251799813685248)), (7285537/562949953421312), by norm_num⟩
  | 4 => ⟨((621465709523111/1125899906842624), (282650502080333/2251799813685248)), (48470213/2251799813685248), by norm_num⟩
  | 5 => ⟨((325292505404471/1125899906842624), (624061139910799/4503599627370496)), (16419151/562949953421312), by norm_num⟩
  | 6 => ⟨((289455374960017/4503599627370496), (721209444972551/9007199254740992)), (224607265/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1039137783/16777216)), (1/8388608), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-1066303961/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((652339098560141/9007199254740992), (-577727394093135/9007199254740992)), (47964193/4503599627370496), by norm_num⟩
  | 1 => ⟨((-842364801/4294967296), (23313087/134217728)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((285145771/1073741824), (-505064079/2147483648)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-1029585417/4294967296), (890455/4194304)), (5/134217728), by norm_num⟩
  | 4 => ⟨((697042249/4294967296), (-617317591/4294967296)), (55/2147483648), by norm_num⟩
  | 5 => ⟨((-755050161/8589934592), (334345405/4294967296)), (121/8589934592), by norm_num⟩
  | 6 => ⟨((681571247/17179869184), (-301808047/8589934592)), (111/17179869184), by norm_num⟩
  | 7 => ⟨((-1054702373/68719476736), (934070105/68719476736)), (87/34359738368), by norm_num⟩
  | 8 => ⟨((714046743/137438953472), (-19761787/4294967296)), (15/17179869184), by norm_num⟩
  | 9 => ⟨((-107426357/68719476736), (380557591/274877906944)), (73/274877906944), by norm_num⟩
  | 10 => ⟨((116366387/274877906944), (-824455249/2199023255552)), (161/2199023255552), by norm_num⟩
  | 11 => ⟨((-916730233/8796093022208), (811878619/8796093022208)), (161/8796093022208), by norm_num⟩
  | 12 => ⟨((206879291/8796093022208), (-91608669/4398046511104)), (147/35184372088832), by norm_num⟩
  | 13 => ⟨((-689525545/140737488355328), (305330307/70368744177664)), (31/35184372088832), by norm_num⟩
  | 14 => ⟨((1067011309/1125899906842624), (-944971199/1125899906842624)), (97/562949953421312), by norm_num⟩
  | 15 => ⟨((-770538717/4503599627370496), (170601963/1125899906842624)), (71/2251799813685248), by norm_num⟩
  | 16 => ⟨((260832191/9007199254740992), (-57749835/2251799813685248)), (195/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-944153435525/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778366039191219/633825300114114700748351602688), (-1116875070207/633825300114114700748351602688)), (92311/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889288878677805/39614081257132168796771975168), (-1256229521579/39614081257132168796771975168)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236129471316747/309485009821345068724781056), (-41700810593/77371252455336267181195264)), (27589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770702165379131/154742504910672534362390528), (-333517104955/38685626227668133590597632)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387273897588351/2417851639229258349412352), (-1250309410771/9671406556917033397649408)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629194116137987/302231454903657293676544), (-1093641149361/604462909807314587353088)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887141600709505/75557863725914323419136), (-1776455459537/75557863725914323419136)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297051872631035/4722366482869645213696), (-1331719426163/4722366482869645213696)), (110391/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810389050401767/295147905179352825856), (-457525943741/147573952589676412928)), (151813/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822637714299523/73786976294838206464), (-2286115092647/73786976294838206464)), (189805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821716205176631/9223372036854775808), (-1284899268789/4611686018427387904)), (213585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592965740624825/1152921504606846976), (-2567199862101/1152921504606846976)), (213653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193689314393803/144115188075855872), (-280422475695/18014398509481984)), (187023/144115188075855872), by norm_num⟩
  | 4 => ⟨((372575634796521/9007199254740992), (-839809535121/9007199254740992)), (140343/18014398509481984), by norm_num⟩
  | 3 => ⟨((743796569762061/4503599627370496), (-2094430853493/4503599627370496)), (351127/9007199254740992), by norm_num⟩
  | 2 => ⟨((556157770839877/1125899906842624), (-8347242462853/4503599627370496)), (703061/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211158359555263/2251799813685248), (-12444930003245/2251799813685248)), (1056623/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170962187960699/2251799813685248), (-24587732136331/2251799813685248)), (2121421/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170962187960699/2251799813685248), (-24587732136331/2251799813685248)), (8092578896529387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261594760574607/281474976710656), (-47410108510775/2251799813685248)), (4136857/2251799813685248), by norm_num⟩
  | 2 => ⟨((1943951081109895/2251799813685248), (-86057799669/2199023255552)), (7863551/2251799813685248), by norm_num⟩
  | 3 => ⟨((1674740395112631/2251799813685248), (-76075663266461/1125899906842624)), (1774061/281474976710656), by norm_num⟩
  | 4 => ⟨((617640464296861/1125899906842624), (-226320271603215/2251799813685248)), (11514407/1125899906842624), by norm_num⟩
  | 5 => ⟨((1309795034395491/4503599627370496), (-248307254993565/2251799813685248)), (29895147/2251799813685248), by norm_num⟩
  | 6 => ⟨((652339098560141/9007199254740992), (-577727394093135/9007199254740992)), (47964193/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1066303961/16777216)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile026Terms1
