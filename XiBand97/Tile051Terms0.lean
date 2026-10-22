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
namespace Reinmann.XiBand97.Tile051Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨51,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76371/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76371/2560))
  have he : value ((69/80), (76371/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-2775388957/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-315884999186683/2251799813685248), (-1197525115158255/2251799813685248)), (3244967/1125899906842624), by norm_num⟩
  | 1 => ⟨((3340985055/34359738368), (25331456215/68719476736)), (35/17179869184), by norm_num⟩
  | 2 => ⟨((-2315794371/68719476736), (-17558427455/137438953472)), (99/137438953472), by norm_num⟩
  | 3 => ⟨((535062113/68719476736), (2028429081/68719476736)), (93/549755813888), by norm_num⟩
  | 4 => ⟨((-5934028721/4398046511104), (-2811999797/549755813888)), (131/4398046511104), by norm_num⟩
  | 5 => ⟨((1645262111/8796093022208), (12474430279/17592186044416)), (37/8796093022208), by norm_num⟩
  | 6 => ⟨((-760272529/35184372088832), (-23057643139/281474976710656)), (139/281474976710656), by norm_num⟩
  | 7 => ⟨((4818109805/2251799813685248), (18265531809/2251799813685248)), (7/140737488355328), by norm_num⟩
  | 8 => ⟨((-3339659227/18014398509481984), (-12660701875/18014398509481984)), (157/36028797018963968), by norm_num⟩
  | 9 => ⟨((1028833501/72057594037927936), (7800648719/144115188075855872)), (49/144115188075855872), by norm_num⟩
  | 10 => ⟨((-4564051459/4611686018427387904), (-4325598133/1152921504606846976)), (55/2305843009213693952), by norm_num⟩
  | 11 => ⟨((4601540947/73786976294838206464), (17444515783/73786976294838206464)), (113/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-4252726845/1180591620717411303424), (-16122155909/1180591620717411303424)), (53/590295810358705651712), by norm_num⟩
  | 13 => ⟨((907004807/4722366482869645213696), (6876939639/9444732965739290427392)), (93/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-5748002969/604462909807314587353088), (-21790771757/604462909807314587353088)), (149/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((4249826189/9671406556917033397649408), (16111159473/9671406556917033397649408)), (7/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-2945755041/154742504910672534362390528), (-22334809529/309485009821345068724781056)), (157/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-2382090081271/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445261042467859/158456325028528675187087900672), (-2825950511729/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892301164704857/39614081257132168796771975168), (-3179015323253/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946117789642189/1237940039285380274899124224), (-3377496715183/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1773901135985975/154742504910672534362390528), (-1688631855505/77371252455336267181195264)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552093734940651/9671406556917033397649408), (-791484278657/2417851639229258349412352)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78813169914083/37778931862957161709568), (-1384973653715/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891401472377137/75557863725914323419136), (-70323435685/1180591620717411303424)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((650122658360629/2361183241434822606848), (-1687559185037/2361183241434822606848)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625166715244761/590295810358705651712), (-145003966071/18446744073709551616)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((457029981729059/18446744073709551616), (-5799167004323/73786976294838206464)), (5953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827878807823787/9223372036854775808), (-203834336671/288230376151711744)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399780559588109/288230376151711744), (-6520992736199/1152921504606846976)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199069386357703/144115188075855872), (-5703948110259/144115188075855872)), (2937/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498358931250395/36028797018963968), (-8552077996815/36028797018963968)), (4411/18014398509481984), by norm_num⟩
  | 3 => ⟨((93602478252215/562949953421312), (-10683363235933/9007199254740992)), (11049/9007199254740992), by norm_num⟩
  | 2 => ⟨((35072691820785/70368744177664), (-10673247944623/2251799813685248)), (1385/281474976710656), by norm_num⟩
  | 1 => ⟨((560252730624641/562949953421312), (-7804948811/549755813888)), (16699/1125899906842624), by norm_num⟩
  | 0 => ⟨((278744065260267/281474976710656), (-7966858305663/281474976710656)), (16855/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278744065260267/281474976710656), (-7966858305663/281474976710656)), (64296724559593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((551628311644645/562949953421312), (-15779125359025/281474976710656)), (68675/1125899906842624), by norm_num⟩
  | 2 => ⟨((134691311890273/140737488355328), (-3865446754249/35184372088832)), (8893/70368744177664), by norm_num⟩
  | 3 => ⟨((1017649688092425/1125899906842624), (-118380306587777/562949953421312)), (593/2199023255552), by norm_num⟩
  | 4 => ⟨((217504969529291/281474976710656), (-427994287389797/1125899906842624)), (676543/1125899906842624), by norm_num⟩
  | 5 => ⟨((254798616996823/562949953421312), (-661450517024977/1125899906842624)), (1559931/1125899906842624), by norm_num⟩
  | 6 => ⟨((-315884999186683/2251799813685248), (-1197525115158255/2251799813685248)), (3244967/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-2775388957/134217728)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-17595549687/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((368165254672551/4503599627370496), (-213342031404465/562949953421312)), (16060415/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3085867867/34359738368), (14305430749/34359738368)), (17/4294967296), by norm_num⟩
  | 2 => ⟨((423771545/8589934592), (-15716122015/68719476736)), (151/68719476736), by norm_num⟩
  | 3 => ⟨((-1241495005/68719476736), (11510616517/137438953472)), (7/8589934592), by norm_num⟩
  | 4 => ⟨((5455686675/1099511627776), (-25291409511/1099511627776)), (249/1099511627776), by norm_num⟩
  | 5 => ⟨((-4794947539/4398046511104), (22228362629/4398046511104)), (221/4398046511104), by norm_num⟩
  | 6 => ⟨((877964715/4398046511104), (-8140117447/8796093022208)), (41/4398046511104), by norm_num⟩
  | 7 => ⟨((-1102334657/35184372088832), (5110190319/35184372088832)), (13/8796093022208), by norm_num⟩
  | 8 => ⟨((2422076801/562949953421312), (-22456471527/1125899906842624)), (231/1125899906842624), by norm_num⟩
  | 9 => ⟨((-2365265189/4503599627370496), (21929738293/9007199254740992)), (57/2251799813685248), by norm_num⟩
  | 10 => ⟨((1039403761/18014398509481984), (-19273823981/72057594037927936)), (203/72057594037927936), by norm_num⟩
  | 11 => ⟨((-3321895985/576460752303423488), (7699803591/288230376151711744)), (41/144115188075855872), by norm_num⟩
  | 12 => ⟨((1216491917/2305843009213693952), (-22557596921/9223372036854775808)), (243/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-3289730385/73786976294838206464), (15250494265/73786976294838206464)), (167/73786976294838206464), by norm_num⟩
  | 14 => ⟨((516305461/147573952589676412928), (-19147863323/1180591620717411303424)), (53/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-4840273273/18889465931478580854784), (22438483145/18889465931478580854784)), (251/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((2658791849/151115727451828646838272), (-12325596661/151115727451828646838272)), (139/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-442346965947/2535301200456458802993406410752)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780505809268117/633825300114114700748351602688), (-2097873500451/633825300114114700748351602688)), (361/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((118230979340711/2475880078570760549798248448), (-2359904458023/39614081257132168796771975168)), (6499/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472898108226295/618970019642690137449562112), (-2507155635721/2475880078570760549798248448)), (3453/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886629102986559/77371252455336267181195264), (-626720608513/38685626227668133590597632)), (6907/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551491217926511/9671406556917033397649408), (-293739002323/1208925819614629174706176)), (6477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260483746092517/604462909807314587353088), (-513970692007/151115727451828646838272)), (5669/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890545572949579/75557863725914323419136), (-3340265314731/75557863725914323419136)), (9213/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649801884591239/2361183241434822606848), (-2504722857795/4722366482869645213696)), (27/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1624285199982367/590295810358705651712), (-3443220281379/590295810358705651712)), (9507/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827018951614759/73786976294838206464), (-4302864985253/73786976294838206464)), (11887/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913320736858971/4611686018427387904), (-1209781944099/2305843009213693952)), (13379/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597886482817253/1152921504606846976), (-1209283467381/288230376151711744)), (13387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598994937861303/72057594037927936), (-4230249346069/144115188075855872)), (11723/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496743215126463/36028797018963968), (-3170444664899/18014398509481984)), (17601/36028797018963968), by norm_num⟩
  | 3 => ⟨((186953277078113/1125899906842624), (-3959132731615/4503599627370496)), (1377/562949953421312), by norm_num⟩
  | 2 => ⟨((1120322012537857/2251799813685248), (-7906500189887/2251799813685248)), (22079/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117522529503225/1125899906842624), (-11830351237463/1125899906842624)), (16617/562949953421312), by norm_num⟩
  | 0 => ⟨((1109103319975515/1125899906842624), (-23543191483277/1125899906842624)), (8367/140737488355328), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109103319975515/1125899906842624), (-23543191483277/1125899906842624)), (31917572558355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((546032504773693/562949953421312), (-46383931072785/1125899906842624)), (134675/1125899906842624), by norm_num⟩
  | 2 => ⟨((1057336010759939/1125899906842624), (-89980055637267/1125899906842624)), (272353/1125899906842624), by norm_num⟩
  | 3 => ⟨((246439097847885/281474976710656), (-84500542630175/562949953421312)), (138767/281474976710656), by norm_num⟩
  | 4 => ⟨((837689292465611/1125899906842624), (-295930213574097/1125899906842624)), (1138591/1125899906842624), by norm_num⟩
  | 5 => ⟨((272736792885875/562949953421312), (-440354546121715/1125899906842624)), (4585591/2251799813685248), by norm_num⟩
  | 6 => ⟨((368165254672551/4503599627370496), (-213342031404465/562949953421312)), (16060415/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-17595549687/536870912)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-2775388957/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1185081427411587/4503599627370496), (671960656056165/4503599627370496)), (3777235/1125899906842624), by norm_num⟩
  | 1 => ⟨((6267058183/17179869184), (-3553525041/17179869184)), (81/17179869184), by norm_num⟩
  | 2 => ⟨((-2171996855/8589934592), (9852463453/68719476736)), (113/34359738368), by norm_num⟩
  | 3 => ⟨((16058810627/137438953472), (-4552804843/68719476736)), (211/137438953472), by norm_num⟩
  | 4 => ⟨((-11131119309/274877906944), (6311527681/274877906944)), (37/68719476736), by norm_num⟩
  | 5 => ⟨((12344806345/1099511627776), (-1749927047/274877906944)), (83/549755813888), by norm_num⟩
  | 6 => ⟨((-11409023617/4398046511104), (3234551997/2199023255552)), (155/4398046511104), by norm_num⟩
  | 7 => ⟨((9037865775/17592186044416), (-10249237015/35184372088832)), (31/4398046511104), by norm_num⟩
  | 8 => ⟨((-12529142361/140737488355328), (1776057435/35184372088832)), (87/70368744177664), by norm_num⟩
  | 9 => ⟨((15439181693/1125899906842624), (-2188567473/281474976710656)), (217/1125899906842624), by norm_num⟩
  | 10 => ⟨((-17122600417/9007199254740992), (4854397995/4503599627370496)), (243/9007199254740992), by norm_num⟩
  | 11 => ⟨((17263246841/72057594037927936), (-9788544825/72057594037927936)), (247/72057594037927936), by norm_num⟩
  | 12 => ⟨((-7977313917/288230376151711744), (4523268165/288230376151711744)), (115/288230376151711744), by norm_num⟩
  | 13 => ⟨((6805480185/2305843009213693952), (-1929409585/1152921504606846976)), (99/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-21564340127/73786976294838206464), (6113667721/36893488147419103232)), (79/18446744073709551616), by norm_num⟩
  | 15 => ⟨((124560513/4611686018427387904), (-1130045745/73786976294838206464)), (235/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-11051362355/4722366482869645213696), (6266304177/4722366482869645213696)), (165/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (106886569417/316912650057057350374175801344)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55628632765649/19807040628566084398385987584), (1013425502989/158456325028528675187087900672)), (1447/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59101783673055/1237940039285380274899124224), (4559907037017/39614081257132168796771975168)), (6513/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945563002672619/1237940039285380274899124224), (2422153708003/1237940039285380274899124224)), (3461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772791301989935/154742504910672534362390528), (75681863035/2417851639229258349412352)), (1731/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551052989457323/9671406556917033397649408), (4540201762171/9671406556917033397649408)), (3247/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630049895219203/302231454903657293676544), (1985983217785/302231454903657293676544)), (5685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889920697255377/75557863725914323419136), (3226556912559/37778931862957161709568)), (9241/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299134283637989/4722366482869645213696), (2419335003625/2361183241434822606848)), (3467/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623638311562857/590295810358705651712), (6651277204969/590295810358705651712)), (9541/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826208324079401/73786976294838206464), (64931678327/576460752303423488)), (5967/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825726747084941/9223372036854775808), (9346253399663/9223372036854775808)), (6719/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798484148482919/576460752303423488), (583835412593/72057594037927936)), (13453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197182577120607/144115188075855872), (4084098071729/72057594037927936)), (2947/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495524509354691/36028797018963968), (1530161251153/4503599627370496)), (17717/36028797018963968), by norm_num⟩
  | 3 => ⟨((373522322462475/2251799813685248), (7641172047929/4503599627370496)), (11103/4503599627370496), by norm_num⟩
  | 2 => ⟨((559382416165875/1125899906842624), (7626709756341/1125899906842624)), (22297/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115136347499193/1125899906842624), (11403870815061/562949953421312)), (33671/1125899906842624), by norm_num⟩
  | 0 => ⟨((138016330009477/140737488355328), (22662740517137/562949953421312)), (68249/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((138016330009477/140737488355328), (22662740517137/562949953421312)), (260349277976607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080957608866167/1125899906842624), (88898226355591/1125899906842624)), (139355/1125899906842624), by norm_num⟩
  | 2 => ⟨((515395041096985/562949953421312), (85349695483379/562949953421312)), (36199/140737488355328), by norm_num⟩
  | 3 => ⟨((917834618506167/1125899906842624), (156279646330657/562949953421312)), (309035/562949953421312), by norm_num⟩
  | 4 => ⟨((661450517024971/1125899906842624), (254798616996825/562949953421312)), (675433/562949953421312), by norm_num⟩
  | 5 => ⟨((157942499593331/1125899906842624), (1197525115158253/2251799813685248)), (1405035/562949953421312), by norm_num⟩
  | 6 => ⟨((-1185081427411587/4503599627370496), (671960656056165/4503599627370496)), (3777235/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-2775388957/67108864)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-12888507187/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-88468608544771/562949953421312), (436483393223229/2251799813685248)), (6299043/2251799813685248), by norm_num⟩
  | 1 => ⟨((8690474405/34359738368), (-5359595651/17179869184)), (39/8589934592), by norm_num⟩
  | 2 => ⟨((-1748347373/8589934592), (2156484109/8589934592)), (253/68719476736), by norm_num⟩
  | 3 => ⟨((15007234913/137438953472), (-18510545507/137438953472)), (273/137438953472), by norm_num⟩
  | 4 => ⟨((-12076606415/274877906944), (14895786859/274877906944)), (111/137438953472), by norm_num⟩
  | 5 => ⟨((7774619287/549755813888), (-4794768821/274877906944)), (145/549755813888), by norm_num⟩
  | 6 => ⟨((-4170922345/1099511627776), (5144588481/1099511627776)), (157/2199023255552), by norm_num⟩
  | 7 => ⟨((15343635547/17592186044416), (-18925475989/17592186044416)), (291/17592186044416), by norm_num⟩
  | 8 => ⟨((-6173657191/35184372088832), (3807422321/17592186044416)), (59/17592186044416), by norm_num⟩
  | 9 => ⟨((8832104837/281474976710656), (-5446942073/140737488355328)), (85/140737488355328), by norm_num⟩
  | 10 => ⟨((-11371779497/2251799813685248), (7013212063/1125899906842624)), (221/2251799813685248), by norm_num⟩
  | 11 => ⟨((831916957/1125899906842624), (-16417933647/18014398509481984)), (261/18014398509481984), by norm_num⟩
  | 12 => ⟨((-7140899683/72057594037927936), (17615763237/144115188075855872)), (141/72057594037927936), by norm_num⟩
  | 13 => ⟨((14145027297/1152921504606846976), (-8723531449/576460752303423488)), (141/576460752303423488), by norm_num⟩
  | 14 => ⟨((-13008881831/9223372036854775808), (16045693993/9223372036854775808)), (261/9223372036854775808), by norm_num⟩
  | 15 => ⟨((2791598349/18446744073709551616), (-3443273099/18446744073709551616)), (113/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-4492904219/295147905179352825856), (11083468537/590295810358705651712)), (23/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (2933548745719/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((3476213849659/1237940039285380274899124224), (434454458119/79228162514264337593543950336)), (5785/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945462827082951/19807040628566084398385987584), (3909595014869/39614081257132168796771975168)), (6509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890774086339643/2475880078570760549798248448), (1038338675581/618970019642690137449562112)), (6917/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886219814290143/77371252455336267181195264), (4152690921857/154742504910672534362390528)), (865/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193840444566007/1208925819614629174706176), (3892442492133/9671406556917033397649408)), (6489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629905898728793/302231454903657293676544), (1702590977767/302231454903657293676544)), (355/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1889453197594527/75557863725914323419136), (5532098427679/75557863725914323419136)), (9233/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298784086581061/4722366482869645213696), (2073958449553/2361183241434822606848)), (433/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405789371341049/147573952589676412928), (1425376456847/147573952589676412928)), (4765/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456402083260855/18446744073709551616), (1781015644275/18446744073709551616)), (745/4611686018427387904), by norm_num⟩
  | 7 => ⟨((912526594420699/4611686018427387904), (2002673389301/2305843009213693952)), (13421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798148263643571/576460752303423488), (8005847890145/1152921504606846976)), (6717/576460752303423488), by norm_num⟩
  | 5 => ⟨((299149197343919/36028797018963968), (1749916515661/36028797018963968)), (11769/144115188075855872), by norm_num⟩
  | 4 => ⟨((747324922825099/18014398509481984), (10488598759515/36028797018963968)), (17683/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493002983596395/9007199254740992), (3272918982859/2251799813685248)), (22155/9007199254740992), by norm_num⟩
  | 2 => ⟨((279422261290263/562949953421312), (13063073374767/2251799813685248)), (2779/281474976710656), by norm_num⟩
  | 1 => ⟨((69596806770147/70368744177664), (19523125825801/1125899906842624)), (33543/1125899906842624), by norm_num⟩
  | 0 => ⟨((137632548722241/140737488355328), (38760450704889/1125899906842624)), (33931/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137632548722241/140737488355328), (38760450704889/1125899906842624)), (129436495067405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1075434505359031/1125899906842624), (75810641251005/1125899906842624)), (137403/1125899906842624), by norm_num⟩
  | 2 => ⟨((15970726435637/17592186044416), (144825270841987/1125899906842624)), (280993/1125899906842624), by norm_num⟩
  | 3 => ⟨((909288827637439/1125899906842624), (32869206472475/140737488355328)), (291239/562949953421312), by norm_num⟩
  | 4 => ⟨((1345877274662285/2251799813685248), (424728372916117/1125899906842624)), (2425813/2251799813685248), by norm_num⟩
  | 5 => ⟨((483972362369519/2251799813685248), (1015422883576083/2251799813685248)), (295623/140737488355328), by norm_num⟩
  | 6 => ⟨((-88468608544771/562949953421312), (436483393223229/2251799813685248)), (6299043/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-12888507187/268435456)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-28697105515/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-959302594230077/4503599627370496), (87259302140833/9007199254740992)), (19444931/9007199254740992), by norm_num⟩
  | 1 => ⟨((26227409471/68719476736), (-596419071/34359738368)), (67/17179869184), by norm_num⟩
  | 2 => ⟨((-23496604637/68719476736), (534319759/34359738368)), (121/34359738368), by norm_num⟩
  | 3 => ⟨((28066842569/137438953472), (-638248325/68719476736)), (291/137438953472), by norm_num⟩
  | 4 => ⟨((-25144515473/274877906944), (142948435/34359738368)), (263/274877906944), by norm_num⟩
  | 5 => ⟨((18021169479/549755813888), (-409806739/274877906944)), (191/549755813888), by norm_num⟩
  | 6 => ⟨((-21526400707/2199023255552), (489516737/1099511627776)), (115/1099511627776), by norm_num⟩
  | 7 => ⟨((22040075603/8796093022208), (-1002395713/8796093022208)), (237/8796093022208), by norm_num⟩
  | 8 => ⟨((-9872628541/17592186044416), (898026005/35184372088832)), (107/17592186044416), by norm_num⟩
  | 9 => ⟨((31447778977/281474976710656), (-1430263643/281474976710656)), (343/281474976710656), by norm_num⟩
  | 10 => ⟨((-5634685577/281474976710656), (512537685/562949953421312)), (31/140737488355328), by norm_num⟩
  | 11 => ⟨((14685092711/4503599627370496), (-1335773455/9007199254740992)), (325/9007199254740992), by norm_num⟩
  | 12 => ⟨((-4385358987/9007199254740992), (24931091/1125899906842624)), (49/9007199254740992), by norm_num⟩
  | 13 => ⟨((19341559363/288230376151711744), (-879665593/288230376151711744)), (109/144115188075855872), by norm_num⟩
  | 14 => ⟨((-19803098365/2305843009213693952), (900656661/2305843009213693952)), (225/2305843009213693952), by norm_num⟩
  | 15 => ⟨((18923940809/18446744073709551616), (-430336027/9223372036854775808)), (217/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-8476787535/73786976294838206464), (771058651/147573952589676412928)), (49/36893488147419103232), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (4033072438827/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889786544600955/316912650057057350374175801344), (298568769865/39614081257132168796771975168)), (5793/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236330738448187/4951760157141521099596496896), (5373467719127/39614081257132168796771975168)), (6519/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890476476389939/2475880078570760549798248448), (5708404974611/2475880078570760549798248448)), (433/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((443035398062421/38685626227668133590597632), (2853693604097/77371252455336267181195264)), (6931/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550443694695493/9671406556917033397649408), (5349594048701/9671406556917033397649408)), (1625/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259566465870307/604462909807314587353088), (4679813241063/604462909807314587353088)), (2845/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472263421492957/18889465931478580854784), (7602668411437/75557863725914323419136)), (9251/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298483711658513/4722366482869645213696), (5700226520963/4722366482869645213696)), (6943/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622743266537237/590295810358705651712), (7834927071293/590295810358705651712)), (9553/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825088756560213/73786976294838206464), (4894665805149/36893488147419103232)), (747/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824466189513177/9223372036854775808), (1375880886647/1152921504606846976)), (3365/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595706438133801/1152921504606846976), (10999606848511/1152921504606846976)), (6739/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196076992057209/144115188075855872), (2404070905597/36028797018963968)), (5907/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493863227909889/36028797018963968), (14407675500331/36028797018963968)), (555/1125899906842624), by norm_num⟩
  | 3 => ⟨((1492007636251443/9007199254740992), (17980270428263/9007199254740992)), (22271/9007199254740992), by norm_num⟩
  | 2 => ⟨((279168915215991/562949953421312), (4484065420161/562949953421312)), (11189/1125899906842624), by norm_num⟩
  | 1 => ⟨((555992002338491/562949953421312), (3349286513757/140737488355328)), (16917/562949953421312), by norm_num⟩
  | 0 => ⟨((274438215933347/281474976710656), (13286930529961/281474976710656)), (17185/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274438215933347/281474976710656), (13286930529961/281474976710656)), (65555573583507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((16684385393655/17592186044416), (103638101048569/1125899906842624)), (70267/562949953421312), by norm_num⟩
  | 2 => ⟨((250789923183975/281474976710656), (98290116702679/562949953421312)), (146219/562949953421312), by norm_num⟩
  | 3 => ⟨((214869362516863/281474976710656), (350299996193951/1125899906842624)), (623235/1125899906842624), by norm_num⟩
  | 4 => ⟨((1094220536119237/2251799813685248), (534816542141341/1125899906842624)), (2678661/2251799813685248), by norm_num⟩
  | 5 => ⟨((23627165412149/2251799813685248), (2079073778799535/4503599627370496)), (5148087/2251799813685248), by norm_num⟩
  | 6 => ⟨((-959302594230077/4503599627370496), (87259302140833/9007199254740992)), (19444931/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-28697105515/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-31166007397/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((57337436755165/4503599627370496), (-1677568998084823/9007199254740992)), (4112109/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1702476503/68719476736), (12452692181/34359738368)), (123/34359738368), by norm_num⟩
  | 2 => ⟨((1656433153/68719476736), (-12115910049/34359738368)), (241/68719476736), by norm_num⟩
  | 3 => ⟨((-1074423361/68719476736), (3929412055/17179869184)), (315/137438953472), by norm_num⟩
  | 4 => ⟨((2090731323/274877906944), (-30585131191/274877906944)), (77/68719476736), by norm_num⟩
  | 5 => ⟨((-203418765/68719476736), (11903183439/274877906944)), (241/549755813888), by norm_num⟩
  | 6 => ⟨((527779519/549755813888), (-1930210455/137438953472)), (315/2199023255552), by norm_num⟩
  | 7 => ⟨((-586863727/2199023255552), (17170359379/4398046511104)), (177/4398046511104), by norm_num⟩
  | 8 => ⟨((570992041/8796093022208), (-16705988289/17592186044416)), (87/8796093022208), by norm_num⟩
  | 9 => ⟨((-246910935/17592186044416), (28896313033/140737488355328)), (303/140737488355328), by norm_num⟩
  | 10 => ⟨((768746391/281474976710656), (-22491851521/562949953421312)), (237/562949953421312), by norm_num⟩
  | 11 => ⟨((-1087935567/2251799813685248), (1989414643/281474976710656)), (169/2251799813685248), by norm_num⟩
  | 12 => ⟨((352837477/4503599627370496), (-2580814763/2251799813685248)), (221/18014398509481984), by norm_num⟩
  | 13 => ⟨((-105629235/9007199254740992), (24723857921/144115188075855872)), (133/72057594037927936), by norm_num⟩
  | 14 => ⟨((1879268575/1152921504606846976), (-13745830301/576460752303423488)), (149/576460752303423488), by norm_num⟩
  | 15 => ⟨((-487585039/2305843009213693952), (891605023/288230376151711744)), (311/9223372036854775808), by norm_num⟩
  | 16 => ⟨((237199169/9223372036854775808), (-6939933053/18446744073709551616)), (305/73786976294838206464), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-1957232276419/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444844323819257/158456325028528675187087900672), (-1158898738435/316912650057057350374175801344)), (2889/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890426213770319/39614081257132168796771975168), (-651783182555/9903520314283042199192993792)), (1625/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945121889397703/1237940039285380274899124224), (-1384801893739/1237940039285380274899124224)), (1727/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771909712277527/154742504910672534362390528), (-2769069803489/154742504910672534362390528)), (6909/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550227175552241/9671406556917033397649408), (-2595435689891/9671406556917033397649408)), (3239/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629688939754419/302231454903657293676544), (-2270439098229/604462909807314587353088)), (2835/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888748859487393/75557863725914323419136), (-1844200210507/37778931862957161709568)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((649128256957701/2361183241434822606848), (-691342586817/1180591620717411303424)), (3457/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811216589413033/295147905179352825856), (-3800873508471/590295810358705651712)), (4755/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824704607620437/73786976294838206464), (-1187206661639/18446744073709551616)), (2973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912019387707097/4611686018427387904), (-5339316637673/9223372036854775808)), (6693/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99705309897129/72057594037927936), (-2667713504307/576460752303423488)), (6697/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195714863043447/144115188075855872), (-1166031402971/36028797018963968)), (5865/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493333340192573/36028797018963968), (-873431175593/4503599627370496)), (8807/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491368503762381/9007199254740992), (-8719034291397/9007199254740992)), (22053/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232142506305965/4503599627370496), (-17392299396825/4503599627370496)), (44207/4503599627370496), by norm_num⟩
  | 1 => ⟨((555581899688137/562949953421312), (-6493561810125/562949953421312)), (33285/1125899906842624), by norm_num⟩
  | 0 => ⟨((548227822771561/562949953421312), (-51493012787205/2251799813685248)), (67089/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548227822771561/562949953421312), (-51493012787205/2251799813685248)), (255924229148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067192645411471/1125899906842624), (-100292760010765/2251799813685248)), (66869/562949953421312), by norm_num⟩
  | 2 => ⟨((2018626124909221/2251799813685248), (-190126484993957/2251799813685248)), (530885/2251799813685248), by norm_num⟩
  | 3 => ⟨((896772290175343/1125899906842624), (-340877805667683/2251799813685248)), (1041473/2251799813685248), by norm_num⟩
  | 4 => ⟨((1376944995050035/2251799813685248), (-67876764311093/281474976710656)), (1974371/2251799813685248), by norm_num⟩
  | 5 => ⟨((88879636476155/281474976710656), (-332045754086431/1125899906842624)), (3366829/2251799813685248), by norm_num⟩
  | 6 => ⟨((57337436755165/4503599627370496), (-1677568998084823/9007199254740992)), (4112109/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-31166007397/536870912)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-962887821/536870912), (-8326166871/134217728)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((523598590156199/4503599627370496), (1071944738787439/9007199254740992)), (4004691/2251799813685248), by norm_num⟩
  | 1 => ⟨((-16613657525/68719476736), (-2125784321/8589934592)), (257/68719476736), by norm_num⟩
  | 2 => ⟨((2159195601/8589934592), (2210222113/8589934592)), (17/4294967296), by norm_num⟩
  | 3 => ⟨((-11973122745/68719476736), (-766004613/4294967296)), (191/68719476736), by norm_num⟩
  | 4 => ⟨((6224352205/68719476736), (12742894507/137438953472)), (201/137438953472), by norm_num⟩
  | 5 => ⟨((-2588635309/68719476736), (-662452605/17179869184)), (169/274877906944), by norm_num⟩
  | 6 => ⟨((897152633/68719476736), (14693668973/1099511627776)), (237/1099511627776), by norm_num⟩
  | 7 => ⟨((-8528349505/2199023255552), (-4364946523/1099511627776)), (143/2199023255552), by norm_num⟩
  | 8 => ⟨((8867102121/8796093022208), (9076651127/8796093022208)), (151/8796093022208), by norm_num⟩
  | 9 => ⟨((-16389884893/70368744177664), (-4194303425/17592186044416)), (141/35184372088832), by norm_num⟩
  | 10 => ⟨((3408180751/70368744177664), (13954894049/281474976710656)), (237/281474976710656), by norm_num⟩
  | 11 => ⟨((-10308527469/1125899906842624), (-10552140507/1125899906842624)), (91/562949953421312), by norm_num⟩
  | 12 => ⟨((7145326751/4503599627370496), (14628372883/9007199254740992)), (255/9007199254740992), by norm_num⟩
  | 13 => ⟨((-9143562631/36028797018963968), (-9359645003/36028797018963968)), (165/36028797018963968), by norm_num⟩
  | 14 => ⟨((5432429707/144115188075855872), (11121619791/288230376151711744)), (99/144115188075855872), by norm_num⟩
  | 15 => ⟨((-753094667/144115188075855872), (-6167135521/1152921504606846976)), (111/1152921504606846976), by norm_num⟩
  | 16 => ⟨((12528130683/18446744073709551616), (3206049449/4611686018427387904)), (233/18446744073709551616), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790819754617223/5070602400912917605986812821504), (1038280140073/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222400214436981/79228162514264337593543950336), (1229320606841/633825300114114700748351602688)), (541/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236278604515083/4951760157141521099596496896), (1382767292757/39614081257132168796771975168)), (4869/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890034254592841/2475880078570760549798248448), (734460704211/1237940039285380274899124224)), (2587/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885850200602387/77371252455336267181195264), (367154762457/38685626227668133590597632)), (10349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031172769053/9671406556917033397649408), (172063648197/1208925819614629174706176)), (9703/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78700412706581/37778931862957161709568), (150515557051/75557863725914323419136)), (8491/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888470959595247/75557863725914323419136), (1956100411697/75557863725914323419136)), (1725/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298048459696775/4722366482869645213696), (733274452169/2361183241434822606848)), (647/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622147706203093/590295810358705651712), (2015649705081/590295810358705651712)), (3559/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824348668927527/73786976294838206464), (1259140109461/36893488147419103232)), (17799/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911819791722179/4611686018427387904), (1415651832253/4611686018427387904)), (20029/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594887313247945/1152921504606846976), (2829103258021/1152921504606846976)), (5009/288230376151711744), by norm_num⟩
  | 5 => ⟨((597684330551785/72057594037927936), (2472992051667/144115188075855872)), (17539/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492817505612009/36028797018963968), (231534179379/2251799813685248)), (26325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490729764998569/9007199254740992), (2311024295405/4503599627370496)), (32933/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230883131810627/4503599627370496), (4609120295735/2251799813685248)), (16487/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220483583820009/2251799813685248), (13762888521063/2251799813685248)), (99129/2251799813685248), by norm_num⟩
  | 0 => ⟨((547350546892371/562949953421312), (6817224976433/562949953421312)), (199089/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547350546892371/562949953421312), (6817224976433/562949953421312)), (759464272505950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128403385107435/2251799813685248), (53026551244371/2251799813685248)), (391967/2251799813685248), by norm_num⟩
  | 2 => ⟨((2010520263429035/2251799813685248), (25060374035733/562949953421312)), (759437/2251799813685248), by norm_num⟩
  | 3 => ⟨((55957230128825/70368744177664), (22375163858591/281474976710656)), (1423743/2251799813685248), by norm_num⟩
  | 4 => ⟨((176210113882809/281474976710656), (284683709015859/2251799813685248)), (622669/562949953421312), by norm_num⟩
  | 5 => ⟨((423251535338597/1125899906842624), (178218857578347/1125899906842624)), (3748215/2251799813685248), by norm_num⟩
  | 6 => ⟨((523598590156199/4503599627370496), (1071944738787439/9007199254740992)), (4004691/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-962887821/536870912), (-8326166871/134217728)), (3/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile051Terms0
