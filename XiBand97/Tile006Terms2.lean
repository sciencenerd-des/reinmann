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
namespace Reinmann.XiBand97.Tile006Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10993/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10993/640))
  have he : value ((69/80), (10993/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-1597980951/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-723446471887511/9007199254740992), (789790680958661/18014398509481984)), (148792923/9007199254740992), by norm_num⟩
  | 1 => ⟨((239112321/1073741824), (-522080597/4294967296)), (199/4294967296), by norm_num⟩
  | 2 => ⟨((-1325920249/4294967296), (180939347/1073741824)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((612705255/2147483648), (-668893857/4294967296)), (259/4294967296), by norm_num⟩
  | 4 => ⟨((-53086865/268435456), (463641891/4294967296)), (181/4294967296), by norm_num⟩
  | 5 => ⟨((942003477/8589934592), (-514195311/8589934592)), (203/8589934592), by norm_num⟩
  | 6 => ⟨((-108824509/2147483648), (475217373/17179869184)), (95/8589934592), by norm_num⟩
  | 7 => ⟨((689658529/34359738368), (-188226047/17179869184)), (303/68719476736), by norm_num⟩
  | 8 => ⟨((-478034865/68719476736), (521873415/137438953472)), (53/34359738368), by norm_num⟩
  | 9 => ⟨((1178128067/549755813888), (-321542299/274877906944)), (263/549755813888), by norm_num⟩
  | 10 => ⟨((-1306585837/2199023255552), (356601821/1099511627776)), (147/1099511627776), by norm_num⟩
  | 11 => ⟨((1317318239/8796093022208), (-359530977/4398046511104)), (299/8796093022208), by norm_num⟩
  | 12 => ⟨((-304365141/8796093022208), (664554355/35184372088832)), (279/35184372088832), by norm_num⟩
  | 13 => ⟨((259655187/35184372088832), (-283467063/70368744177664)), (15/8796093022208), by norm_num⟩
  | 14 => ⟨((-822762335/562949953421312), (224553595/281474976710656)), (3/8796093022208), by norm_num⟩
  | 15 => ⟨((1216630171/4503599627370496), (-664101083/4503599627370496)), (143/2251799813685248), by norm_num⟩
  | 16 => ⟨((-843303773/18014398509481984), (460319793/18014398509481984)), (25/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (3441420503727/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778272058607221/633825300114114700748351602688), (1017653319615/158456325028528675187087900672)), (92601/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944591357374827/19807040628566084398385987584), (286154296095/2475880078570760549798248448)), (52101/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888922393671985/2475880078570760549798248448), (1215858571675/618970019642690137449562112)), (110745/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770588139253703/154742504910672534362390528), (2431048585251/77371252455336267181195264)), (55389/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548988001537185/9671406556917033397649408), (4556795722607/9671406556917033397649408)), (51945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629146701660905/302231454903657293676544), (3985776232159/604462909807314587353088)), (22735/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886986213511093/75557863725914323419136), (1618556143305/18889465931478580854784)), (147843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648467102295783/2361183241434822606848), (4853340094589/4722366482869645213696)), (55471/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810307238577065/295147905179352825856), (3334780239487/295147905179352825856)), (2385/9223372036854775808), by norm_num⟩
  | 8 => ⟨((455607610913321/18446744073709551616), (8331279811877/73786976294838206464)), (190943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821479263296633/9223372036854775808), (292653013195/288230376151711744)), (107503/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592724105612149/1152921504606846976), (9355160665229/1152921504606846976)), (215253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193472617537909/144115188075855872), (2043705260187/36028797018963968)), (188623/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489966995294123/36028797018963968), (1530045368901/4503599627370496)), (141745/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487155413065607/9007199254740992), (15262229711165/9007199254740992)), (355335/9007199254740992), by norm_num⟩
  | 2 => ⟨((555925260948545/1125899906842624), (1900623248423/281474976710656)), (89199/562949953421312), by norm_num⟩
  | 1 => ⟨((552406972794555/562949953421312), (22664692806663/1125899906842624)), (538857/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083682966854701/1125899906842624), (44760181969365/1125899906842624)), (546213/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083682966854701/1125899906842624), (44760181969365/1125899906842624)), (2083637239696311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((520634779182439/562949953421312), (43081846351283/562949953421312)), (547447/281474976710656), by norm_num⟩
  | 2 => ⟨((1912813216686341/2251799813685248), (159374078818587/1125899906842624)), (4385541/1125899906842624), by norm_num⟩
  | 3 => ⟨((1579738124283405/2251799813685248), (16922732346625/70368744177664)), (8692251/1125899906842624), by norm_num⟩
  | 4 => ⟨((978026805479151/2251799813685248), (759811355664155/2251799813685248)), (16376743/1125899906842624), by norm_num⟩
  | 5 => ⟨((336817805681335/4503599627370496), (1320038963376285/4503599627370496)), (101110691/4503599627370496), by norm_num⟩
  | 6 => ⟨((-723446471887511/9007199254740992), (789790680958661/18014398509481984)), (148792923/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1597980951/33554432)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-81995171/33554432), (-408230485/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2915287902403/1125899906842624), (1563739630531959/18014398509481984)), (255323607/18014398509481984), by norm_num⟩
  | 1 => ⟨((15753999/2147483648), (-1056291577/4294967296)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((-5579305/536870912), (1461279/4194304)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((10538241/1073741824), (-1413159309/4294967296)), (237/4294967296), by norm_num⟩
  | 4 => ⟨((-29857085/4294967296), (1000945453/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((33836597/8589934592), (-567178403/4294967296)), (193/8589934592), by norm_num⟩
  | 6 => ⟨((-31955433/17179869184), (1071291613/17179869184)), (23/2147483648), by norm_num⟩
  | 7 => ⟨((51735177/68719476736), (-867199341/34359738368)), (75/17179869184), by norm_num⟩
  | 8 => ⟨((-18322099/68719476736), (1228480373/137438953472)), (215/137438953472), by norm_num⟩
  | 9 => ⟨((46142591/549755813888), (-386727443/137438953472)), (273/549755813888), by norm_num⟩
  | 10 => ⟨((-26146361/1099511627776), (1753090163/2199023255552)), (39/274877906944), by norm_num⟩
  | 11 => ⟨((13468767/2199023255552), (-112883601/549755813888)), (81/2199023255552), by norm_num⟩
  | 12 => ⟨((-25439927/17592186044416), (852862199/17592186044416)), (77/8796093022208), by norm_num⟩
  | 13 => ⟨((44354917/140737488355328), (-185872351/17592186044416)), (135/70368744177664), by norm_num⟩
  | 14 => ⟨((-35904841/562949953421312), (300923443/140737488355328)), (55/140737488355328), by norm_num⟩
  | 15 => ⟨((27126953/2251799813685248), (-454709501/1125899906842624)), (335/4503599627370496), by norm_num⟩
  | 16 => ⟨((-38428223/18014398509481984), (644144513/9007199254740992)), (239/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (1042490764283/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444549279297909/158456325028528675187087900672), (2465964475607/633825300114114700748351602688)), (92443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889098736988201/39614081257132168796771975168), (2773618618275/39614081257132168796771975168)), (104015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472208400850181/618970019642690137449562112), (2946234975567/2475880078570760549798248448)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770499839159161/154742504910672534362390528), (736352154409/38685626227668133590597632)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774452870321639/4835703278458516698824704), (2760442855371/9671406556917033397649408)), (51833/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258221945070419/604462909807314587353088), (2414510091591/604462909807314587353088)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943435534015551/37778931862957161709568), (980483608491/18889465931478580854784)), (147475/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648424348504553/2361183241434822606848), (735003147861/1180591620717411303424)), (55321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620498286314067/590295810358705651712), (4040181443779/590295810358705651712)), (76095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822287275352883/73786976294838206464), (5046725205939/73786976294838206464)), (47581/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821321040877619/9223372036854775808), (5672754740115/9223372036854775808)), (107117/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796284714293705/576460752303423488), (177085819173/36028797018963968)), (214383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596670627045201/72057594037927936), (4951650721279/144115188075855872)), (93877/72057594037927936), by norm_num⟩
  | 4 => ⟨((372444471001867/9007199254740992), (3706995037877/18014398509481984)), (281967/36028797018963968), by norm_num⟩
  | 3 => ⟨((371733213580107/2251799813685248), (9243928492983/9007199254740992)), (44131/1125899906842624), by norm_num⟩
  | 2 => ⟨((2223297202132591/4503599627370496), (2302168135229/562949953421312)), (707867/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209124566999783/2251799813685248), (3431289463461/281474976710656)), (1066247/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166764548281427/2251799813685248), (27100641184217/1125899906842624)), (2150351/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166764548281427/2251799813685248), (27100641184217/1125899906842624)), (8202938088423918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083635854379133/2251799813685248), (104308932253717/2251799813685248)), (4241813/2251799813685248), by norm_num⟩
  | 2 => ⟨((1923198498368683/2251799813685248), (193038324148497/2251799813685248)), (4121527/1125899906842624), by norm_num⟩
  | 3 => ⟨((1626000964777273/2251799813685248), (82434284982557/562949953421312)), (15493611/2251799813685248), by norm_num⟩
  | 4 => ⟨((1125833895446629/2251799813685248), (476199442233715/2251799813685248)), (26913091/2251799813685248), by norm_num⟩
  | 5 => ⟨((924359301415505/4503599627370496), (238085761354643/1125899906842624)), (76588815/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2915287902403/1125899906842624), (1563739630531959/18014398509481984)), (255323607/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-408230485/8388608)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83649375/33554432), (-416466295/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((606511009710679/9007199254740992), (863848952494977/18014398509481984)), (76763325/9007199254740992), by norm_num⟩
  | 1 => ⟨((-417957853/2147483648), (-297647073/2147483648)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((1208053575/4294967296), (430155347/2147483648)), (159/4294967296), by norm_num⟩
  | 3 => ⟨((-1163907979/4294967296), (-414436289/2147483648)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((105128961/536870912), (598937473/4294967296)), (57/2147483648), by norm_num⟩
  | 5 => ⟨((-15193089/134217728), (-692460783/8589934592)), (67/4294967296), by norm_num⟩
  | 6 => ⟨((936825075/17179869184), (166789091/4294967296)), (131/17179869184), by norm_num⟩
  | 7 => ⟨((-386824677/17179869184), (-137737851/8589934592)), (55/17179869184), by norm_num⟩
  | 8 => ⟨((559033561/68719476736), (796227189/137438953472)), (161/137438953472), by norm_num⟩
  | 9 => ⟨((-718139919/274877906944), (-511420573/274877906944)), (53/137438953472), by norm_num⟩
  | 10 => ⟨((103784567/137438953472), (73909779/137438953472)), (125/1099511627776), by norm_num⟩
  | 11 => ⟨((-872657401/4398046511104), (-621459601/4398046511104)), (133/4398046511104), by norm_num⟩
  | 12 => ⟨((420384051/8796093022208), (9355465/274877906944)), (65/8796093022208), by norm_num⟩
  | 13 => ⟨((-747733039/70368744177664), (-532495199/70368744177664)), (117/70368744177664), by norm_num⟩
  | 14 => ⟨((308746637/140737488355328), (439745453/281474976710656)), (49/140737488355328), by norm_num⟩
  | 15 => ⟨((-951885397/2251799813685248), (-338940757/1125899906842624)), (153/2251799813685248), by norm_num⟩
  | 16 => ⟨((687825667/9007199254740992), (122458099/2251799813685248)), (7/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (806096872379/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778123940258897/633825300114114700748351602688), (119164390313/79228162514264337593543950336)), (46147/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944508292318955/19807040628566084398385987584), (1072248244235/39614081257132168796771975168)), (103837/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944373271355091/1237940039285380274899124224), (1138974168485/2475880078570760549798248448)), (55167/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770413032675215/154742504910672534362390528), (1138648529323/154742504910672534362390528)), (55171/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774412314733797/4835703278458516698824704), (1067137133747/9671406556917033397649408)), (51727/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258151242479133/604462909807314587353088), (466699637423/302231454903657293676544)), (90531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378340763209/37778931862957161709568), (758062955271/37778931862957161709568)), (18391/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296763348728533/4722366482869645213696), (1136527819175/4722366482869645213696)), (13795/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620381649167963/590295810358705651712), (780902791033/295147905179352825856)), (151767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822142552531555/73786976294838206464), (243859716805/9223372036854775808)), (189743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455289925371829/2305843009213693952), (2192842633141/9223372036854775808)), (213507/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796204963891891/576460752303423488), (1095238284991/576460752303423488)), (213565/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193203754296037/144115188075855872), (1914008555635/144115188075855872)), (186935/144115188075855872), by norm_num⟩
  | 4 => ⟨((744787874327017/18014398509481984), (1432852190351/18014398509481984)), (280533/36028797018963968), by norm_num⟩
  | 3 => ⟨((92917959825373/562949953421312), (1786429813699/4503599627370496)), (350897/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222827612400167/4503599627370496), (7117982327845/4503599627370496)), (87811/562949953421312), by norm_num⟩
  | 1 => ⟨((2208473304013631/2251799813685248), (1325986891841/281474976710656)), (527739/1125899906842624), by norm_num⟩
  | 0 => ⟨((270709022814659/281474976710656), (20941054982521/2251799813685248)), (132375/140737488355328), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((270709022814659/281474976710656), (20941054982521/2251799813685248)), (504970551073980287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1041322022908929/1125899906842624), (40280188294349/2251799813685248)), (4113375/2251799813685248), by norm_num⟩
  | 2 => ⟨((1925474769853407/2251799813685248), (74508660855031/2251799813685248)), (7755915/2251799813685248), by norm_num⟩
  | 3 => ⟨((1643974533749147/2251799813685248), (15927764286597/281474976710656)), (1722145/281474976710656), by norm_num⟩
  | 4 => ⟨((149126037763119/281474976710656), (186054470437999/2251799813685248)), (21675831/2251799813685248), by norm_num⟩
  | 5 => ⟨((308342805271117/1125899906842624), (394288207197265/4503599627370496)), (53099449/4503599627370496), by norm_num⟩
  | 6 => ⟨((606511009710679/9007199254740992), (863848952494977/18014398509481984)), (76763325/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-416466295/8388608)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-424256703/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((676820767967277/9007199254740992), (-433396229022787/18014398509481984)), (29174837/4503599627370496), by norm_num⟩
  | 1 => ⟨((-237567121/1073741824), (304248035/4294967296)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((699501891/2147483648), (-447919887/4294967296)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((-343273439/1073741824), (219812129/2147483648)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((505373847/2147483648), (-80902925/1073741824)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((-1190433963/8589934592), (381141961/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((1168386721/17179869184), (-187041541/8589934592)), (57/8589934592), by norm_num⟩
  | 7 => ⟨((-982926687/34359738368), (314704231/34359738368)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((1447083825/137438953472), (-231656851/68719476736)), (147/137438953472), by norm_num⟩
  | 9 => ⟨((-118356945/34359738368), (75788829/68719476736)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((1115183367/1099511627776), (-89262233/274877906944)), (59/549755813888), by norm_num⟩
  | 11 => ⟨((-298508125/1099511627776), (191147053/2199023255552)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((292979653/4398046511104), (-375213889/17592186044416)), (127/17592186044416), by norm_num⟩
  | 13 => ⟨((-1061736259/70368744177664), (339936739/70368744177664)), (117/70368744177664), by norm_num⟩
  | 14 => ⟨((223301259/70368744177664), (-71494499/70368744177664)), (25/70368744177664), by norm_num⟩
  | 15 => ⟨((-175332515/281474976710656), (224545269/1125899906842624)), (159/2251799813685248), by norm_num⟩
  | 16 => ⟨((1032511783/9007199254740992), (-330579921/9007199254740992)), (119/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-201812121341/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778052469524501/633825300114114700748351602688), (-119325441433/158456325028528675187087900672)), (11531/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944468108891861/19807040628566084398385987584), (-16776461587/1237940039285380274899124224)), (51891/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888661201722699/2475880078570760549798248448), (-570252008435/2475880078570760549798248448)), (110271/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770327746537617/154742504910672534362390528), (-570085942937/154742504910672534362390528)), (110275/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744731957243/9671406556917033397649408), (-534279195035/9671406556917033397649408)), (25847/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629040695181269/302231454903657293676544), (-467317995861/604462909807314587353088)), (90469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117915205055569/4722366482869645213696), (-379530672005/37778931862957161709568)), (147019/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296678393589095/4722366482869645213696), (-284503535703/2361183241434822606848)), (1723/73786976294838206464), by norm_num⟩
  | 9 => ⟨((810132495311297/295147905179352825856), (-195478876543/147573952589676412928)), (75817/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113874810077377/4611686018427387904), (-488345545245/36893488147419103232)), (23695/9223372036854775808), by norm_num⟩
  | 7 => ⟨((113812264355749/576460752303423488), (-1097811315847/9223372036854775808)), (106639/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796123426673551/576460752303423488), (-1096604912129/1152921504606846976)), (53327/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193061510295005/144115188075855872), (-958173875837/144115188075855872)), (93339/72057594037927936), by norm_num⟩
  | 4 => ⟨((186170409084413/4503599627370496), (-179319302203/4503599627370496)), (280083/36028797018963968), by norm_num⟩
  | 3 => ⟨((92901457171605/562949953421312), (-1788466820303/9007199254740992)), (175111/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111152082484899/2251799813685248), (-1781397457195/2251799813685248)), (5475/35184372088832), by norm_num⟩
  | 1 => ⟨((2207699656682135/2251799813685248), (-1327246185395/562949953421312)), (526051/1125899906842624), by norm_num⟩
  | 0 => ⟨((541042641429911/562949953421312), (-5238985478995/1125899906842624)), (526967/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((541042641429911/562949953421312), (-5238985478995/1125899906842624)), (2010219576122093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((519975668039839/562949953421312), (-5035109293005/562949953421312)), (4071297/2251799813685248), by norm_num⟩
  | 2 => ⟨((1920947618059787/2251799813685248), (-37205926422017/2251799813685248)), (7593837/2251799813685248), by norm_num⟩
  | 3 => ⟨((409523023311281/562949953421312), (-15869669076203/562949953421312)), (3301781/562949953421312), by norm_num⟩
  | 4 => ⟨((297463849508659/562949953421312), (-2886133491769/70368744177664)), (19959907/2251799813685248), by norm_num⟩
  | 5 => ⟨((624933965599739/2251799813685248), (-195204933938265/4503599627370496)), (5682749/562949953421312), by norm_num⟩
  | 6 => ⟨((676820767967277/9007199254740992), (-433396229022787/18014398509481984)), (29174837/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-424256703/8388608)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-431647423/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((504253891638575/18014398509481984), (-631434511914579/9007199254740992)), (95968633/9007199254740992), by norm_num⟩
  | 1 => ⟨((-11254919/134217728), (901989339/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((539467585/4294967296), (-1351059287/4294967296)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((-67337519/536870912), (1349137303/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((201725179/2147483648), (-252603385/1073741824)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-483451703/8589934592), (1210771381/8589934592)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((482763957/17179869184), (-1209048967/17179869184)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((-413209019/34359738368), (129356679/4294967296)), (85/17179869184), by norm_num⟩
  | 8 => ⟨((309465899/68719476736), (-193758989/17179869184)), (129/68719476736), by norm_num⟩
  | 9 => ⟨((-206017107/137438953472), (257977803/68719476736)), (173/274877906944), by norm_num⟩
  | 10 => ⟨((493737677/1099511627776), (-1236531889/1099511627776)), (209/1099511627776), by norm_num⟩
  | 11 => ⟨((-537856689/4398046511104), (1347024905/4398046511104)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((537091547/17592186044416), (-1345108661/17592186044416)), (29/2199023255552), by norm_num⟩
  | 13 => ⟨((-495071533/70368744177664), (1239872439/70368744177664)), (27/8796093022208), by norm_num⟩
  | 14 => ⟨((423743363/281474976710656), (-530617983/140737488355328)), (187/281474976710656), by norm_num⟩
  | 15 => ⟨((-338512445/1125899906842624), (423890511/562949953421312)), (151/1125899906842624), by norm_num⟩
  | 16 => ⟨((63380791/1125899906842624), (-317465621/2251799813685248)), (57/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1551280442397/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888991321216375/316912650057057350374175801344), (-1834316954989/633825300114114700748351602688)), (92381/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857586868215/39614081257132168796771975168), (-1031572410415/19807040628566084398385987584)), (103941/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888577554339575/2475880078570760549798248448), (-2191513708431/2475880078570760549798248448)), (55225/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110640249031923/9671406556917033397649408), (-136929007853/9671406556917033397649408)), (55233/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548666083354789/9671406556917033397649408), (-2053245189523/9671406556917033397649408)), (103577/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258012451253253/604462909807314587353088), (-897949948869/302231454903657293676544)), (90647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943265513562559/37778931862957161709568), (-1458522429375/37778931862957161709568)), (73665/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296594004273515/4722366482869645213696), (-2186653333797/4722366482869645213696)), (27631/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405037158107035/147573952589676412928), (-3004812714313/590295810358705651712)), (76007/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910925515000605/36893488147419103232), (-469158055941/9223372036854775808)), (95041/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820831393600987/9223372036854775808), (-4218642487867/9223372036854775808)), (213931/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592081189972523/1152921504606846976), (-1053480574197/288230376151711744)), (107021/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192915626932167/144115188075855872), (-3681878426923/144115188075855872)), (187413/144115188075855872), by norm_num⟩
  | 4 => ⟨((744571299377771/18014398509481984), (-689028379339/4503599627370496)), (281369/36028797018963968), by norm_num⟩
  | 3 => ⟨((371536063099395/2251799813685248), (-6871787436485/9007199254740992)), (352151/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221736442555093/4503599627370496), (-6844117165689/2251799813685248)), (352813/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103412147636321/1125899906842624), (-2549314840477/281474976710656)), (1061761/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081163011676781/1125899906842624), (-40240807690591/2251799813685248)), (2136883/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081163011676781/1125899906842624), (-40240807690591/2251799813685248)), (8151561745650481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((518922072941623/562949953421312), (-38641865560743/1125899906842624)), (2090163/1125899906842624), by norm_num⟩
  | 2 => ⟨((1910697870801865/2251799813685248), (-8904928785075/140737488355328)), (7993717/2251799813685248), by norm_num⟩
  | 3 => ⟨((403062708518305/562949953421312), (-120896206605075/1125899906842624)), (14577241/2251799813685248), by norm_num⟩
  | 4 => ⟨((564190734327631/1125899906842624), (-173119305500187/1125899906842624)), (24004653/2251799813685248), by norm_num⟩
  | 5 => ⟨((512196313387897/2251799813685248), (-694003490028479/4503599627370496)), (62879025/4503599627370496), by norm_num⟩
  | 6 => ⟨((504253891638575/18014398509481984), (-631434511914579/9007199254740992)), (95968633/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-431647423/8388608)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-88110603/33554432), (-1754709893/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-288325740527367/9007199254740992), (-292331749623025/4503599627370496)), (233536137/18014398509481984), by norm_num⟩
  | 1 => ⟨((209287211/2147483648), (848780223/4294967296)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-318589805/2147483648), (-1292065217/4294967296)), (131/2147483648), by norm_num⟩
  | 3 => ⟨((646635873/4294967296), (1311240515/4294967296)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-123043589/1073741824), (-249506323/1073741824)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((149843587/2147483648), (607702079/4294967296)), (253/8589934592), by norm_num⟩
  | 6 => ⟨((-304134775/8589934592), (-77090109/1073741824)), (259/17179869184), by norm_num⟩
  | 7 => ⟨((66138939/4294967296), (1072926019/34359738368)), (227/34359738368), by norm_num⟩
  | 8 => ⟨((-50340371/8589934592), (-816636835/68719476736)), (175/68719476736), by norm_num⟩
  | 9 => ⟨((544932939/274877906944), (1105008519/274877906944)), (239/274877906944), by norm_num⟩
  | 10 => ⟨((-20738257/34359738368), (-336422323/274877906944)), (293/1099511627776), by norm_num⟩
  | 11 => ⟨((22959305/137438953472), (744905681/2199023255552)), (41/549755813888), by norm_num⟩
  | 12 => ⟨((-93200159/2199023255552), (-755960687/8796093022208)), (21/1099511627776), by norm_num⟩
  | 13 => ⟨((349230739/35184372088832), (1416331861/70368744177664)), (317/70368744177664), by norm_num⟩
  | 14 => ⟨((-607566183/281474976710656), (-616007733/140737488355328)), (139/140737488355328), by norm_num⟩
  | 15 => ⟨((493266367/1125899906842624), (1000239661/1125899906842624)), (57/281474976710656), by norm_num⟩
  | 16 => ⟨((-375440131/4503599627370496), (-761313023/4503599627370496)), (175/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-2642930613655/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777914394916897/633825300114114700748351602688), (-3124925273491/633825300114114700748351602688)), (23127/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888780636872883/39614081257132168796771975168), (-3514735518965/39614081257132168796771975168)), (26023/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118030972749173/154742504910672534362390528), (-3733405614901/2475880078570760549798248448)), (27655/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770161734611145/154742504910672534362390528), (-3732280025207/154742504910672534362390528)), (55323/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193573587317447/1208925819614629174706176), (-3497816970407/9671406556917033397649408)), (51879/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257944464269239/604462909807314587353088), (-1529697364881/302231454903657293676544)), (1419/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((943210016351653/37778931862957161709568), (-4969276508835/75557863725914323419136)), (147627/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296510307890295/4722366482869645213696), (-931249591735/1180591620717411303424)), (110765/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810016409388927/295147905179352825856), (-5118691082819/590295810358705651712)), (152375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113856573005315/4611686018427387904), (-3196797183619/36893488147419103232)), (190579/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820665796494975/9223372036854775808), (-3593120263431/4611686018427387904)), (26819/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591913719256843/1152921504606846976), (-28039283061/4503599627370496)), (107371/576460752303423488), by norm_num⟩
  | 5 => ⟨((298191747089533/36028797018963968), (-6271602444131/144115188075855872)), (11757/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488915452751149/36028797018963968), (-9389034997965/36028797018963968)), (141297/18014398509481984), by norm_num⟩
  | 3 => ⟨((742926512437759/4503599627370496), (-11704205348583/9007199254740992)), (176995/4503599627370496), by norm_num⟩
  | 2 => ⟨((555283059745547/1125899906842624), (-11656186159143/2251799813685248)), (710229/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102932047272967/1125899906842624), (-17364627600933/1125899906842624)), (267745/562949953421312), by norm_num⟩
  | 0 => ⟨((1080096440624651/1125899906842624), (-68506043800483/2251799813685248)), (2164611/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080096440624651/1125899906842624), (-68506043800483/2251799813685248)), (8257335671431731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((517557131170295/562949953421312), (-131438209774221/2251799813685248)), (2142405/1125899906842624), by norm_num⟩
  | 2 => ⟨((1895625941290541/2251799813685248), (-120839840848151/1125899906842624)), (8378831/2251799813685248), by norm_num⟩
  | 3 => ⟨((392462578074773/562949953421312), (-406904975586243/2251799813685248)), (15905609/2251799813685248), by norm_num⟩
  | 4 => ⟨((1020898185485881/2251799813685248), (-141837631195711/562949953421312)), (6981415/562949953421312), by norm_num⟩
  | 5 => ⟨((639796204599637/4503599627370496), (-2009528381493/8796093022208)), (78786567/4503599627370496), by norm_num⟩
  | 6 => ⟨((-288325740527367/9007199254740992), (-292331749623025/4503599627370496)), (233536137/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1754709893/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile006Terms2
