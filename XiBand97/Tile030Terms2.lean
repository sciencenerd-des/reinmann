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
namespace Reinmann.XiBand97.Tile030Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (31473/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (31473/1280))
  have he : value ((69/80), (31473/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-285939089/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((484877171314957/9007199254740992), (666491752654403/9007199254740992)), (102868313/4503599627370496), by norm_num⟩
  | 1 => ⟨((-641043175/4294967296), (-881150969/4294967296)), (137/2147483648), by norm_num⟩
  | 2 => ⟨((888674539/4294967296), (305383655/1073741824)), (191/2147483648), by norm_num⟩
  | 3 => ⟨((-205327417/1073741824), (-141117213/536870912)), (355/4294967296), by norm_num⟩
  | 4 => ⟨((569288481/4294967296), (782519987/4294967296)), (31/536870912), by norm_num⟩
  | 5 => ⟨((-631361129/8589934592), (-216960609/2147483648)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((291750791/8589934592), (802056717/17179869184)), (257/17179869184), by norm_num⟩
  | 7 => ⟨((-231115701/17179869184), (-635363831/34359738368)), (205/34359738368), by norm_num⟩
  | 8 => ⟨((320394393/68719476736), (55050081/8589934592)), (143/68719476736), by norm_num⟩
  | 9 => ⟨((-394809725/274877906944), (-542688831/274877906944)), (355/549755813888), by norm_num⟩
  | 10 => ⟨((875715993/2199023255552), (601861173/1099511627776)), (99/549755813888), by norm_num⟩
  | 11 => ⟨((-882909195/8796093022208), (-1213609819/8796093022208)), (401/8796093022208), by norm_num⟩
  | 12 => ⟨((815981359/35184372088832), (1121613633/35184372088832)), (373/35184372088832), by norm_num⟩
  | 13 => ⟨((-696117143/140737488355328), (-478426663/70368744177664)), (5/2199023255552), by norm_num⟩
  | 14 => ⟨((551441869/562949953421312), (757988783/562949953421312)), (255/562949953421312), by norm_num⟩
  | 15 => ⟨((-203856201/1125899906842624), (-560424307/2251799813685248)), (379/4503599627370496), by norm_num⟩
  | 16 => ⟨((141302351/4503599627370496), (776913057/18014398509481984)), (265/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1226860966447/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778279809102915/633825300114114700748351602688), (1451167195475/633825300114114700748351602688)), (92343/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889191864163853/39614081257132168796771975168), (204027999009/4951760157141521099596496896)), (103895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472233170891177/618970019642690137449562112), (1733815029677/2475880078570760549798248448)), (110399/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770599068258809/154742504910672534362390528), (866669697941/77371252455336267181195264)), (110411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96812432877341/604462909807314587353088), (25382820281/151115727451828646838272)), (103523/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258303640256233/604462909807314587353088), (1420932947283/604462909807314587353088)), (22649/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887004118581235/75557863725914323419136), (577017401215/18889465931478580854784)), (294483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296948743498093/4722366482869645213696), (1730224492147/4722366482869645213696)), (220905/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620636269837361/590295810358705651712), (2377714430087/590295810358705651712)), (303811/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911230191567247/36893488147419103232), (1485064019905/36893488147419103232)), (189933/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910758324744545/4611686018427387904), (834656412721/2305843009213693952)), (213745/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796383056327961/576460752303423488), (3335168497763/1152921504606846976)), (213833/576460752303423488), by norm_num⟩
  | 5 => ⟨((74594659945135/9007199254740992), (728596931283/36028797018963968)), (187203/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490040245972015/36028797018963968), (136369488129/1125899906842624)), (281003/18014398509481984), by norm_num⟩
  | 3 => ⟨((743632497683231/4503599627370496), (1360307203407/2251799813685248)), (703205/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223973973667535/4503599627370496), (2710477057317/1125899906842624)), (176063/562949953421312), by norm_num⟩
  | 1 => ⟨((2210170681788055/2251799813685248), (16161847572397/2251799813685248)), (1059007/1125899906842624), by norm_num⟩
  | 0 => ⟨((135561188704249/140737488355328), (31921781576861/2251799813685248)), (4257177/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135561188704249/140737488355328), (31921781576861/2251799813685248)), (16239841469771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088751831890463/2251799813685248), (61495408319227/2251799813685248)), (8321899/2251799813685248), by norm_num⟩
  | 2 => ⟨((241978799774357/281474976710656), (57042658054679/1125899906842624)), (7946595/1125899906842624), by norm_num⟩
  | 3 => ⟨((103651084138553/140737488355328), (196154046705179/2251799813685248)), (7234147/562949953421312), by norm_num⟩
  | 4 => ⟨((1204312953448523/2251799813685248), (288929123814173/2251799813685248)), (11916017/562949953421312), by norm_num⟩
  | 5 => ⟨((607020945178451/2251799813685248), (309051527869589/2251799813685248)), (126430411/4503599627370496), by norm_num⟩
  | 6 => ⟨((484877171314957/9007199254740992), (666491752654403/9007199254740992)), (102868313/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-285939089/4194304)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1168765401/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1334692993213621/18014398509481984), (-816120157300527/18014398509481984)), (307288155/18014398509481984), by norm_num⟩
  | 1 => ⟨((-28174147/134217728), (68910197/536870912)), (209/4294967296), by norm_num⟩
  | 2 => ⟨((319293477/1073741824), (-780949159/4294967296)), (149/2147483648), by norm_num⟩
  | 3 => ⟨((-75385545/268435456), (737531859/4294967296)), (71/1073741824), by norm_num⟩
  | 4 => ⟨((53395833/268435456), (-130599069/1073741824)), (203/4294967296), by norm_num⟩
  | 5 => ⟨((-484101717/4294967296), (74003005/1073741824)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((457187815/8589934592), (-559110137/17179869184)), (221/17179869184), by norm_num⟩
  | 7 => ⟨((-92522187/4294967296), (56574225/4294967296)), (181/34359738368), by norm_num⟩
  | 8 => ⟨((1048540379/137438953472), (-641147397/137438953472)), (259/137438953472), by norm_num⟩
  | 9 => ⟨((-165041033/68719476736), (807336605/549755813888)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((748154331/1099511627776), (-457471369/1099511627776)), (47/274877906944), by norm_num⟩
  | 11 => ⟨((-770793031/4398046511104), (471314177/4398046511104)), (49/1099511627776), by norm_num⟩
  | 12 => ⟨((727940367/17592186044416), (-445111205/17592186044416)), (187/17592186044416), by norm_num⟩
  | 13 => ⟨((-1269175607/140737488355328), (776058465/140737488355328)), (41/17592186044416), by norm_num⟩
  | 14 => ⟨((513692181/281474976710656), (-1226975/1099511627776)), (67/140737488355328), by norm_num⟩
  | 15 => ⟨((-776213089/2251799813685248), (474628361/2251799813685248)), (51/562949953421312), by norm_num⟩
  | 16 => ⟨((1099588641/18014398509481984), (-672361703/18014398509481984)), (291/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-89360490075/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778199993137377/633825300114114700748351602688), (-211378173897/158456325028528675187087900672)), (92283/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889102131581973/39614081257132168796771975168), (-237750135751/9903520314283042199192993792)), (6489/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1888837421119083/2475880078570760549798248448), (-1010186309623/2475880078570760549798248448)), (220639/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770503893964395/154742504910672534362390528), (-1009903199899/154742504910672534362390528)), (220653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548909793739339/9671406556917033397649408), (-946483556277/9671406556917033397649408)), (206877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112871516621/302231454903657293676544), (-827872542419/604462909807314587353088)), (181033/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943438855419627/37778931862957161709568), (-336182394493/18889465931478580854784)), (294205/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324213522723327/1180591620717411303424), (-504027278415/2361183241434822606848)), (220679/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1582525753125/576460752303423488), (-692637495903/295147905179352825856)), (303473/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822298382427103/73786976294838206464), (-865197284359/36893488147419103232)), (379401/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910667455134933/4611686018427387904), (-1945046433649/9223372036854775808)), (106727/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592585011808297/1152921504606846976), (-971494608747/576460752303423488)), (427011/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74584800783721/9007199254740992), (-848902043483/72057594037927936)), (373751/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489805055650617/36028797018963968), (-2542090388677/36028797018963968)), (140215/9007199254740992), by norm_num⟩
  | 3 => ⟨((743486750364101/4503599627370496), (-792387911183/2251799813685248)), (350743/4503599627370496), by norm_num⟩
  | 2 => ⟨((69481200951961/140737488355328), (-6314983961487/4503599627370496)), (351051/1125899906842624), by norm_num⟩
  | 1 => ⟨((552331466142873/562949953421312), (-9412403460621/2251799813685248)), (527353/562949953421312), by norm_num⟩
  | 0 => ⟨((541840668267231/562949953421312), (-9292933636631/1125899906842624)), (4231353/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541840668267231/562949953421312), (-9292933636631/1125899906842624)), (16141330727584075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1042969160403067/1125899906842624), (-35777882856075/2251799813685248)), (8215225/2251799813685248), by norm_num⟩
  | 2 => ⟨((965862639047599/1125899906842624), (-4142822578701/140737488355328)), (3870321/562949953421312), by norm_num⟩
  | 3 => ⟨((1655195459550645/2251799813685248), (-14215819806545/281474976710656)), (27472929/2251799813685248), by norm_num⟩
  | 4 => ⟨((1210915047886575/2251799813685248), (-167190424332257/2251799813685248)), (5395403/281474976710656), by norm_num⟩
  | 5 => ⟨((319380658633183/1125899906842624), (-179814741484627/2251799813685248)), (105663881/4503599627370496), by norm_num⟩
  | 6 => ⟨((1334692993213621/18014398509481984), (-816120157300527/18014398509481984)), (307288155/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1168765401/16777216)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-298086139/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-557120064646765/18014398509481984), (-690520552502427/9007199254740992)), (263263409/9007199254740992), by norm_num⟩
  | 1 => ⟨((383921647/4294967296), (951700737/4294967296)), (365/4294967296), by norm_num⟩
  | 2 => ⟨((-554838143/4294967296), (-687692233/2147483648)), (265/2147483648), by norm_num⟩
  | 3 => ⟨((534562833/4294967296), (1325124139/4294967296)), (513/4294967296), by norm_num⟩
  | 4 => ⟨((-386271329/4294967296), (-957525347/4294967296)), (93/1073741824), by norm_num⟩
  | 5 => ⟨((55823387/1073741824), (138380211/1073741824)), (27/536870912), by norm_num⟩
  | 6 => ⟨((-430267577/17179869184), (-1066587343/17179869184)), (419/17179869184), by norm_num⟩
  | 7 => ⟨((355323787/34359738368), (880809695/34359738368)), (87/8589934592), by norm_num⟩
  | 8 => ⟨((-64188615/17179869184), (-636466867/68719476736)), (253/68719476736), by norm_num⟩
  | 9 => ⟨((164914631/137438953472), (204402873/68719476736)), (327/274877906944), by norm_num⟩
  | 10 => ⟨((-190665837/549755813888), (-472640233/549755813888)), (95/274877906944), by norm_num⟩
  | 11 => ⟨((400796473/4398046511104), (993531623/4398046511104)), (401/4398046511104), by norm_num⟩
  | 12 => ⟨((-386150269/17592186044416), (-29913289/549755813888)), (97/4398046511104), by norm_num⟩
  | 13 => ⟨((343420871/70368744177664), (425651819/35184372088832)), (347/70368744177664), by norm_num⟩
  | 14 => ⟨((-70900999/70368744177664), (-351511999/140737488355328)), (575/562949953421312), by norm_num⟩
  | 15 => ⟨((437184523/2251799813685248), (67733357/140737488355328)), (445/2251799813685248), by norm_num⟩
  | 16 => ⟨((-157953225/4503599627370496), (-783098329/9007199254740992)), (323/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-2545609710495/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778119569234027/633825300114114700748351602688), (-3010516869673/633825300114114700748351602688)), (184993/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944505712986215/19807040628566084398385987584), (-846523200789/9903520314283042199192993792)), (208155/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888740741072065/2475880078570760549798248448), (-3596808129319/2475880078570760549798248448)), (221209/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110650429424417/9671406556917033397649408), (-3595778555241/154742504910672534362390528)), (221259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774409235115801/4835703278458516698824704), (-3369948805711/9671406556917033397649408)), (207483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39317045968993/18889465931478580854784), (-1473805994615/302231454903657293676544)), (5675/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943373293536325/37778931862957161709568), (-4787820497615/75557863725914323419136)), (9225/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((81047197015681/295147905179352825856), (-448634163237/590295810358705651712)), (221487/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405092340914971/147573952589676412928), (-4932065175353/590295810358705651712)), (304685/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822125674908475/73786976294838206464), (-1540179535963/18446744073709551616)), (95267/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821138626862027/9223372036854775808), (-865601571363/1152921504606846976)), (6703/144115188075855872), by norm_num⟩
  | 6 => ⟨((796193124800005/576460752303423488), (-6917324738755/1152921504606846976)), (429357/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596590057261347/72057594037927936), (-755530506651/18014398509481984)), (376097/144115188075855872), by norm_num⟩
  | 4 => ⟨((744767232667349/18014398509481984), (-9049557673157/36028797018963968)), (564967/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486625604451805/9007199254740992), (-705161333907/562949953421312)), (11057/140737488355328), by norm_num⟩
  | 2 => ⟨((2222673831777243/4503599627370496), (-2809657635041/562949953421312)), (1419623/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104083770260949/1125899906842624), (-16748410708017/1125899906842624)), (535071/562949953421312), by norm_num⟩
  | 0 => ⟨((2164763838949881/2251799813685248), (-66121457329989/2251799813685248)), (1081037/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164763838949881/2251799813685248), (-66121457329989/2251799813685248)), (4123828890086936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2079150376890475/2251799813685248), (-63565748134765/1125899906842624)), (2141993/562949953421312), by norm_num⟩
  | 2 => ⟨((119535044983967/140737488355328), (-234768203440655/2251799813685248)), (16789559/2251799813685248), by norm_num⟩
  | 3 => ⟨((24999255425199/35184372088832), (-398799610353021/2251799813685248)), (8005309/562949953421312), by norm_num⟩
  | 4 => ⟨((1066172210132975/2251799813685248), (-566711453455185/2251799813685248)), (3552853/140737488355328), by norm_num⟩
  | 5 => ⟨((22636373613953/140737488355328), (-1073296123688979/4503599627370496)), (164885585/4503599627370496), by norm_num⟩
  | 6 => ⟨((-557120064646765/18014398509481984), (-690520552502427/9007199254740992)), (263263409/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-298086139/4194304)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1214648523/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-87938197186467/1125899906842624), (100619715874361/9007199254740992)), (240725945/18014398509481984), by norm_num⟩
  | 1 => ⟨((493867217/2147483648), (-35317971/1073741824)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-363540471/1073741824), (207983221/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((1427230311/4294967296), (-204131301/4294967296)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-262649535/1073741824), (586965/16777216)), (93/2147483648), by norm_num⟩
  | 5 => ⟨((618684423/4294967296), (-176976141/8589934592)), (221/8589934592), by norm_num⟩
  | 6 => ⟨((-607226177/8589934592), (173698483/17179869184)), (219/17179869184), by norm_num⟩
  | 7 => ⟨((1021680243/34359738368), (-9132939/2147483648)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((-752068783/68719476736), (215131053/137438953472)), (69/34359738368), by norm_num⟩
  | 9 => ⟨((984186951/274877906944), (-70382251/137438953472)), (91/137438953472), by norm_num⟩
  | 10 => ⟨((-144893921/137438953472), (165788995/1099511627776)), (217/1099511627776), by norm_num⟩
  | 11 => ⟨((620554631/2199023255552), (-11094445/274877906944)), (117/2199023255552), by norm_num⟩
  | 12 => ⟨((-152265437/2199023255552), (87111777/8796093022208)), (231/17592186044416), by norm_num⟩
  | 13 => ⟨((137949627/8796093022208), (-157843269/70368744177664)), (211/70368744177664), by norm_num⟩
  | 14 => ⟨((-928421163/281474976710656), (265577071/562949953421312)), (357/562949953421312), by norm_num⟩
  | 15 => ⟨((1457962379/2251799813685248), (-208526795/2251799813685248)), (283/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1073220315/9007199254740992), (76749303/4503599627370496)), (105/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1953611326823/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778041146511535/633825300114114700748351602688), (2310223314761/316912650057057350374175801344)), (92655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944461427975493/19807040628566084398385987584), (2598414881027/19807040628566084398385987584)), (52133/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236080771825815/309485009821345068724781056), (5520198158173/2475880078570760549798248448)), (110817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885155893219899/77371252455336267181195264), (5518585723171/154742504910672534362390528)), (13857/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387182194711553/2417851639229258349412352), (2585980632085/4835703278458516698824704)), (3249/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258066441741453/604462909807314587353088), (1130938414995/151115727451828646838272)), (22753/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943308567818287/37778931862957161709568), (1836972430533/18889465931478580854784)), (73985/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296657164471577/4722366482869645213696), (5508109424767/4722366482869645213696)), (27761/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405058292814373/147573952589676412928), (7569089291677/590295810358705651712)), (152795/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821953249090225/73786976294838206464), (4727261346711/36893488147419103232)), (191155/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455235412169941/2305843009213693952), (10626939114859/9223372036854775808)), (215273/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592185530995437/1152921504606846976), (10615197377753/1152921504606846976)), (215553/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149125036179939/18014398509481984), (4637548878123/72057594037927936)), (47231/36028797018963968), by norm_num⟩
  | 4 => ⟨((186157045529361/4503599627370496), (3471567630447/9007199254740992)), (284015/36028797018963968), by norm_num⟩
  | 3 => ⟨((743131703712387/4503599627370496), (17311733538261/9007199254740992)), (89031/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110952993439027/2251799813685248), (17242683943703/2251799813685248)), (357785/2251799813685248), by norm_num⟩
  | 1 => ⟨((137931753576967/140737488355328), (6422944571769/281474976710656)), (540841/1125899906842624), by norm_num⟩
  | 0 => ⟨((16889214483423/17592186044416), (25348414936497/562949953421312)), (1098409/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((16889214483423/17592186044416), (25348414936497/562949953421312)), (4190097813132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1035434555192019/1125899906842624), (97342039379623/1125899906842624)), (1103977/562949953421312), by norm_num⟩
  | 2 => ⟨((471911063761925/562949953421312), (89520667542441/562949953421312)), (17355/4398046511104), by norm_num⟩
  | 3 => ⟨((762718251876277/1125899906842624), (600348833026927/2251799813685248)), (17723593/2251799813685248), by norm_num⟩
  | 4 => ⟨((218329555064403/562949953421312), (813388489792751/2251799813685248)), (33463503/2251799813685248), by norm_num⟩
  | 5 => ⟨((89780519469143/4503599627370496), (1261829730985355/4503599627370496)), (100263115/4503599627370496), by norm_num⟩
  | 6 => ⟨((-87938197186467/1125899906842624), (100619715874361/9007199254740992)), (240725945/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1214648523/16777216)), (1/16777216), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-617904091/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-226732625828961/18014398509481984), (335196069018249/4503599627370496)), (115297057/9007199254740992), by norm_num⟩
  | 1 => ⟨((80970555/2147483648), (-957639391/4294967296)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-242566105/4294967296), (1434415615/4294967296)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((60555259/1073741824), (-1432375051/4294967296)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-11337959/268435456), (536376521/2147483648)), (191/4294967296), by norm_num⟩
  | 5 => ⟨((108689567/4294967296), (-321368091/2147483648)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-27133737/2147483648), (1283643683/17179869184)), (29/2147483648), by norm_num⟩
  | 7 => ⟨((185795227/34359738368), (-1098700803/34359738368)), (201/34359738368), by norm_num⟩
  | 8 => ⟨((-278296379/137438953472), (1645706727/137438953472)), (303/137438953472), by norm_num⟩
  | 9 => ⟨((46316747/68719476736), (-1095577057/274877906944)), (51/68719476736), by norm_num⟩
  | 10 => ⟨((-111002059/549755813888), (1312822219/1099511627776)), (123/549755813888), by norm_num⟩
  | 11 => ⟨((120920891/2199023255552), (-357533081/1099511627776)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((-15093609/1099511627776), (1428097853/17592186044416)), (271/17592186044416), by norm_num⟩
  | 13 => ⟨((222603873/70368744177664), (-658184435/35184372088832)), (63/17592186044416), by norm_num⟩
  | 14 => ⟨((-11908243/17592186044416), (1126711059/281474976710656)), (109/140737488355328), by norm_num⟩
  | 15 => ⟨((304417347/2251799813685248), (-450043291/562949953421312)), (351/2251799813685248), by norm_num⟩
  | 16 => ⟨((-113994109/4503599627370496), (337052303/2251799813685248)), (265/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1132175328869/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777980602650719/633825300114114700748351602688), (1338744655709/316912650057057350374175801344)), (5779/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888855180067759/39614081257132168796771975168), (3011498006929/39614081257132168796771975168)), (104039/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944287423792411/1237940039285380274899124224), (3198873038657/2475880078570760549798248448)), (110561/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770241109721391/154742504910672534362390528), (3197924357387/154742504910672534362390528)), (13823/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548663209844407/9671406556917033397649408), (2997046449993/9671406556917033397649408)), (6481/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258009758695565/604462909807314587353088), (2621408389773/604462909807314587353088)), (90757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943263158932159/37778931862957161709568), (2128950420857/37778931862957161709568)), (36881/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648295090271525/2361183241434822606848), (3191774622797/4722366482869645213696)), (55341/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405035725320321/147573952589676412928), (4386008734177/590295810358705651712)), (76125/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821843156897947/73786976294838206464), (5478491512243/73786976294838206464)), (95203/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455205390761857/2305843009213693952), (3078890288511/4611686018427387904)), (214337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796035072734331/576460752303423488), (6150884067301/1152921504606846976)), (214499/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192904600990151/144115188075855872), (5374273858293/144115188075855872)), (187869/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489123345054497/36028797018963968), (8045933547245/36028797018963968)), (282169/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486115455074533/9007199254740992), (5015190783977/4503599627370496)), (353351/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221664739799561/4503599627370496), (9989927982319/2251799813685248)), (354315/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206681758433229/2251799813685248), (29768210959595/2251799813685248)), (4171/8796093022208), by norm_num⟩
  | 0 => ⟨((540475683839521/562949953421312), (58734289191713/2251799813685248)), (269371/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540475683839521/562949953421312), (58734289191713/2251799813685248)), (1027568818212413699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2074062575206663/2251799813685248), (28194739978921/562949953421312)), (1062573/562949953421312), by norm_num⟩
  | 2 => ⟨((238088242014613/281474976710656), (207754364850967/2251799813685248)), (8255367/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591945609542275/2251799813685248), (175730972878189/1125899906842624)), (15489065/2251799813685248), by norm_num⟩
  | 4 => ⟨((535297434029151/1125899906842624), (496943199006995/2251799813685248)), (13367781/1125899906842624), by norm_num⟩
  | 5 => ⟨((399334267197501/2251799813685248), (472532980365305/2251799813685248)), (4652835/281474976710656), by norm_num⟩
  | 6 => ⟨((-226732625828961/18014398509481984), (335196069018249/4503599627370496)), (115297057/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-617904091/8388608)), (1/16777216), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-627967621/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1119170868978565/18014398509481984), (334405825575687/9007199254740992)), (255009867/18014398509481984), by norm_num⟩
  | 1 => ⟨((-812373357/4294967296), (-485470791/4294967296)), (187/4294967296), by norm_num⟩
  | 2 => ⟨((1236644457/4294967296), (369506679/2147483648)), (287/4294967296), by norm_num⟩
  | 3 => ⟨((-627498633/2147483648), (-749980917/4294967296)), (293/4294967296), by norm_num⟩
  | 4 => ⟨((477608417/2147483648), (570833433/4294967296)), (225/4294967296), by norm_num⟩
  | 5 => ⟨((-581635817/4294967296), (-347583039/4294967296)), (69/2147483648), by norm_num⟩
  | 6 => ⟨((590267765/8589934592), (176370727/4294967296)), (283/17179869184), by norm_num⟩
  | 7 => ⟨((-1026904831/34359738368), (-613673869/34359738368)), (249/34359738368), by norm_num⟩
  | 8 => ⟨((195402175/17179869184), (233542983/34359738368)), (191/68719476736), by norm_num⟩
  | 9 => ⟨((-1057611211/274877906944), (-158005967/68719476736)), (261/274877906944), by norm_num⟩
  | 10 => ⟨((1287968425/1099511627776), (769684339/1099511627776)), (5/17179869184), by norm_num⟩
  | 11 => ⟨((-356477161/1099511627776), (-426058407/2199023255552)), (179/2199023255552), by norm_num⟩
  | 12 => ⟨((90441893/1099511627776), (108095365/2199023255552)), (183/8796093022208), by norm_num⟩
  | 13 => ⟨((-84723807/4398046511104), (-405044633/35184372088832)), (173/35184372088832), by norm_num⟩
  | 14 => ⟨((589585215/140737488355328), (88083391/35184372088832)), (303/281474976710656), by norm_num⟩
  | 15 => ⟨((-478668111/562949953421312), (-572099969/1125899906842624)), (31/140737488355328), by norm_num⟩
  | 16 => ⟨((364328951/2251799813685248), (217721399/2251799813685248)), (95/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (701651408475/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888959631235813/316912650057057350374175801344), (829612479453/633825300114114700748351602688)), (184563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888786379650221/39614081257132168796771975168), (116637847093/4951760157141521099596496896)), (207645/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502022445687/2475880078570760549798248448), (495578139855/1237940039285380274899124224)), (220635/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442542148492207/38685626227668133590597632), (123857228853/19342813113834066795298816)), (220649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548595554799411/9671406556917033397649408), (928612239895/9671406556917033397649408)), (206873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628975444361259/302231454903657293676544), (406109437297/302231454903657293676544)), (181029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886431268918655/75557863725914323419136), (1319261904869/75557863725914323419136)), (294199/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162064928893945/590295810358705651712), (494463591395/2361183241434822606848)), (220673/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620046492889655/590295810358705651712), (679465831681/295147905179352825856)), (37933/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821723952483513/73786976294838206464), (1697400741709/73786976294838206464)), (189695/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820689250757515/9223372036854775808), (1907839652169/9223372036854775808)), (213447/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397985017316365/288230376151711744), (1905671813365/1152921504606846976)), (106749/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192793293377583/144115188075855872), (832513649485/72057594037927936)), (46717/18014398509481984), by norm_num⟩
  | 4 => ⟨((186120173183495/4503599627370496), (2492678063467/36028797018963968)), (280417/18014398509481984), by norm_num⟩
  | 3 => ⟨((371480430554165/2251799813685248), (3107355926551/9007199254740992)), (350723/4503599627370496), by norm_num⟩
  | 2 => ⟨((555325819520443/1125899906842624), (3094655157947/2251799813685248)), (1404109/4503599627370496), by norm_num⟩
  | 1 => ⟨((137887754205347/140737488355328), (2305179468625/562949953421312)), (2109229/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161202323389515/2251799813685248), (9094988493545/1125899906842624)), (4230845/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161202323389515/2251799813685248), (9094988493545/1125899906842624)), (16139392861373137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((518525734278957/562949953421312), (17458132951243/1125899906842624)), (4094801/1125899906842624), by norm_num⟩
  | 2 => ⟨((477471822982515/562949953421312), (64321818681513/2251799813685248)), (15340643/2251799813685248), by norm_num⟩
  | 3 => ⟨((1618053323112463/2251799813685248), (54555215497865/1125899906842624)), (13449525/1125899906842624), by norm_num⟩
  | 4 => ⟨((289345377689011/562949953421312), (78402393670129/1125899906842624)), (41263939/2251799813685248), by norm_num⟩
  | 5 => ⟨((1167905079408555/4503599627370496), (322378500189387/4503599627370496)), (96329175/4503599627370496), by norm_num⟩
  | 6 => ⟨((1119170868978565/18014398509481984), (334405825575687/9007199254740992)), (255009867/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-627967621/8388608)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile030Terms2
