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
namespace Reinmann.XiBand97.Tile013Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5149/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5149/256))
  have he : value ((69/80), (5149/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1871191649/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((584308194226069/9007199254740992), (581292578465451/9007199254740992)), (94069479/9007199254740992), by norm_num⟩
  | 1 => ⟨((-386249139/2147483648), (-768511413/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((1070910007/4294967296), (532691519/2147483648)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-989731003/4294967296), (-984622999/4294967296)), (21/536870912), by norm_num⟩
  | 4 => ⟨((343014627/2147483648), (42655541/268435456)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((-760830789/8589934592), (-189226035/2147483648)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((703156955/17179869184), (699527961/17179869184)), (125/17179869184), by norm_num⟩
  | 7 => ⟨((-69627323/4294967296), (-277071905/17179869184)), (101/34359738368), by norm_num⟩
  | 8 => ⟨((386095861/68719476736), (768206439/137438953472)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-951542249/549755813888), (-946631337/549755813888)), (177/549755813888), by norm_num⟩
  | 10 => ⟨((1055294123/2199023255552), (262461937/549755813888)), (199/2199023255552), by norm_num⟩
  | 11 => ⟨((-531981197/4398046511104), (-529235641/4398046511104)), (203/8796093022208), by norm_num⟩
  | 12 => ⟨((983310045/35184372088832), (244558795/8796093022208)), (95/17592186044416), by norm_num⟩
  | 13 => ⟨((-838865951/140737488355328), (-417268281/70368744177664)), (41/35184372088832), by norm_num⟩
  | 14 => ⟨((83065367/70368744177664), (661093331/562949953421312)), (33/140737488355328), by norm_num⟩
  | 15 => ⟨((-982639359/4503599627370496), (-488783977/2251799813685248)), (197/4503599627370496), by norm_num⟩
  | 16 => ⟨((681113701/18014398509481984), (677598471/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1019698718323/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778280158013111/633825300114114700748351602688), (150766200263/79228162514264337593543950336)), (92319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944596138025135/19807040628566084398385987584), (678307112823/19807040628566084398385987584)), (103867/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888933146795069/2475880078570760549798248448), (1441051103151/2475880078570760549798248448)), (110367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885299780130485/77371252455336267181195264), (22510247217/2417851639229258349412352)), (110377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999417837129/9671406556917033397649408), (675097497371/4835703278458516698824704)), (103489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157288012637923/75557863725914323419136), (1181000948741/604462909807314587353088)), (22641/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58968903894809/2361183241434822606848), (1918340011249/75557863725914323419136)), (73593/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296949398013119/4722366482869645213696), (1438067148015/4722366482869645213696)), (110407/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620637250905561/590295810358705651712), (494056304547/147573952589676412928)), (75919/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822461730959613/73786976294838206464), (2468607016467/73786976294838206464)), (189839/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821518332556575/9223372036854775808), (2774882329725/9223372036854775808)), (213627/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592768003752761/1152921504606846976), (1386004722975/576460752303423488)), (213701/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193516447280215/144115188075855872), (2422280145739/144115188075855872)), (187071/144115188075855872), by norm_num⟩
  | 4 => ⟨((745021771823419/18014398509481984), (3626973654451/36028797018963968)), (280771/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487269928701329/9007199254740992), (4522457315601/9007199254740992)), (175627/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111993130500757/2251799813685248), (1126402768269/562949953421312)), (351691/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210195118915713/2251799813685248), (13432904960055/2251799813685248)), (66079/140737488355328), by norm_num⟩
  | 0 => ⟨((2169051646224389/2251799813685248), (6632977154981/562949953421312)), (265419/281474976710656), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169051646224389/2251799813685248), (6632977154981/562949953421312)), (1012493134618663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2089031659575065/2251799813685248), (51113850991343/2251799813685248)), (2070343/1125899906842624), by norm_num⟩
  | 2 => ⟨((968434365798695/1125899906842624), (94838317611339/2251799813685248)), (7870745/2251799813685248), by norm_num⟩
  | 3 => ⟨((830994423706673/1125899906842624), (163148936084227/2251799813685248)), (14202905/2251799813685248), by norm_num⟩
  | 4 => ⟨((1214845714505997/2251799813685248), (120415549637859/1125899906842624)), (2877949/281474976710656), by norm_num⟩
  | 5 => ⟨((314826052266789/1125899906842624), (259856695161597/2251799813685248)), (59534439/4503599627370496), by norm_num⟩
  | 6 => ⟨((584308194226069/9007199254740992), (581292578465451/9007199254740992)), (94069479/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1871191649/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1912106583/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1417716423927757/18014398509481984), (-20670817781247/562949953421312)), (141640973/18014398509481984), by norm_num⟩
  | 1 => ⟨((-957654259/4294967296), (446814245/4294967296)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1356619413/4294967296), (-632960041/4294967296)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-40037419/134217728), (298885139/2147483648)), (135/4294967296), by norm_num⟩
  | 4 => ⟨((453738199/2147483648), (-211701341/2147483648)), (97/4294967296), by norm_num⟩
  | 5 => ⟨((-8034607/67108864), (479836051/8589934592)), (7/536870912), by norm_num⟩
  | 6 => ⟨((971253579/17179869184), (-453159301/17179869184)), (27/4294967296), by norm_num⟩
  | 7 => ⟨((-49138725/2147483648), (91706927/8589934592)), (89/34359738368), by norm_num⟩
  | 8 => ⟨((1113763931/137438953472), (-519650579/137438953472)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((-1402458147/549755813888), (654347091/549755813888)), (163/549755813888), by norm_num⟩
  | 10 => ⟨((794692627/1099511627776), (-185390491/549755813888)), (47/549755813888), by norm_num⟩
  | 11 => ⟨((-818739547/4398046511104), (382000591/4398046511104)), (99/4398046511104), by norm_num⟩
  | 12 => ⟨((386610635/8796093022208), (-360763057/17592186044416)), (95/17592186044416), by norm_num⟩
  | 13 => ⟨((-674061791/70368744177664), (19656129/4398046511104)), (21/17592186044416), by norm_num⟩
  | 14 => ⟨((1091291921/562949953421312), (-254582889/281474976710656)), (69/281474976710656), by norm_num⟩
  | 15 => ⟨((-824496755/2251799813685248), (96171685/562949953421312)), (53/1125899906842624), by norm_num⟩
  | 16 => ⟨((291996901/4503599627370496), (-544949803/18014398509481984)), (19/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-568653893669/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444550033450799/158456325028528675187087900672), (-672562457505/633825300114114700748351602688)), (92267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944551148809071/19807040628566084398385987584), (-94559093605/4951760157141521099596496896)), (103805/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944418803927397/1237940039285380274899124224), (-803552034435/2475880078570760549798248448)), (110297/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770504092300341/154742504910672534362390528), (-401663421905/77371252455336267181195264)), (110303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454995997659/4835703278458516698824704), (-94109967429/1208925819614629174706176)), (103415/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258225928812871/604462909807314587353088), (-164632673713/151115727451828646838272)), (45247/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943439017891095/37778931862957161709568), (-1069664320787/75557863725914323419136)), (18383/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296854354748141/4722366482869645213696), (-200464100183/1180591620717411303424)), (27577/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620506766699031/590295810358705651712), (-1101916206979/590295810358705651712)), (151689/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822298925776707/73786976294838206464), (-1376441434743/73786976294838206464)), (94817/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227666948595355/1152921504606846976), (-386796557447/2305843009213693952)), (53343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592585774156747/1152921504606846976), (-386387483329/288230376151711744)), (213413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193357573691133/144115188075855872), (-1350517670867/144115188075855872)), (186783/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489806384970881/36028797018963968), (-1011052619379/18014398509481984)), (280267/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486975489318241/9007199254740992), (-630304950069/2251799813685248)), (175249/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111701691543815/2251799813685248), (-5023256128661/4503599627370496)), (701489/4503599627370496), by norm_num⟩
  | 1 => ⟨((17260435260833/17592186044416), (-467944139673/140737488355328)), (1053477/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167391938410859/2251799813685248), (-14784181114143/2251799813685248)), (527997/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167391938410859/2251799813685248), (-14784181114143/2251799813685248)), (2014148714305686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2086050995354489/2251799813685248), (-28460003209929/2251799813685248)), (4093375/2251799813685248), by norm_num⟩
  | 2 => ⟨((966071396976519/1125899906842624), (-1647821268987/70368744177664)), (7687617/2251799813685248), by norm_num⟩
  | 3 => ⟨((828314149210851/1125899906842624), (-45244888590841/1125899906842624)), (6776333/1125899906842624), by norm_num⟩
  | 4 => ⟨((1215129738766227/2251799813685248), (-133144984457311/2251799813685248)), (21030385/2251799813685248), by norm_num⟩
  | 5 => ⟨((1295685954214979/4503599627370496), (-71848496122249/1125899906842624)), (50368131/4503599627370496), by norm_num⟩
  | 6 => ⟨((1417716423927757/18014398509481984), (-20670817781247/562949953421312)), (141640973/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1912106583/33554432)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-975341105/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-22926521727393/18014398509481984), (-93062726807337/1125899906842624)), (15138735/1125899906842624), by norm_num⟩
  | 1 => ⟨((31598173/8589934592), (1026099691/4294967296)), (337/8589934592), by norm_num⟩
  | 2 => ⟨((-22832617/4294967296), (-92681549/268435456)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((10999125/2147483648), (1428715369/4294967296)), (119/2147483648), by norm_num⟩
  | 4 => ⟨((-3973945/1073741824), (-2064759277/8589934592)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((18377885/8589934592), (298396095/2147483648)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((-17706307/17179869184), (-143745941/2147483648)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((29244463/68719476736), (1899333523/68719476736)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((-10565921/68719476736), (-686222497/68719476736)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((27146169/549755813888), (1763056111/549755813888)), (155/274877906944), by norm_num⟩
  | 10 => ⟨((-1961563/137438953472), (-2038355037/2199023255552)), (361/2199023255552), by norm_num⟩
  | 11 => ⟨((16493517/4398046511104), (1071200697/4398046511104)), (3/68719476736), by norm_num⟩
  | 12 => ⟨((-31781597/35184372088832), (-1032056081/17592186044416)), (93/8796093022208), by norm_num⟩
  | 13 => ⟨((28264809/140737488355328), (917854077/70368744177664)), (333/140737488355328), by norm_num⟩
  | 14 => ⟨((-23341659/562949953421312), (-757982715/281474976710656)), (277/562949953421312), by norm_num⟩
  | 15 => ⟨((17990953/2251799813685248), (1168454311/2251799813685248)), (215/2251799813685248), by norm_num⟩
  | 16 => ⟨((-26000271/18014398509481984), (-1688633671/18014398509481984)), (313/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-1033096306999/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778121226840047/633825300114114700748351602688), (-2443543366093/633825300114114700748351602688)), (92441/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889013382270621/39614081257132168796771975168), (-2748389294629/39614081257132168796771975168)), (26003/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944371470598295/1237940039285380274899124224), (-2919420859559/2475880078570760549798248448)), (55265/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770409207527037/154742504910672534362390528), (-1459292781365/77371252455336267181195264)), (110551/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774410402980477/4835703278458516698824704), (-341910844411/1208925819614629174706176)), (103663/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629073829842487/302231454903657293676544), (-2392489030827/604462909807314587353088)), (45363/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943375207560715/37778931862957161709568), (-971533118853/18889465931478580854784)), (73735/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296758260539517/4722366482869645213696), (-1456572815987/2361183241434822606848)), (55319/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620374022594345/590295810358705651712), (-4003214253679/590295810358705651712)), (19023/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911066037632053/36893488147419103232), (-5000478626787/73786976294838206464)), (47579/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821146618797115/9223372036854775808), (-5620675795819/9223372036854775808)), (13389/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592395228840919/1152921504606846976), (-5614603058861/1152921504606846976)), (214371/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193189079176543/144115188075855872), (-2452976761775/72057594037927936)), (187741/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489550120711947/36028797018963968), (-7345301150961/36028797018963968)), (281945/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486649022113327/9007199254740992), (-4578909268975/4503599627370496)), (353017/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222732147580965/4503599627370496), (-18244385453429/4503599627370496)), (707791/4503599627370496), by norm_num⟩
  | 1 => ⟨((276035436160477/281474976710656), (-13594525122145/1125899906842624)), (1066093/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165108286148087/2251799813685248), (-26835793102673/1125899906842624)), (268737/281474976710656), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165108286148087/2251799813685248), (-26835793102673/1125899906842624)), (1025150300146007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1040237507594923/1125899906842624), (-12901324011761/281474976710656)), (4236741/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917454578452283/2251799813685248), (-190715939178699/2251799813685248)), (4108585/1125899906842624), by norm_num⟩
  | 3 => ⟨((808299980497209/1125899906842624), (-324797212025295/2251799813685248)), (15386089/2251799813685248), by norm_num⟩
  | 4 => ⟨((278433077144119/562949953421312), (-466353320663859/2251799813685248)), (26530343/2251799813685248), by norm_num⟩
  | 5 => ⟨((908530349151063/4503599627370496), (-922626882334159/4503599627370496)), (18616315/1125899906842624), by norm_num⟩
  | 6 => ⟨((-22926521727393/18014398509481984), (-93062726807337/1125899906842624)), (15138735/1125899906842624), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-975341105/16777216)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-993585811/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-317135349078273/4503599627370496), (-320538774947145/9007199254740992)), (64073805/4503599627370496), by norm_num⟩
  | 1 => ⟨((890527423/4294967296), (450042183/4294967296)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-327762957/1073741824), (-662560873/4294967296)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((643385351/2147483648), (162572505/1073741824)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-947204453/4294967296), (-478684821/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((1115594285/8589934592), (281891649/4294967296)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((-1094933099/17179869184), (-553341839/17179869184)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((921132485/34359738368), (465508937/34359738368)), (99/17179869184), by norm_num⟩
  | 8 => ⟨((-1356109197/137438953472), (-342665665/68719476736)), (147/68719476736), by norm_num⟩
  | 9 => ⟨((443664531/137438953472), (28026615/17179869184)), (97/137438953472), by norm_num⟩
  | 10 => ⟨((-1045074511/1099511627776), (-528145009/1099511627776)), (115/549755813888), by norm_num⟩
  | 11 => ⟨((1118966591/4398046511104), (282743773/2199023255552)), (31/549755813888), by norm_num⟩
  | 12 => ⟨((-1098242949/17592186044416), (-138753631/4398046511104)), (245/17592186044416), by norm_num⟩
  | 13 => ⟨((248746873/17592186044416), (251416369/35184372088832)), (7/2199023255552), by norm_num⟩
  | 14 => ⟨((-104631427/35184372088832), (-26438577/17592186044416)), (95/140737488355328), by norm_num⟩
  | 15 => ⟨((657239151/1125899906842624), (332146247/1125899906842624)), (301/2251799813685248), by norm_num⟩
  | 16 => ⟨((-967600287/9007199254740992), (-244496089/4503599627370496)), (7/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-3482742689827/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889021749113249/316912650057057350374175801344), (-4118482141705/633825300114114700748351602688)), (46303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944462815557671/19807040628566084398385987584), (-4632253255081/39614081257132168796771975168)), (6513/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888649295623425/2475880078570760549798248448), (-1230123014353/618970019642690137449562112)), (110751/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885157550614027/77371252455336267181195264), (-4919055697373/154742504910672534362390528)), (110785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774366046090523/4835703278458516698824704), (-2305044480367/4835703278458516698824704)), (103897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78629346653067/37778931862957161709568), (-2016151254307/302231454903657293676544)), (90947/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886622565788391/75557863725914323419136), (-6549632479015/75557863725914323419136)), (147855/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296661573577447/4722366482869645213696), (-4909723549113/4722366482869645213696)), (110951/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810119889928355/295147905179352825856), (-1686701937873/147573952589676412928)), (152653/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910981163848275/36893488147419103232), (-131678428919/1152921504606846976)), (190961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455238246154669/2305843009213693952), (-4736238802733/4611686018427387904)), (215031/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796099133500067/576460752303423488), (-9462023212645/1152921504606846976)), (13455/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193013004304051/144115188075855872), (-8267519025107/144115188075855872)), (188651/144115188075855872), by norm_num⟩
  | 4 => ⟨((744639283866093/18014398509481984), (-3094450183975/9007199254740992)), (283537/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486296617763793/9007199254740992), (-3857805128451/2251799813685248)), (177703/4503599627370496), by norm_num⟩
  | 2 => ⟨((555497170277867/1125899906842624), (-15369786433485/2251799813685248)), (356887/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103536226549349/1125899906842624), (-11450742476499/562949953421312)), (539041/1125899906842624), by norm_num⟩
  | 0 => ⟨((270288461775283/281474976710656), (-45192535324895/1125899906842624)), (546493/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((270288461775283/281474976710656), (-45192535324895/1125899906842624)), (2084705354930686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((129546515276467/140737488355328), (-86792943368799/1125899906842624)), (4373679/2251799813685248), by norm_num⟩
  | 2 => ⟨((1894545250776215/2251799813685248), (-159782919183949/1125899906842624)), (272691/70368744177664), by norm_num⟩
  | 3 => ⟨((1548618736440825/2251799813685248), (-537731584939945/2251799813685248)), (4290031/562949953421312), by norm_num⟩
  | 4 => ⟨((936612890984257/2251799813685248), (-369811384898897/1125899906842624)), (496853/35184372088832), by norm_num⟩
  | 5 => ⟨((73319542871381/1125899906842624), (-1230553828893647/4503599627370496)), (94683257/4503599627370496), by norm_num⟩
  | 6 => ⟨((-317135349078273/4503599627370496), (-320538774947145/9007199254740992)), (64073805/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-993585811/16777216)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-2021788939/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-71837559954793/1125899906842624), (726627547918313/18014398509481984)), (247656601/18014398509481984), by norm_num⟩
  | 1 => ⟨((820946109/4294967296), (-518985175/4294967296)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((-1229667377/4294967296), (777370319/4294967296)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((613959041/2147483648), (-776264451/4294967296)), (17/268435456), by norm_num⟩
  | 4 => ⟨((-919628457/4294967296), (581370117/4294967296)), (205/4294967296), by norm_num⟩
  | 5 => ⟨((1101984259/8589934592), (-696651689/8589934592)), (31/1073741824), by norm_num⟩
  | 6 => ⟨((-1100416603/17179869184), (695660649/17179869184)), (125/8589934592), by norm_num⟩
  | 7 => ⟨((470936219/17179869184), (-297716151/17179869184)), (27/4294967296), by norm_num⟩
  | 8 => ⟨((-705399415/68719476736), (445938941/68719476736)), (163/68719476736), by norm_num⟩
  | 9 => ⟨((939194575/274877906944), (-148434853/68719476736)), (219/274877906944), by norm_num⟩
  | 10 => ⟨((-140678775/137438953472), (11116777/17179869184)), (265/1099511627776), by norm_num⟩
  | 11 => ⟨((1225995481/4398046511104), (-775049021/4398046511104)), (291/4398046511104), by norm_num⟩
  | 12 => ⟨((-612125705/8796093022208), (773946455/17592186044416)), (293/17592186044416), by norm_num⟩
  | 13 => ⟨((1128470603/70368744177664), (-713395807/70368744177664)), (17/4398046511104), by norm_num⟩
  | 14 => ⟨((-241471129/70368744177664), (610612241/281474976710656)), (235/281474976710656), by norm_num⟩
  | 15 => ⟨((385804189/562949953421312), (-487794879/1125899906842624)), (189/1125899906842624), by norm_num⟩
  | 16 => ⟨((-288941515/2251799813685248), (730651431/9007199254740992)), (285/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (3357933941821/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777975993193653/633825300114114700748351602688), (3970600669533/633825300114114700748351602688)), (92591/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888849741230081/39614081257132168796771975168), (4465909492929/39614081257132168796771975168)), (104191/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944284365469815/1237940039285380274899124224), (296486030621/154742504910672534362390528)), (110731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221279326669883/19342813113834066795298816), (4742367935567/154742504910672534362390528)), (27691/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387164179093921/2417851639229258349412352), (555559218575/1208925819614629174706176)), (25969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((39312614816933/18889465931478580854784), (3887418786281/604462909807314587353088)), (90927/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886515676038989/75557863725914323419136), (1578562989647/18889465931478580854784)), (147821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648290769908351/2361183241434822606848), (4733236796353/4722366482869645213696)), (110923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810064975130073/295147905179352825856), (6504217596487/590295810358705651712)), (38153/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821825365593949/73786976294838206464), (4062150308117/36893488147419103232)), (190905/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910399674211595/4611686018427387904), (9131632613877/9223372036854775808)), (214959/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796022593840199/576460752303423488), (9121383240337/1152921504606846976)), (6725/36028797018963968), by norm_num⟩
  | 5 => ⟨((596439842617395/72057594037927936), (996211280087/18014398509481984)), (94285/72057594037927936), by norm_num⟩
  | 4 => ⟨((744539918463597/18014398509481984), (5965760648705/18014398509481984)), (283397/36028797018963968), by norm_num⟩
  | 3 => ⟨((743025190724663/4503599627370496), (14874185789935/9007199254740992)), (355197/9007199254740992), by norm_num⟩
  | 2 => ⟨((555375678565635/1125899906842624), (14813979593235/2251799813685248)), (713247/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206359677126849/2251799813685248), (44141730575213/2251799813685248)), (269257/562949953421312), by norm_num⟩
  | 0 => ⟨((2160946299660523/2251799813685248), (21771891079893/562949953421312)), (2182807/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2160946299660523/2251799813685248), (21771891079893/562949953421312)), (8326747902877043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035195188716063/1125899906842624), (167147673358083/2251799813685248)), (2179157/1125899906842624), by norm_num⟩
  | 2 => ⟨((945594262947607/1125899906842624), (38420481743933/281474976710656)), (4330711/1125899906842624), by norm_num⟩
  | 3 => ⟨((773186293159659/1125899906842624), (516283010892185/2251799813685248)), (16913219/2251799813685248), by norm_num⟩
  | 4 => ⟨((235891309639413/562949953421312), (354545679404549/1125899906842624)), (30985123/2251799813685248), by norm_num⟩
  | 5 => ⟨((86043351172155/1125899906842624), (1188514099819351/4503599627370496)), (45481635/2251799813685248), by norm_num⟩
  | 6 => ⟨((-71837559954793/1125899906842624), (726627547918313/18014398509481984)), (247656601/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-2021788939/33554432)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-256839615/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-33530511785813/18014398509481984), (1303352701606347/18014398509481984)), (53286997/4503599627370496), by norm_num⟩
  | 1 => ⟨((48677633/8589934592), (-236516389/1073741824)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-9262509/1073741824), (1440158907/4294967296)), (15/268435456), by norm_num⟩
  | 3 => ⟨((37599889/4294967296), (-365383009/1073741824)), (123/2147483648), by norm_num⟩
  | 4 => ⟨((-14309213/2147483648), (1112416769/4294967296)), (189/4294967296), by norm_num⟩
  | 5 => ⟨((544559/134217728), (-677355563/4294967296)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-35369005/17179869184), (343704035/4294967296)), (237/17179869184), by norm_num⟩
  | 7 => ⟨((240361/268435456), (-1195902453/34359738368)), (13/2147483648), by norm_num⟩
  | 8 => ⟨((-46834205/137438953472), (910237963/68719476736)), (319/137438953472), by norm_num⟩
  | 9 => ⟨((31686175/274877906944), (-1231662179/274877906944)), (217/274877906944), by norm_num⟩
  | 10 => ⟨((-9646927/274877906944), (187491157/137438953472)), (133/549755813888), by norm_num⟩
  | 11 => ⟨((1335013/137438953472), (-830285141/2199023255552)), (37/549755813888), by norm_num⟩
  | 12 => ⟨((-21677211/8796093022208), (1685214495/17592186044416)), (303/17592186044416), by norm_num⟩
  | 13 => ⟨((10153347/17592186044416), (-1578668721/70368744177664)), (285/70368744177664), by norm_num⟩
  | 14 => ⟨((-17664053/140737488355328), (85826649/17592186044416)), (249/281474976710656), by norm_num⟩
  | 15 => ⟨((28681923/1125899906842624), (-69680309/70368744177664)), (51/281474976710656), by norm_num⟩
  | 16 => ⟨((-43661379/9007199254740992), (848573057/4503599627370496)), (39/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (2079641653021/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444479097309331/158456325028528675187087900672), (38420446557/9903520314283042199192993792)), (92443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888782989785947/39614081257132168796771975168), (2765641505911/39614081257132168796771975168)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118031138132567/154742504910672534362390528), (45901670305/38685626227668133590597632)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770164544998223/154742504910672534362390528), (1468410831499/77371252455336267181195264)), (110553/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774295753827693/4835703278458516698824704), (21502578725/75557863725914323419136)), (103665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257947096465197/604462909807314587353088), (2407348957919/604462909807314587353088)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471606159086843/18889465931478580854784), (1955090306371/37778931862957161709568)), (73737/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648257022911185/2361183241434822606848), (1465547494049/2361183241434822606848)), (110641/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620038421253597/590295810358705651712), (2013876913329/295147905179352825856)), (152189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227714108038535/9223372036854775808), (5030942206143/73786976294838206464)), (95161/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820675406012185/9223372036854775808), (5654657841201/9223372036854775808)), (214231/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591924515181635/1152921504606846976), (706027997955/144115188075855872)), (214381/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192777765828511/144115188075855872), (154217705495/4503599627370496)), (187751/144115188075855872), by norm_num⟩
  | 4 => ⟨((186116783983193/4503599627370496), (7388012720507/36028797018963968)), (140981/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485881170788543/9007199254740992), (9209799607775/9007199254740992)), (353041/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110601157412061/2251799813685248), (18344144847849/4503599627370496)), (707853/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103001691130135/1125899906842624), (6832065175011/562949953421312)), (1066221/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160606444465563/2251799813685248), (26954379844629/1125899906842624)), (2150297/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160606444465563/2251799813685248), (26954379844629/1125899906842624)), (8202732094771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071815631718937/2251799813685248), (51725563209429/1125899906842624)), (1057347/562949953421312), by norm_num⟩
  | 2 => ⟨((1901464708477011/2251799813685248), (190364755810821/2251799813685248)), (2042821/562949953421312), by norm_num⟩
  | 3 => ⟨((397385379860965/562949953421312), (160747799476777/1125899906842624)), (15181575/2251799813685248), by norm_num⟩
  | 4 => ⟨((538076876808045/1125899906842624), (226943176631143/1125899906842624)), (25768325/2251799813685248), by norm_num⟩
  | 5 => ⟨((845629415153105/4503599627370496), (867664167675613/4503599627370496)), (17508915/1125899906842624), by norm_num⟩
  | 6 => ⟨((-33530511785813/18014398509481984), (1303352701606347/18014398509481984)), (53286997/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-256839615/4194304)), (1/16777216), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile013Terms2
