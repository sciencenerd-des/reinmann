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
namespace Reinmann.XiBand97.Tile035Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6581/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6581/256))
  have he : value ((69/80), (6581/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1195796489/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-458001907303487/9007199254740992), (-171309548136761/2251799813685248)), (149229713/4503599627370496), by norm_num⟩
  | 1 => ⟨((605512105/4294967296), (905935137/4294967296)), (397/4294967296), by norm_num⟩
  | 2 => ⟨((-839418017/4294967296), (-313973193/1073741824)), (553/4294967296), by norm_num⟩
  | 3 => ⟨((24243343/134217728), (1160691379/4294967296)), (513/4294967296), by norm_num⟩
  | 4 => ⟨((-537734555/4294967296), (-804529957/4294967296)), (357/4294967296), by norm_num⟩
  | 5 => ⟨((596366705/8589934592), (446126137/4294967296)), (199/4294967296), by norm_num⟩
  | 6 => ⟨((-551159867/17179869184), (-824616197/17179869184)), (185/8589934592), by norm_num⟩
  | 7 => ⟨((436611323/34359738368), (326617367/17179869184)), (295/34359738368), by norm_num⟩
  | 8 => ⟨((-605271815/137438953472), (-226393907/34359738368)), (411/137438953472), by norm_num⟩
  | 9 => ⟨((11653957/8589934592), (557953061/274877906944)), (509/549755813888), by norm_num⟩
  | 10 => ⟨((-413588861/1099511627776), (-309394873/549755813888)), (567/2199023255552), by norm_num⟩
  | 11 => ⟨((833972227/8796093022208), (623872535/4398046511104)), (287/4398046511104), by norm_num⟩
  | 12 => ⟨((-770753997/35184372088832), (-1153161303/35184372088832)), (533/35184372088832), by norm_num⟩
  | 13 => ⟨((657533489/140737488355328), (983766777/140737488355328)), (457/140737488355328), by norm_num⟩
  | 14 => ⟨((-520877125/562949953421312), (-779308763/562949953421312)), (91/140737488355328), by norm_num⟩
  | 15 => ⟨((770228289/4503599627370496), (1152374767/4503599627370496)), (541/4503599627370496), by norm_num⟩
  | 16 => ⟨((-533881567/18014398509481984), (-798765321/18014398509481984)), (377/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-1406811836585/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889137501292695/316912650057057350374175801344), (-3328036743023/633825300114114700748351602688)), (185055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889186190098423/39614081257132168796771975168), (-1871626757575/19807040628566084398385987584)), (104115/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944463151106953/1237940039285380274899124224), (-248514730427/154742504910672534362390528)), (55323/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885296145278335/77371252455336267181195264), (-3975143403561/154742504910672534362390528)), (221347/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774496075563733/4835703278458516698824704), (-465692087543/1208925819614629174706176)), (207571/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258297291743561/604462909807314587353088), (-3258684721355/604462909807314587353088)), (45421/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943496507306105/37778931862957161709568), (-5293188617379/75557863725914323419136)), (295345/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648469863538999/2361183241434822606848), (-1983994953297/2361183241434822606848)), (221605/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810311377461103/295147905179352825856), (-5452897482497/590295810358705651712)), (152431/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113902613493883/4611686018427387904), (-6811491326817/73786976294838206464)), (381311/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821493464093561/9223372036854775808), (-3828282360319/4611686018427387904)), (429297/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592740061566825/1152921504606846976), (-956077108633/144115188075855872)), (429699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149186068573479/18014398509481984), (-1670901643295/36028797018963968)), (47055/18014398509481984), by norm_num⟩
  | 4 => ⟨((744997409328949/18014398509481984), (-2501890960595/9007199254740992)), (565567/36028797018963968), by norm_num⟩
  | 3 => ⟨((743598518159673/4503599627370496), (-3119567513965/2251799813685248)), (708549/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223804711355463/4503599627370496), (-24863168902301/4503599627370496)), (1421877/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104917028688133/1125899906842624), (-37061965483225/2251799813685248)), (1072397/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083989303621723/1125899906842624), (-73196616714967/2251799813685248)), (2168849/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083989303621723/1125899906842624), (-73196616714967/2251799813685248)), (8273502354148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042449126302073/1125899906842624), (-35235969511193/562949953421312)), (8634465/2251799813685248), by norm_num⟩
  | 2 => ⟨((960772694059369/1125899906842624), (-130497233042169/1125899906842624)), (17069863/2251799813685248), by norm_num⟩
  | 3 => ⟨((804738179932261/1125899906842624), (-445432768562235/2251799813685248)), (33089671/2251799813685248), by norm_num⟩
  | 4 => ⟨((1062263078234753/2251799813685248), (-636747109181643/2251799813685248)), (30196409/1125899906842624), by norm_num⟩
  | 5 => ⟨((160528471921849/1125899906842624), (-150189404081485/562949953421312)), (91134225/2251799813685248), by norm_num⟩
  | 6 => ⟨((-458001907303487/9007199254740992), (-171309548136761/2251799813685248)), (149229713/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1195796489/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-305485857/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1311266199054705/18014398509481984), (426625846762251/9007199254740992)), (569130113/18014398509481984), by norm_num⟩
  | 1 => ⟨((442874061/2147483648), (-9005681/67108864)), (387/4294967296), by norm_num⟩
  | 2 => ⟨((-1254756699/4294967296), (816480499/4294967296)), (551/4294967296), by norm_num⟩
  | 3 => ⟨((74062363/268435456), (-771087815/4294967296)), (261/2147483648), by norm_num⟩
  | 4 => ⟨((-839337901/4294967296), (68270509/536870912)), (93/1073741824), by norm_num⟩
  | 5 => ⟨((951209337/8589934592), (-618959735/8589934592)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((-898326329/17179869184), (584548327/17179869184)), (201/8589934592), by norm_num⟩
  | 7 => ⟨((727185755/34359738368), (-473185749/34359738368)), (327/34359738368), by norm_num⟩
  | 8 => ⟨((-8047939/1073741824), (670318089/137438953472)), (465/137438953472), by norm_num⟩
  | 9 => ⟨((648576801/274877906944), (-844068513/549755813888)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((-735022579/1099511627776), (478285235/1099511627776)), (335/1099511627776), by norm_num⟩
  | 11 => ⟨((47328995/274877906944), (-246378929/2199023255552)), (347/4398046511104), by norm_num⟩
  | 12 => ⟨((-357581707/8796093022208), (465362713/17592186044416)), (329/17592186044416), by norm_num⟩
  | 13 => ⟨((623449393/70368744177664), (-811367291/140737488355328)), (9/2199023255552), by norm_num⟩
  | 14 => ⟨((-252337877/140737488355328), (656793325/562949953421312)), (469/562949953421312), by norm_num⟩
  | 15 => ⟨((762588843/2251799813685248), (-248111415/1125899906842624)), (89/562949953421312), by norm_num⟩
  | 16 => ⟨((-1080288443/18014398509481984), (175738143/4503599627370496)), (253/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1670416896863/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778192008793443/633825300114114700748351602688), (1975647587705/316912650057057350374175801344)), (92589/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59034147104201/1237940039285380274899124224), (1111061657831/9903520314283042199192993792)), (208375/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888826822192719/2475880078570760549798248448), (4720833164453/2475880078570760549798248448)), (221457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55327894900639/4835703278458516698824704), (4719507187325/154742504910672534362390528)), (110761/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548898541335469/9671406556917033397649408), (2211564736681/4835703278458516698824704)), (103873/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258215198938911/604462909807314587353088), (1934415075947/302231454903657293676544)), (22731/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943429634369095/37778931862957161709568), (1571052385389/18889465931478580854784)), (18477/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296839116116349/4722366482869645213696), (4710848435029/4722366482869645213696)), (110919/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810241962763809/295147905179352825856), (6473666430625/590295810358705651712)), (305211/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911133773205291/36893488147419103232), (4043230209893/36893488147419103232)), (11931/2305843009213693952), by norm_num⟩
  | 7 => ⟨((455324101347967/2305843009213693952), (4544770575329/4611686018427387904)), (214949/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398135437241241/288230376151711744), (2269972260695/288230376151711744)), (53797/144115188075855872), by norm_num⟩
  | 5 => ⟨((298328404637293/36028797018963968), (3967026559387/72057594037927936)), (377117/144115188075855872), by norm_num⟩
  | 4 => ⟨((744864810436779/18014398509481984), (11879402164287/36028797018963968)), (566753/36028797018963968), by norm_num⟩
  | 3 => ⟨((743430328721257/4503599627370496), (7405683366317/4503599627370496)), (355165/4503599627370496), by norm_num⟩
  | 2 => ⟨((555779350233931/1125899906842624), (14754637154397/2251799813685248)), (44573/140737488355328), by norm_num⟩
  | 1 => ⟨((1104383516011341/1125899906842624), (21990479740857/1125899906842624)), (1076867/1125899906842624), by norm_num⟩
  | 0 => ⟨((135356390073505/140737488355328), (43417144193495/1125899906842624)), (2182307/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((135356390073505/140737488355328), (43417144193495/1125899906842624)), (8324840549949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039774045484925/1125899906842624), (41757089557367/562949953421312)), (8732085/2251799813685248), by norm_num⟩
  | 2 => ⟨((1908083375836041/2251799813685248), (308503004026333/2251799813685248)), (4355915/562949953421312), by norm_num⟩
  | 3 => ⟨((393641571077973/562949953421312), (261412870629363/1125899906842624)), (17151191/1125899906842624), by norm_num⟩
  | 4 => ⟨((489810909158677/1125899906842624), (365584800102231/1125899906842624)), (998445/35184372088832), by norm_num⟩
  | 5 => ⟨((188760084301019/2251799813685248), (1272350568460943/4503599627370496)), (6068501/140737488355328), by norm_num⟩
  | 6 => ⟨((-1311266199054705/18014398509481984), (426625846762251/9007199254740992)), (569130113/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-305485857/4194304)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1246595419/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((170413717814095/4503599627370496), (1324010550047697/18014398509481984)), (402028567/18014398509481984), by norm_num⟩
  | 1 => ⟨((-469740865/4294967296), (-14256249/67108864)), (279/4294967296), by norm_num⟩
  | 2 => ⟨((678862865/4294967296), (82411719/268435456)), (405/4294967296), by norm_num⟩
  | 3 => ⟨((-654055351/4294967296), (-635201347/2147483648)), (49/536870912), by norm_num⟩
  | 4 => ⟨((472615779/4294967296), (917984017/4294967296)), (285/4294967296), by norm_num⟩
  | 5 => ⟨((-68301765/1073741824), (-1061326031/8589934592)), (331/8589934592), by norm_num⟩
  | 6 => ⟨((526446647/17179869184), (511271131/8589934592)), (321/17179869184), by norm_num⟩
  | 7 => ⟨((-434750435/34359738368), (-844436365/34359738368)), (267/34359738368), by norm_num⟩
  | 8 => ⟨((314147595/68719476736), (1220367511/137438953472)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((-201778519/137438953472), (-783847953/274877906944)), (251/274877906944), by norm_num⟩
  | 10 => ⟨((233285973/549755813888), (906244795/1099511627776)), (73/274877906944), by norm_num⟩
  | 11 => ⟨((-490387773/4398046511104), (-238125851/1099511627776)), (309/4398046511104), by norm_num⟩
  | 12 => ⟨((472467657/17592186044416), (917696313/17592186044416)), (75/4398046511104), by norm_num⟩
  | 13 => ⟨((-210093411/35184372088832), (-816148771/70368744177664)), (269/70368744177664), by norm_num⟩
  | 14 => ⟨((693997785/562949953421312), (168498097/70368744177664)), (223/281474976710656), by norm_num⟩
  | 15 => ⟨((-8357965/35184372088832), (-1038980567/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | 16 => ⟨((12078813/281474976710656), (375380011/4503599627370496)), (251/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (713405593957/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889061450568045/316912650057057350374175801344), (1687391092729/633825300114114700748351602688)), (46183/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944507679135705/19807040628566084398385987584), (237238064599/4951760157141521099596496896)), (207845/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888745163490037/2475880078570760549798248448), (1008005418897/1237940039285380274899124224)), (220861/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885205783908103/77371252455336267181195264), (503858571371/38685626227668133590597632)), (27611/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548823165240449/9671406556917033397649408), (236107159293/1208925819614629174706176)), (25889/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258149870436785/604462909807314587353088), (1652137992655/604462909807314587353088)), (90627/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886754281791969/75557863725914323419136), (2683577030885/75557863725914323419136)), (4603/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1296761400198743/4722366482869645213696), (1005839744467/2361183241434822606848)), (220993/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620378728565865/590295810358705651712), (1382214969357/295147905179352825856)), (37993/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911069270130997/36893488147419103232), (3453095096469/73786976294838206464)), (380049/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113822168217525/576460752303423488), (242586035139/576460752303423488)), (213859/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24881317169431/18014398509481984), (242324153083/72057594037927936)), (427923/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193198134487121/144115188075855872), (3387829985463/144115188075855872)), (374663/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489565934493189/36028797018963968), (1268085735901/9007199254740992)), (70307/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486672676877783/9007199254740992), (3162003601413/4503599627370496)), (87985/1125899906842624), by norm_num⟩
  | 2 => ⟨((2222791054359777/4503599627370496), (6299439035767/2251799813685248)), (1410195/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208400614666375/2251799813685248), (18775923531763/2251799813685248)), (2121403/2251799813685248), by norm_num⟩
  | 0 => ⟨((135341014824507/140737488355328), (37064947730295/2251799813685248)), (2133691/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((135341014824507/140737488355328), (37064947730295/2251799813685248)), (8139385227683639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((260226668260753/281474976710656), (71287440167615/2251799813685248)), (8347989/2251799813685248), by norm_num⟩
  | 2 => ⟨((961201098451933/1125899906842624), (131812022940325/2251799813685248)), (15964175/2251799813685248), by norm_num⟩
  | 3 => ⟨((1633473710635687/2251799813685248), (225060612350013/2251799813685248)), (14563389/1125899906842624), by norm_num⟩
  | 4 => ⟨((1162440847626981/2251799813685248), (326521559633367/2251799813685248)), (48079867/2251799813685248), by norm_num⟩
  | 5 => ⟨((1105473397556913/4503599627370496), (337118776049201/2251799813685248)), (15895977/562949953421312), by norm_num⟩
  | 6 => ⟨((170413717814095/4503599627370496), (1324010550047697/18014398509481984)), (402028567/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1246595419/16777216)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1269914201/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1360112375727603/18014398509481984), (-412640308902363/18014398509481984)), (115243899/18014398509481984), by norm_num⟩
  | 1 => ⟨((-954811071/4294967296), (289677193/4294967296)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((351422867/1073741824), (-426468409/4294967296)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((-86228599/268435456), (418570069/4294967296)), (123/4294967296), by norm_num⟩
  | 4 => ⟨((3967107/16777216), (-308113507/4294967296)), (23/1073741824), by norm_num⟩
  | 5 => ⟨((-1196124619/8589934592), (45361071/1073741824)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((73373249/1073741824), (-89041937/4294967296)), (55/8589934592), by norm_num⟩
  | 7 => ⟨((-987625391/34359738368), (299632629/34359738368)), (95/34359738368), by norm_num⟩
  | 8 => ⟨((1454001349/137438953472), (-110281249/34359738368)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-951381833/274877906944), (288636807/274877906944)), (95/274877906944), by norm_num⟩
  | 10 => ⟨((1120514301/1099511627776), (-169974693/549755813888)), (57/549755813888), by norm_num⟩
  | 11 => ⟨((-599870179/2199023255552), (2843637/34359738368)), (31/1099511627776), by norm_num⟩
  | 12 => ⟨((588760379/8796093022208), (-22327775/1099511627776)), (123/17592186044416), by norm_num⟩
  | 13 => ⟨((-533405849/35184372088832), (323656719/70368744177664)), (113/70368744177664), by norm_num⟩
  | 14 => ⟨((448737421/140737488355328), (-272282131/281474976710656)), (97/281474976710656), by norm_num⟩
  | 15 => ⟨((-352341321/562949953421312), (427582997/2251799813685248)), (77/1125899906842624), by norm_num⟩
  | 16 => ⟨((1037447519/9007199254740992), (-314748011/9007199254740992)), (115/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-5995293725/158456325028528675187087900672)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889026240642775/316912650057057350374175801344), (-113434783283/158456325028528675187087900672)), (92245/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((14757314309863/309485009821345068724781056), (-7974134745/618970019642690137449562112)), (103779/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944330608665623/1237940039285380274899124224), (-271050384109/1237940039285380274899124224)), (27567/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221290970389407/19342813113834066795298816), (-541942901259/154742504910672534362390528)), (1723/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((193593093565955/1208925819614629174706176), (-507903801077/9671406556917033397649408)), (12923/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629040702944797/302231454903657293676544), (-111062057503/151115727451828646838272)), (45233/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943321654023039/37778931862957161709568), (-721589286285/75557863725914323419136)), (73507/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296678415639733/4722366482869645213696), (-540917292957/4722366482869645213696)), (110267/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620265023673365/590295810358705651712), (-743315226259/590295810358705651712)), (37907/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910998503320975/36893488147419103232), (-232118865673/18446744073709551616)), (94775/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455249071596401/2305843009213693952), (-1043616435093/9223372036854775808)), (213267/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592246917043269/1152921504606846976), (-1042469593549/1152921504606846976)), (213295/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596530786943065/72057594037927936), (-455436196175/72057594037927936)), (186665/144115188075855872), by norm_num⟩
  | 4 => ⟨((23271302870685/562949953421312), (-681867907649/18014398509481984)), (280061/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486423480847651/9007199254740992), (-850088459317/4503599627370496)), (350189/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222304578581451/4503599627370496), (-3386913213579/4503599627370496)), (175179/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103850239497061/1125899906842624), (-5046900636267/2251799813685248)), (525967/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164173008228101/2251799813685248), (-9960715818269/2251799813685248)), (1053683/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164173008228101/2251799813685248), (-9960715818269/2251799813685248)), (4019481663230514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519978015498907/562949953421312), (-2393275834903/281474976710656)), (1017341/562949953421312), by norm_num⟩
  | 2 => ⟨((960491155145227/1125899906842624), (-17684709791501/1125899906842624)), (474167/140737488355328), by norm_num⟩
  | 3 => ⟨((1638210474211737/2251799813685248), (-60346420610979/2251799813685248)), (6591261/1125899906842624), by norm_num⟩
  | 4 => ⟨((1190199879691039/2251799813685248), (-87805441429805/2251799813685248)), (9943719/1125899906842624), by norm_num⟩
  | 5 => ⟨((625662170104793/2251799813685248), (-185639993734505/4503599627370496)), (22574167/2251799813685248), by norm_num⟩
  | 6 => ⟨((1360112375727603/18014398509481984), (-412640308902363/18014398509481984)), (115243899/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1269914201/16777216)), (1/16777216), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-646018305/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-57589043058845/18014398509481984), (-1358599889849639/18014398509481984)), (446433133/18014398509481984), by norm_num⟩
  | 1 => ⟨((82264593/8589934592), (1940727967/8589934592)), (5/67108864), by norm_num⟩
  | 2 => ⟨((-30805337/2147483648), (-1453475351/4294967296)), (481/4294967296), by norm_num⟩
  | 3 => ⟨((15380757/1073741824), (1451407673/4294967296)), (241/2147483648), by norm_num⟩
  | 4 => ⟨((-23038315/2147483648), (-543503601/2147483648)), (181/2147483648), by norm_num⟩
  | 5 => ⟨((55213299/8589934592), (1302553023/8589934592)), (435/8589934592), by norm_num⟩
  | 6 => ⟨((-27567377/8589934592), (-1300700043/17179869184)), (109/4294967296), by norm_num⟩
  | 7 => ⟨((11797783/8589934592), (556649871/17179869184)), (375/34359738368), by norm_num⟩
  | 8 => ⟨((-70685999/137438953472), (-52111687/4294967296)), (141/34359738368), by norm_num⟩
  | 9 => ⟨((23528481/137438953472), (555067245/137438953472)), (377/274877906944), by norm_num⟩
  | 10 => ⟨((-7048503/137438953472), (-83141643/68719476736)), (453/1099511627776), by norm_num⟩
  | 11 => ⟨((61426699/4398046511104), (724567573/2199023255552)), (495/4398046511104), by norm_num⟩
  | 12 => ⟨((-61339315/17592186044416), (-723536821/8796093022208)), (31/1099511627776), by norm_num⟩
  | 13 => ⟨((56540359/70368744177664), (1333860065/70368744177664)), (459/70368744177664), by norm_num⟩
  | 14 => ⟨((-24197111/140737488355328), (-142710273/35184372088832)), (395/281474976710656), by norm_num⟩
  | 15 => ⟨((19330151/562949953421312), (228011611/281474976710656)), (633/2251799813685248), by norm_num⟩
  | 16 => ⟨((-57907957/9007199254740992), (-341530871/2251799813685248)), (119/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-131332521595/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444495284059187/158456325028528675187087900672), (-2484713551661/633825300114114700748351602688)), (92445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944427904831019/19807040628566084398385987584), (-698668723659/9903520314283042199192993792)), (6501/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((944287777821731/1237940039285380274899124224), (-2968559316089/2475880078570760549798248448)), (221071/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770241861736057/154742504910672534362390528), (-185479941367/9671406556917033397649408)), (27639/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548663961524413/9671406556917033397649408), (-2781264172361/9671406556917033397649408)), (25917/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314502615760039/151115727451828646838272), (-1216335782429/302231454903657293676544)), (181463/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886527549756885/75557863725914323419136), (-3951339713587/75557863725914323419136)), (147479/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324147795197521/1180591620717411303424), (-2961972922337/4722366482869645213696)), (221291/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620144400487671/590295810358705651712), (-4070224932347/590295810358705651712)), (304391/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821845216416407/73786976294838206464), (-5084051932493/73786976294838206464)), (380663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28450377103321/144115188075855872), (-5714434822603/9223372036854775808)), (428487/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199009129323525/144115188075855872), (-713504557135/144115188075855872)), (428787/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596453742625907/72057594037927936), (-2493671084435/72057594037927936)), (46941/18014398509481984), by norm_num⟩
  | 4 => ⟨((744564190799535/18014398509481984), (-7466654844731/36028797018963968)), (563971/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486122988106879/9007199254740992), (-9308238651619/9007199254740992)), (706153/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110841748162025/2251799813685248), (-2317678316781/562949953421312)), (353971/1125899906842624), by norm_num⟩
  | 1 => ⟨((2206719044069319/2251799813685248), (-6906293209637/562949953421312)), (1066399/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162013460482673/2251799813685248), (-54506426844525/2251799813685248)), (537707/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162013460482673/2251799813685248), (-54506426844525/2251799813685248)), (2051189423681163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((518621951244403/562949953421312), (-13083270968903/281474976710656)), (8468521/2251799813685248), by norm_num⟩
  | 2 => ⟨((238284095029301/281474976710656), (-192849015506673/2251799813685248)), (16390633/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597249041309563/2251799813685248), (-326514659841587/2251799813685248)), (15279305/1125899906842624), by norm_num⟩
  | 4 => ⟨((542808615138857/1125899906842624), (-463207452310759/2251799813685248)), (26106915/1125899906842624), by norm_num⟩
  | 5 => ⟨((428103608918043/2251799813685248), (-893269443163551/4503599627370496)), (143654103/4503599627370496), by norm_num⟩
  | 6 => ⟨((-57589043058845/18014398509481984), (-1358599889849639/18014398509481984)), (446433133/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-646018305/8388608)), (1/8388608), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-656539719/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1255083352388279/18014398509481984), (-353013083672559/18014398509481984)), (456406425/18014398509481984), by norm_num⟩
  | 1 => ⟨((911028249/4294967296), (256241859/4294967296)), (333/4294967296), by norm_num⟩
  | 2 => ⟨((-1386822973/4294967296), (-390067045/4294967296)), (509/4294967296), by norm_num⟩
  | 3 => ⟨((1407404553/4294967296), (395855957/4294967296)), (259/2147483648), by norm_num⟩
  | 4 => ⟨((-1071218685/4294967296), (-150649043/2147483648)), (99/1073741824), by norm_num⟩
  | 5 => ⟨((1304539729/8589934592), (366923513/8589934592)), (121/2147483648), by norm_num⟩
  | 6 => ⟨((-1323900159/17179869184), (-93092239/4294967296)), (493/17179869184), by norm_num⟩
  | 7 => ⟨((1151612497/34359738368), (323910183/34359738368)), (431/34359738368), by norm_num⟩
  | 8 => ⟨((-438263761/34359738368), (-246537955/68719476736)), (329/68719476736), by norm_num⟩
  | 9 => ⟨((593023935/137438953472), (333595705/274877906944)), (447/274877906944), by norm_num⟩
  | 10 => ⟨((-1444379741/1099511627776), (-101563961/274877906944)), (547/1099511627776), by norm_num⟩
  | 11 => ⟨((799535733/2199023255552), (224882733/2199023255552)), (19/137438953472), by norm_num⟩
  | 12 => ⟨((-811401493/8796093022208), (-456440351/17592186044416)), (619/17592186044416), by norm_num⟩
  | 13 => ⟨((1520203109/70368744177664), (106895607/17592186044416)), (291/35184372088832), by norm_num⟩
  | 14 => ⟨((-1322369279/281474976710656), (-185969185/140737488355328)), (127/70368744177664), by norm_num⟩
  | 15 => ⟨((1073595451/1125899906842624), (150983295/562949953421312)), (207/562949953421312), by norm_num⟩
  | 16 => ⟨((-102143295/562949953421312), (-459672029/9007199254740992)), (79/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-3735121383425/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222238646556605/79228162514264337593543950336), (-4416300280357/633825300114114700748351602688)), (92635/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472193618844029/9903520314283042199192993792), (-4967184940713/39614081257132168796771975168)), (208485/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888488634672571/2475880078570760549798248448), (-5276217836451/2475880078570760549798248448)), (55395/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442538593795529/38685626227668133590597632), (-2637312476769/77371252455336267181195264)), (221653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548581342447121/9671406556917033397649408), (-4943268869605/9671406556917033397649408)), (207877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314484392868975/151115727451828646838272), (-4323668701253/604462909807314587353088)), (90985/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886407977397817/75557863725914323419136), (-438924434551/4722366482869645213696)), (147923/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296500519590855/4722366482869645213696), (-5264319851533/4722366482869645213696)), (55503/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620018147934615/590295810358705651712), (-3616967466679/295147905179352825856)), (152737/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821685014521489/73786976294838206464), (-9035664615577/73786976294838206464)), (382153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227580079098253/1152921504606846976), (-2538960285725/2305843009213693952)), (430349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198985681110593/144115188075855872), (-10144247114297/1152921504606846976)), (107721/288230376151711744), by norm_num⟩
  | 5 => ⟨((298184691608033/36028797018963968), (-2215795955209/36028797018963968)), (188813/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488866173237057/36028797018963968), (-13268738129569/36028797018963968)), (141911/9007199254740992), by norm_num⟩
  | 3 => ⟨((742889661477005/4503599627370496), (-1033776131609/562949953421312)), (177917/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110474371642945/2251799813685248), (-8236141921657/1125899906842624)), (178711/562949953421312), by norm_num⟩
  | 1 => ⟨((68921855439573/70368744177664), (-24538519458441/1125899906842624)), (540115/562949953421312), by norm_num⟩
  | 0 => ⟨((1079555014899991/1125899906842624), (-24199996260531/562949953421312)), (2192459/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079555014899991/1125899906842624), (-24199996260531/562949953421312)), (8363567356589889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033037185500235/1125899906842624), (-185630904948775/2251799813685248)), (8785845/2251799813685248), by norm_num⟩
  | 2 => ⟨((1880364519039229/2251799813685248), (-340640631417955/2251799813685248)), (17570953/2251799813685248), by norm_num⟩
  | 3 => ⟨((759333637010153/1125899906842624), (-568903641583633/2251799813685248)), (34661321/2251799813685248), by norm_num⟩
  | 4 => ⟨((440247601879029/1125899906842624), (-767364254400641/2251799813685248)), (64266785/2251799813685248), by norm_num⟩
  | 5 => ⟨((41394422314121/1125899906842624), (-1200214231174255/4503599627370496)), (188120865/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1255083352388279/18014398509481984), (-353013083672559/18014398509481984)), (456406425/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-656539719/8388608)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile035Terms2
