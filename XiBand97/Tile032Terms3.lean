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
namespace Reinmann.XiBand97.Tile032Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63841/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63841/2560))
  have he : value ((69/80), (63841/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1293256237/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-71896978172459/9007199254740992), (-622112825625231/9007199254740992)), (52483863/2251799813685248), by norm_num⟩
  | 1 => ⟨((211941349/8589934592), (458473481/2147483648)), (621/8589934592), by norm_num⟩
  | 2 => ⟨((-163779927/4294967296), (-708580497/2147483648)), (241/2147483648), by norm_num⟩
  | 3 => ⟨((42187559/1073741824), (1460168265/4294967296)), (499/4294967296), by norm_num⟩
  | 4 => ⟨((-8150221/268435456), (-282090131/1073741824)), (387/4294967296), by norm_num⟩
  | 5 => ⟨((80616573/4294967296), (1395124113/8589934592)), (15/268435456), by norm_num⟩
  | 6 => ⟨((-83063083/8589934592), (-359365655/4294967296)), (497/17179869184), by norm_num⟩
  | 7 => ⟨((9169697/2147483648), (1269502281/34359738368)), (55/4294967296), by norm_num⟩
  | 8 => ⟨((-113375691/68719476736), (-981021361/68719476736)), (171/34359738368), by norm_num⟩
  | 9 => ⟨((19469393/34359738368), (1347723855/274877906944)), (59/34359738368), by norm_num⟩
  | 10 => ⟨((-192578305/1099511627776), (-1666348661/1099511627776)), (293/549755813888), by norm_num⟩
  | 11 => ⟨((54115247/1099511627776), (1873001619/4398046511104)), (661/4398046511104), by norm_num⟩
  | 12 => ⟨((-111515017/8796093022208), (-964921253/8796093022208)), (171/4398046511104), by norm_num⟩
  | 13 => ⟨((6628801/2199023255552), (1835453881/70368744177664)), (653/70368744177664), by norm_num⟩
  | 14 => ⟨((-187336277/281474976710656), (-202623781/35184372088832)), (579/281474976710656), by norm_num⟩
  | 15 => ⟨((154417169/1125899906842624), (334036645/281474976710656)), (15/35184372088832), by norm_num⟩
  | 16 => ⟨((-59663753/2251799813685248), (-1032521451/4503599627370496)), (373/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-2196014264915/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777854221235575/633825300114114700748351602688), (-649083030341/158456325028528675187087900672)), (184911/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944356523299513/19807040628566084398385987584), (-730049416179/9903520314283042199192993792)), (208059/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472105972028369/618970019642690137449562112), (-3101866085853/2475880078570760549798248448)), (55275/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885045107364025/77371252455336267181195264), (-3100917051045/154742504910672534362390528)), (221143/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548521814268603/9671406556917033397649408), (-2906101742669/9671406556917033397649408)), (207367/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628943053008175/302231454903657293676544), (-2541831433523/604462909807314587353088)), (45373/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886325510538105/75557863725914323419136), (-4128587698361/75557863725914323419136)), (147505/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296439687225723/4722366482869645213696), (-3094789292531/4722366482869645213696)), (55333/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809968077567689/295147905179352825856), (-4252653217383/590295810358705651712)), (152227/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821584997248983/73786976294838206464), (-2655898112733/36893488147419103232)), (190375/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820531508514567/9223372036854775808), (-2985123691425/4611686018427387904)), (428595/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795890279626655/576460752303423488), (-5963349969145/1152921504606846976)), (214455/576460752303423488), by norm_num⟩
  | 5 => ⟨((596325869595309/72057594037927936), (-5210180974101/144115188075855872)), (187825/72057594037927936), by norm_num⟩
  | 4 => ⟨((186093137854849/4503599627370496), (-3899897146279/18014398509481984)), (564185/36028797018963968), by norm_num⟩
  | 3 => ⟨((371411121654619/2251799813685248), (-9722710243807/9007199254740992)), (706475/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220728289718503/4503599627370496), (-2420566497115/562949953421312)), (708345/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205290744101017/2251799813685248), (-14422653956633/1125899906842624)), (133401/140737488355328), by norm_num⟩
  | 0 => ⟨((539793753221757/562949953421312), (-56889030837191/2251799813685248)), (1076635/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539793753221757/562949953421312), (-56889030837191/2251799813685248)), (4107036592723655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1034461488568473/1125899906842624), (-109097951908963/2251799813685248)), (8476393/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895612521269673/2251799813685248), (-100237711226041/1125899906842624)), (16397339/2251799813685248), by norm_num⟩
  | 3 => ⟨((1577918434042325/2251799813685248), (-337528867972553/2251799813685248)), (1907933/140737488355328), by norm_num⟩
  | 4 => ⟨((1055111930170827/2251799813685248), (-473037629329669/2251799813685248)), (51934211/2251799813685248), by norm_num⟩
  | 5 => ⟨((395015836230683/2251799813685248), (-886593280791919/4503599627370496)), (140977441/4503599627370496), by norm_num⟩
  | 6 => ⟨((-71896978172459/9007199254740992), (-622112825625231/9007199254740992)), (52483863/2251799813685248), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1293256237/16777216)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-655927169/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-566733253020439/9007199254740992), (-205080224168069/9007199254740992)), (428343205/18014398509481984), by norm_num⟩
  | 1 => ⟨((847334307/4294967296), (38327447/536870912)), (161/2147483648), by norm_num⟩
  | 2 => ⟨((-1328405909/4294967296), (-480701953/4294967296)), (507/4294967296), by norm_num⟩
  | 3 => ⟨((694201507/2147483648), (502412731/4294967296)), (133/1073741824), by norm_num⟩
  | 4 => ⟨((-1088332405/4294967296), (-393828053/4294967296)), (419/4294967296), by norm_num⟩
  | 5 => ⟨((85311499/536870912), (493938233/8589934592)), (527/8589934592), by norm_num⟩
  | 6 => ⟨((-1426633129/17179869184), (-64530853/2147483648)), (553/17179869184), by norm_num⟩
  | 7 => ⟨((1278057121/34359738368), (57810319/4294967296)), (497/34359738368), by norm_num⟩
  | 8 => ⟨((-1001835177/68719476736), (-181263921/34359738368)), (49/8589934592), by norm_num⟩
  | 9 => ⟨((1396110401/274877906944), (126300439/68719476736)), (137/68719476736), by norm_num⟩
  | 10 => ⟨((-875499217/549755813888), (-316811437/549755813888)), (345/549755813888), by norm_num⟩
  | 11 => ⟨((998226447/2199023255552), (180610987/1099511627776)), (395/2199023255552), by norm_num⟩
  | 12 => ⟨((-1043311083/8796093022208), (-188768235/4398046511104)), (415/8796093022208), by norm_num⟩
  | 13 => ⟨((503276287/17592186044416), (182117449/17592186044416)), (201/17592186044416), by norm_num⟩
  | 14 => ⟨((-450862825/70368744177664), (-326301833/140737488355328)), (181/70368744177664), by norm_num⟩
  | 15 => ⟨((1507922965/1125899906842624), (34103917/70368744177664)), (607/1125899906842624), by norm_num⟩
  | 16 => ⟨((-591010467/2251799813685248), (-213865269/2251799813685248)), (239/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-3640002530981/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777788859587779/633825300114114700748351602688), (-2151638328021/316912650057057350374175801344)), (5789/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944319592842317/19807040628566084398385987584), (-2420016824603/19807040628566084398385987584)), (208459/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472086241852697/618970019642690137449562112), (-5141114947057/2475880078570760549798248448)), (110775/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885005397841953/77371252455336267181195264), (-5139516906625/154742504910672534362390528)), (110811/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193555853735067/1208925819614629174706176), (-4816599638211/9671406556917033397649408)), (103923/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257819966152949/604462909807314587353088), (-4212827734169/604462909807314587353088)), (181941/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471554260840413/18889465931478580854784), (-855333047155/9444732965739290427392)), (295795/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162044683970657/590295810358705651712), (-5129216267641/4722366482869645213696)), (110985/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809910852577119/295147905179352825856), (-7048153635441/590295810358705651712)), (305411/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227679979091927/9223372036854775808), (-8803417519691/73786976294838206464)), (191033/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820365313893971/9223372036854775808), (-4947267773455/4611686018427387904)), (430241/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795805383790321/576460752303423488), (-154420434487/18014398509481984)), (215381/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192499136637181/144115188075855872), (-1079309388331/18014398509481984)), (11797/4503599627370496), by norm_num⟩
  | 4 => ⟨((1488508158885279/36028797018963968), (-12925604170891/36028797018963968)), (567431/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485334302816929/9007199254740992), (-8055691389011/4503599627370496)), (711349/9007199254740992), by norm_num⟩
  | 2 => ⟨((555016543808571/1125899906842624), (-16043083989199/2251799813685248)), (714445/2251799813685248), by norm_num⟩
  | 1 => ⟨((551048532086633/562949953421312), (-373349236579/17592186044416)), (1079433/1125899906842624), by norm_num⟩
  | 0 => ⟨((8424115305513/8796093022208), (-94220872936973/2251799813685248)), (1095033/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((8424115305513/8796093022208), (-94220872936973/2251799813685248)), (4177219393016624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((515357952596649/562949953421312), (-45118184619193/562949953421312)), (4378177/1125899906842624), by norm_num⟩
  | 2 => ⟨((58521669448481/70368744177664), (-5162984539947/35184372088832)), (2179469/281474976710656), by norm_num⟩
  | 3 => ⟨((1508924541484861/2251799813685248), (-137400308910581/562949953421312)), (34117715/2251799813685248), by norm_num⟩
  | 4 => ⟨((438491854754137/1125899906842624), (-736572396401331/2251799813685248)), (31189361/1125899906842624), by norm_num⟩
  | 5 => ⟨((100613531551771/2251799813685248), (-1147459003400965/4503599627370496)), (89396553/2251799813685248), by norm_num⟩
  | 6 => ⟨((-566733253020439/9007199254740992), (-205080224168069/9007199254740992)), (428343205/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-655927169/8388608)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-664830393/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-54877112904021/1125899906842624), (380521126955975/9007199254740992)), (427210069/18014398509481984), by norm_num⟩
  | 1 => ⟨((332646215/2147483648), (-576647103/4294967296)), (325/4294967296), by norm_num⟩
  | 2 => ⟨((-528583789/2147483648), (916307767/4294967296)), (519/4294967296), by norm_num⟩
  | 3 => ⟨((1119911823/4294967296), (-970691803/4294967296)), (69/536870912), by norm_num⟩
  | 4 => ⟨((-889785015/4294967296), (771227701/4294967296)), (441/4294967296), by norm_num⟩
  | 5 => ⟨((565556935/4294967296), (-245100315/2147483648)), (563/8589934592), by norm_num⟩
  | 6 => ⟨((-599123461/8589934592), (519294663/8589934592)), (75/2147483648), by norm_num⟩
  | 7 => ⟨((544013317/17179869184), (-943055081/34359738368)), (547/34359738368), by norm_num⟩
  | 8 => ⟨((-864451803/68719476736), (749269953/68719476736)), (109/17179869184), by norm_num⟩
  | 9 => ⟨((305252707/68719476736), (-264580027/68719476736)), (309/137438953472), by norm_num⟩
  | 10 => ⟨((-194021907/137438953472), (336339827/274877906944)), (395/549755813888), by norm_num⟩
  | 11 => ⟨((224222569/549755813888), (-777386237/2199023255552)), (459/2199023255552), by norm_num⟩
  | 12 => ⟨((-950121859/8796093022208), (823525103/8796093022208)), (61/1099511627776), by norm_num⟩
  | 13 => ⟨((464544371/17592186044416), (-805294495/35184372088832)), (479/35184372088832), by norm_num⟩
  | 14 => ⟨((-843626867/140737488355328), (731219787/140737488355328)), (437/140737488355328), by norm_num⟩
  | 15 => ⟨((714957759/562949953421312), (-154923723/140737488355328)), (93/140737488355328), by norm_num⟩
  | 16 => ⟨((-568043561/2251799813685248), (492355931/2251799813685248)), (593/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (3162024875299/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777734770025395/633825300114114700748351602688), (934494037217/158456325028528675187087900672)), (11571/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944289241819267/19807040628566084398385987584), (4204215345517/39614081257132168796771975168)), (104163/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888280668886573/2475880078570760549798248448), (4465728623593/2475880078570760549798248448)), (221401/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769946719020837/154742504910672534362390528), (1116080652715/38685626227668133590597632)), (221463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774193496778403/4835703278458516698824704), (4183809023967/9671406556917033397649408)), (25961/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257767844715671/604462909807314587353088), (1829669997373/302231454903657293676544)), (181793/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943066393435481/37778931862957161709568), (742953676471/9444732965739290427392)), (295535/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296294664707933/4722366482869645213696), (2227637424495/2361183241434822606848)), (3465/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1619735970777251/590295810358705651712), (47828345953/4611686018427387904)), (152547/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821333601350181/73786976294838206464), (238955532487/2305843009213693952)), (190815/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455061772277865/2305843009213693952), (4297106201447/4611686018427387904)), (3357/72057594037927936), by norm_num⟩
  | 6 => ⟨((1591494146289233/1152921504606846976), (8583987812043/1152921504606846976)), (430149/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192398892243131/144115188075855872), (7499498858773/144115188075855872)), (188445/72057594037927936), by norm_num⟩
  | 4 => ⟨((23255646547727/562949953421312), (11226297790057/36028797018963968)), (141589/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485157078555801/9007199254740992), (6996388675403/4503599627370496)), (709735/9007199254740992), by norm_num⟩
  | 2 => ⟨((138733148332467/281474976710656), (13932771890619/2251799813685248)), (356213/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203736675655707/2251799813685248), (41499245557841/2251799813685248)), (537693/562949953421312), by norm_num⟩
  | 0 => ⟨((1077920712059737/1125899906842624), (81807946518765/2251799813685248)), (4355771/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077920712059737/1125899906842624), (81807946518765/2251799813685248)), (16615947731978606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515250032177657/562949953421312), (156643551398709/2251799813685248)), (8656799/2251799813685248), by norm_num⟩
  | 2 => ⟨((468867647857077/562949953421312), (35842704315051/281474976710656)), (4262745/562949953421312), by norm_num⟩
  | 3 => ⟨((190690195542021/281474976710656), (29852537268899/140737488355328)), (32745219/2251799813685248), by norm_num⟩
  | 4 => ⟨((466088390997615/1125899906842624), (323586060018887/1125899906842624)), (29129581/1125899906842624), by norm_num⟩
  | 5 => ⟨((399788468940439/4503599627370496), (1071638465528655/4503599627370496)), (163445339/4503599627370496), by norm_num⟩
  | 6 => ⟨((-54877112904021/1125899906842624), (380521126955975/9007199254740992)), (427210069/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-664830393/8388608)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-673370117/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((11263872063813/1125899906842624), (276794778712279/4503599627370496)), (5409633/281474976710656), by norm_num⟩
  | 1 => ⟨((-276618999/8589934592), (-849693319/4294967296)), (267/4294967296), by norm_num⟩
  | 2 => ⟨((27825069/536870912), (683764321/2147483648)), (27/268435456), by norm_num⟩
  | 3 => ⟨((-238841179/4294967296), (-1467301629/4294967296)), (233/2147483648), by norm_num⟩
  | 4 => ⟨((24025003/536870912), (295191359/1073741824)), (377/4294967296), by norm_num⟩
  | 5 => ⟨((-61866801/2147483648), (-1520294927/8589934592)), (487/8589934592), by norm_num⟩
  | 6 => ⟨((265522067/17179869184), (1631213529/17179869184)), (525/17179869184), by norm_num⟩
  | 7 => ⟨((-122097509/17179869184), (-1500192513/34359738368)), (485/34359738368), by norm_num⟩
  | 8 => ⟨((24563545/8589934592), (1207233353/68719476736)), (49/8589934592), by norm_num⟩
  | 9 => ⟨((-281127115/274877906944), (-1727081891/274877906944)), (563/274877906944), by norm_num⟩
  | 10 => ⟨((180982655/549755813888), (1111852429/549755813888)), (91/137438953472), by norm_num⟩
  | 11 => ⟨((-52960063/549755813888), (-650711801/1099511627776)), (107/549755813888), by norm_num⟩
  | 12 => ⟨((113647911/4398046511104), (1396373657/8796093022208)), (461/8796093022208), by norm_num⟩
  | 13 => ⟨((-225119085/35184372088832), (-1383001049/35184372088832)), (459/35184372088832), by norm_num⟩
  | 14 => ⟨((51759313/35184372088832), (1271916755/140737488355328)), (53/17592186044416), by norm_num⟩
  | 15 => ⟨((-177713921/562949953421312), (-1091771225/562949953421312)), (183/281474976710656), by norm_num⟩
  | 16 => ⟨((143009761/2251799813685248), (878569001/2251799813685248)), (591/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (458986854255/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777685522809451/633825300114114700748351602688), (2170232274831/633825300114114700748351602688)), (184827/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472130841468295/9903520314283042199192993792), (2440926112147/39614081257132168796771975168)), (207959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888222488473577/2475880078570760549798248448), (2592749642887/2475880078570760549798248448)), (220989/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769888968113183/154742504910672534362390528), (2591923888929/154742504910672534362390528)), (6907/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((24192707938403/151115727451828646838272), (75907863215/302231454903657293676544)), (12953/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628860662730849/302231454903657293676544), (2124543530271/604462909807314587353088)), (181381/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471514511590897/18889465931478580854784), (1725370175589/37778931862957161709568)), (294815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162029919382261/590295810358705651712), (2586618552153/4722366482869645213696)), (110587/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809830565077265/295147905179352825856), (888566844513/147573952589676412928)), (38027/73786976294838206464), by norm_num⟩
  | 8 => ⟨((56913808214905/2305843009213693952), (554917149009/9223372036854775808)), (190211/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910073185259831/4611686018427387904), (2494725126723/4611686018427387904)), (214093/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795698264800819/576460752303423488), (4983451631973/1152921504606846976)), (428449/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298079239389675/36028797018963968), (1088445160097/36028797018963968)), (187595/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488245412596253/36028797018963968), (1629303533943/9007199254740992)), (563379/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485024203256631/9007199254740992), (1015377276397/1125899906842624)), (705265/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109750326897789/2251799813685248), (2021967199319/562949953421312)), (1413665/4503599627370496), by norm_num⟩
  | 1 => ⟨((550870354138917/562949953421312), (24088555979899/2251799813685248)), (2128365/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077841832255057/1125899906842624), (23740538103907/1125899906842624)), (1072093/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077841832255057/1125899906842624), (23740538103907/1125899906842624)), (4089710237743186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((257833621610687/281474976710656), (90908774157001/2251799813685248)), (4195751/1125899906842624), by norm_num⟩
  | 2 => ⟨((235719160106883/281474976710656), (5204578651849/70368744177664)), (16050941/2251799813685248), by norm_num⟩
  | 3 => ⟨((783446128855329/1125899906842624), (139473162167185/1125899906842624)), (29257791/2251799813685248), by norm_num⟩
  | 4 => ⟨((527875586667547/1125899906842624), (97050997442143/562949953421312)), (47966219/2251799813685248), by norm_num⟩
  | 5 => ⟨((53507653992379/281474976710656), (728034197712785/4503599627370496)), (61516189/2251799813685248), by norm_num⟩
  | 6 => ⟨((11263872063813/1125899906842624), (276794778712279/4503599627370496)), (5409633/281474976710656), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-673370117/8388608)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1363149725/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((985105268801325/18014398509481984), (226702602147313/9007199254740992)), (196738019/18014398509481984), by norm_num⟩
  | 1 => ⟨((-382610329/2147483648), (-352200967/4294967296)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((1246581389/4294967296), (71719047/536870912)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((-1353827503/4294967296), (-623113543/4294967296)), (279/4294967296), by norm_num⟩
  | 4 => ⟨((1102725175/4294967296), (507541019/4294967296)), (229/4294967296), by norm_num⟩
  | 5 => ⟨((-718557015/4294967296), (-661447055/8589934592)), (301/8589934592), by norm_num⟩
  | 6 => ⟨((780376041/8589934592), (359176393/8589934592)), (165/8589934592), by norm_num⟩
  | 7 => ⟨((-1452880273/34359738368), (-167175909/8589934592)), (309/34359738368), by norm_num⟩
  | 8 => ⟨((1183406047/68719476736), (272337625/34359738368)), (127/34359738368), by norm_num⟩
  | 9 => ⟨((-428405683/68719476736), (-197178283/68719476736)), (93/68719476736), by norm_num⟩
  | 10 => ⟨((558314829/274877906944), (513940705/549755813888)), (61/137438953472), by norm_num⟩
  | 11 => ⟨((-1322940809/2199023255552), (-152224403/549755813888)), (73/549755813888), by norm_num⟩
  | 12 => ⟨((718378145/4398046511104), (661282401/8796093022208)), (319/8796093022208), by norm_num⟩
  | 13 => ⟨((-720167799/17592186044416), (-82866227/4398046511104)), (161/17592186044416), by norm_num⟩
  | 14 => ⟨((1340786407/140737488355328), (77138905/17592186044416)), (151/70368744177664), by norm_num⟩
  | 15 => ⟨((-1164909747/562949953421312), (-134040533/140737488355328)), (33/70368744177664), by norm_num⟩
  | 16 => ⟨((1853217/4398046511104), (436716997/2251799813685248)), (217/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (280943281153/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888817863435377/316912650057057350374175801344), (332078191231/316912650057057350374175801344)), (184531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944233742011189/19807040628566084398385987584), (746995780687/39614081257132168796771975168)), (207607/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888163299483697/2475880078570760549798248448), (793455662011/2475880078570760549798248448)), (13787/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769829987537671/154742504910672534362390528), (793200028739/154742504910672534362390528)), (220603/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193534779378681/1208925819614629174706176), (185838383063/2417851639229258349412352)), (206827/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673357621399/604462909807314587353088), (325081488113/302231454903657293676544)), (180985/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942990256340705/37778931862957161709568), (1056006304453/75557863725914323419136)), (294123/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40505673958425/147573952589676412928), (197890009813/1180591620717411303424)), (55153/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809791129181385/295147905179352825856), (1087672951963/590295810358705651712)), (303373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821144152599971/73786976294838206464), (1358508942275/73786976294838206464)), (2963/576460752303423488), by norm_num⟩
  | 7 => ⟨((1820037653445857/9223372036854775808), (1526835939277/9223372036854775808)), (426737/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591289317857799/1152921504606846976), (1524979865523/1152921504606846976)), (213409/576460752303423488), by norm_num⟩
  | 5 => ⟨((149028104513265/18014398509481984), (333068080865/36028797018963968)), (373559/144115188075855872), by norm_num⟩
  | 4 => ⟨((186013824550943/4503599627370496), (997122957921/18014398509481984)), (140131/9007199254740992), by norm_num⟩
  | 3 => ⟨((742430773673903/4503599627370496), (2485539849791/9007199254740992)), (350491/4503599627370496), by norm_num⟩
  | 2 => ⟨((277399103836409/562949953421312), (4949344707517/4503599627370496)), (175369/562949953421312), by norm_num⟩
  | 1 => ⟨((550765760084553/562949953421312), (1842478900589/562949953421312)), (2106923/2251799813685248), by norm_num⟩
  | 0 => ⟨((538754544615979/562949953421312), (14524835680617/2251799813685248)), (1055991/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538754544615979/562949953421312), (14524835680617/2251799813685248)), (4028285982372093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1031151248533565/1125899906842624), (13900562892269/1125899906842624)), (2034833/562949953421312), by norm_num⟩
  | 2 => ⟨((1888408845658077/2251799813685248), (50923115614703/2251799813685248)), (7554867/1125899906842624), by norm_num⟩
  | 3 => ⟨((1582509592104381/2251799813685248), (5338155582861/140737488355328)), (26026107/2251799813685248), by norm_num⟩
  | 4 => ⟨((1108909256604343/2251799813685248), (120048787465849/2251799813685248)), (4819419/281474976710656), by norm_num⟩
  | 5 => ⟨((1079374836630699/4503599627370496), (236474327524063/4503599627370496)), (84168959/4503599627370496), by norm_num⟩
  | 6 => ⟨((985105268801325/18014398509481984), (226702602147313/9007199254740992)), (196738019/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1363149725/16777216)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1378939839/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((916224125440199/18014398509481984), (-256134878708571/9007199254740992)), (201848241/18014398509481984), by norm_num⟩
  | 1 => ⟨((-719958603/4294967296), (402535809/4294967296)), (161/4294967296), by norm_num⟩
  | 2 => ⟨((1186433053/4294967296), (-165836545/1073741824)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((-325857483/1073741824), (728760265/4294967296)), (295/4294967296), by norm_num⟩
  | 4 => ⟨((536986553/2147483648), (-600468737/4294967296)), (245/4294967296), by norm_num⟩
  | 5 => ⟨((-707928031/4294967296), (49476175/536870912)), (163/4294967296), by norm_num⟩
  | 6 => ⟨((388869217/4294967296), (-434841071/8589934592)), (181/8589934592), by norm_num⟩
  | 7 => ⟨((-91546393/2147483648), (409475781/17179869184)), (43/4294967296), by norm_num⟩
  | 8 => ⟨((301721977/17179869184), (-674782687/68719476736)), (285/68719476736), by norm_num⟩
  | 9 => ⟨((-883934591/137438953472), (30888523/8589934592)), (105/68719476736), by norm_num⟩
  | 10 => ⟨((1165321685/549755813888), (-325771305/274877906944)), (279/549755813888), by norm_num⟩
  | 11 => ⟨((-174577735/274877906944), (48804049/137438953472)), (169/1099511627776), by norm_num⟩
  | 12 => ⟨((191793245/1099511627776), (-6702091/68719476736)), (187/4398046511104), by norm_num⟩
  | 13 => ⟨((-97249115/2199023255552), (434983357/17592186044416)), (191/17592186044416), by norm_num⟩
  | 14 => ⟨((732610785/70368744177664), (-409609767/70368744177664)), (181/70368744177664), by norm_num⟩
  | 15 => ⟨((-643884169/281474976710656), (360001859/281474976710656)), (5/8796093022208), by norm_num⟩
  | 16 => ⟨((1061068591/2251799813685248), (-593253699/2251799813685248)), (133/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-664084806269/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888792757685923/316912650057057350374175801344), (-784913662821/633825300114114700748351602688)), (184555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888411004680379/39614081257132168796771975168), (-882812618825/39614081257132168796771975168)), (103817/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888103300562063/2475880078570760549798248448), (-468858301607/1237940039285380274899124224)), (13789/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769770000292331/154742504910672534362390528), (-234352748449/38685626227668133590597632)), (220637/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774111004695725/4835703278458516698824704), (-878498236147/9671406556917033397649408)), (206861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628812086295459/302231454903657293676544), (-192090385773/151115727451828646838272)), (181017/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885900610258363/75557863725914323419136), (-623989782789/37778931862957161709568)), (294179/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162015207524207/590295810358705651712), (-935453058203/4722366482869645213696)), (220657/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404874980001517/147573952589676412928), (-642692351701/295147905179352825856)), (303441/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910520639606739/36893488147419103232), (-802718546753/36893488147419103232)), (94839/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819921989010361/9223372036854775808), (-1804339547103/9223372036854775808)), (426853/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591173738547867/1152921504606846976), (-901060361875/576460752303423488)), (213475/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192123799935101/144115188075855872), (-787181551769/72057594037927936)), (186845/72057594037927936), by norm_num⟩
  | 4 => ⟨((743979616749193/18014398509481984), (-2356568697767/36028797018963968)), (280377/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484672678336891/9007199254740992), (-2937023386429/9007199254740992)), (350663/4503599627370496), by norm_num⟩
  | 2 => ⟨((554704023903291/1125899906842624), (-5848065878227/4503599627370496)), (701907/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101250220900049/1125899906842624), (-2176857791521/562949953421312)), (263581/281474976710656), by norm_num⟩
  | 0 => ⟨((2153902977901669/2251799813685248), (-17157892186851/2251799813685248)), (4229153/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153902977901669/2251799813685248), (-17157892186851/2251799813685248)), (16132938393599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060131463177131/2251799813685248), (-32823908103351/2251799813685248)), (1019379/281474976710656), by norm_num⟩
  | 2 => ⟨((1884299044187707/2251799813685248), (-60060015474893/2251799813685248)), (15159535/2251799813685248), by norm_num⟩
  | 3 => ⟨((1575173628184539/2251799813685248), (-25129016590517/562949953421312)), (26179575/2251799813685248), by norm_num⟩
  | 4 => ⟨((548687424235781/1125899906842624), (-140625517401795/2251799813685248)), (19481681/1125899906842624), by norm_num⟩
  | 5 => ⟨((1052008277747395/4503599627370496), (-34265680481933/562949953421312)), (85685517/4503599627370496), by norm_num⟩
  | 6 => ⟨((916224125440199/18014398509481984), (-256134878708571/9007199254740992)), (201848241/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1378939839/16777216)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile032Terms3
