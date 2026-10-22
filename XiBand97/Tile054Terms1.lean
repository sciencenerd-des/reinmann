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
namespace Reinmann.XiBand97.Tile054Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨54,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15489/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15489/512))
  have he : value ((69/80), (15489/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-2230374333/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1190087584221823/9007199254740992), (645348927640683/9007199254740992)), (1893941/562949953421312), by norm_num⟩
  | 1 => ⟨((19950025095/68719476736), (-10818302343/68719476736)), (511/68719476736), by norm_num⟩
  | 2 => ⟨((-2739667841/8589934592), (1485639987/8589934592)), (141/17179869184), by norm_num⟩
  | 3 => ⟨((8026220685/34359738368), (-2176189795/17179869184)), (415/68719476736), by norm_num⟩
  | 4 => ⟨((-2204426169/17179869184), (9563155405/137438953472)), (229/68719476736), by norm_num⟩
  | 5 => ⟨((1937447743/34359738368), (-8404960037/274877906944)), (405/274877906944), by norm_num⟩
  | 6 => ⟨((-11352020795/549755813888), (1538965397/137438953472)), (149/274877906944), by norm_num⟩
  | 7 => ⟨((14253108053/2199023255552), (-1932258625/549755813888)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((-15658639659/8796093022208), (8491212281/8796093022208)), (415/8796093022208), by norm_num⟩
  | 9 => ⟨((15291354625/35184372088832), (-1036505573/4398046511104)), (51/4398046511104), by norm_num⟩
  | 10 => ⟨((-13439416081/140737488355328), (3643896831/70368744177664)), (361/140737488355328), by norm_num⟩
  | 11 => ⟨((21475938413/1125899906842624), (-5822879763/562949953421312)), (579/1125899906842624), by norm_num⟩
  | 12 => ⟨((-7864576617/2251799813685248), (2132362421/1125899906842624)), (213/2251799813685248), by norm_num⟩
  | 13 => ⟨((5316997241/9007199254740992), (-11532994755/36028797018963968)), (579/36028797018963968), by norm_num⟩
  | 14 => ⟨((-1668948145/18014398509481984), (7240165579/144115188075855872)), (183/72057594037927936), by norm_num⟩
  | 15 => ⟨((15646096565/1152921504606846976), (-8484410535/1152921504606846976)), (431/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-4297248489/2305843009213693952), (2330269419/2305843009213693952)), (119/2305843009213693952), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (3445021541499/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55594905047275/19807040628566084398385987584), (4078211749143/633825300114114700748351602688)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945021527981867/19807040628566084398385987584), (4587203677923/39614081257132168796771975168)), (6513/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889836303551479/2475880078570760549798248448), (152279973593/77371252455336267181195264)), (3461/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771501821027765/154742504910672534362390528), (4871896327051/154742504910672534362390528)), (1731/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549844335800973/9671406556917033397649408), (71348026085/151115727451828646838272)), (12987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629521226680479/302231454903657293676544), (3994360455483/604462909807314587353088)), (1421/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944101482578521/37778931862957161709568), (6488719135823/75557863725914323419136)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297846370402605/4722366482869645213696), (1216171900987/1180591620717411303424)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621868058352153/590295810358705651712), (6685936892375/590295810358705651712)), (19081/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823996449672411/73786976294838206464), (8352909195039/73786976294838206464)), (23869/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455809921297849/2305843009213693952), (4695410229049/4611686018427387904)), (26877/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24913794659563/18014398509481984), (9383069736011/1152921504606846976)), (6727/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195009647152311/144115188075855872), (8201469572435/144115188075855872)), (23579/144115188075855872), by norm_num⟩
  | 4 => ⟨((11658349840095/281474976710656), (6142389638173/18014398509481984)), (35437/36028797018963968), by norm_num⟩
  | 3 => ⟨((745013028892995/4503599627370496), (15325497834533/9007199254740992)), (22209/4503599627370496), by norm_num⟩
  | 2 => ⟨((278677819472289/562949953421312), (15279818855835/2251799813685248)), (5575/281474976710656), by norm_num⟩
  | 1 => ⟨((1109080322157075/1125899906842624), (11402827718753/562949953421312)), (67357/1125899906842624), by norm_num⟩
  | 0 => ⟨((273029120512569/281474976710656), (45155772317885/1125899906842624)), (34137/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((273029120512569/281474976710656), (45155772317885/1125899906842624)), (130222321630382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1057535718189447/1125899906842624), (43800841361083/562949953421312)), (275855/1125899906842624), by norm_num⟩
  | 2 => ⟨((986506645644449/1125899906842624), (164565087694139/1125899906842624)), (280569/562949953421312), by norm_num⟩
  | 3 => ⟨((420158882713687/562949953421312), (72095464110391/281474976710656)), (143421/140737488355328), by norm_num⟩
  | 4 => ⟨((1106616756928553/2251799813685248), (430468811165193/1125899906842624)), (4600885/2251799813685248), by norm_num⟩
  | 5 => ⟨((53666744067723/562949953421312), (1692384898072829/4503599627370496)), (2010057/562949953421312), by norm_num⟩
  | 6 => ⟨((-1190087584221823/9007199254740992), (645348927640683/9007199254740992)), (1893941/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-2230374333/33554432)), (1/134217728), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-9349297735/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1058608934106519/9007199254740992), (-638392371427899/9007199254740992)), (7501049/4503599627370496), by norm_num⟩
  | 1 => ⟨((-18596932609/68719476736), (2803712383/17179869184)), (133/34359738368), by norm_num⟩
  | 2 => ⟨((5352627475/17179869184), (-3227893169/17179869184)), (309/68719476736), by norm_num⟩
  | 3 => ⟨((-16433173643/68719476736), (9909998257/68719476736)), (239/68719476736), by norm_num⟩
  | 4 => ⟨((9459695165/68719476736), (-11409307129/137438953472)), (277/137438953472), by norm_num⟩
  | 5 => ⟨((-17425402457/274877906944), (5254180103/137438953472)), (129/137438953472), by norm_num⟩
  | 6 => ⟨((13374490645/549755813888), (-8065464521/549755813888)), (25/68719476736), by norm_num⟩
  | 7 => ⟨((-8798829367/1099511627776), (10612239071/2199023255552)), (133/1099511627776), by norm_num⟩
  | 8 => ⟨((2532506667/1099511627776), (-47725749/34359738368)), (309/8796093022208), by norm_num⟩
  | 9 => ⟨((-20733554131/35184372088832), (12503335617/35184372088832)), (319/35184372088832), by norm_num⟩
  | 10 => ⟨((9548154533/70368744177664), (-5757998841/70368744177664)), (297/140737488355328), by norm_num⟩
  | 11 => ⟨((-3997352417/140737488355328), (9642387125/562949953421312)), (251/562949953421312), by norm_num⟩
  | 12 => ⟨((12272325449/2251799813685248), (-3700402809/1125899906842624)), (97/1125899906842624), by norm_num⟩
  | 13 => ⟨((-17389583775/18014398509481984), (5243379905/9007199254740992)), (277/18014398509481984), by norm_num⟩
  | 14 => ⟨((5720142339/36028797018963968), (-6899044803/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | 15 => ⟨((-7024594389/288230376151711744), (8472340117/576460752303423488)), (57/144115188075855872), by norm_num⟩
  | 16 => ⟨((4043681581/1152921504606846976), (-2438535507/1152921504606846976)), (265/4611686018427387904), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-176718132309/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778905365368873/633825300114114700748351602688), (-836669264301/633825300114114700748351602688)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889895522529139/39614081257132168796771975168), (-941089333807/39614081257132168796771975168)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944840104596093/1237940039285380274899124224), (-124963109075/309485009821345068724781056)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771346468582963/154742504910672534362390528), (-249869272165/38685626227668133590597632)), (13791/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774849740360489/4835703278458516698824704), (-936767821859/9671406556917033397649408)), (12931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629458246250057/302231454903657293676544), (-409714988009/302231454903657293676544)), (11315/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887999753941551/75557863725914323419136), (-665560189819/37778931862957161709568)), (18389/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297695251708751/4722366482869645213696), (-498971895501/2361183241434822606848)), (13793/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621662363938533/590295810358705651712), (-1371528731241/590295810358705651712)), (2371/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823742468841359/73786976294838206464), (-1713445503263/73786976294838206464)), (23713/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911479132351949/4611686018427387904), (-3762304029/18014398509481984)), (13341/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797103407070187/576460752303423488), (-240580358585/144115188075855872)), (417/18014398509481984), by norm_num⟩
  | 5 => ⟨((74673384084691/9007199254740992), (-1682200493555/144115188075855872)), (365/2251799813685248), by norm_num⟩
  | 4 => ⟨((745963785571365/18014398509481984), (-157473837155/2251799813685248)), (35053/36028797018963968), by norm_num⟩
  | 3 => ⟨((744810279583559/4503599627370496), (-3142978420337/9007199254740992)), (43841/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228674331903883/4503599627370496), (-1566625983365/1125899906842624)), (87757/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217194326018033/2251799813685248), (-9351270536627/2251799813685248)), (131825/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091459458901645/1125899906842624), (-9254739288227/1125899906842624)), (132207/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091459458901645/1125899906842624), (-9254739288227/1125899906842624)), (504329685691451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528998223104517/562949953421312), (-17943287275209/1125899906842624)), (516999/2251799813685248), by norm_num⟩
  | 2 => ⟨((496951155174543/562949953421312), (-67444482604909/2251799813685248)), (988117/2251799813685248), by norm_num⟩
  | 3 => ⟨((1752739487697123/2251799813685248), (-119074931392969/2251799813685248)), (1803737/2251799813685248), by norm_num⟩
  | 4 => ⟨((339496971917989/562949953421312), (-185369350311577/2251799813685248)), (2998723/2251799813685248), by norm_num⟩
  | 5 => ⟨((1607398043138635/4503599627370496), (-111790280352127/1125899906842624)), (1027645/562949953421312), by norm_num⟩
  | 6 => ⟨((1058608934106519/9007199254740992), (-638392371427899/9007199254740992)), (7501049/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-9349297735/134217728)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-19472580545/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1067296307197/8796093022208), (319465917776881/9007199254740992)), (12372501/4503599627370496), by norm_num⟩
  | 1 => ⟨((19994256013/68719476736), (-5844465745/68719476736)), (455/68719476736), by norm_num⟩
  | 2 => ⟨((-23972065989/68719476736), (7007208391/68719476736)), (137/17179869184), by norm_num⟩
  | 3 => ⟨((4790208643/17179869184), (-5600850625/68719476736)), (441/68719476736), by norm_num⟩
  | 4 => ⟨((-11486418661/68719476736), (6715126619/137438953472)), (531/137438953472), by norm_num⟩
  | 5 => ⟨((22034583207/274877906944), (-3220434075/137438953472)), (1/536870912), by norm_num⟩
  | 6 => ⟨((-17612207637/549755813888), (5148175763/549755813888)), (411/549755813888), by norm_num⟩
  | 7 => ⟨((24132702535/2199023255552), (-7054163615/2199023255552)), (283/1099511627776), by norm_num⟩
  | 8 => ⟨((-3616730833/1099511627776), (4228786397/4398046511104)), (341/4398046511104), by norm_num⟩
  | 9 => ⟨((15417852031/17592186044416), (-2253374869/8796093022208)), (365/17592186044416), by norm_num⟩
  | 10 => ⟨((-14788157801/70368744177664), (4322685557/70368744177664)), (11/2199023255552), by norm_num⟩
  | 11 => ⟨((12894710431/281474976710656), (-7538434373/562949953421312)), (77/70368744177664), by norm_num⟩
  | 12 => ⟨((-10306721729/1125899906842624), (1506364679/562949953421312)), (247/1125899906842624), by norm_num⟩
  | 13 => ⟨((15208885731/9007199254740992), (-277854211/562949953421312)), (183/4503599627370496), by norm_num⟩
  | 14 => ⟨((-20839608685/72057594037927936), (6091568449/72057594037927936)), (63/9007199254740992), by norm_num⟩
  | 15 => ⟨((3331413277/72057594037927936), (-1947592425/144115188075855872)), (81/72057594037927936), by norm_num⟩
  | 16 => ⟨((-15976760297/2305843009213693952), (4670122669/2305843009213693952)), (391/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1860916407153/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444692155035125/158456325028528675187087900672), (4404642409205/633825300114114700748351602688)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889741144490009/39614081257132168796771975168), (4954299652281/39614081257132168796771975168)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472378869579703/618970019642690137449562112), (5262829754329/2475880078570760549798248448)), (13849/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885590473046607/77371252455336267181195264), (328848559323/9671406556917033397649408)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549543462842507/9671406556917033397649408), (2465698720615/4835703278458516698824704)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314694784232115/151115727451828646838272), (4313641988479/604462909807314587353088)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887774977581791/75557863725914323419136), (3503586703539/37778931862957161709568)), (18491/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297525293886117/4722366482869645213696), (5253197458979/4722366482869645213696)), (3469/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621426439111237/590295810358705651712), (1804900122701/147573952589676412928)), (4773/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911722108932025/36893488147419103232), (9019182823927/73786976294838206464)), (5971/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822618140021433/9223372036854775808), (5069635361925/4611686018427387904)), (26897/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398465239869671/288230376151711744), (10130136299841/1152921504606846976)), (13465/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194465090636011/144115188075855872), (8853597193775/144115188075855872)), (11801/72057594037927936), by norm_num⟩
  | 4 => ⟨((745725580541223/18014398509481984), (13259862078291/36028797018963968)), (8869/9007199254740992), by norm_num⟩
  | 3 => ⟨((744501339025975/4503599627370496), (8269458567911/4503599627370496)), (44477/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113685892587865/2251799813685248), (16485098708317/2251799813685248)), (22337/1125899906842624), by norm_num⟩
  | 1 => ⟨((69221083310843/70368744177664), (24593268302945/1125899906842624)), (67505/1125899906842624), by norm_num⟩
  | 0 => ⟨((544505736015695/562949953421312), (12162505606059/281474976710656)), (136993/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544505736015695/562949953421312), (12162505606059/281474976710656)), (522586826804732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051229469281353/1125899906842624), (23528038421795/281474976710656)), (276849/1125899906842624), by norm_num⟩
  | 2 => ⟨((243411135606201/281474976710656), (175741144967211/1125899906842624)), (140815/281474976710656), by norm_num⟩
  | 3 => ⟨((12727301781357/17592186044416), (607902729672145/2251799813685248)), (1150019/1125899906842624), by norm_num⟩
  | 4 => ⟨((507239490028563/1125899906842624), (879590685854973/2251799813685248)), (2284919/1125899906842624), by norm_num⟩
  | 5 => ⟨((113459386923387/2251799813685248), (396272464555159/1125899906842624)), (3843855/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1067296307197/8796093022208), (319465917776881/9007199254740992)), (12372501/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-19472580545/268435456)), (1/134217728), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-20179173559/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1029708712222937/9007199254740992), (117807245682041/4503599627370496)), (10032463/9007199254740992), by norm_num⟩
  | 1 => ⟨((-9760780435/34359738368), (-4466858035/68719476736)), (3/1073741824), by norm_num⟩
  | 2 => ⟨((12127314105/34359738368), (5549862617/68719476736)), (241/68719476736), by norm_num⟩
  | 3 => ⟨((-20090162309/68719476736), (-4596963507/68719476736)), (101/34359738368), by norm_num⟩
  | 4 => ⟨((24961088959/137438953472), (2855756297/68719476736)), (127/68719476736), by norm_num⟩
  | 5 => ⟨((-3101298797/34359738368), (-2838515125/137438953472)), (255/274877906944), by norm_num⟩
  | 6 => ⟨((20550501343/549755813888), (1175574185/137438953472)), (213/549755813888), by norm_num⟩
  | 7 => ⟨((-14590307841/1099511627776), (-834626317/274877906944)), (153/1099511627776), by norm_num⟩
  | 8 => ⟨((2265972061/549755813888), (2073968485/2199023255552)), (3/68719476736), by norm_num⟩
  | 9 => ⟨((-20020369929/17592186044416), (-4580993849/17592186044416)), (107/8796093022208), by norm_num⟩
  | 10 => ⟨((19899500147/70368744177664), (4553336831/70368744177664)), (215/70368744177664), by norm_num⟩
  | 11 => ⟨((-4495309113/70368744177664), (-4114406171/281474976710656)), (49/70368744177664), by norm_num⟩
  | 12 => ⟨((7446949005/562949953421312), (3407971751/1125899906842624)), (165/1125899906842624), by norm_num⟩
  | 13 => ⟨((-2846918939/1125899906842624), (-5211379487/9007199254740992)), (127/4503599627370496), by norm_num⟩
  | 14 => ⟨((16169892121/36028797018963968), (3699940441/36028797018963968)), (91/18014398509481984), by norm_num⟩
  | 15 => ⟨((-10714845989/144115188075855872), (-2451735095/144115188075855872)), (61/72057594037927936), by norm_num⟩
  | 16 => ⟨((13312696025/1152921504606846976), (6092332841/2305843009213693952)), (153/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (293014930223/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889331627802685/316912650057057350374175801344), (346728669151/633825300114114700748351602688)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944811607892481/19807040628566084398385987584), (389996929411/39614081257132168796771975168)), (3243/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889390967085187/2475880078570760549798248448), (207140586333/1237940039285380274899124224)), (13783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885528660357379/77371252455336267181195264), (414179327193/154742504910672534362390528)), (13783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387357126170985/2417851639229258349412352), (388184943751/9671406556917033397649408)), (6461/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258679488512867/604462909807314587353088), (339553690039/604462909807314587353088)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943807404976489/37778931862957161709568), (551572076223/75557863725914323419136)), (9187/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162175838459721/590295810358705651712), (413501805227/4722366482869645213696)), (6891/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101329117634729/36893488147419103232), (568277105923/590295810358705651712)), (9475/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911623632847305/36893488147419103232), (354957422289/36893488147419103232)), (23689/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455600427350407/2305843009213693952), (399030642369/4611686018427387904)), (26653/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593650943386551/1152921504606846976), (398660406773/576460752303423488)), (26655/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194288527533987/144115188075855872), (174205901577/36028797018963968)), (23327/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491200680020505/36028797018963968), (1043573506947/36028797018963968)), (34995/36028797018963968), by norm_num⟩
  | 3 => ⟨((186089328351639/1125899906842624), (650781870459/4503599627370496)), (43755/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113435244409879/2251799813685248), (324304845229/562949953421312)), (87541/4503599627370496), by norm_num⟩
  | 1 => ⟨((69203391721533/70368744177664), (1935004324987/1125899906842624)), (131393/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177626750283183/2251799813685248), (7653851801147/2251799813685248)), (65779/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177626750283183/2251799813685248), (7653851801147/2251799813685248)), (250926973583030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((263233861491713/281474976710656), (14803476155905/2251799813685248)), (15959/70368744177664), by norm_num⟩
  | 2 => ⟨((246162705252315/281474976710656), (27688260161223/2251799813685248)), (961901/2251799813685248), by norm_num⟩
  | 3 => ⟨((1721903649667881/2251799813685248), (48429292753955/2251799813685248)), (1706109/2251799813685248), by norm_num⟩
  | 4 => ⟨((41114428283347/70368744177664), (74065709959709/2251799813685248)), (1341319/1125899906842624), by norm_num⟩
  | 5 => ⟨((766267046609423/2251799813685248), (173097835181217/4503599627370496)), (1655625/1125899906842624), by norm_num⟩
  | 6 => ⟨((1029708712222937/9007199254740992), (117807245682041/4503599627370496)), (10032463/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-20179173559/268435456)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-20829176121/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-288693759077925/4503599627370496), (-199771174255615/2251799813685248)), (1394635/562949953421312), by norm_num⟩
  | 1 => ⟨((11298902463/68719476736), (15637296907/68719476736)), (439/68719476736), by norm_num⟩
  | 2 => ⟨((-7245278153/34359738368), (-10027218663/34359738368)), (283/34359738368), by norm_num⟩
  | 3 => ⟨((12389181029/68719476736), (8573102689/34359738368)), (487/68719476736), by norm_num⟩
  | 4 => ⟨((-993050685/8589934592), (-10994787117/68719476736)), (157/34359738368), by norm_num⟩
  | 5 => ⟨((2037699773/34359738368), (2820107215/34359738368)), (81/34359738368), by norm_num⟩
  | 6 => ⟨((-6968795631/274877906944), (-2411144063/68719476736)), (139/137438953472), by norm_num⟩
  | 7 => ⟨((10214061643/1099511627776), (14135914091/1099511627776)), (205/549755813888), by norm_num⟩
  | 8 => ⟨((-409352357/137438953472), (-9064475941/2199023255552)), (33/274877906944), by norm_num⟩
  | 9 => ⟨((3733219787/4398046511104), (10333298551/8796093022208)), (303/8796093022208), by norm_num⟩
  | 10 => ⟨((-7660415755/35184372088832), (-10601754991/35184372088832)), (313/35184372088832), by norm_num⟩
  | 11 => ⟨((7144937625/140737488355328), (19776701565/281474976710656)), (293/140737488355328), by norm_num⟩
  | 12 => ⟨((-12217602113/1125899906842624), (-8454372995/562949953421312)), (63/140737488355328), by norm_num⟩
  | 13 => ⟨((9642317135/4503599627370496), (13344639127/4503599627370496)), (25/281474976710656), by norm_num⟩
  | 14 => ⟨((-14132602937/36028797018963968), (-19559042031/36028797018963968)), (589/36028797018963968), by norm_num⟩
  | 15 => ⟨((9666509553/144115188075855872), (6689060305/72057594037927936)), (405/144115188075855872), by norm_num⟩
  | 16 => ⟨((-12397053733/1152921504606846976), (-17157100931/1152921504606846976)), (521/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-2861191756125/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889275387713401/316912650057057350374175801344), (-1692651232821/316912650057057350374175801344)), (11567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118093522380237/2475880078570760549798248448), (-237982468791/2475880078570760549798248448)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236156970383745/309485009821345068724781056), (-252799236415/154742504910672534362390528)), (1729/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770921647206529/154742504910672534362390528), (-126367485435/4835703278458516698824704)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387325203071033/2417851639229258349412352), (-1894966149245/4835703278458516698824704)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629283629785777/302231454903657293676544), (-3315098777299/604462909807314587353088)), (11357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943715752419683/37778931862957161709568), (-168280894993/2361183241434822606848)), (9231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297268413231085/4722366482869645213696), (-4036951062095/4722366482869645213696)), (13853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405268600872769/147573952589676412928), (-2773949699921/295147905179352825856)), (19057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823005934405423/73786976294838206464), (-3465256870475/36893488147419103232)), (5959/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455531872396283/2305843009213693952), (-1947708859717/2305843009213693952)), (26835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593373327594935/1152921504606846976), (-972918694881/144115188075855872)), (26861/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194041802403525/144115188075855872), (-6802015807603/144115188075855872)), (5883/36028797018963968), by norm_num⟩
  | 4 => ⟨((372705748140203/9007199254740992), (-5093104996543/18014398509481984)), (35355/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488229269240037/9007199254740992), (-3175843842601/2251799813685248)), (44295/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225860233782715/4503599627370496), (-12659368455393/2251799813685248)), (22223/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106447508775961/1125899906842624), (-18879293550611/1125899906842624)), (134099/2251799813685248), by norm_num⟩
  | 0 => ⟨((543502861457801/562949953421312), (-74642198537033/2251799813685248)), (135625/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543502861457801/562949953421312), (-74642198537033/2251799813685248)), (517368320945357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096436050892443/2251799813685248), (-72063685668373/1125899906842624)), (541743/2251799813685248), by norm_num⟩
  | 2 => ⟨((971283368470091/1125899906842624), (-268366499858811/2251799813685248)), (16845/35184372088832), by norm_num⟩
  | 3 => ⟨((1643816171723581/2251799813685248), (-463025028038889/2251799813685248)), (1058515/1125899906842624), by norm_num⟩
  | 4 => ⟨((1104778237705853/2251799813685248), (-169004372497359/562949953421312)), (3961495/2251799813685248), by norm_num⟩
  | 5 => ⟨((678155583010949/4503599627370496), (-1326671059673969/4503599627370496)), (1566439/562949953421312), by norm_num⟩
  | 6 => ⟨((-288693759077925/4503599627370496), (-199771174255615/2251799813685248)), (1394635/562949953421312), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-20829176121/268435456)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-1339436531/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-250217071661507/9007199254740992), (890321363647649/9007199254740992)), (9984087/4503599627370496), by norm_num⟩
  | 1 => ⟨((5037972999/68719476736), (-8963047487/34359738368)), (101/17179869184), by norm_num⟩
  | 2 => ⟨((-6647749785/68719476736), (11826998083/34359738368)), (67/8589934592), by norm_num⟩
  | 3 => ⟨((1461982733/17179869184), (-10404041993/34359738368)), (237/34359738368), by norm_num⟩
  | 4 => ⟨((-3858256247/68719476736), (1716053955/8589934592)), (315/68719476736), by norm_num⟩
  | 5 => ⟨((4072863771/137438953472), (-7246023629/68719476736)), (335/137438953472), by norm_num⟩
  | 6 => ⟨((-3582840329/274877906944), (6374223923/137438953472)), (37/34359738368), by norm_num⟩
  | 7 => ⟨((5403040589/1099511627776), (-4806269247/274877906944)), (7/17179869184), by norm_num⟩
  | 8 => ⟨((-3564733467/2199023255552), (25368040169/4398046511104)), (297/2199023255552), by norm_num⟩
  | 9 => ⟨((65330111/137438953472), (-7438634705/4398046511104)), (175/4398046511104), by norm_num⟩
  | 10 => ⟨((-1103423413/8796093022208), (245387293/549755813888)), (371/35184372088832), by norm_num⟩
  | 11 => ⟨((4235632939/140737488355328), (-7535605925/70368744177664)), (179/70368744177664), by norm_num⟩
  | 12 => ⟨((-3726026051/562949953421312), (26515861399/1125899906842624)), (79/140737488355328), by norm_num⟩
  | 13 => ⟨((94549965/70368744177664), (-21531347193/4503599627370496)), (515/4503599627370496), by norm_num⟩
  | 14 => ⟨((-4562702229/18014398509481984), (16234988465/18014398509481984)), (195/9007199254740992), by norm_num⟩
  | 15 => ⟨((3210995403/72057594037927936), (-2856337687/18014398509481984)), (551/144115188075855872), by norm_num⟩
  | 16 => ⟨((-4237000477/576460752303423488), (7538038909/288230376151711744)), (183/288230376151711744), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (2403019368659/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778454076745643/633825300114114700748351602688), (2842902450829/633825300114114700748351602688)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889387695781117/39614081257132168796771975168), (3197625387583/39614081257132168796771975168)), (813/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944570234590769/1237940039285380274899124224), (424585941641/309485009821345068724781056)), (27/4835703278458516698824704), by norm_num⟩
  | 14 => ⟨((442701633244225/38685626227668133590597632), (424474957881/19342813113834066795298816)), (13827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549193083469759/9671406556917033397649408), (3182619079459/9671406556917033397649408)), (12965/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314618296877355/151115727451828646838272), (1391924439617/302231454903657293676544)), (2837/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887278994941481/75557863725914323419136), (2260993632419/37778931862957161709568)), (9223/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81072146443375/295147905179352825856), (1694972397407/2361183241434822606848)), (865/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101307379001169/36893488147419103232), (2329331778759/295147905179352825856)), (9519/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227851408705143/9223372036854775808), (5819565659433/73786976294838206464)), (11905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821909534724983/9223372036854775808), (6541839433249/9223372036854775808)), (26803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398289168589943/288230376151711744), (6535379425465/1152921504606846976)), (3353/144115188075855872), by norm_num⟩
  | 5 => ⟨((596926846116229/72057594037927936), (2855598117739/72057594037927936)), (23495/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490543742836331/36028797018963968), (4276144843631/18014398509481984)), (35291/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487885292893265/9007199254740992), (5332508423295/4503599627370496)), (22099/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112593736573101/2251799813685248), (10627074691703/2251799813685248)), (88651/4503599627370496), by norm_num⟩
  | 1 => ⟨((552980907121693/562949953421312), (31692042868641/2251799813685248)), (133615/2251799813685248), by norm_num⟩
  | 0 => ⟨((543054577515491/562949953421312), (7828816685047/281474976710656)), (67449/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543054577515491/562949953421312), (7828816685047/281474976710656)), (257297518016624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2093707342096537/2251799813685248), (60417089817753/1125899906842624)), (535531/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940229992394631/2251799813685248), (224701509913557/2251799813685248)), (1053341/2251799813685248), by norm_num⟩
  | 3 => ⟨((1649348060275385/2251799813685248), (96805365694817/562949953421312)), (2025413/2251799813685248), by norm_num⟩
  | 4 => ⟨((1141490707600061/2251799813685248), (567246666111727/2251799813685248)), (3663643/2251799813685248), by norm_num⟩
  | 5 => ⟨((54469332118191/281474976710656), (1150203129689321/4503599627370496)), (11120357/4503599627370496), by norm_num⟩
  | 6 => ⟨((-250217071661507/9007199254740992), (890321363647649/9007199254740992)), (9984087/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-1339436531/16777216)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-21991254689/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((845911958940143/9007199254740992), (-418321403315291/18014398509481984)), (16852975/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8738601877/34359738368), (270088997/4294967296)), (11/4294967296), by norm_num⟩
  | 2 => ⟨((11832286285/34359738368), (-5851316501/68719476736)), (15/4294967296), by norm_num⟩
  | 3 => ⟨((-21361616835/68719476736), (1320471569/17179869184)), (219/68719476736), by norm_num⟩
  | 4 => ⟨((14462082691/68719476736), (-1787951649/34359738368)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((-1958202297/17179869184), (1936745129/68719476736)), (41/34359738368), by norm_num⟩
  | 6 => ⟨((441909177/8589934592), (-3496535357/274877906944)), (75/137438953472), by norm_num⟩
  | 7 => ⟨((-21882738023/1099511627776), (5410739015/1099511627776)), (117/549755813888), by norm_num⟩
  | 8 => ⟨((3703722069/549755813888), (-3663138219/2199023255552)), (5/68719476736), by norm_num⟩
  | 9 => ⟨((-17830871633/8796093022208), (4408872085/8796093022208)), (195/8796093022208), by norm_num⟩
  | 10 => ⟨((4828689551/8796093022208), (-4775778775/35184372088832)), (107/17592186044416), by norm_num⟩
  | 11 => ⟨((-19020121759/140737488355328), (2351463395/70368744177664)), (213/140737488355328), by norm_num⟩
  | 12 => ⟨((17169148185/562949953421312), (-2122626973/281474976710656)), (195/562949953421312), by norm_num⟩
  | 13 => ⟨((-1788265969/281474976710656), (3537341785/2251799813685248)), (41/562949953421312), by norm_num⟩
  | 14 => ⟨((5534530305/4503599627370496), (-2736942609/9007199254740992)), (1/70368744177664), by norm_num⟩
  | 15 => ⟨((-999185727/4503599627370496), (3952948257/72057594037927936)), (187/72057594037927936), by norm_num⟩
  | 16 => ⟨((21646760871/576460752303423488), (-5352391161/576460752303423488)), (255/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-78937859155/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55573957273295/19807040628566084398385987584), (-46689300525/79228162514264337593543950336)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118080598716365/2475880078570760549798248448), (-420118588671/39614081257132168796771975168)), (3243/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889036558680363/2475880078570760549798248448), (-111567423197/618970019642690137449562112)), (13783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442675750621357/38685626227668133590597632), (-13942192155/4835703278458516698824704)), (1723/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774548213561631/4835703278458516698824704), (-104534698627/2417851639229258349412352)), (6461/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258389016390417/604462909807314587353088), (-365744525895/604462909807314587353088)), (2827/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887142972195557/75557863725914323419136), (-594096988879/75557863725914323419136)), (18375/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297052986294269/4722366482869645213696), (-445364717101/4722366482869645213696)), (6891/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810389885064055/295147905179352825856), (-612038648353/590295810358705651712)), (18951/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822640007720615/73786976294838206464), (-764541907637/73786976294838206464)), (23691/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910859534552657/4611686018427387904), (-859413916519/9223372036854775808)), (13327/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796484479316637/576460752303423488), (-858545115181/1152921504606846976)), (26657/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596846263759733/72057594037927936), (-750250756343/144115188075855872)), (729/4503599627370496), by norm_num⟩
  | 4 => ⟨((5821516215575/140737488355328), (-1123426646911/36028797018963968)), (34999/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487601535631819/9007199254740992), (-1400878335031/9007199254740992)), (2735/562949953421312), by norm_num⟩
  | 2 => ⟨((2224651997195705/4503599627370496), (-1395784107383/2251799813685248)), (43777/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105599979355053/1125899906842624), (-2080986786991/1125899906842624)), (131419/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171085848291403/2251799813685248), (-4111492293221/1125899906842624)), (263197/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2171085848291403/2251799813685248), (-4111492293221/1125899906842624)), (1004016884810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093234982314703/2251799813685248), (-7928238273155/1125899906842624)), (509449/2251799813685248), by norm_num⟩
  | 2 => ⟨((1945724143287451/2251799813685248), (-14739912136625/1125899906842624)), (477163/1125899906842624), by norm_num⟩
  | 3 => ⟨((1680865838397107/2251799813685248), (-1592048876851/70368744177664)), (1674207/2251799813685248), by norm_num⟩
  | 4 => ⟨((626768529564247/1125899906842624), (-19014269768699/562949953421312)), (2575195/2251799813685248), by norm_num⟩
  | 5 => ⟨((1390505914261485/4503599627370496), (-42339628349685/1125899906842624)), (6082183/4503599627370496), by norm_num⟩
  | 6 => ⟨((845911958940143/9007199254740992), (-418321403315291/18014398509481984)), (16852975/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-21991254689/268435456)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile054Terms1
