/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile064Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨64,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (16205/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (16205/512))
  have he : value ((69/80), (16205/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-37335622511/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1231699679944717/9007199254740992), (-280935752496207/4503599627370496)), (3772965/9007199254740992), by norm_num⟩
  | 1 => ⟨((-41295178355/137438953472), (37675716555/274877906944)), (255/274877906944), by norm_num⟩
  | 2 => ⟨((90734780807/274877906944), (-5173875649/34359738368)), (283/274877906944), by norm_num⟩
  | 3 => ⟨((-66454896803/274877906944), (236836807/2147483648)), (209/274877906944), by norm_num⟩
  | 4 => ⟨((36504083135/274877906944), (-16652276901/274877906944)), (29/68719476736), by norm_num⟩
  | 5 => ⟨((-32083067455/549755813888), (7317758415/274877906944)), (103/549755813888), by norm_num⟩
  | 6 => ⟨((93991605771/4398046511104), (-10719172427/1099511627776)), (19/274877906944), by norm_num⟩
  | 7 => ⟨((-59005904647/8796093022208), (26917061835/8796093022208)), (193/8796093022208), by norm_num⟩
  | 8 => ⟨((64824611949/35184372088832), (-29571414907/35184372088832)), (107/17592186044416), by norm_num⟩
  | 9 => ⟨((-63304102485/140737488355328), (28877795387/140737488355328)), (211/140737488355328), by norm_num⟩
  | 10 => ⟨((27818665965/281474976710656), (-25380400705/562949953421312)), (47/140737488355328), by norm_num⟩
  | 11 => ⟨((-44453713867/2251799813685248), (40557411063/4503599627370496)), (303/4503599627370496), by norm_num⟩
  | 12 => ⟨((32558264221/9007199254740992), (-29704580127/18014398509481984)), (7/562949953421312), by norm_num⟩
  | 13 => ⟨((-88046545651/144115188075855872), (40164697547/144115188075855872)), (153/72057594037927936), by norm_num⟩
  | 14 => ⟨((55273724015/576460752303423488), (-12607265799/288230376151711744)), (97/288230376151711744), by norm_num⟩
  | 15 => ⟨((-64772685273/4611686018427387904), (14773863609/2305843009213693952)), (115/2305843009213693952), by norm_num⟩
  | 16 => ⟨((71160068011/36893488147419103232), (-1014421757/1152921504606846976)), (255/36893488147419103232), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (-557488848483/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045626029023/633825300114114700748351602688), (-329977264947/316912650057057350374175801344)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945026648485461/19807040628566084398385987584), (-742325509679/39614081257132168796771975168)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472461955449223/618970019642690137449562112), (-197142098937/618970019642690137449562112)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771514055608207/154742504910672534362390528), (-394198468387/77371252455336267181195264)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((378382950777/2361183241434822606848), (-738940004967/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((39345434852611/18889465931478580854784), (-646390439485/604462909807314587353088)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888223015028663/75557863725914323419136), (-525021608299/37778931862957161709568)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297862652963775/4722366482869645213696), (-393616972413/2361183241434822606848)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810946234134969/295147905179352825856), (-1081961896633/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912014995346343/36893488147419103232), (-1351725610987/73786976294838206464)), (5927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823281577558853/9223372036854775808), (-23745198089/144115188075855872)), (1667/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594529940529975/1152921504606846976), (-1518445373743/1152921504606846976)), (3335/576460752303423488), by norm_num⟩
  | 5 => ⟨((597528335633931/72057594037927936), (-331809461073/36028797018963968)), (5837/144115188075855872), by norm_num⟩
  | 4 => ⟨((746175470447209/18014398509481984), (-994028222741/18014398509481984)), (8759/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490149038438327/9007199254740992), (-1240088811567/4503599627370496)), (10953/9007199254740992), by norm_num⟩
  | 2 => ⟨((139358068365089/281474976710656), (-2472853454269/2251799813685248)), (21921/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109385492472001/1125899906842624), (-3691022961523/1125899906842624)), (16459/1125899906842624), by norm_num⟩
  | 0 => ⟨((2186050344970235/2251799813685248), (-14618670778321/2251799813685248)), (32993/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2186050344970235/2251799813685248), (-14618670778321/2251799813685248)), (125858311179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132632860394809/140737488355328), (-28383651249757/2251799813685248)), (8061/140737488355328), by norm_num⟩
  | 2 => ⟨((1999561465918735/2251799813685248), (-53498252636131/2251799813685248)), (123175/1125899906842624), by norm_num⟩
  | 3 => ⟨((1774306920477625/2251799813685248), (-47505574791803/1125899906842624)), (7019/35184372088832), by norm_num⟩
  | 4 => ⟨((1394057282726277/2251799813685248), (-149728176727073/2251799813685248)), (745829/2251799813685248), by norm_num⟩
  | 5 => ⟨((1706170476559661/4503599627370496), (-370778350592543/4503599627370496)), (1022649/2251799813685248), by norm_num⟩
  | 6 => ⟨((1231699679944717/9007199254740992), (-280935752496207/4503599627370496)), (3772965/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-37335622511/536870912)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-19562963367/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-502668928462393/4503599627370496), (719370202817169/9007199254740992)), (3497869/4503599627370496), by norm_num⟩
  | 1 => ⟨((70644408043/274877906944), (-25274827657/137438953472)), (495/274877906944), by norm_num⟩
  | 2 => ⟨((-5083273777/17179869184), (29098720695/137438953472)), (287/137438953472), by norm_num⟩
  | 3 => ⟨((7803113615/34359738368), (-22334093499/137438953472)), (443/274877906944), by norm_num⟩
  | 4 => ⟨((-71869332355/549755813888), (12856537689/137438953472)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((66194101329/1099511627776), (-2960327203/68719476736)), (237/549755813888), by norm_num⟩
  | 6 => ⟨((-50805850321/2199023255552), (284016887/17179869184)), (183/1099511627776), by norm_num⟩
  | 7 => ⟨((66848453477/8796093022208), (-47833457383/8796093022208)), (121/2199023255552), by norm_num⟩
  | 8 => ⟨((-76962126233/35184372088832), (27535151479/17592186044416)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((78760819817/140737488355328), (-56357359403/140737488355328)), (9/2199023255552), by norm_num⟩
  | 10 => ⟨((-72541395849/562949953421312), (51907046257/562949953421312)), (533/562949953421312), by norm_num⟩
  | 11 => ⟨((7592397123/281474976710656), (-43461960339/2251799813685248)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((-46619041161/9007199254740992), (33358287329/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 13 => ⟨((66058036447/72057594037927936), (-47267873927/72057594037927936)), (123/18014398509481984), by norm_num⟩
  | 14 => ⟨((-43458357141/288230376151711744), (1943541105/18014398509481984)), (163/144115188075855872), by norm_num⟩
  | 15 => ⟨((53368834837/2305843009213693952), (-4773513361/288230376151711744)), (403/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-61443141763/18446744073709551616), (43965682825/18446744073709551616)), (233/9223372036854775808), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (205202533797/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889448829248081/316912650057057350374175801344), (60720513913/9903520314283042199192993792)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944943207729345/19807040628566084398385987584), (1092774551317/9903520314283042199192993792)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472417491603853/618970019642690137449562112), (2321674425871/1237940039285380274899124224)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885667794472565/77371252455336267181195264), (2321144032627/77371252455336267181195264)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387422151202159/2417851639229258349412352), (4351018136395/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258906300289469/604462909807314587353088), (3806014125239/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471995481371167/18889465931478580854784), (6182660692449/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297680773502027/4722366482869645213696), (2317573837631/2361183241434822606848)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621640659598273/590295810358705651712), (3185163014005/295147905179352825856)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823712646439091/73786976294838206464), (7958405759751/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822921018281289/9223372036854775808), (8947018592801/9223372036854775808)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797082477654123/576460752303423488), (4469643409175/576460752303423488)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298683085180079/36028797018963968), (1953295491397/36028797018963968)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491854534854421/36028797018963968), (11702395576931/36028797018963968)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((744755624037813/4503599627370496), (7298804014303/4503599627370496)), (11097/9007199254740992), by norm_num⟩
  | 2 => ⟨((557100476125275/1125899906842624), (7276038191093/1125899906842624)), (2785/562949953421312), by norm_num⟩
  | 1 => ⟨((277081502090403/281474976710656), (21714453976917/1125899906842624)), (16819/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090652339613959/1125899906842624), (10743820083427/281474976710656)), (17037/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090652339613959/1125899906842624), (10743820083427/281474976710656)), (64990999461936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((263716970746595/281474976710656), (83259781365407/1125899906842624)), (68617/1125899906842624), by norm_num⟩
  | 2 => ⟨((982160183727345/1125899906842624), (156013991604517/1125899906842624)), (138725/1125899906842624), by norm_num⟩
  | 3 => ⟨((1670305246866657/2251799813685248), (68048114102805/281474976710656)), (280475/1125899906842624), by norm_num⟩
  | 4 => ⟨((553682585202961/1125899906842624), (807610845934165/2251799813685248)), (275853/562949953421312), by norm_num⟩
  | 5 => ⟨((63729282091267/562949953421312), (1588631665380471/4503599627370496)), (234591/281474976710656), by norm_num⟩
  | 6 => ⟨((-502668928462393/4503599627370496), (719370202817169/9007199254740992)), (3497869/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-19562963367/268435456)), (1/536870912), by norm_num⟩, -12, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-40745453901/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((500688903948649/4503599627370496), (-270996462028055/4503599627370496)), (1673167/4503599627370496), by norm_num⟩
  | 1 => ⟨((-73278781489/274877906944), (9915483631/68719476736)), (247/274877906944), by norm_num⟩
  | 2 => ⟨((10982177733/34359738368), (-11888145663/68719476736)), (299/274877906944), by norm_num⟩
  | 3 => ⟨((-8778037357/34359738368), (38008704383/274877906944)), (241/274877906944), by norm_num⟩
  | 4 => ⟨((84195257131/549755813888), (-22785223141/274877906944)), (73/137438953472), by norm_num⟩
  | 5 => ⟨((-40378281813/549755813888), (43709263087/1099511627776)), (283/1099511627776), by norm_num⟩
  | 6 => ⟨((64548594055/2199023255552), (-34936745111/2199023255552)), (57/549755813888), by norm_num⟩
  | 7 => ⟨((-88446153457/8796093022208), (47871231971/8796093022208)), (315/8796093022208), by norm_num⟩
  | 8 => ⟨((26510576659/8796093022208), (-28697550211/17592186044416)), (191/17592186044416), by norm_num⟩
  | 9 => ⟨((-28253149533/35184372088832), (955746111/2199023255552)), (103/35184372088832), by norm_num⟩
  | 10 => ⟨((54198474965/281474976710656), (-7333693061/70368744177664)), (25/35184372088832), by norm_num⟩
  | 11 => ⟨((-47259006149/1125899906842624), (6394701063/281474976710656)), (177/1125899906842624), by norm_num⟩
  | 12 => ⟨((37774049147/4503599627370496), (-20445097933/4503599627370496)), (143/4503599627370496), by norm_num⟩
  | 13 => ⟨((-55740439313/36028797018963968), (15084678057/18014398509481984)), (213/36028797018963968), by norm_num⟩
  | 14 => ⟨((76376991961/288230376151711744), (-20669416117/144115188075855872)), (147/144115188075855872), by norm_num⟩
  | 15 => ⟨((-12209601865/288230376151711744), (6608412693/288230376151711744)), (95/576460752303423488), by norm_num⟩
  | 16 => ⟨((29277346595/4611686018427387904), (-15846281557/4611686018427387904)), (115/4611686018427387904), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (-323111762047/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889389345940671/316912650057057350374175801344), (-764780064573/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944876521828071/19807040628566084398385987584), (-430111090559/19807040628566084398385987584)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889528861232217/2475880078570760549798248448), (-913793278523/2475880078570760549798248448)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885597580465013/77371252455336267181195264), (-456788235229/77371252455336267181195264)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549557672608373/9671406556917033397649408), (-53515478371/604462909807314587353088)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19668632081213/9444732965739290427392), (-187246622619/151115727451828646838272)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943899135141835/37778931862957161709568), (-608335790103/37778931862957161709568)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162193026139249/590295810358705651712), (-114015790299/590295810358705651712)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810727397149365/295147905179352825856), (-626780399349/295147905179352825856)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823483177572419/73786976294838206464), (-1566032215983/73786976294838206464)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822666796669429/9223372036854775808), (-880261912877/4611686018427387904)), (3335/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796957819569595/576460752303423488), (-219868395747/144115188075855872)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((597259848259891/72057594037927936), (-1537306898633/144115188075855872)), (5839/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491546555543209/36028797018963968), (-2302421276121/36028797018963968)), (4381/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489145438475793/9007199254740992), (-2871843715531/9007199254740992)), (5479/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227727528618763/4503599627370496), (-2862590352099/2251799813685248)), (21933/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107891343628427/1125899906842624), (-4270825303099/1125899906842624)), (32941/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180129731010971/2251799813685248), (-16899695020503/2251799813685248)), (66057/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180129731010971/2251799813685248), (-16899695020503/2251799813685248)), (251987465865325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2110613925563857/2251799813685248), (-32723626083723/2251799813685248)), (128901/2251799813685248), by norm_num⟩
  | 2 => ⟨((988902361571677/1125899906842624), (-15335941607131/562949953421312)), (122693/1125899906842624), by norm_num⟩
  | 3 => ⟨((1735477746049217/2251799813685248), (-107759126935159/2251799813685248)), (444427/2251799813685248), by norm_num⟩
  | 4 => ⟨((666193983887951/1125899906842624), (-83050707080217/1125899906842624)), (727583/2251799813685248), by norm_num⟩
  | 5 => ⟨((1552241017399949/4503599627370496), (-393128242240557/4503599627370496)), (121045/281474976710656), by norm_num⟩
  | 6 => ⟨((500688903948649/4503599627370496), (-270996462028055/4503599627370496)), (1673167/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-40745453901/536870912)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-21111983183/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-525057639172057/4503599627370496), (57166687586583/4503599627370496)), (2751911/4503599627370496), by norm_num⟩
  | 1 => ⟨((79633741401/274877906944), (-2167570223/68719476736)), (105/68719476736), by norm_num⟩
  | 2 => ⟨((-49470603389/137438953472), (5386209661/137438953472)), (131/68719476736), by norm_num⟩
  | 3 => ⟨((81953220887/274877906944), (-8922818803/274877906944)), (109/68719476736), by norm_num⟩
  | 4 => ⟨((-101823051777/549755813888), (11086185889/549755813888)), (17/17179869184), by norm_num⟩
  | 5 => ⟨((101208311385/1099511627776), (-11019254815/1099511627776)), (543/1099511627776), by norm_num⟩
  | 6 => ⟨((-83831068659/2199023255552), (9127273189/2199023255552)), (113/549755813888), by norm_num⟩
  | 7 => ⟨((119035645697/8796093022208), (-12960241053/8796093022208)), (645/8796093022208), by norm_num⟩
  | 8 => ⟨((-73948116889/17592186044416), (4025623647/8796093022208)), (201/8796093022208), by norm_num⟩
  | 9 => ⟨((81668518843/70368744177664), (-8891821307/70368744177664)), (223/35184372088832), by norm_num⟩
  | 10 => ⟨((-81175458221/281474976710656), (4419069179/140737488355328)), (445/281474976710656), by norm_num⟩
  | 11 => ⟨((18337585085/281474976710656), (-998270399/140737488355328)), (101/281474976710656), by norm_num⟩
  | 12 => ⟨((-15189062373/1125899906842624), (3307478337/2251799813685248)), (21/281474976710656), by norm_num⟩
  | 13 => ⟨((46453417963/18014398509481984), (-5057707639/18014398509481984)), (129/9007199254740992), by norm_num⟩
  | 14 => ⟨((-8245171943/18014398509481984), (3590837527/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | 15 => ⟨((87417525717/1152921504606846976), (-4758877893/576460752303423488)), (245/576460752303423488), by norm_num⟩
  | 16 => ⟨((-54306097741/4611686018427387904), (5912683661/4611686018427387904)), (611/9223372036854775808), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (3951007227849/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778651616876047/633825300114114700748351602688), (4675282166929/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889609467873553/39614081257132168796771975168), (5258676014269/39614081257132168796771975168)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889375505049193/2475880078570760549798248448), (2793059035067/1237940039285380274899124224)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442760224425021/38685626227668133590597632), (698092465437/19342813113834066795298816)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774706043870533/4835703278458516698824704), (5234229161675/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258664104078309/604462909807314587353088), (2289243185749/302231454903657293676544)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943793950043503/37778931862957161709568), (3718647736825/37778931862957161709568)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648692427747867/2361183241434822606848), (5575570227549/4722366482869645213696)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621233125020683/590295810358705651712), (3831253780477/295147905179352825856)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((113950141185401/4611686018427387904), (2393070872525/18446744073709551616)), (5975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911172751230169/4611686018427387904), (10760775958451/9223372036854775808)), (6729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796793890649623/576460752303423488), (5375362705835/576460752303423488)), (3369/576460752303423488), by norm_num⟩
  | 5 => ⟨((597112726888267/72057594037927936), (9395582231883/144115188075855872)), (2953/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491090499488637/36028797018963968), (3517694820789/9007199254740992)), (4439/18014398509481984), by norm_num⟩
  | 3 => ⟨((744274876303297/4503599627370496), (8774479606521/4503599627370496)), (2783/2251799813685248), by norm_num⟩
  | 2 => ⟨((2174277040177/4398046511104), (8744868288667/1125899906842624)), (699/140737488355328), by norm_num⟩
  | 1 => ⟨((1106845542160221/1125899906842624), (13043361688337/562949953421312)), (4227/281474976710656), by norm_num⟩
  | 0 => ⟨((1087597539227777/1125899906842624), (51582980528985/1125899906842624)), (34341/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087597539227777/1125899906842624), (51582980528985/1125899906842624)), (131000523093795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1048234924153901/1125899906842624), (49828161765005/562949953421312)), (69493/1125899906842624), by norm_num⟩
  | 2 => ⟨((483553230077945/562949953421312), (185563988596259/1125899906842624)), (70851/562949953421312), by norm_num⟩
  | 3 => ⟨((1600250441334167/2251799813685248), (159392616566599/562949953421312)), (290143/1125899906842624), by norm_num⟩
  | 4 => ⟨((956703771997101/2251799813685248), (906183945680921/2251799813685248)), (144171/281474976710656), by norm_num⟩
  | 5 => ⟨((5224307872067/281474976710656), (1540011849521067/4503599627370496)), (119271/140737488355328), by norm_num⟩
  | 6 => ⟨((-525057639172057/4503599627370496), (57166687586583/4503599627370496)), (2751911/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-21111983183/268435456)), (1/536870912), by norm_num⟩, -13, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-87168131977/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((865283781545171/9007199254740992), (472436957003635/9007199254740992)), (1455797/4503599627370496), by norm_num⟩
  | 1 => ⟨((-67730989975/274877906944), (-36980495279/274877906944)), (115/137438953472), by norm_num⟩
  | 2 => ⟨((86863279609/274877906944), (23713274401/137438953472)), (149/137438953472), by norm_num⟩
  | 3 => ⟨((-18566659435/68719476736), (-20274449313/137438953472)), (257/274877906944), by norm_num⟩
  | 4 => ⟨((11905635297/68719476736), (26001467869/274877906944)), (167/274877906944), by norm_num⟩
  | 5 => ⟨((-48859762569/549755813888), (-13338489661/274877906944)), (87/274877906944), by norm_num⟩
  | 6 => ⟨((83548544405/2199023255552), (45616733981/2199023255552)), (75/549755813888), by norm_num⟩
  | 7 => ⟨((-30613969327/2199023255552), (-16714944645/2199023255552)), (111/2199023255552), by norm_num⟩
  | 8 => ⟨((78523280955/17592186044416), (42872986527/17592186044416)), (287/17592186044416), by norm_num⟩
  | 9 => ⟨((-11189346613/8796093022208), (-3054639979/4398046511104)), (83/17592186044416), by norm_num⟩
  | 10 => ⟨((45920171849/140737488355328), (25071989925/140737488355328)), (43/35184372088832), by norm_num⟩
  | 11 => ⟨((-85660302021/1125899906842624), (-46769734145/1125899906842624)), (81/281474976710656), by norm_num⟩
  | 12 => ⟨((36619056105/2251799813685248), (39987333181/4503599627370496)), (279/4503599627370496), by norm_num⟩
  | 13 => ⟨((-57800630417/18014398509481984), (-31558610631/18014398509481984)), (111/9007199254740992), by norm_num⟩
  | 14 => ⟨((84717537057/144115188075855872), (23127496589/72057594037927936)), (41/18014398509481984), by norm_num⟩
  | 15 => ⟨((-905400801/9007199254740992), (-31637790675/576460752303423488)), (113/288230376151711744), by norm_num⟩
  | 16 => ⟨((74313830489/4611686018427387904), (5071833179/576460752303423488)), (73/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (81374132893/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444639148759167/158456325028528675187087900672), (770241427217/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472375807788011/9903520314283042199192993792), (216588690927/9903520314283042199192993792)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263493049055/2475880078570760549798248448), (460147133221/1237940039285380274899124224)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((55341558047699/4835703278458516698824704), (57503795695/9671406556917033397649408)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549309019474485/9671406556917033397649408), (431154443319/4835703278458516698824704)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258574950488689/604462909807314587353088), (94284039981/75557863725914323419136)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471861239324883/18889465931478580854784), (76576737469/4722366482869645213696)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297279337128445/4722366482869645213696), (459257208243/2361183241434822606848)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621090778446677/590295810358705651712), (1262297238129/590295810358705651712)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911514216141801/36893488147419103232), (1576882066741/73786976294838206464)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227769448177969/1152921504606846976), (886316418811/4611686018427387904)), (3335/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796702449497547/576460752303423488), (1770935050155/1152921504606846976)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((597036664164177/72057594037927936), (1547660317111/144115188075855872)), (5839/144115188075855872), by norm_num⟩
  | 4 => ⟨((93179878796269/2251799813685248), (2317680163391/36028797018963968)), (4381/18014398509481984), by norm_num⟩
  | 3 => ⟨((744155833728613/4503599627370496), (2890444270159/9007199254740992)), (5479/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226065516607745/4503599627370496), (720121137251/562949953421312)), (21933/4503599627370496), by norm_num⟩
  | 1 => ⟨((553325862723789/562949953421312), (268494496817/70368744177664)), (32943/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175226125173287/2251799813685248), (16986138726827/2251799813685248)), (33031/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175226125173287/2251799813685248), (16986138726827/2251799813685248)), (126003269675826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050564117194851/1125899906842624), (16408515756977/1125899906842624)), (128629/2251799813685248), by norm_num⟩
  | 2 => ⟨((980030034856627/1125899906842624), (7655297671641/281474976710656)), (243795/2251799813685248), by norm_num⟩
  | 3 => ⟨((213056508413971/281474976710656), (106615823994733/2251799813685248)), (437681/2251799813685248), by norm_num⟩
  | 4 => ⟨((1285100877196259/2251799813685248), (161401169421511/2251799813685248)), (352017/1125899906842624), by norm_num⟩
  | 5 => ⟨((721837668340425/2251799813685248), (368446223582605/4503599627370496)), (1809019/4503599627370496), by norm_num⟩
  | 6 => ⟨((865283781545171/9007199254740992), (472436957003635/9007199254740992)), (1455797/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-87168131977/1073741824)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-2802707597/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-62780378775355/2251799813685248), (-445033340933987/4503599627370496)), (2496585/4503599627370496), by norm_num⟩
  | 1 => ⟨((2528091717/34359738368), (17920967107/68719476736)), (101/68719476736), by norm_num⟩
  | 2 => ⟨((-26687115903/274877906944), (-94588919195/274877906944)), (535/274877906944), by norm_num⟩
  | 3 => ⟨((23476276277/274877906944), (41604263417/137438953472)), (473/274877906944), by norm_num⟩
  | 4 => ⟨((-15488809745/274877906944), (-54898018157/274877906944)), (157/137438953472), by norm_num⟩
  | 5 => ⟨((8175171377/274877906944), (1810987715/17179869184)), (333/549755813888), by norm_num⟩
  | 6 => ⟨((-28766327925/2199023255552), (-12744801075/274877906944)), (147/549755813888), by norm_num⟩
  | 7 => ⟨((21690282445/4398046511104), (9609788769/549755813888)), (445/4398046511104), by norm_num⟩
  | 8 => ⟨((-14310474717/8796093022208), (-25360783487/4398046511104)), (589/17592186044416), by norm_num⟩
  | 9 => ⟨((16784961419/35184372088832), (14873013677/8796093022208)), (347/35184372088832), by norm_num⟩
  | 10 => ⟨((-2214823773/17592186044416), (-62801177213/140737488355328)), (23/8796093022208), by norm_num⟩
  | 11 => ⟨((17003772835/562949953421312), (60267602557/562949953421312)), (355/562949953421312), by norm_num⟩
  | 12 => ⟨((-29915954221/4503599627370496), (-106033105511/4503599627370496)), (627/4503599627370496), by norm_num⟩
  | 13 => ⟨((24292282541/18014398509481984), (86100752087/18014398509481984)), (1/35184372088832), by norm_num⟩
  | 14 => ⟨((-18316778941/72057594037927936), (-64921377395/72057594037927936)), (97/18014398509481984), by norm_num⟩
  | 15 => ⟨((12890407925/288230376151711744), (91376659661/576460752303423488)), (549/576460752303423488), by norm_num⟩
  | 16 => ⟨((-8504631379/1152921504606846976), (-60287060859/2305843009213693952)), (91/576460752303423488), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-2404342831219/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778454071975805/633825300114114700748351602688), (-711117044733/158456325028528675187087900672)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944693845074371/19807040628566084398385987584), (-799846617673/9903520314283042199192993792)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944570231423497/1237940039285380274899124224), (-3398558248149/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885403263124397/77371252455336267181195264), (-3397669887813/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549193076744293/9671406556917033397649408), (-1592185947171/4835703278458516698824704)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258473181207099/604462909807314587353088), (-2785382071495/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887278983918023/75557863725914323419136), (-2262238862993/37778931862957161709568)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297154334142693/4722366482869645213696), (-3391811786587/4722366482869645213696)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620918050600929/590295810358705651712), (-4661229283599/590295810358705651712)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822811251206621/73786976294838206464), (-5686299547/72057594037927936)), (5953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910954755852095/4611686018427387904), (-6545442284103/9223372036854775808)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398289162123025/288230376151711744), (-6538978702017/1152921504606846976)), (6707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193853666403147/144115188075855872), (-5714341583071/144115188075855872)), (5875/144115188075855872), by norm_num⟩
  | 4 => ⟨((745271848860621/18014398509481984), (-2139249918533/9007199254740992)), (8823/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487885225392775/9007199254740992), (-10670890279399/9007199254740992)), (5525/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112593652498139/2251799813685248), (-1329115883463/281474976710656)), (5541/1125899906842624), by norm_num⟩
  | 1 => ⟨((276490411748253/281474976710656), (-31709494848997/2251799813685248)), (33405/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172217315521671/2251799813685248), (-62665017675879/2251799813685248)), (67451/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172217315521671/2251799813685248), (-62665017675879/2251799813685248)), (257305153853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093703504529579/2251799813685248), (-60450327620483/1125899906842624)), (133889/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940215719838599/2251799813685248), (-224824714914303/2251799813685248)), (65839/562949953421312), by norm_num⟩
  | 3 => ⟨((1649298869509381/2251799813685248), (-387430928303589/2251799813685248)), (506419/2251799813685248), by norm_num⟩
  | 4 => ⟨((1141346589132449/2251799813685248), (-283768294224309/1125899906842624)), (916103/2251799813685248), by norm_num⟩
  | 5 => ⟨((435462447122061/2251799813685248), (-575322855519375/2251799813685248)), (2780911/4503599627370496), by norm_num⟩
  | 6 => ⟨((-62780378775355/2251799813685248), (-445033340933987/4503599627370496)), (2496585/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-2802707597/33554432)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-92031320869/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-274959671324557/4503599627370496), (675946713425403/9007199254740992)), (4958167/9007199254740992), by norm_num⟩
  | 1 => ⟨((11361764423/68719476736), (-55862354529/274877906944)), (103/68719476736), by norm_num⟩
  | 2 => ⟨((-61536456861/274877906944), (1181859847/4294967296)), (35/17179869184), by norm_num⟩
  | 3 => ⟨((27773969063/137438953472), (-17069524247/68719476736)), (127/68719476736), by norm_num⟩
  | 4 => ⟨((-37606651253/274877906944), (23112564285/137438953472)), (173/137438953472), by norm_num⟩
  | 5 => ⟨((40736279795/549755813888), (-1564749609/17179869184)), (377/549755813888), by norm_num⟩
  | 6 => ⟨((-9192990891/274877906944), (45199151929/1099511627776)), (171/549755813888), by norm_num⟩
  | 7 => ⟨((56903041899/4398046511104), (-69943755697/4398046511104)), (133/1099511627776), by norm_num⟩
  | 8 => ⟨((-19262036757/4398046511104), (11838200105/2199023255552)), (181/4398046511104), by norm_num⟩
  | 9 => ⟨((23183361117/17592186044416), (-56992782533/35184372088832)), (219/17592186044416), by norm_num⟩
  | 10 => ⟨((-12556341147/35184372088832), (3858482905/8796093022208)), (119/35184372088832), by norm_num⟩
  | 11 => ⟨((24729601577/281474976710656), (-60793980549/562949953421312)), (471/562949953421312), by norm_num⟩
  | 12 => ⟨((-22323000841/1125899906842624), (13719429271/562949953421312)), (427/2251799813685248), by norm_num⟩
  | 13 => ⟨((37201111949/9007199254740992), (-5715831261/1125899906842624)), (179/4503599627370496), by norm_num⟩
  | 14 => ⟨((-57567130683/72057594037927936), (8845004569/9007199254740992)), (139/18014398509481984), by norm_num⟩
  | 15 => ⟨((41571914619/288230376151711744), (-12774782081/72057594037927936)), (101/72057594037927936), by norm_num⟩
  | 16 => ⟨((-879522123/36028797018963968), (69189502367/2305843009213693952)), (549/2305843009213693952), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (1467878942915/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889180123053347/316912650057057350374175801344), (434102481583/79228162514264337593543950336)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472320509757767/9903520314283042199192993792), (3906116895337/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944514039129499/1237940039285380274899124224), (259328697315/154742504910672534362390528)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885346997630291/77371252455336267181195264), (4148145612867/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774543711761225/4835703278458516698824704), (3887703664551/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157297572420457/75557863725914323419136), (3400558188507/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943564107546633/37778931862957161709568), (2761845267677/37778931862957161709568)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81065062709913/295147905179352825856), (4140829145859/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620761808334667/590295810358705651712), (5690490910385/590295810358705651712)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911307665366071/36893488147419103232), (7108392187397/73786976294838206464)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910844126780899/4611686018427387904), (1997613237209/2305843009213693952)), (6711/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796467166654557/576460752303423488), (249448381863/36028797018963968)), (6717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298414488709805/36028797018963968), (6975444568431/144115188075855872)), (5885/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490247767283511/36028797018963968), (10444965843841/36028797018963968)), (4421/18014398509481984), by norm_num⟩
  | 3 => ⟨((743755597972439/4503599627370496), (13024398818199/9007199254740992)), (5539/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224426972748213/4503599627370496), (25953545250387/4503599627370496)), (11117/2251799813685248), by norm_num⟩
  | 1 => ⟨((138172023553367/140737488355328), (19346396239629/1125899906842624)), (16773/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084877693558763/1125899906842624), (38219557619017/1125899906842624)), (33937/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084877693558763/1125899906842624), (38219557619017/1125899906842624)), (129459385398482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2088105467018387/2251799813685248), (147308105335339/2251799813685248)), (135411/2251799813685248), by norm_num⟩
  | 2 => ⟨((30104285477607/35184372088832), (68299779184953/562949953421312)), (67213/562949953421312), by norm_num⟩
  | 3 => ⟨((1615346073558791/2251799813685248), (467506663572145/2251799813685248)), (525305/2251799813685248), by norm_num⟩
  | 4 => ⟨((265429951004919/562949953421312), (335369533638923/1125899906842624)), (485893/1125899906842624), by norm_num⟩
  | 5 => ⟨((300807399378133/2251799813685248), (1265009343602541/4503599627370496)), (2990639/4503599627370496), by norm_num⟩
  | 6 => ⟨((-274959671324557/4503599627370496), (675946713425403/9007199254740992)), (4958167/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-92031320869/1073741824)), (1/536870912), by norm_num⟩, -14, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile064Terms1
