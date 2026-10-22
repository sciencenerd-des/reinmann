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
namespace Reinmann.XiBand97.Tile063Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨63,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80667/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80667/2560))
  have he : value ((69/80), (80667/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1017427393/536870912), (-74341318385/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1343952372142473/9007199254740992), (-163020584930157/9007199254740992)), (1458727/4503599627370496), by norm_num⟩
  | 1 => ⟨((-22529336417/68719476736), (10931177851/274877906944)), (99/137438953472), by norm_num⟩
  | 2 => ⟨((99004023373/274877906944), (-12009126317/274877906944)), (55/68719476736), by norm_num⟩
  | 3 => ⟨((-72511357803/274877906944), (8795582499/274877906944)), (163/274877906944), by norm_num⟩
  | 4 => ⟨((39830934375/274877906944), (-9662935019/549755813888)), (91/274877906944), by norm_num⟩
  | 5 => ⟨((-35007003179/549755813888), (8492655325/1099511627776)), (81/549755813888), by norm_num⟩
  | 6 => ⟨((102557663685/4398046511104), (-12440180671/4398046511104)), (15/274877906944), by norm_num⟩
  | 7 => ⟨((-16095872803/2199023255552), (1952419337/2199023255552)), (153/8796093022208), by norm_num⟩
  | 8 => ⟨((70732494633/35184372088832), (-8579807505/35184372088832)), (85/17592186044416), by norm_num⟩
  | 9 => ⟨((-17268352847/35184372088832), (4189280871/70368744177664)), (21/17592186044416), by norm_num⟩
  | 10 => ⟨((60707918857/562949953421312), (-7363832713/562949953421312)), (149/562949953421312), by norm_num⟩
  | 11 => ⟨((-24252532973/1125899906842624), (2941817131/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 12 => ⟨((17762753837/4503599627370496), (-4309221935/9007199254740992)), (89/9007199254740992), by norm_num⟩
  | 13 => ⟨((-96070792103/144115188075855872), (5826663597/72057594037927936)), (243/144115188075855872), by norm_num⟩
  | 14 => ⟨((60311173021/576460752303423488), (-7315707691/576460752303423488)), (77/288230376151711744), by norm_num⟩
  | 15 => ⟨((-70675835547/4611686018427387904), (4286467397/2305843009213693952)), (183/4611686018427387904), by norm_num⟩
  | 16 => ⟨((19411335361/9223372036854775808), (-9418331515/36893488147419103232)), (203/36893488147419103232), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (-19654726125/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889522920247285/316912650057057350374175801344), (-186137901417/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890053550458031/39614081257132168796771975168), (-104685188877/19807040628566084398385987584)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472462026724959/618970019642690137449562112), (-222413029003/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771514358442243/154742504910672534362390528), (-55591168327/38685626227668133590597632)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774928434558927/4835703278458516698824704), (-208415518169/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259054198992951/604462909807314587353088), (-91156116035/302231454903657293676544)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888223511310385/75557863725914323419136), (-148080569143/37778931862957161709568)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297863055996151/4722366482869645213696), (-111018340131/2361183241434822606848)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621893072474779/590295810358705651712), (-76290930017/147573952589676412928)), (4737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228003852614519/9223372036854775808), (-381249693579/73786976294838206464)), (5921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823282614501529/9223372036854775808), (-53578034895/1152921504606846976)), (6661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99658194121319/72057594037927936), (-428272529917/1152921504606846976)), (3331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195057835243795/144115188075855872), (-187171567555/72057594037927936)), (2915/72057594037927936), by norm_num⟩
  | 4 => ⟨((373088243656829/9007199254740992), (-70090627227/4503599627370496)), (8745/36028797018963968), by norm_num⟩
  | 3 => ⟨((186269010324775/1125899906842624), (-349763254279/4503599627370496)), (2733/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229736681750109/4503599627370496), (-697461225381/2251799813685248)), (5467/1125899906842624), by norm_num⟩
  | 1 => ⟨((554696523369163/562949953421312), (-520521933173/562949953421312)), (8203/562949953421312), by norm_num⟩
  | 0 => ⟨((1093047667729531/1125899906842624), (-4123174012751/2251799813685248)), (32835/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093047667729531/1125899906842624), (-4123174012751/2251799813685248)), (125255589011764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((265287559428447/281474976710656), (-2001432681045/562949953421312)), (127749/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000220085685317/2251799813685248), (-15090654168113/2251799813685248)), (120857/1125899906842624), by norm_num⟩
  | 3 => ⟨((444161670036331/562949953421312), (-13404668296775/1125899906842624)), (216329/1125899906842624), by norm_num⟩
  | 4 => ⟨((700718302391671/1125899906842624), (-42304576602551/2251799813685248)), (693029/2251799813685248), by norm_num⟩
  | 5 => ⟨((871407337410597/2251799813685248), (-105315191590939/4503599627370496)), (1777343/4503599627370496), by norm_num⟩
  | 6 => ⟨((1343952372142473/9007199254740992), (-163020584930157/9007199254740992)), (1458727/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-74341318385/1073741824)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-533107351/268435456), (-77906106309/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-590661869587379/4503599627370496), (364241566175005/9007199254740992)), (1681851/2251799813685248), by norm_num⟩
  | 1 => ⟨((83010816401/274877906944), (-6398751835/68719476736)), (475/274877906944), by norm_num⟩
  | 2 => ⟨((-95569734201/274877906944), (14733670589/137438953472)), (549/274877906944), by norm_num⟩
  | 3 => ⟨((73352481771/274877906944), (-22617020175/274877906944)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-42225082765/274877906944), (26038806751/549755813888)), (491/549755813888), by norm_num⟩
  | 5 => ⟨((19445369225/274877906944), (-11991313653/549755813888)), (455/1099511627776), by norm_num⟩
  | 6 => ⟨((-14924872435/549755813888), (4601836677/549755813888)), (351/2199023255552), by norm_num⟩
  | 7 => ⟨((39275187181/4398046511104), (-24219704075/8796093022208)), (29/549755813888), by norm_num⟩
  | 8 => ⟨((-90434460527/35184372088832), (6970991195/8796093022208)), (537/35184372088832), by norm_num⟩
  | 9 => ⟨((46274009045/70368744177664), (-28535645171/140737488355328)), (69/17592186044416), by norm_num⟩
  | 10 => ⟨((-5327492171/35184372088832), (6570575119/140737488355328)), (511/562949953421312), by norm_num⟩
  | 11 => ⟨((35685829981/1125899906842624), (-22006266649/2251799813685248)), (215/1125899906842624), by norm_num⟩
  | 12 => ⟨((-27389886715/4503599627370496), (8445216923/4503599627370496)), (83/2251799813685248), by norm_num⟩
  | 13 => ⟨((19405398415/18014398509481984), (-11966664981/36028797018963968)), (473/72057594037927936), by norm_num⟩
  | 14 => ⟨((-51065806987/288230376151711744), (31490587883/576460752303423488)), (625/576460752303423488), by norm_num⟩
  | 15 => ⟨((3919445531/144115188075855872), (-2416991941/288230376151711744)), (193/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-18049713705/4611686018427387904), (22261318453/18446744073709551616)), (447/18446744073709551616), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (3702684272385/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778895461735713/633825300114114700748351602688), (4382575355511/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889883819587067/39614081257132168796771975168), (4929512886961/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944833523419667/1237940039285380274899124224), (5236543266155/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771332487841617/154742504910672534362390528), (5235346064601/154742504910672534362390528)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774842752384713/4835703278458516698824704), (1226716258745/2417851639229258349412352)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314725848783337/151115727451828646838272), (4292235146445/604462909807314587353088)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887976843722323/75557863725914323419136), (6972497865455/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648838323344623/2361183241434822606848), (2613643741929/2361183241434822606848)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202704309135837/73786976294838206464), (1796032810999/147573952589676412928)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823704146008867/73786976294838206464), (8975081477785/73786976294838206464)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911455200887711/4611686018427387904), (10089979734707/9223372036854775808)), (1681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594153024153337/1152921504606846976), (2520312126197/288230376151711744)), (6733/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194720425076099/144115188075855872), (8811273158841/144115188075855872)), (5901/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491833717356675/36028797018963968), (6598639789451/18014398509481984)), (8869/36028797018963968), by norm_num⟩
  | 3 => ⟨((744740045769787/4503599627370496), (16462265689401/9007199254740992)), (11119/9007199254740992), by norm_num⟩
  | 2 => ⟨((34817566514501/70368744177664), (16410803202731/2251799813685248)), (349/70368744177664), by norm_num⟩
  | 1 => ⟨((554124362998791/562949953421312), (24487683149497/1125899906842624)), (8437/562949953421312), by norm_num⟩
  | 0 => ⟨((1090422315458767/1125899906842624), (48462094204703/1125899906842624)), (34241/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090422315458767/1125899906842624), (48462094204703/1125899906842624)), (130619053367232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263494171254431/281474976710656), (46935032726723/562949953421312)), (69273/1125899906842624), by norm_num⟩
  | 2 => ⟨((978821702244585/1125899906842624), (87873584328175/562949953421312)), (2207/17592186044416), by norm_num⟩
  | 3 => ⟨((823523345067535/1125899906842624), (152789019470911/562949953421312)), (144845/562949953421312), by norm_num⟩
  | 4 => ⟨((1038836149525389/2251799813685248), (894042702301145/2251799813685248)), (145257/281474976710656), by norm_num⟩
  | 5 => ⟨((31071611064393/562949953421312), (206227008441261/562949953421312)), (997475/1125899906842624), by norm_num⟩
  | 6 => ⟨((-590661869587379/4503599627370496), (364241566175005/9007199254740992)), (1681851/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-77906106309/1073741824)), (1/536870912), by norm_num⟩, -12, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-2220696383/1073741824), (-10141356155/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1123962421420009/9007199254740992), (-91134953656255/4503599627370496)), (2552005/9007199254740992), by norm_num⟩
  | 1 => ⟨((-82249272983/274877906944), (3334534829/68719476736)), (189/274877906944), by norm_num⟩
  | 2 => ⟨((49306285719/137438953472), (-15991730607/274877906944)), (229/274877906944), by norm_num⟩
  | 3 => ⟨((-78820872963/274877906944), (12782165075/274877906944)), (185/274877906944), by norm_num⟩
  | 4 => ⟨((47251049669/274877906944), (-15325146605/549755813888)), (7/17179869184), by norm_num⟩
  | 5 => ⟨((-90642454909/1099511627776), (918702415/68719476736)), (217/1099511627776), by norm_num⟩
  | 6 => ⟨((18112592845/549755813888), (-11749078283/2199023255552)), (175/2199023255552), by norm_num⟩
  | 7 => ⟨((-6204585823/549755813888), (8049445507/4398046511104)), (121/4398046511104), by norm_num⟩
  | 8 => ⟨((29755894029/8796093022208), (-9650863665/17592186044416)), (147/17592186044416), by norm_num⟩
  | 9 => ⟨((-63423571227/70368744177664), (10285226827/70368744177664)), (159/70368744177664), by norm_num⟩
  | 10 => ⟨((15208308163/70368744177664), (-9865158715/281474976710656)), (155/281474976710656), by norm_num⟩
  | 11 => ⟨((-106088524367/2251799813685248), (17204085417/2251799813685248)), (273/2251799813685248), by norm_num⟩
  | 12 => ⟨((84796390359/9007199254740992), (-13751198365/9007199254740992)), (55/2251799813685248), by norm_num⟩
  | 13 => ⟨((-15640989507/9007199254740992), (10145825709/36028797018963968)), (41/9007199254740992), by norm_num⟩
  | 14 => ⟨((42863376915/144115188075855872), (-13902072861/288230376151711744)), (227/288230376151711744), by norm_num⟩
  | 15 => ⟨((-54817007403/1152921504606846976), (17779047891/2305843009213693952)), (293/2305843009213693952), by norm_num⟩
  | 16 => ⟨((16430680365/2305843009213693952), (-10658073723/9223372036854775808)), (177/9223372036854775808), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (-209417890497/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778972079395/633825300114114700748351602688), (-247837817481/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889753374693573/39614081257132168796771975168), (-278767231831/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889529233550001/2475880078570760549798248448), (-296127712985/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771195556392493/154742504910672534362390528), (-74014364931/38685626227668133590597632)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774779033965043/4835703278458516698824704), (-277479247955/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629396411831125/302231454903657293676544), (-30339968491/75557863725914323419136)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798918297917/75557863725914323419136), (-394279782869/75557863725914323419136)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648772367672779/2361183241434822606848), (-36948445231/590295810358705651712)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621455583156363/590295810358705651712), (-406234305623/590295810358705651712)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823484261456431/73786976294838206464), (-507495178577/73786976294838206464)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455667037583143/2305843009213693952), (-285261516567/4611686018427387904)), (3331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398479290093247/288230376151711744), (-17812880579/36028797018963968)), (6663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597260607854703/72057594037927936), (-498186561349/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((372887302383047/9007199254740992), (-746133191917/36028797018963968)), (8747/36028797018963968), by norm_num⟩
  | 3 => ⟨((744574705144913/4503599627370496), (-930663311409/9007199254740992)), (10935/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113868713066997/2251799813685248), (-927665449727/2251799813685248)), (21875/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215802386519833/2251799813685248), (-2768055272173/2251799813685248)), (32827/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180188352001195/2251799813685248), (-5476634739171/2251799813685248)), (65713/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180188352001195/2251799813685248), (-5476634739171/2251799813685248)), (250675210005950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055420474721207/1125899906842624), (-5302467472437/1125899906842624)), (127567/2251799813685248), by norm_num⟩
  | 2 => ⟨((494663981908979/562949953421312), (-19882167865693/2251799813685248)), (120183/1125899906842624), by norm_num⟩
  | 3 => ⟨((108654307200687/140737488355328), (-545951746335/35184372088832)), (426665/2251799813685248), by norm_num⟩
  | 4 => ⟨((335404293432249/562949953421312), (-210747006559/8796093022208)), (672043/2251799813685248), by norm_num⟩
  | 5 => ⟨((1596079628666553/4503599627370496), (-128576086040781/4503599627370496)), (833007/2251799813685248), by norm_num⟩
  | 6 => ⟨((1123962421420009/9007199254740992), (-91134953656255/4503599627370496)), (2552005/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-10141356155/134217728)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2301277821/1073741824), (-42037404441/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1026283131090093/9007199254740992), (-250114280540203/9007199254740992)), (2845637/4503599627370496), by norm_num⟩
  | 1 => ⟨((38913235123/137438953472), (18966999479/274877906944)), (433/274877906944), by norm_num⟩
  | 2 => ⟨((-48347878361/137438953472), (-11782805783/137438953472)), (135/68719476736), by norm_num⟩
  | 3 => ⟨((80093309629/274877906944), (2439931037/34359738368)), (225/137438953472), by norm_num⟩
  | 4 => ⟨((-99512198851/549755813888), (-6063000859/137438953472)), (281/274877906944), by norm_num⟩
  | 5 => ⟨((12363926233/137438953472), (6026396461/274877906944)), (561/1099511627776), by norm_num⟩
  | 6 => ⟨((-81928540037/2199023255552), (-19966710187/2199023255552)), (467/2199023255552), by norm_num⟩
  | 7 => ⟨((29083539135/2199023255552), (14175831691/4398046511104)), (333/4398046511104), by norm_num⟩
  | 8 => ⟨((-18067469949/4398046511104), (-8806404609/8796093022208)), (13/549755813888), by norm_num⟩
  | 9 => ⟨((39907534419/35184372088832), (9725819277/35184372088832)), (231/35184372088832), by norm_num⟩
  | 10 => ⟨((-19833299531/70368744177664), (-19334202397/281474976710656)), (461/281474976710656), by norm_num⟩
  | 11 => ⟨((71685669661/1125899906842624), (8735216019/562949953421312)), (209/562949953421312), by norm_num⟩
  | 12 => ⟨((-59377399079/4503599627370496), (-7235398791/2251799813685248)), (87/1125899906842624), by norm_num⟩
  | 13 => ⟨((45399167329/18014398509481984), (2766044703/4503599627370496)), (267/18014398509481984), by norm_num⟩
  | 14 => ⟨((-64464395881/144115188075855872), (-15710543717/144115188075855872)), (381/144115188075855872), by norm_num⟩
  | 15 => ⟨((667450025/9007199254740992), (2602615637/144115188075855872)), (507/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-53073632177/4611686018427387904), (-25869027613/9223372036854775808)), (79/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-1890443673463/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222331575373459/79228162514264337593543950336), (-2236988465075/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944805316344657/19807040628566084398385987584), (-5032254182539/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((14760756367885/19342813113834066795298816), (-5345597953559/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771042289159381/154742504910672534362390528), (-1336069841365/38685626227668133590597632)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549413478684775/9671406556917033397649408), (-1252215271929/2417851639229258349412352)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258665407540311/604462909807314587353088), (-547669104885/75557863725914323419136)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887590180050263/75557863725914323419136), (-7117072650195/75557863725914323419136)), (289/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648693353469649/2361183241434822606848), (-5335507424391/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810617950194967/295147905179352825856), (-7332590798985/590295810358705651712)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((56975189755665/2305843009213693952), (-9160142068191/73786976294838206464)), (5973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911175132301769/4611686018427387904), (-5148733534071/4611686018427387904)), (3363/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796796566348239/576460752303423488), (-10287854626187/1152921504606846976)), (3367/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194230797659863/144115188075855872), (-1123882953971/18014398509481984)), (2951/72057594037927936), by norm_num⟩
  | 4 => ⟨((745549917193821/18014398509481984), (-13464989222749/36028797018963968)), (1109/4503599627370496), by norm_num⟩
  | 3 => ⟨((372140930296301/2251799813685248), (-16793452958047/9007199254740992)), (11123/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113247246250219/2251799813685248), (-8368416226005/1125899906842624)), (11173/2251799813685248), by norm_num⟩
  | 1 => ⟨((553440084302093/562949953421312), (-12481945148201/562949953421312)), (16885/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087700535504365/1125899906842624), (-6170438950765/140737488355328)), (17137/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087700535504365/1125899906842624), (-6170438950765/140737488355328)), (65372469188499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((131079114080545/140737488355328), (-47688713430063/562949953421312)), (69229/1125899906842624), by norm_num⟩
  | 2 => ⟨((484294440961779/562949953421312), (-88831971937305/562949953421312)), (70343/562949953421312), by norm_num⟩
  | 3 => ⟨((1610445013314261/2251799813685248), (-305681383770985/1125899906842624)), (286459/1125899906842624), by norm_num⟩
  | 4 => ⟨((246443832826703/562949953421312), (-437235190415373/1125899906842624)), (70661/140737488355328), by norm_num⟩
  | 5 => ⟨((91950694553049/2251799813685248), (-382818811930995/1125899906842624)), (466993/562949953421312), by norm_num⟩
  | 6 => ⟨((-1026283131090093/9007199254740992), (-250114280540203/9007199254740992)), (2845637/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-42037404441/536870912)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-2375405559/1073741824), (-21695747307/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((644365359370983/9007199254740992), (186531831162715/2251799813685248)), (57241/140737488355328), by norm_num⟩
  | 1 => ⟨((-50438370193/274877906944), (-58403894103/274877906944)), (289/274877906944), by norm_num⟩
  | 2 => ⟨((32342966305/137438953472), (37450757663/137438953472)), (187/137438953472), by norm_num⟩
  | 3 => ⟨((-55305380429/274877906944), (-64039531203/274877906944)), (161/137438953472), by norm_num⟩
  | 4 => ⟨((35463874999/274877906944), (41064538603/274877906944)), (13/17179869184), by norm_num⟩
  | 5 => ⟨((-36385217357/549755813888), (-21065692381/274877906944)), (215/549755813888), by norm_num⟩
  | 6 => ⟨((31108746627/1099511627776), (72043245517/2199023255552)), (185/1099511627776), by norm_num⟩
  | 7 => ⟨((-45595634099/4398046511104), (-52796364657/4398046511104)), (273/4398046511104), by norm_num⟩
  | 8 => ⟨((58475246193/17592186044416), (33855000401/8796093022208)), (11/549755813888), by norm_num⟩
  | 9 => ⟨((-520784879/549755813888), (-4824242307/4398046511104)), (101/17592186044416), by norm_num⟩
  | 10 => ⟨((8549035781/35184372088832), (19798299529/70368744177664)), (209/140737488355328), by norm_num⟩
  | 11 => ⟨((-3986880697/70368744177664), (-36932098659/562949953421312)), (49/140737488355328), by norm_num⟩
  | 12 => ⟨((54539451105/4503599627370496), (63152641817/4503599627370496)), (169/2251799813685248), by norm_num⟩
  | 13 => ⟨((-21521681549/9007199254740992), (-3115064001/1125899906842624)), (269/18014398509481984), by norm_num⟩
  | 14 => ⟨((7886003323/18014398509481984), (36525629293/72057594037927936)), (397/144115188075855872), by norm_num⟩
  | 15 => ⟨((-5393919775/72057594037927936), (-49966074339/576460752303423488)), (137/288230376151711744), by norm_num⟩
  | 16 => ⟨((55340524245/4611686018427387904), (4005014071/288230376151711744)), (177/2305843009213693952), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (1118229619241/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444638993825997/158456325028528675187087900672), (1323065984331/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889502499236133/39614081257132168796771975168), (1488162123653/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472315667469481/618970019642690137449562112), (1580815475165/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770928983203111/154742504910672534362390528), (395103562121/38685626227668133590597632)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549308145484123/9671406556917033397649408), (1481212191609/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78660883217267/37778931862957161709568), (323908663867/151115727451828646838272)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471860881183637/18889465931478580854784), (65768995929/2361183241434822606848)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648639086915801/2361183241434822606848), (788878794931/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810544517329769/295147905179352825856), (2168282541723/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911513018228429/36893488147419103232), (677163258353/18446744073709551616)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113884537091173/576460752303423488), (380612338375/1152921504606846976)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593401536905933/1152921504606846976), (3041981373529/1152921504606846976)), (6681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298517492768157/36028797018963968), (664613822117/36028797018963968)), (5849/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490872196401887/36028797018963968), (3981135062853/36028797018963968)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488302892627553/9007199254740992), (4964980181661/9007199254740992)), (10983/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226043655225565/4503599627370496), (4947862392877/2251799813685248)), (21995/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213259954485115/2251799813685248), (7379139442471/1125899906842624)), (16533/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087548381338695/1125899906842624), (29177003540043/2251799813685248)), (66431/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087548381338695/1125899906842624), (29177003540043/2251799813685248)), (253414162642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2100628395440157/2251799813685248), (14091573673397/562949953421312)), (130059/2251799813685248), by norm_num⟩
  | 2 => ⟨((122387169747329/140737488355328), (13145555663907/281474976710656)), (15573/140737488355328), by norm_num⟩
  | 3 => ⟨((424490108069145/562949953421312), (45726191969537/562949953421312)), (228317/1125899906842624), by norm_num⟩
  | 4 => ⟨((19773179451179/35184372088832), (275837183078511/2251799813685248)), (190707/562949953421312), by norm_num⟩
  | 5 => ⟨((1354793876128327/4503599627370496), (155017065717377/1125899906842624)), (2088575/4503599627370496), by norm_num⟩
  | 6 => ⟨((644365359370983/9007199254740992), (186531831162715/2251799813685248)), (57241/140737488355328), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-21695747307/268435456)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-611009281/268435456), (-5580648287/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((173729931052039/18014398509481984), (-920725361485411/9007199254740992)), (4527993/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6995899169/274877906944), (74153046075/274877906944)), (367/274877906944), by norm_num⟩
  | 2 => ⟨((4615644745/137438953472), (-97847069879/274877906944)), (243/137438953472), by norm_num⟩
  | 3 => ⟨((-8120634063/274877906944), (86074675649/274877906944)), (215/137438953472), by norm_num⟩
  | 4 => ⟨((10715409423/549755813888), (-113578001833/549755813888)), (285/274877906944), by norm_num⟩
  | 5 => ⟨((-11311431911/1099511627776), (119895543289/1099511627776)), (151/274877906944), by norm_num⟩
  | 6 => ⟨((2487626441/549755813888), (-52735202051/1099511627776)), (267/1099511627776), by norm_num⟩
  | 7 => ⟨((-3751422167/2199023255552), (79526412287/4398046511104)), (405/4398046511104), by norm_num⟩
  | 8 => ⟨((4950109083/8796093022208), (-52468690311/8796093022208)), (537/17592186044416), by norm_num⟩
  | 9 => ⟨((-2903027035/17592186044416), (30770640387/17592186044416)), (633/70368744177664), by norm_num⟩
  | 10 => ⟨((1532250955/35184372088832), (-8120548405/17592186044416)), (21/8796093022208), by norm_num⟩
  | 11 => ⟨((-11763485421/1125899906842624), (124687085317/1125899906842624)), (81/140737488355328), by norm_num⟩
  | 12 => ⟨((10348170807/4503599627370496), (-6855340967/281474976710656)), (573/4503599627370496), by norm_num⟩
  | 13 => ⟨((-2100724309/4503599627370496), (44533262341/9007199254740992)), (467/18014398509481984), by norm_num⟩
  | 14 => ⟨((3167961077/36028797018963968), (-33578809255/36028797018963968)), (177/36028797018963968), by norm_num⟩
  | 15 => ⟨((-139340515/9007199254740992), (94524162863/576460752303423488)), (501/576460752303423488), by norm_num⟩
  | 16 => ⟨((5883641719/2305843009213693952), (-124727342415/4611686018427387904)), (83/576460752303423488), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-1923606611231/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889227815897227/316912650057057350374175801344), (-568932778989/158456325028528675187087900672)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889389532031711/39614081257132168796771975168), (-1279843767585/19807040628566084398385987584)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236142816794145/309485009821345068724781056), (-1359518161125/1237940039285380274899124224)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885404363228379/77371252455336267181195264), (-2718325915333/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774597638044687/4835703278458516698824704), (-636918991127/2417851639229258349412352)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157309405272081/75557863725914323419136), (-278557767789/75557863725914323419136)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887282588782593/75557863725914323419136), (-1809918579715/37778931862957161709568)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((162144657672295/590295810358705651712), (-678410328973/1180591620717411303424)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810461219225855/295147905179352825856), (-932312105625/147573952589676412928)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911408639812579/36893488147419103232), (-4658549719573/73786976294838206464)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455479259979603/2305843009213693952), (-654591431287/1152921504606846976)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593165107692197/1152921504606846976), (-2615782266829/576460752303423488)), (6697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193862113065461/144115188075855872), (-142869128521/4503599627370496)), (5865/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490558451206947/36028797018963968), (-855764908105/4503599627370496)), (8807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487907299366237/9007199254740992), (-4268692136509/4503599627370496)), (11025/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225242293448787/4503599627370496), (-8507053520511/2251799813685248)), (5525/1125899906842624), by norm_num⟩
  | 1 => ⟨((276504085386509/281474976710656), (-25369971215469/2251799813685248)), (16639/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086271277667699/1125899906842624), (-50137965148475/2251799813685248)), (67069/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086271277667699/1125899906842624), (-50137965148475/2251799813685248)), (255847939498137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094958579587761/2251799813685248), (-96746488973829/2251799813685248)), (33101/562949953421312), by norm_num⟩
  | 2 => ⟨((1944884949560513/2251799813685248), (-180015901847877/2251799813685248)), (128871/1125899906842624), by norm_num⟩
  | 3 => ⟨((416352701438793/562949953421312), (-155480170154431/1125899906842624)), (486435/2251799813685248), by norm_num⟩
  | 4 => ⟨((1188780993058231/2251799813685248), (-229983459348519/1125899906842624)), (853875/2251799813685248), by norm_num⟩
  | 5 => ⟨((133407805154125/562949953421312), (-971311796118711/4503599627370496)), (39075/70368744177664), by norm_num⟩
  | 6 => ⟨((173729931052039/18014398509481984), (-920725361485411/9007199254740992)), (4527993/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5580648287/67108864)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-2507931583/1073741824), (-91624690657/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-190215813199827/2251799813685248), (424737981995769/9007199254740992)), (4916565/9007199254740992), by norm_num⟩
  | 1 => ⟨((15720030859/68719476736), (-17550838891/137438953472)), (51/34359738368), by norm_num⟩
  | 2 => ⟨((-42570632729/137438953472), (11882138197/68719476736)), (555/274877906944), by norm_num⟩
  | 3 => ⟨((76855607015/274877906944), (-42903235645/274877906944)), (503/274877906944), by norm_num⟩
  | 4 => ⟨((-13008052627/68719476736), (29046028979/274877906944)), (171/137438953472), by norm_num⟩
  | 5 => ⟨((14090583813/137438953472), (-31463241847/549755813888)), (93/137438953472), by norm_num⟩
  | 6 => ⟨((-25438672219/549755813888), (28401346137/1099511627776)), (337/1099511627776), by norm_num⟩
  | 7 => ⟨((78730515907/4398046511104), (-21974934605/2199023255552)), (131/1099511627776), by norm_num⟩
  | 8 => ⟨((-53301547359/8796093022208), (14877306519/4398046511104)), (357/8796093022208), by norm_num⟩
  | 9 => ⟨((32076281343/17592186044416), (-17905996849/17592186044416)), (27/2199023255552), by norm_num⟩
  | 10 => ⟨((-69491344113/140737488355328), (19396135347/70368744177664)), (235/70368744177664), by norm_num⟩
  | 11 => ⟨((68431290327/562949953421312), (-19100257537/281474976710656)), (465/562949953421312), by norm_num⟩
  | 12 => ⟨((-15442947461/562949953421312), (34482970843/2251799813685248)), (211/1125899906842624), by norm_num⟩
  | 13 => ⟨((25735555063/4503599627370496), (-14366402481/4503599627370496)), (353/9007199254740992), by norm_num⟩
  | 14 => ⟨((-39824671465/36028797018963968), (22231393787/36028797018963968)), (549/72057594037927936), by norm_num⟩
  | 15 => ⟨((28759255885/144115188075855872), (-16054328111/144115188075855872)), (399/288230376151711744), by norm_num⟩
  | 16 => ⟨((-77881508683/2305843009213693952), (43475926469/2305843009213693952)), (543/2305843009213693952), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (3429061992823/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778357892217939/633825300114114700748351602688), (4056368075231/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889279259895483/39614081257132168796771975168), (570308406771/4951760157141521099596496896)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944512476345825/1237940039285380274899124224), (4846464352027/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110668167220931/9671406556917033397649408), (4845162807595/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48408878285461/302231454903657293676544), (4540957528949/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78648591862273/37778931862957161709568), (3971955557937/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887122776191897/75557863725914323419136), (6451836693965/75557863725914323419136)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297036586914011/4722366482869645213696), (302288187877/295147905179352825856)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202594398540693/73786976294838206464), (6646658336327/590295810358705651712)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822606235784601/73786976294838206464), (8302802481403/73786976294838206464)), (373/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821676896218093/9223372036854775808), (9333065855965/9223372036854775808)), (105/144115188075855872), by norm_num⟩
  | 6 => ⟨((199115196484989/144115188075855872), (9323587690739/1152921504606846976)), (841/144115188075855872), by norm_num⟩
  | 5 => ⟨((149205651608945/18014398509481984), (1018435483197/18014398509481984)), (5895/144115188075855872), by norm_num⟩
  | 4 => ⟨((745112756291539/18014398509481984), (3049983502945/9007199254740992)), (2215/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487477901266407/9007199254740992), (475396860481/281474976710656)), (11105/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112172020671287/2251799813685248), (3789239483677/562949953421312)), (5575/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105293713932615/1125899906842624), (22596382018971/1125899906842624)), (8419/562949953421312), by norm_num⟩
  | 0 => ⟨((1084632547458089/1125899906842624), (44638341821239/1125899906842624)), (17067/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084632547458089/1125899906842624), (44638341821239/1125899906842624)), (65105440379905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((521553991747969/562949953421312), (21501111293121/281474976710656)), (68473/1125899906842624), by norm_num⟩
  | 2 => ⟨((59989652170441/70368744177664), (318720777327843/2251799813685248)), (274675/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591413949264881/2251799813685248), (543421622620311/2251799813685248)), (546079/2251799813685248), by norm_num⟩
  | 4 => ⟨((993556924725937/2251799813685248), (48006529339013/140737488355328)), (1035429/2251799813685248), by norm_num⟩
  | 5 => ⟨((176379305259563/2251799813685248), (1355636517724725/4503599627370496)), (1620105/2251799813685248), by norm_num⟩
  | 6 => ⟨((-190215813199827/2251799813685248), (424737981995769/9007199254740992)), (4916565/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-91624690657/1073741824)), (1/536870912), by norm_num⟩, -14, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile063Terms1
