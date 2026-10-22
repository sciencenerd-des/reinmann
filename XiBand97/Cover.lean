/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RationalBallCover
import XiBand97.Data

noncomputable section
namespace Reinmann.XiBand97.Cover
open RationalBallCover

private theorem cell6 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((9203/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨0,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨0,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell7 : ∀ z ∈ rectangle ((29/40)) (1) ((9203/640)) ((4691/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨1,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨1,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell5 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((4691/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell6 cell7

private theorem cell8 : ∀ z ∈ rectangle ((29/40)) (1) ((4691/320)) ((487/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨2,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨2,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell4 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((487/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell5 cell8

private theorem cell10 : ∀ z ∈ rectangle ((29/40)) (1) ((487/32)) ((5049/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨3,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨3,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨3,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell11 : ∀ z ∈ rectangle ((29/40)) (1) ((5049/320)) ((1307/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨4,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨4,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨4,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell9 : ∀ z ∈ rectangle ((29/40)) (1) ((487/32)) ((1307/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell10 cell11

private theorem cell3 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((1307/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell4 cell9

private theorem cell14 : ∀ z ∈ rectangle ((29/40)) (1) ((1307/80)) ((5407/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨5,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨5,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell15 : ∀ z ∈ rectangle ((29/40)) (1) ((5407/320)) ((2793/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨6,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨6,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨6,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell13 : ∀ z ∈ rectangle ((29/40)) (1) ((1307/80)) ((2793/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell14 cell15

private theorem cell17 : ∀ z ∈ rectangle ((29/40)) (1) ((2793/160)) ((1153/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨7,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨7,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell18 : ∀ z ∈ rectangle ((29/40)) (1) ((1153/64)) ((743/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨8,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨8,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell16 : ∀ z ∈ rectangle ((29/40)) (1) ((2793/160)) ((743/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell17 cell18

private theorem cell12 : ∀ z ∈ rectangle ((29/40)) (1) ((1307/80)) ((743/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell13 cell16

private theorem cell2 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((743/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell3 cell12

private theorem cell22 : ∀ z ∈ rectangle ((29/40)) (1) ((743/40)) ((6123/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨9,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨9,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨9,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell24 : ∀ z ∈ rectangle ((29/40)) (1) ((6123/320)) ((2485/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨10,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨10,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨10,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell25 : ∀ z ∈ rectangle ((29/40)) (1) ((2485/128)) ((3151/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨11,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨11,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨11,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell23 : ∀ z ∈ rectangle ((29/40)) (1) ((6123/320)) ((3151/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell24 cell25

private theorem cell21 : ∀ z ∈ rectangle ((29/40)) (1) ((743/40)) ((3151/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell22 cell23

private theorem cell28 : ∀ z ∈ rectangle ((29/40)) (1) ((3151/160)) ((12783/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨12,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨12,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨12,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell29 : ∀ z ∈ rectangle ((29/40)) (1) ((12783/640)) ((6481/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨13,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨13,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨13,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell27 : ∀ z ∈ rectangle ((29/40)) (1) ((3151/160)) ((6481/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell28 cell29

private theorem cell31 : ∀ z ∈ rectangle ((29/40)) (1) ((6481/320)) ((13141/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨14,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨14,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨14,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell32 : ∀ z ∈ rectangle ((29/40)) (1) ((13141/640)) ((333/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨15,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨15,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨15,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell30 : ∀ z ∈ rectangle ((29/40)) (1) ((6481/320)) ((333/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell31 cell32

private theorem cell26 : ∀ z ∈ rectangle ((29/40)) (1) ((3151/160)) ((333/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell27 cell30

private theorem cell20 : ∀ z ∈ rectangle ((29/40)) (1) ((743/40)) ((333/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell21 cell26

private theorem cell37 : ∀ z ∈ rectangle ((29/40)) (1) ((333/16)) ((26819/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨16,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨16,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨16,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell38 : ∀ z ∈ rectangle ((29/40)) (1) ((26819/1280)) ((13499/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨17,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨17,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨17,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell36 : ∀ z ∈ rectangle ((29/40)) (1) ((333/16)) ((13499/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell37 cell38

private theorem cell39 : ∀ z ∈ rectangle ((29/40)) (1) ((13499/640)) ((6839/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨18,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨18,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨18,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell35 : ∀ z ∈ rectangle ((29/40)) (1) ((333/16)) ((6839/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell36 cell39

private theorem cell41 : ∀ z ∈ rectangle ((29/40)) (1) ((6839/320)) ((13857/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨19,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨19,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨19,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell42 : ∀ z ∈ rectangle ((29/40)) (1) ((13857/640)) ((3509/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨20,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨20,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨20,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell40 : ∀ z ∈ rectangle ((29/40)) (1) ((6839/320)) ((3509/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell41 cell42

private theorem cell34 : ∀ z ∈ rectangle ((29/40)) (1) ((333/16)) ((3509/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell35 cell40

private theorem cell45 : ∀ z ∈ rectangle ((29/40)) (1) ((3509/160)) ((2843/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨21,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨21,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨21,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell46 : ∀ z ∈ rectangle ((29/40)) (1) ((2843/128)) ((7197/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨22,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨22,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨22,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell44 : ∀ z ∈ rectangle ((29/40)) (1) ((3509/160)) ((7197/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell45 cell46

private theorem cell48 : ∀ z ∈ rectangle ((29/40)) (1) ((7197/320)) ((14573/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨23,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨23,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨23,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell49 : ∀ z ∈ rectangle ((29/40)) (1) ((14573/640)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨24,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨24,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨24,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell47 : ∀ z ∈ rectangle ((29/40)) (1) ((7197/320)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell48 cell49

private theorem cell43 : ∀ z ∈ rectangle ((29/40)) (1) ((3509/160)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell44 cell47

private theorem cell33 : ∀ z ∈ rectangle ((29/40)) (1) ((333/16)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell34 cell43

private theorem cell19 : ∀ z ∈ rectangle ((29/40)) (1) ((743/40)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell20 cell33

private theorem cell1 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) ((461/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell2 cell19

private theorem cell55 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) ((14931/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨25,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨25,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨25,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell56 : ∀ z ∈ rectangle ((29/40)) (1) ((14931/640)) ((1511/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨26,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨26,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨26,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell54 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) ((1511/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell55 cell56

private theorem cell58 : ∀ z ∈ rectangle ((29/40)) (1) ((1511/64)) ((15289/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨27,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨27,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨27,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell59 : ∀ z ∈ rectangle ((29/40)) (1) ((15289/640)) ((3867/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨28,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨28,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨28,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell57 : ∀ z ∈ rectangle ((29/40)) (1) ((1511/64)) ((3867/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell58 cell59

private theorem cell53 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) ((3867/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell54 cell57

private theorem cell62 : ∀ z ∈ rectangle ((29/40)) (1) ((3867/160)) ((15647/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨29,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨29,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨29,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell63 : ∀ z ∈ rectangle ((29/40)) (1) ((15647/640)) ((7913/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨30,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨30,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨30,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell61 : ∀ z ∈ rectangle ((29/40)) (1) ((3867/160)) ((7913/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell62 cell63

private theorem cell66 : ∀ z ∈ rectangle ((29/40)) (1) ((7913/320)) ((31831/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨31,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨31,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨31,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell67 : ∀ z ∈ rectangle ((29/40)) (1) ((31831/1280)) ((3201/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨32,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨32,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨32,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell65 : ∀ z ∈ rectangle ((29/40)) (1) ((7913/320)) ((3201/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell66 cell67

private theorem cell68 : ∀ z ∈ rectangle ((29/40)) (1) ((3201/128)) ((2023/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨33,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨33,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨33,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell64 : ∀ z ∈ rectangle ((29/40)) (1) ((7913/320)) ((2023/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell65 cell68

private theorem cell60 : ∀ z ∈ rectangle ((29/40)) (1) ((3867/160)) ((2023/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell61 cell64

private theorem cell52 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) ((2023/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell53 cell60

private theorem cell72 : ∀ z ∈ rectangle ((29/40)) (1) ((2023/80)) ((16363/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨34,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨34,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨34,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell73 : ∀ z ∈ rectangle ((29/40)) (1) ((16363/640)) ((8271/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨35,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨35,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨35,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell71 : ∀ z ∈ rectangle ((29/40)) (1) ((2023/80)) ((8271/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell72 cell73

private theorem cell75 : ∀ z ∈ rectangle ((29/40)) (1) ((8271/320)) ((16721/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨36,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨36,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨36,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell76 : ∀ z ∈ rectangle ((29/40)) (1) ((16721/640)) ((845/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨37,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨37,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨37,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell74 : ∀ z ∈ rectangle ((29/40)) (1) ((8271/320)) ((845/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell75 cell76

private theorem cell70 : ∀ z ∈ rectangle ((29/40)) (1) ((2023/80)) ((845/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell71 cell74

private theorem cell79 : ∀ z ∈ rectangle ((29/40)) (1) ((845/32)) ((17079/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨38,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨38,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨38,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell80 : ∀ z ∈ rectangle ((29/40)) (1) ((17079/640)) ((8629/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨39,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨39,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨39,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell78 : ∀ z ∈ rectangle ((29/40)) (1) ((845/32)) ((8629/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell79 cell80

private theorem cell82 : ∀ z ∈ rectangle ((29/40)) (1) ((8629/320)) ((17437/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨40,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨40,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨40,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell83 : ∀ z ∈ rectangle ((29/40)) (1) ((17437/640)) ((1101/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨41,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨41,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨41,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell81 : ∀ z ∈ rectangle ((29/40)) (1) ((8629/320)) ((1101/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell82 cell83

private theorem cell77 : ∀ z ∈ rectangle ((29/40)) (1) ((845/32)) ((1101/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell78 cell81

private theorem cell69 : ∀ z ∈ rectangle ((29/40)) (1) ((2023/80)) ((1101/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell70 cell77

private theorem cell51 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) ((1101/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell52 cell69

private theorem cell88 : ∀ z ∈ rectangle ((29/40)) (1) ((1101/40)) ((3559/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨42,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨42,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨42,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell89 : ∀ z ∈ rectangle ((29/40)) (1) ((3559/128)) ((8987/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨43,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨43,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell87 : ∀ z ∈ rectangle ((29/40)) (1) ((1101/40)) ((8987/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell88 cell89

private theorem cell91 : ∀ z ∈ rectangle ((29/40)) (1) ((8987/320)) ((18153/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨44,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨44,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨44,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell92 : ∀ z ∈ rectangle ((29/40)) (1) ((18153/640)) ((4583/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨45,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨45,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨45,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell90 : ∀ z ∈ rectangle ((29/40)) (1) ((8987/320)) ((4583/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell91 cell92

private theorem cell86 : ∀ z ∈ rectangle ((29/40)) (1) ((1101/40)) ((4583/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell87 cell90

private theorem cell95 : ∀ z ∈ rectangle ((29/40)) (1) ((4583/160)) ((18511/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨46,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨46,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨46,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell96 : ∀ z ∈ rectangle ((29/40)) (1) ((18511/640)) ((1869/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨47,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨47,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨47,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell94 : ∀ z ∈ rectangle ((29/40)) (1) ((4583/160)) ((1869/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell95 cell96

private theorem cell98 : ∀ z ∈ rectangle ((29/40)) (1) ((1869/64)) ((18869/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨48,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨48,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨48,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell100 : ∀ z ∈ rectangle ((29/40)) (1) ((18869/640)) ((37917/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨49,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨49,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨49,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell101 : ∀ z ∈ rectangle ((29/40)) (1) ((37917/1280)) ((2381/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨50,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨50,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨50,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell99 : ∀ z ∈ rectangle ((29/40)) (1) ((18869/640)) ((2381/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell100 cell101

private theorem cell97 : ∀ z ∈ rectangle ((29/40)) (1) ((1869/64)) ((2381/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell98 cell99

private theorem cell93 : ∀ z ∈ rectangle ((29/40)) (1) ((4583/160)) ((2381/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell94 cell97

private theorem cell85 : ∀ z ∈ rectangle ((29/40)) (1) ((1101/40)) ((2381/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell86 cell93

private theorem cell106 : ∀ z ∈ rectangle ((29/40)) (1) ((2381/80)) ((7655/256)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨51,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨51,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨51,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell107 : ∀ z ∈ rectangle ((29/40)) (1) ((7655/256)) ((19227/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨52,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨52,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨52,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell105 : ∀ z ∈ rectangle ((29/40)) (1) ((2381/80)) ((19227/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell106 cell107

private theorem cell109 : ∀ z ∈ rectangle ((29/40)) (1) ((19227/640)) ((38633/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨53,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨53,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨53,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell110 : ∀ z ∈ rectangle ((29/40)) (1) ((38633/1280)) ((9703/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨54,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨54,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨54,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell108 : ∀ z ∈ rectangle ((29/40)) (1) ((19227/640)) ((9703/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell109 cell110

private theorem cell104 : ∀ z ∈ rectangle ((29/40)) (1) ((2381/80)) ((9703/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell105 cell108

private theorem cell113 : ∀ z ∈ rectangle ((29/40)) (1) ((9703/320)) ((38991/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨55,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨55,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨55,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell114 : ∀ z ∈ rectangle ((29/40)) (1) ((38991/1280)) ((3917/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨56,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨56,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨56,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell112 : ∀ z ∈ rectangle ((29/40)) (1) ((9703/320)) ((3917/128)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell113 cell114

private theorem cell116 : ∀ z ∈ rectangle ((29/40)) (1) ((3917/128)) ((39349/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨57,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨57,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨57,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell117 : ∀ z ∈ rectangle ((29/40)) (1) ((39349/1280)) ((4941/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨58,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨58,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨58,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell115 : ∀ z ∈ rectangle ((29/40)) (1) ((3917/128)) ((4941/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell116 cell117

private theorem cell111 : ∀ z ∈ rectangle ((29/40)) (1) ((9703/320)) ((4941/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell112 cell115

private theorem cell103 : ∀ z ∈ rectangle ((29/40)) (1) ((2381/80)) ((4941/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell104 cell111

private theorem cell121 : ∀ z ∈ rectangle ((29/40)) (1) ((4941/160)) ((39707/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨59,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨59,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨59,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell122 : ∀ z ∈ rectangle ((29/40)) (1) ((39707/1280)) ((19943/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨60,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨60,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨60,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell120 : ∀ z ∈ rectangle ((29/40)) (1) ((4941/160)) ((19943/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell121 cell122

private theorem cell124 : ∀ z ∈ rectangle ((29/40)) (1) ((19943/640)) ((8013/256)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨61,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨61,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨61,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell125 : ∀ z ∈ rectangle ((29/40)) (1) ((8013/256)) ((10061/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨62,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨62,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨62,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell123 : ∀ z ∈ rectangle ((29/40)) (1) ((19943/640)) ((10061/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell124 cell125

private theorem cell119 : ∀ z ∈ rectangle ((29/40)) (1) ((4941/160)) ((10061/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell120 cell123

private theorem cell128 : ∀ z ∈ rectangle ((29/40)) (1) ((10061/320)) ((40423/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨63,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨63,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨63,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell129 : ∀ z ∈ rectangle ((29/40)) (1) ((40423/1280)) ((20301/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨64,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨64,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨64,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell127 : ∀ z ∈ rectangle ((29/40)) (1) ((10061/320)) ((20301/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell128 cell129

private theorem cell131 : ∀ z ∈ rectangle ((29/40)) (1) ((20301/640)) ((40781/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨65,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨65,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨65,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell132 : ∀ z ∈ rectangle ((29/40)) (1) ((40781/1280)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨66,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨66,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨66,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell130 : ∀ z ∈ rectangle ((29/40)) (1) ((20301/640)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell131 cell132

private theorem cell126 : ∀ z ∈ rectangle ((29/40)) (1) ((10061/320)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell127 cell130

private theorem cell118 : ∀ z ∈ rectangle ((29/40)) (1) ((4941/160)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell119 cell126

private theorem cell102 : ∀ z ∈ rectangle ((29/40)) (1) ((2381/80)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell103 cell118

private theorem cell84 : ∀ z ∈ rectangle ((29/40)) (1) ((1101/40)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell85 cell102

private theorem cell50 : ∀ z ∈ rectangle ((29/40)) (1) ((461/20)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell51 cell84

private theorem cell0 : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell1 cell50

theorem box_covered : ∀ z ∈ rectangle ((29/40)) (1) ((141/10)) (32),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := cell0
end Reinmann.XiBand97.Cover
