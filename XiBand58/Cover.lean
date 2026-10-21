/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RationalBallCover
import XiBand58.Data

noncomputable section
namespace Reinmann.XiBand58.Cover
open RationalBallCover

private theorem cell4 : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) ((461/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨0,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨0,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell5 : ∀ z ∈ rectangle ((7/8)) (1) ((461/32)) ((1177/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨1,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨1,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell3 : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) ((1177/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell4 cell5

private theorem cell6 : ∀ z ∈ rectangle ((7/8)) (1) ((1177/80)) ((613/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨2,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨2,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell2 : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) ((613/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell3 cell6

private theorem cell8 : ∀ z ∈ rectangle ((7/8)) (1) ((613/40)) ((255/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨3,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨3,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨3,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell9 : ∀ z ∈ rectangle ((7/8)) (1) ((255/16)) ((331/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨4,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨4,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨4,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell7 : ∀ z ∈ rectangle ((7/8)) (1) ((613/40)) ((331/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell8 cell9

private theorem cell1 : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) ((331/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell2 cell7

private theorem cell12 : ∀ z ∈ rectangle ((7/8)) (1) ((331/20)) ((1373/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨5,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨5,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell13 : ∀ z ∈ rectangle ((7/8)) (1) ((1373/80)) ((711/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨6,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨6,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨6,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell11 : ∀ z ∈ rectangle ((7/8)) (1) ((331/20)) ((711/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell12 cell13

private theorem cell15 : ∀ z ∈ rectangle ((7/8)) (1) ((711/40)) ((1471/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨7,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨7,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell16 : ∀ z ∈ rectangle ((7/8)) (1) ((1471/80)) (19),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨8,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨8,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

private theorem cell14 : ∀ z ∈ rectangle ((7/8)) (1) ((711/40)) (19),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell15 cell16

private theorem cell10 : ∀ z ∈ rectangle ((7/8)) (1) ((331/20)) (19),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell11 cell14

private theorem cell0 : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) (19),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell1 cell10

theorem box_covered : ∀ z ∈ rectangle ((7/8)) (1) ((141/10)) (19),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := cell0
end Reinmann.XiBand58.Cover
