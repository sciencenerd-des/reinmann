/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RectangleTileRules

noncomputable section
namespace Reinmann.XiBand58.Data
open CertifiedTaylorModel
def count : ℕ := 9
def degree : ℕ := 16

def coordinate (i:Fin count) : QComplex :=
  match i.val with
  | 0 => ((15/16), (4561/320))
  | 1 => ((15/16), (4659/320))
  | 2 => ((15/16), (2403/160))
  | 3 => ((15/16), (2501/160))
  | 4 => ((15/16), (2599/160))
  | 5 => ((15/16), (2697/160))
  | 6 => ((15/16), (559/32))
  | 7 => ((15/16), (2893/160))
  | 8 => ((15/16), (2991/160))
  | _ => (0,0)

def radius (i:Fin count) : ℚ :=
  match i.val with
  | 0 => (173423/1048576)
  | 1 => (173423/1048576)
  | 2 => (163873/524288)
  | 3 => (163873/524288)
  | 4 => (163873/524288)
  | 5 => (163873/524288)
  | 6 => (163873/524288)
  | 7 => (163873/524288)
  | 8 => (163873/524288)
  | _ => 0

def centre (i:Fin count) : ℂ := value (coordinate i)
theorem centre_mem_quarter (i:Fin count) : centre i ∈ XiAdaptiveTiles.quarter 32 := by
  fin_cases i <;> norm_num [centre,coordinate,count,value,XiAdaptiveTiles.quarter]
end Reinmann.XiBand58.Data
