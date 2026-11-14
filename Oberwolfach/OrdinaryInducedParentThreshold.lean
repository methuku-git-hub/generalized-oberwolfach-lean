module

public import Oberwolfach.InducedSetEmbedding
public import Oberwolfach.OddSharpThreshold

@[expose] public section
/-! The original inner-neighborhood density and ambient conflict degree
bound directly imply their induced-domain versions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ordinary_induced_parent_threshold_from_density
    (P : SimpleGraph V) (A : Finset V) (density α : ℝ)
    (hthreshold : cycleThreshold 3 + α ≤ density)
    (hmin : ∀ v, density*A.card ≤ ((A ∩ P.neighborFinset v).card : ℝ)) :
    ∀ v : {x : V // x ∈ (A : Set V)},
      (cycleThreshold 3 + α)*A.card ≤ (((P.induce (A : Set V)).degree v) : ℝ) := by
  intro v
  have h := (mul_le_mul_of_nonneg_right hthreshold (by positivity : (0:ℝ)≤A.card)).trans (hmin v.val)
  have he := induced_degree_intersection P A v
  rw [he]
  simpa only [Finset.inter_comm] using h

theorem ordinary_induced_conflict_degree_from_ambient
    (F : SimpleGraph V) (A : Finset V) (L : ℝ)
    (hF : ∀ v, (F.degree v : ℝ) ≤ L) :
    ∀ v : {x : V // x ∈ (A : Set V)}, (((F.induce (A : Set V)).degree v) : ℝ) ≤ L := by
  intro v
  have hh := induced_degree_le_ambient F A v
  have hr : (((F.induce (A : Set V)).degree v) : ℝ) ≤ F.degree v.val := by exact_mod_cast hh
  exact hr.trans (hF v.val)
end Oberwolfach
