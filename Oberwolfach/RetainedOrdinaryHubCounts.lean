module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.RawIntervalNeighbourCounts

@[expose] public section
/-! A fixed hub loses at most the realised number of changed labels when
ordinary spokes are recomputed after start retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retained_ordinary_hub_count_lower
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (ζ:ℝ) (good:RetainedRestrictionGood π d σ g₀ t (fun _:Unit=>Finset.univ)
      (fun _:Unit=>Finset.univ) ζ J)
    (g:Γ) (j:Color) (u:U) (s err:ℝ)
    (hraw:|rawIntervalNeighbourCount π d σ j Finset.univ {u}-s*(Fintype.card V:ℝ)|≤err):
    s*(Fintype.card V:ℝ)-err-ζ*(Fintype.card V:ℝ)≤
      ((Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u)).card:ℝ) := by
  let A:Finset V:=Finset.univ.filter (fun v=>rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))
  let B:Finset V:=Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u)
  let C:Finset V:=Finset.univ.filter (fun v=>retainedRawFamilyState π d σ g₀ t J (v,u)≠rawIntervalFamilyState π d σ (v,u))
  have hsub:A⊆B∪C:=by
    intro v hv
    have hvA:rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j):=(Finset.mem_filter.mp hv).2
    by_cases hchange:retainedRawFamilyState π d σ g₀ t J (v,u)≠rawIntervalFamilyState π d σ (v,u)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hchange⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j)
      exact (not_ne_iff.mp hchange).trans hvA
  have hcard:A.card≤B.card+C.card:=(Finset.card_le_card hsub).trans (Finset.card_union_le B C)
  have hc:((C.card:ℕ):ℝ)≤ζ*(Fintype.card V:ℝ):=by simpa [C] using (good ()).1 u
  have hA:rawIntervalNeighbourCount π d σ j Finset.univ {u}=(A.card:ℝ):=by
    unfold rawIntervalNeighbourCount
    simp only [Finset.mem_singleton,forall_eq]
    rw [Finset.sum_boole]
  rw [hA] at hraw
  have hh:((A.card:ℕ):ℝ)≤(B.card:ℝ)+(C.card:ℝ):=by exact_mod_cast hcard
  have hl: -err≤(A.card:ℝ)-s*(Fintype.card V:ℝ):=(abs_le.mp hraw).1
  change _≤(B.card:ℝ)
  linarith
end Oberwolfach
