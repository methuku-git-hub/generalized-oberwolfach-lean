module

public import Oberwolfach.MarkedWheels
public import Oberwolfach.Neighbourhoods
public import Oberwolfach.BipartiteIntersectionEstimates

@[expose] public section

/-! Compatible-hub estimates for any fixed vertex tuple. Its rim edges
need not belong to either of the two hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}

def potentialMarkedHubs (H : Bool → V → U → Prop) (C : Fin (m+1) → V) : Finset U :=
  common Finset.univ Finset.univ (fun i=>Finset.univ.filter (fun u=>H (decide (i=0)) (C i) u))

theorem potentialMarkedHubs_mem (H : Bool → V → U → Prop) (C : Fin (m+1) → V) (u : U) :
    u∈potentialMarkedHubs H C ↔ MarkedHubCompatible (H false) (H true) C u := by
  simp only [potentialMarkedHubs,common,Finset.mem_filter,Finset.mem_univ,true_and,true_implies]
  constructor
  · intro h
    refine ⟨?_,fun i=>?_⟩
    · simpa only [decide_true] using h 0
    · simpa only [Fin.succ_ne_zero,decide_false] using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j=>?_) i
    · simpa only [decide_true] using h.1
    · simpa only [Fin.succ_ne_zero,decide_false] using h.2 j

theorem potentialMarkedHubs_change (H H' : Bool → V → U → Prop)
    (C : Fin (m+1) → V) (d : ℝ)
    (hd : ∀ j v,(∑ u,bipAdj (fun v u=>¬(H j v u↔H' j v u)) v u)≤d) :
    |((potentialMarkedHubs H' C).card:ℝ)-(potentialMarkedHubs H C).card|≤((m:ℝ)+1)*d := by
  have hh := neighbourhood_stability (Finset.univ : Finset U) (Finset.univ : Finset (Fin (m+1)))
    (fun i=>Finset.univ.filter (fun u=>H (decide (i=0)) (C i) u))
    (fun i=>Finset.univ.filter (fun u=>H' (decide (i=0)) (C i) u)) d (by
      intro i _
      have he : changed (Finset.univ.filter (fun u=>H (decide (i=0)) (C i) u))
          (Finset.univ.filter (fun u=>H' (decide (i=0)) (C i) u))=
            Finset.univ.filter (fun u=>¬(H (decide (i=0)) (C i) u↔H' (decide (i=0)) (C i) u)) := by
        ext u
        simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      rw [he]
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      convert hd (decide (i=0)) (C i) using 1 <;> simp only [bipAdj] <;> congr!)
  simpa only [potentialMarkedHubs,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hh

theorem potentialMarkedHubs_mono (H H' : Bool → V → U → Prop)
    (hsub : ∀ j v u,H' j v u → H j v u) (C : Fin (m+1) → V) :
    potentialMarkedHubs H' C⊆potentialMarkedHubs H C := by
  intro u hu
  rw [potentialMarkedHubs_mem] at hu ⊢
  exact ⟨hsub true _ _ hu.1,fun i=>hsub false _ _ (hu.2 i)⟩

theorem potentialMarkedHubs_deletion (H H' : Bool → V → U → Prop)
    (hsub : ∀ j v u,H' j v u → H j v u) (C : Fin (m+1) → V) (d : ℝ)
    (hd : ∀ j v,(∑ u,bipAdj (fun v u=>¬(H j v u↔H' j v u)) v u)≤d) :
    0≤((potentialMarkedHubs H C).card:ℝ)-(potentialMarkedHubs H' C).card ∧
      ((potentialMarkedHubs H C).card:ℝ)-(potentialMarkedHubs H' C).card≤((m:ℝ)+1)*d := by
  constructor
  · apply sub_nonneg.mpr
    exact_mod_cast Finset.card_le_card (potentialMarkedHubs_mono H H' hsub C)
  · have hh := potentialMarkedHubs_change H H' C d hd
    rw [abs_sub_comm] at hh
    exact (le_abs_self _).trans hh

end Oberwolfach
