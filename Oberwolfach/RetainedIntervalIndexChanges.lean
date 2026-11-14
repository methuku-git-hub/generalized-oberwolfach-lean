module

public import Oberwolfach.RetainedIntervalGeometry
public import Oberwolfach.RawIntervalFamily

@[expose] public section

/-! For a fixed vertex, only d+1 starts can change its retained pair state.
This is a deterministic union over the actual removed hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retainedInterval_index_changes_card
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color) (R : U→V→Γ→Prop)
    (hR : ∀ u a g,R u a g → rawIntervalColouredStart π d (fun e=>σ (u,e)) a g)
    (g₀ : Γ) (hother : ∀ u a g,g≠g₀ → rawIntervalColouredStart π d (fun e=>σ (u,e)) a g → R u a g)
    (x : V) (T : Finset U) :
    (T.filter (fun u=>retainedIntervalState π d (fun e=>σ (u,e)) (R u) x≠rawIntervalFamilyState π d σ (x,u))).card≤
    ∑ a∈permutationWindow π d 0 x,
      (T.filter (fun u=>rawIntervalColouredStart π d (fun e=>σ (u,e)) a g₀ ∧ ¬R u a g₀)).card := by
  let A := permutationWindow π d 0 x
  let D := fun a=>T.filter (fun u=>rawIntervalColouredStart π d (fun e=>σ (u,e)) a g₀ ∧ ¬R u a g₀)
  have hsub : T.filter (fun u=>retainedIntervalState π d (fun e=>σ (u,e)) (R u) x≠rawIntervalFamilyState π d σ (x,u))⊆A.biUnion D := by
    intro u hu
    obtain ⟨huT,hu⟩ := Finset.mem_filter.mp hu
    obtain ⟨a,ha,hn,hxa⟩ := retainedIntervalState_change_selected π d (fun e=>σ (u,e)) (R u)
      (hR u) g₀ (hother u) x hu
    exact Finset.mem_biUnion.mpr ⟨a,(permutationWindow_dual π 0 d a x).mp hxa,
      Finset.mem_filter.mpr ⟨huT,ha,hn⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

end Oberwolfach
