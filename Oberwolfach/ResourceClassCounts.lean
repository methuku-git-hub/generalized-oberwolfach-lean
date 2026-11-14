module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Exact class sizes of a disjoint union. These identities keep the
integer number of factors visible for the later root partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C I : Type*} [DecidableEq V] [DecidableEq C] [DecidableEq I]

theorem resource_biUnion_class_card (R : C → Finset V) (M : Finset C)
    (κ : V → I) (a : I → ℕ)
    (hdisj : ∀ C₀∈M,∀ D∈M,C₀≠D → Disjoint (R C₀) (R D))
    (hR : ∀ C₀∈M,∀ i,((R C₀).filter (fun v => κ v=i)).card=a i) (i : I) :
    ((M.biUnion R).filter (fun v => κ v=i)).card=M.card*a i := by
  have he : (M.biUnion R).filter (fun v => κ v=i)=
      M.biUnion (fun C₀ => (R C₀).filter (fun v => κ v=i)) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_biUnion]
    aesop
  rw [he,Finset.card_biUnion (by
    intro C₀ hC D hD hne
    exact (hdisj C₀ hC D hD hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  calc
    _ = ∑ _C₀∈M,a i := Finset.sum_congr rfl (fun C₀ hC => hR C₀ hC i)
    _ = _ := by simp

theorem resource_leftover_class_card (R : C → Finset V) (M : Finset C)
    (A : Finset V) (κ : V → I) (a : I → ℕ) (k : ℕ)
    (hdisj : ∀ C₀∈M,∀ D∈M,C₀≠D → Disjoint (R C₀) (R D))
    (hR : ∀ C₀∈M,∀ i,((R C₀).filter (fun v => κ v=i)).card=a i)
    (hA : ∀ i,(A.filter (fun v => κ v=i)).card=a i*k)
    (hsub : M.biUnion R⊆A) (hk : M.card ≤ k) (i : I) :
    ((A\M.biUnion R).filter (fun v => κ v=i)).card=a i*(k-M.card) := by
  have he : (A\M.biUnion R).filter (fun v => κ v=i)=
      A.filter (fun v => κ v=i)\(M.biUnion R).filter (fun v => κ v=i) := by
    ext v;simp only [Finset.mem_filter,Finset.mem_sdiff];tauto
  rw [he,Finset.card_sdiff_of_subset (by
    intro v hv
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩),
    hA,resource_biUnion_class_card R M κ a hdisj hR]
  rw [Nat.mul_comm M.card,← Nat.mul_sub_left_distrib]

end Oberwolfach
