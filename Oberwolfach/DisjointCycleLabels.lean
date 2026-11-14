module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Ordered labels of vertex-disjoint resources are jointly injective.
Exact coverage gives one occurrence of every covered vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [DecidableEq V] [DecidableEq C] {c : ℕ}

theorem disjoint_resource_tuple_injective (R : C → Finset V) (f : C → Fin c → V)
    (hf : ∀ C₀,Function.Injective (f C₀)) (hmem : ∀ C₀ i,f C₀ i∈R C₀)
    (M : Finset C) (hM : ∀ C₀∈M,∀ C₁∈M,C₀≠C₁ → Disjoint (R C₀) (R C₁)) :
    Function.Injective (fun p : M×Fin c => f p.1.val p.2) := by
  rintro ⟨C₀,i⟩ ⟨C₁,j⟩ he
  have hC : C₀=C₁ := by
    apply Subtype.ext
    by_contra hne
    have hv : f C₀.val i∈R C₁.val := by
      change f C₀.val i=f C₁.val j at he
      rw [he]
      exact hmem C₁.val j
    exact Finset.disjoint_left.mp (hM _ C₀.property _ C₁.property hne) (hmem _ _) hv
  subst C₁
  exact Prod.ext rfl (hf C₀.val he)

theorem resource_factor_vertex_unique (R : C → Finset V) (M : Finset C)
    (hM : ∀ C₀∈M,∀ C₁∈M,C₀≠C₁ → Disjoint (R C₀) (R C₁))
    (v : V) (hv : v∈M.biUnion R) :
    ∃! C₀ : M,v∈R C₀.val := by
  obtain ⟨C₀,hC₀,hv₀⟩ := Finset.mem_biUnion.mp hv
  refine ⟨⟨C₀,hC₀⟩,hv₀,?_⟩
  intro C₁ hv₁
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hM _ C₁.property _ hC₀ hne) hv₁ hv₀

end Oberwolfach
