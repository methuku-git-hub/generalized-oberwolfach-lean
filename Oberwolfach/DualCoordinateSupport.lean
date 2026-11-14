module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section

/-! Restrict two resource-coordinate families along injections and take
unions. A primitive coordinate can affect at most the sum of the two
original incidence bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {R T E:Type} [Fintype R] [Fintype T] [DecidableEq R] [DecidableEq T] [DecidableEq E]

theorem paired_coordinate_support_bounds
    (S:R→Finset E) (f g:T↪R) (B:ℕ)
    (hread:∀ r,(S r).card≤B)
    (haffect:∀ e,(Finset.univ.filter (fun r=>e∈S r)).card≤B):
    (∀ t,((S (f t))∪(S (g t))).card≤2*B) ∧
    (∀ e,(Finset.univ.filter (fun t=>e∈(S (f t))∪(S (g t)))).card≤2*B):=by
  constructor
  · intro t
    exact (Finset.card_union_le _ _).trans (by have h1:=hread (f t);have h2:=hread (g t);omega)
  · intro e
    let A:=Finset.univ.filter (fun r=>e∈S r)
    let T₁:=Finset.univ.filter (fun t=>e∈S (f t))
    let T₂:=Finset.univ.filter (fun t=>e∈S (g t))
    have h1:T₁.card≤B:=by
      have hsub:T₁.image f⊆A:=by
        intro r hr
        obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩
      calc
        T₁.card=(T₁.image f).card:=(Finset.card_image_of_injective T₁ f.injective).symm
        _≤A.card:=Finset.card_le_card hsub
        _≤B:=haffect e
    have h2:T₂.card≤B:=by
      have hsub:T₂.image g⊆A:=by
        intro r hr
        obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩
      calc
        T₂.card=(T₂.image g).card:=(Finset.card_image_of_injective T₂ g.injective).symm
        _≤A.card:=Finset.card_le_card hsub
        _≤B:=haffect e
    have heq:Finset.univ.filter (fun t=>e∈S (f t)∪S (g t))=T₁∪T₂:=by
      ext t
      simp [T₁,T₂]
    rw [heq]
    exact (Finset.card_union_le _ _).trans (by omega)
end Oberwolfach
