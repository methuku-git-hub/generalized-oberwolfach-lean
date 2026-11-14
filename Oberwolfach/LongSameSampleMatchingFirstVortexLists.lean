module

public import Oberwolfach.LongSameSampleMatchingListsDeletion
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! Specialize the common-deletion continuation to the first actual vortex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_same_sample_matching_and_first_vortex_lists
    {n:ℕ} {U:Type} [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (hε:0≤ε)
    (Ω:Type) (mass:Ω→ℝ) (Good:Ω→Prop)
    (Match:Ω→SimpleGraph (Fin n)→ℝ→Prop)
    (Lists:Ω→SimpleGraph (Fin n)→Finset (Fin n)→Prop)
    (Δ ζ:ℝ) (hζΔ:ζ≤Δ)
    (hSample:∃z,0<mass z ∧ Good z ∧
      (∀(Del:SimpleGraph (Fin n)) (δ:ℝ),(∀x,(Del.degree x:ℝ)≤δ)→δ≤Δ*n→Match z Del δ) ∧
      (∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
        ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤ε*n→Lists z Del Inner)):
    ∃z,0<mass z ∧ Good z ∧
      ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
        Match z Del (ζ*n) ∧ Lists z Del (Q.extendedVertices 1) := by
  obtain ⟨z,hm,hgood,hBoth⟩:=long_same_sample_matching_and_lists_after_deletion n Ω mass Good Match Lists Δ ζ ε hζΔ hSample
  refine ⟨z,hm,hgood,?_⟩
  intro Del hDel
  obtain ⟨hMatch,hLists⟩:=hBoth Del hDel
  have hInner:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_upper hε
  exact ⟨hMatch,hLists (Q.extendedVertices 1) hInner⟩
end Oberwolfach
