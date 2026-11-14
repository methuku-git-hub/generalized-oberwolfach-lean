module

public import Oberwolfach.LongProtectedRegularClassSelection
public import Oberwolfach.VortexFirstPairProtectedSize
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! The first vortex set itself supplies the protected graph required by
the regular-class event, at its original small size scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_vortex_protection_graph
    {n:ℕ} {U:Type} [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ) (β ε α:ℝ)
    (Q:Vortex U G D β ε m) (hε:0≤ε) (hsmall:ε≤α/100000):
    let I:=Q.extendedVertices 1
    let Z:=spanningRestriction (⊤:SimpleGraph (Fin n)) I;
    (∀v,(Z.degree v:ℝ)≤α/100000*n) ∧
    (∀x∈I,∀y∈I,x≠y→Z.Adj x y) := by
  intro I Z
  have hsize:((I.card:ℕ):ℝ)≤ε*n:=by
    simpa only [I,Fintype.card_fin] using Q.first_inner_vertex_size_upper hε
  constructor
  · intro v
    have hdegree:Z.degree v≤I.card:=by
      dsimp [Z]
      rw [spanningRestriction_degree]
      split_ifs
      · exact Finset.card_le_card Finset.inter_subset_right
      · exact Nat.zero_le _
    have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
    have hh:=mul_le_mul_of_nonneg_right hsmall hn
    exact (Nat.cast_le.mpr hdegree).trans (hsize.trans hh)
  · intro x hx y hy hxy
    exact (spanningRestriction_adj (⊤:SimpleGraph (Fin n)) I x y).2 ⟨hxy,hx,hy⟩
end Oberwolfach
