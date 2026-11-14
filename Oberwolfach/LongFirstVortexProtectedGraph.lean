module

public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.VortexFirstPairProtectedSize

@[expose] public section
/-! The protected graph of the first vortex set is sparse and supported
inside that set, as needed by protected partition and correction deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_vortex_protected_graph
    {n:ℕ} {U:Type} [Fintype U] {P:SimpleGraph (Fin n)}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)
    (hε:0≤ε) (cap:ℝ) (hcap:ε≤cap):
    let I:=Q.extendedVertices 1
    let Z:=spanningRestriction (⊤:SimpleGraph (Fin n)) I;
    (∀x y,Z.Adj x y→x∈I ∧ y∈I) ∧
    (∀v,(Z.degree v:ℝ)≤cap*n) := by
  intro I Z
  constructor
  · intro x y hxy
    exact ((spanningRestriction_adj ⊤ I x y).mp hxy).2
  · have hsize:(I.card:ℝ)≤cap*n:=by
      simpa only [I,Fintype.card_fin] using (vortex_first_pair_protected_size Q hε cap hcap).1
    intro v
    have hd:Z.degree v≤I.card:=by
      dsimp only [Z]
      rw [spanningRestriction_degree]
      split_ifs with hv
      · exact Finset.card_le_card (Finset.inter_subset_right)
      · exact Nat.zero_le _
    exact (by exact_mod_cast hd : (Z.degree v:ℝ)≤I.card).trans hsize
end Oberwolfach
