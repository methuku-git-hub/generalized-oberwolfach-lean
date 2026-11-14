module

public import Oberwolfach.BipartiteDeletionEstimates

@[expose] public section

/-! Sparse intersection data persist under degree-controlled deletion, with
exactly the same supplied density profiles and exceptional sets. The two
original ambient cardinalities remain the normalising scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

theorem SparseIntersectionData.deletion {H : A → B → Prop} {p q : B → ℝ} {L δ D : ℝ}
    (h : SparseIntersectionData H p q L δ D) (H' : A → B → Prop)
    (hsub : ∀ x u,H' x u → H x u) (d ρ : ℝ) (hd : 0≤d) (hρ : 0≤ρ)
    (hrow : ∀ x,(∑ u,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d)
    (hcol : ∀ u,(∑ x,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d)
    (hcolScale : 3*d≤ρ*Fintype.card A) (hrowScale : 2*L^2*d≤ρ*Fintype.card B) :
    SparseIntersectionData H' p q L (δ+ρ) D := by
  refine ⟨h.one_le_L,add_nonneg h.delta_nonneg hρ,h.D_nonneg,h.density,h.inverse_bounds,
    h.inverse_identity,?_,?_,?_,?_⟩
  · intro u
    have hloss := bipColumnDegree_deletion H H' hsub u d (hcol u)
    have hbase := h.degree_error u
    have ht := abs_sub_le (bipColumnDegree H' u) (bipColumnDegree H u) ((Fintype.card A:ℝ)*p u)
    nlinarith
  · intro u v huv
    have hloss := bipPairIntersection_deletion H H' hsub v u d hcol
    have hbase := h.pair_error u v huv
    have ht := abs_sub_le (bipPairIntersection H' v u) (bipPairIntersection H v u) ((Fintype.card A:ℝ)*p v*p u)
    nlinarith
  · intro u v t huv hut hvt
    have hloss := bipTripleIntersection_deletion H H' hsub u v t d hcol
    have hbase := h.triple_error u v t huv hut hvt
    have ht := abs_sub_le (bipTripleIntersection H' u v t) (bipTripleIntersection H u v t)
      ((Fintype.card A:ℝ)*p u*p v*p t)
    nlinarith
  · intro x
    obtain ⟨E,hE,hbound⟩ := h.exceptions x
    refine ⟨E,hE,?_⟩
    intro y hy
    have hloss := bipWeightedCodegree_deletion H H' hsub q L d h.inverse_bounds hrow x y
    have hbase := hbound y hy
    have ht := abs_sub_le (bipWeightedCodegree H' q x y) (bipWeightedCodegree H q x y) (Fintype.card B:ℝ)
    nlinarith

end Oberwolfach
