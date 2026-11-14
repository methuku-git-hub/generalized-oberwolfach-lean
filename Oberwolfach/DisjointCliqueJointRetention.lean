module

public import Oberwolfach.CliqueTupleApproximation

@[expose] public section

/-! Joint clique-retention estimates in the equalized colouring law. The
cliques here have disjoint vertex sets; the cost of making this restriction
is handled separately by DisjointCliqueRestrictions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_clique_joint_retention
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K B s A : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (T : J → Finset V) (hT : ∀ j,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (hdis : ∀ i j,i≠j → Disjoint (T i) (T j))
    (hsize : ∀ j,(T j).card≤s)
    (hcross : ∀ i j,i≠j → ∀ v∈T i,((T j).filter (G.Adj v)).card≤A)
    (c : C) (hc : ∀ j,∀ v∈T j,c∈L v)
    (hbound : ∀ v,c∈L v → (colourNeighbourSet G L v c).card≤K)
    (hpair : ∀ u v,u≠v → ¬G.Adj u v →
      (colourNeighbourSet G L u c∩colourNeighbourSet G L v c).card≤B)
    (hsmall : 2*((Fintype.card J)^2*B)≤l) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega) K u))
    let b := (((1-1/(l : ℝ))^K)/(l : ℝ))^(Fintype.card J)
    |μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      (∏ j,((T j).card : ℝ))*b|≤
      (∏ j,((T j).card : ℝ))*(2*(((Fintype.card J)^2*B : ℕ) : ℝ)/(l : ℝ))*b+
        (((Fintype.card J)^2*A*s^(Fintype.card J-1) : ℕ) : ℝ)*b := by
  classical
  dsimp only
  apply clique_tuple_approximation G T hT _ c hsize hcross
  · have hlr : (1 : ℝ)≤l := by exact_mod_cast (show 1≤l by omega)
    have hq : 0≤1-1/(l : ℝ) := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hlr)
    exact pow_nonneg (div_nonneg (pow_nonneg hq _) (Nat.cast_nonneg _)) _
  · positivity
  · intro f hgood
    have hfi : Function.Injective (fun j=>(f j).val) := by
      intro i j he
      by_contra hij
      apply Finset.disjoint_left.mp (hdis i j hij) (f i).property
      change (f i).val=(f j).val at he
      rw [he]
      exact (f j).property
    exact equalized_tuple_retention_bounds G L hL hl hcard (fun j=>(f j).val) hfi hgood c
      (fun j=>hc j (f j).val (f j).property)
      (fun j=>hbound (f j).val (hc j (f j).val (f j).property))
      (fun i j hij=>hpair (f i).val (f j).val (fun he=>hij (hfi he)) (hgood i j)) hsmall

end Oberwolfach
