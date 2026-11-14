module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Add the prescribed external roots to a dense random neighbourhood
before selecting a bounded induced graph. All roots keep their ambient
degree bounds; the enlargement cost is explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem enlarged_neighbour_density {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (T Z : Finset V) (δ α : ℝ)
    (hnonneg : 0≤δ+α/2)
    (hmargin : (δ+α/2)*(Z.card:ℝ)≤α*(T.card:ℝ)/2)
    (hdeg : ∀ v∈T∪Z,(δ+α)*(T.card:ℝ)≤((P.neighborFinset v∩T).card:ℝ)) :
    ∀ v∈T∪Z,(δ+α/2)*((T∪Z).card:ℝ)≤((P.neighborFinset v∩(T∪Z)).card:ℝ) := by
  intro v hv
  have hc : ((T∪Z).card:ℝ)≤T.card+Z.card := by exact_mod_cast Finset.card_union_le T Z
  have hd : ((P.neighborFinset v∩T).card:ℝ)≤(P.neighborFinset v∩(T∪Z)).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left)
  have hm := mul_le_mul_of_nonneg_left hc hnonneg
  nlinarith only [hmargin,hdeg v hv,hd,hm]

theorem enlarged_induced_degree {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (T Z : Finset V) (δ α : ℝ)
    (hnonneg : 0≤δ+α/2)
    (hmargin : (δ+α/2)*(Z.card:ℝ)≤α*(T.card:ℝ)/2)
    (hdeg : ∀ v∈T∪Z,(δ+α)*(T.card:ℝ)≤((P.neighborFinset v∩T).card:ℝ)) :
    ∀ v : {v // v∈((T∪Z:Finset V):Set V)},
      (δ+α/2)*Fintype.card {v // v∈((T∪Z:Finset V):Set V)}≤((P.induce ((T∪Z:Finset V):Set V)).degree v:ℝ) := by
  intro v
  rw [induced_degree_intersection]
  have hc : Fintype.card {v // v∈((T∪Z:Finset V):Set V)}=(T∪Z).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [hc]
  exact enlarged_neighbour_density P T Z δ α hnonneg hmargin hdeg v.val v.property

end Oberwolfach
