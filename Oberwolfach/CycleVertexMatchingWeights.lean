module

public import Oberwolfach.FractionalCycleIncidence
public import Oberwolfach.OrdinaryCyclePairLoads

@[expose] public section

/-! Conversion of an edge-fractional cycle decomposition to weights for
vertex-disjoint cycle packing. The resources are graph vertices, not edges.
Every cycle is a physical cycle subgraph and occurs exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryCycleVertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (C : OrdinaryCycle G r) : Finset V :=
  C.val.val.support.toFinset

theorem ordinaryCycleVertices_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (C : OrdinaryCycle G r) :
    (ordinaryCycleVertices G r C).card=r := C.val.property.support_card

theorem ordinary_cycle_vertex_weight_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (a : OrdinaryCycle G r → ℝ)
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then a C else 0)=if G.Adj x y then 1 else 0)
    (v : V) :
    2*(∑ C,if v∈ordinaryCycleVertices G r C then a C else 0)=(G.degree v : ℝ) := by
  have hrow (C : OrdinaryCycle G r) :
      (∑ u,if C.val.val.Adj v u then a C else 0)=
        2*(if v∈ordinaryCycleVertices G r C then a C else 0) := by
    have hs : (∑ u,if C.val.val.Adj v u then a C else 0)=
        (C.val.val.degree v : ℝ)*a C := by
      calc
        _ = (∑ u,if C.val.val.Adj v u then (1 : ℝ) else 0)*a C := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          split_ifs <;> simp
        _ = _ := by rw [graph_adjacency_row_sum]
    rw [hs]
    rcases C.val.property.degree_zero_or_two v with hz|ht
    · have hn : v∉ordinaryCycleVertices G r C := by
        simpa only [ordinaryCycleVertices,Set.mem_toFinset] using
          (C.val.val.degree_eq_zero_iff_notMem_support v).mp hz
      simp [hz,hn]
    · have hm : v∈ordinaryCycleVertices G r C := by
        apply Set.mem_toFinset.mpr
        exact (C.val.val.degree_pos_iff_mem_support v).mp (by omega)
      simp [ht,hm]
  calc
    _ = ∑ C : OrdinaryCycle G r,∑ u,if C.val.val.Adj v u then a C else 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun C _=>(hrow C).symm)
    _ = ∑ u,∑ C : OrdinaryCycle G r,if C.val.val.Adj v u then a C else 0 := Finset.sum_comm
    _ = ∑ u,if G.Adj v u then (1 : ℝ) else 0 := Finset.sum_congr rfl (fun u _=>he v u)
    _ = _ := graph_adjacency_row_sum G v

theorem ordinary_cycle_rescaled_vertex_load
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (a : OrdinaryCycle G r → ℝ)
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then a C else 0)=if G.Adj x y then 1 else 0)
    (d : ℝ) (v : V) :
    (∑ C,if v∈ordinaryCycleVertices G r C then 2*a C/d else 0)=
      (G.degree v : ℝ)/d := by
  calc
    _ = 2*(∑ C,if v∈ordinaryCycleVertices G r C then a C else 0)/d := by
      rw [Finset.mul_sum,Finset.sum_div]
      exact Finset.sum_congr rfl (fun C _=>by split_ifs <;> simp)
    _ = _ := by rw [ordinary_cycle_vertex_weight_identity G r a he v]

theorem ordinary_cycle_vertex_pair_load
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V : ℝ)^(r-2))
    (x y : V) (hxy : x≠y) :
    (∑ C,if x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C then a C else 0)≤
      (r : ℝ)^2*B := by
  have hc : ({x,y} : Finset V).card=2 := by simp [hxy]
  have hh := ordinary_cycle_event_weight_bound G r hr hn a ha B hB hb {x,y}
    (by rw [hc])
    (fun C=>x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C) (by
      intro C h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl
      · exact Set.mem_toFinset.mp h.1
      · exact Set.mem_toFinset.mp h.2)
  simp only [hc,Nat.sub_self,pow_zero,div_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro C _
  split_ifs <;> rfl

theorem ordinary_cycle_rescaled_vertex_pair_load
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V : ℝ)^(r-2))
    {d : ℝ} (hd : 0<d) (x y : V) (hxy : x≠y) :
    (∑ C,if x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C then 2*a C/d else 0)≤
      2*(r : ℝ)^2*B/d := by
  have he : (∑ C,if x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C then 2*a C/d else 0)=
      (2/d)*(∑ C,if x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C then a C else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (ordinary_cycle_vertex_pair_load G r hr hn a ha B hB hb x y hxy)
    (by positivity : 0≤2/d)
  convert hh using 1 <;> ring

theorem ordinary_cycle_vertex_matching_weights
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V : ℝ)^(r-2))
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then a C else 0)=if G.Adj x y then 1 else 0)
    {d η : ℝ} (hd : (Fintype.card V : ℝ)/2≤d)
    (hdeg : ∀ v,(1-η)*d≤(G.degree v : ℝ) ∧ (G.degree v : ℝ)≤d) :
    ∃ b : OrdinaryCycle G r → ℝ,(∀ C,0≤b C) ∧
      (∀ v,1-η≤(∑ C,if v∈ordinaryCycleVertices G r C then b C else 0) ∧
        (∑ C,if v∈ordinaryCycleVertices G r C then b C else 0)≤1) ∧
      (∀ x y,x≠y →
        (∑ C,if x∈ordinaryCycleVertices G r C ∧ y∈ordinaryCycleVertices G r C then b C else 0)≤
          4*(r : ℝ)^2*B/(Fintype.card V : ℝ)) := by
  have hnR : (0 : ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hdpos : 0<d := by linarith
  refine ⟨fun C=>2*a C/d,fun C=>div_nonneg (mul_nonneg (by norm_num) (ha C)) hdpos.le,?_,?_⟩
  · intro v
    rw [ordinary_cycle_rescaled_vertex_load G r a he]
    exact ⟨(le_div_iff₀ hdpos).mpr (hdeg v).1,(div_le_one hdpos).mpr (hdeg v).2⟩
  · intro x y hxy
    apply (ordinary_cycle_rescaled_vertex_pair_load G r hr hn a ha B hB hb hdpos x y hxy).trans
    apply (div_le_div_iff₀ hdpos hnR).mpr
    have hp := mul_nonneg (mul_nonneg (sq_nonneg (r : ℝ)) hB)
      (show 0≤2*d-(Fintype.card V : ℝ) by linarith)
    nlinarith

end Oberwolfach
