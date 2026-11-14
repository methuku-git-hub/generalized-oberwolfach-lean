module

public import Oberwolfach.OrderedOrdinarySharpRimPairs

@[expose] public section
/-! Uniform near/far bounds for a fixed ordinary rim root and a second
ordinary rim request. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem ordered_ordinary_rim_pair_near_far
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (x y a c:V):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))≤
      if a∈({x,y}:Finset V) ∨ c∈({x,y}:Finset V) then
        ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)
      else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 :=by
  split_ifs with hnear
  · have hb:=orderedOrdinary_rim_pair_bound hm hn hu w B hB hw x y a c
    have hp:((m:ℝ)+1)^3≤((m:ℝ)+1)^4:=by
      have hm0:0≤((m:ℝ)+1)^3:=by positivity
      have hm1:(1:ℝ)≤(m:ℝ)+1:=le_add_of_nonneg_left (Nat.cast_nonneg m)
      calc
        _ = ((m:ℝ)+1)^3*1:=by ring
        _ ≤ ((m:ℝ)+1)^3*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hm1 hm0
        _ = _:=by ring
    exact hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) (by positivity))
  · have hdis:Disjoint ({x,y}:Finset V) {a,c}:=by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz'
      rcases hz' with rfl|rfl
      · exact hnear (Or.inl hz)
      · exact hnear (Or.inr hz)
    exact ordered_ordinary_disjoint_rims_all_lengths hm hn hu w B hB hw x y a c hdis
end Oberwolfach
