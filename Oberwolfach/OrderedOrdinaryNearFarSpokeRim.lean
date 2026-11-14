module

public import Oberwolfach.OrderedOrdinarySharpSpokePairs

@[expose] public section
/-! Near/far fixed-weight bounds for a spoke root and a rim resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem ordered_ordinary_spoke_rim_pair_near_far
    (hm:2≤m) (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (v a c:V) (u:U):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inl (a,c))≤
      if a=v ∨ c=v then ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ)
      else ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ)^2 :=by
  split_ifs with hnear
  · have hb:=orderedOrdinary_spoke_rim_pair_bound hm hn w B hB hw v u a c
    have hp:((m:ℝ)+1)^2≤((m:ℝ)+1)^3:=by
      have hm0:0≤((m:ℝ)+1)^2:=by positivity
      have hm1:(1:ℝ)≤(m:ℝ)+1:=le_add_of_nonneg_left (Nat.cast_nonneg m)
      calc
        _ = ((m:ℝ)+1)^2*1:=by ring
        _ ≤ ((m:ℝ)+1)^2*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hm1 hm0
        _ = _:=by ring
    exact hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) (by positivity))
  · have hva:v≠a:=by intro h;apply hnear;exact Or.inl h.symm
    have hvc:v≠c:=by intro h;apply hnear;exact Or.inr h.symm
    exact ordered_ordinary_spoke_rim_three_vertices hm hn w B hB hw v a c u hva hvc
end Oberwolfach
