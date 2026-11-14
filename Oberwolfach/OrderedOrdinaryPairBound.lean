module

public import Oberwolfach.OrderedOrdinaryRimPairBound
public import Oberwolfach.OrderedOrdinarySpokePairBound

@[expose] public section
/-! Uniform omitted-pair bound for every pair of ordered-wheel resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_omitted_pair_symm
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (e f:(V×V)⊕(V×U)):
    resourceOmittedPairWeight orderedOrdinaryResources w e f=
      resourceOmittedPairWeight orderedOrdinaryResources w f e:=by
  unfold resourceOmittedPairWeight
  apply Finset.sum_congr rfl
  intro W _
  split_ifs <;> simp_all [Ne.symm]

theorem orderedOrdinary_omitted_pair_bound (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e f:(V×V)⊕(V×U)):
    resourceOmittedPairWeight orderedOrdinaryResources w e f≤((m:ℝ)+1)^3*B/(Fintype.card V:ℝ):=by
  have hb:(1:ℝ)≤(m:ℝ)+1:=by have hm0:(0:ℝ)≤m:=Nat.cast_nonneg _; linarith
  have hp:((m:ℝ)+1)^2≤((m:ℝ)+1)^3:=by
    calc
      _ = ((m:ℝ)+1)^2*1:=by ring
      _ ≤ ((m:ℝ)+1)^2*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _:=by ring
  have hscale:((m:ℝ)+1)^2*B/(Fintype.card V:ℝ)≤((m:ℝ)+1)^3*B/(Fintype.card V:ℝ):=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) (by positivity)
  cases e with
  | inl e=>
    cases f with
    | inl f=>exact orderedOrdinary_rim_pair_bound hm hn hu w B hB hw e.1 e.2 f.1 f.2
    | inr f=>
      rw [orderedOrdinary_omitted_pair_symm]
      exact (orderedOrdinary_spoke_rim_pair_bound hm hn w B hB hw f.1 f.2 e.1 e.2).trans hscale
  | inr e=>
    cases f with
    | inl f=>exact (orderedOrdinary_spoke_rim_pair_bound hm hn w B hB hw e.1 e.2 f.1 f.2).trans hscale
    | inr f=>exact (orderedOrdinary_spoke_spoke_pair_bound hm hn w B hB hw e.1 f.1 e.2 f.2).trans hscale
end Oberwolfach
