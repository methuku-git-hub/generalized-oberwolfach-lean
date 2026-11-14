module

public import Oberwolfach.OrderedOrdinaryIncidence

@[expose] public section
/-! Incidence sums retain every position of an ordered cycle exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_spoke_weighted_sum
    (w:(Fin r→V)→ℝ) (v:V) (u:U):
    (∑ W:OrderedOrdinaryWheel (U:=U) π b r,if Sum.inr (v,u)∈orderedOrdinaryResources W then w W.1.val else 0)=
      ∑ i:Fin r,∑ C:{C:Fin r→V // PermutationSeparated π b C},if C.val i=v then w C.val else 0 :=by
  change (∑ W:({C:Fin r→V // PermutationSeparated π b C}×U),if Sum.inr (v,u)∈orderedOrdinaryResources W then w W.1.val else 0)=_
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single u]
  · have hh:=orderedOrdinary_spoke_indicator (C,u) v u
    simp only [if_pos rfl] at hh
    have hm:=congrArg (fun z:ℝ=>w C.val*z) hh
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero] at hm
    exact hm.symm
  · intro v' _ hv'
    have hn:Sum.inr (v,u)∉orderedOrdinaryResources (C,v'):=by
      intro h
      obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke (C,v') (v,u)).mp h
      exact hv' (congrArg Prod.snd hi)
    simp [hn]
  · simp

theorem orderedOrdinary_rim_weighted_sum
    (w:(Fin r→V)→ℝ) (a:U→ℝ) (hr:3≤r) (x y:V):
    (∑ W:OrderedOrdinaryWheel (U:=U) π b r,if Sum.inl (x,y)∈orderedOrdinaryResources W then w W.1.val*a W.2 else 0)=
      (∑ i:Fin r,∑ C:{C:Fin r→V // PermutationSeparated π b C},if C.val i=x ∧ C.val (cycleNext i)=y then w C.val else 0)*(∑ u,a u) :=by
  change (∑ W:({C:Fin r→V // PermutationSeparated π b C}×U),if Sum.inl (x,y)∈orderedOrdinaryResources W then w W.1.val*a W.2 else 0)=_
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hh:=orderedOrdinary_rim_indicator (C,u) hr x y
  have hm:=congrArg (fun z:ℝ=>w C.val*a u*z) hh
  simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero] at hm
  simpa [Finset.sum_mul] using hm.symm
end Oberwolfach
