module

public import Oberwolfach.SharedVortexPermutation

@[expose] public section
/-! The protected partition can use the first vertex set of every class's
vortex when their total size fits its deterministic budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem vortex_first_level_total_bound {V:Type} [Fintype V] {k:ℕ} {U:Fin k→Type}
    [∀ a,Fintype (U a)] {G:SimpleGraph V} {D m:ℕ} {β ε η:ℝ}
    (he:0≤ε) (hbudget:(k:ℝ)*ε≤η)
    (Q:∀ a,Vortex (U a) G D β ε m) :
    ((∑ a:Fin k,((Q a).vertices 1).card:ℕ):ℝ)≤η*Fintype.card V := by
  have hsingle : ∀ a:Fin k,(((Q a).vertices 1).card:ℝ)≤ε*Fintype.card V := by
    intro a
    rw [(Q a).sizes 1 (by have := (Q a).length_pos;omega)]
    simpa only [floorOrbit_zero] using floorOrbit_shrinks he (Fintype.card V) 0
  have hsum : (∑ a:Fin k,(((Q a).vertices 1).card:ℝ))≤
      ∑ _a:Fin k,ε*(Fintype.card V:ℝ):=Finset.sum_le_sum (fun a _=>hsingle a)
  have hnonneg:(0:ℝ)≤Fintype.card V:=by positivity
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  push_cast
  nlinarith
theorem vortex_first_level_partition_budget {V:Type} [Fintype V] {K k:ℕ}
    {U:Fin k→Type} [∀ a,Fintype (U a)] {G:SimpleGraph V} {D m:ℕ}
    {β ε α:ℝ} (he:0≤ε) (hk:k≤K+1)
    (hbudget:((K:ℝ)+1)*ε≤(α/2)/100000)
    (Q:∀ a,Vortex (U a) G D β ε m) :
    ((∑ a:Fin k,((Q a).vertices 1).card:ℕ):ℝ)≤(α/2)/100000*Fintype.card V := by
  have hkR:(k:ℝ)≤(K:ℝ)+1:=by exact_mod_cast hk
  have hke: (k:ℝ)*ε≤(α/2)/100000:=
    (mul_le_mul_of_nonneg_right hkR he).trans hbudget
  exact vortex_first_level_total_bound he hke Q
end Oberwolfach
