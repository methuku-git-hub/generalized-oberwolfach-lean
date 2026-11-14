module

public import Oberwolfach.RawIntervalLabelCounts

@[expose] public section

/-! Hub-count estimates as cardinalities of actual common spoke
neighbourhoods, including singleton and separated-pair tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawIntervalLabelCount_card (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (T : Finset V) :
    rawIntervalLabelCount π d σ j T=
      (Fintype.card {u : U // ∀ v∈T,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)}:ℝ) := by
  unfold rawIntervalLabelCount
  rw [Fintype.card_subtype]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalCommonHubs_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hm : 0<Fintype.card U) (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH)
    {I : Type} [Fintype I] (T : I → Finset V)
    (hsep : ∀ i,∀ x∈T i,∀ y∈T i,x≠y → ¬PermutationClose π (3*d) x y)
    (hT : ∀ i,(T i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(T i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card U))))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ i,
        |(Fintype.card {u : U // ∀ v∈T i,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)}:ℝ)-
          pH^(T i).card*Fintype.card U|<t) := by
  have hh := rawIntervalLabelCount_common_event π d hd q hq hQ s hs hS hnoshort hm j T hsep hT k hk hsize t ht
  simpa only [rawIntervalLabelCount_card,hj,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_comm] using hh

end Oberwolfach
