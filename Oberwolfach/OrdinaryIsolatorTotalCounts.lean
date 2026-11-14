module

public import Oberwolfach.OrdinaryIsolatorSurvivalCounts

@[expose] public section

/-! Add the surviving configurations over eligible hubs. The root edge
and endpoint spokes are used only after the common potential event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_card_eq_sum_fibres {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    (Fintype.card A:ℝ)=∑ b,(Fintype.card {a : A // f a=b}:ℝ) := by
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hh
  exact_mod_cast hh.symm


theorem ordinary_isolator_total_count_lower {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (P F : SimpleGraph V) (H : V → U → Prop) (k : ℕ) (hk : 2≤k)
    (θ α : ℝ) (x y : V) (σ : Sym2 V → Bool) (hn : 0<Fintype.card V)
    (hroot : (retainedGraph P σ).Adj x y) (c η : ℝ) (hc : 0≤c)
    (hhubs : η*Fintype.card V≤(Fintype.card {u : U // H x u ∧ H y u}:ℝ))
    (hpotential : ∀ u,H x u → H y u →
      c≤rootedInducedSurvivalSum P
        (fun S : OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ) :
    c*η*(Fintype.card V:ℝ)^(k-1)≤
      Fintype.card (OrdinaryIsolatorConfiguration P (retainedGraph P σ\F) F H k θ α x y) := by
  let C := OrdinaryIsolatorConfiguration P (retainedGraph P σ\F) F H k θ α x y
  have hden : (0:ℝ)<(Fintype.card V:ℝ)^(k-2) := by positivity
  have hhub (u : U) :
      (if H x u ∧ H y u then c*(Fintype.card V:ℝ)^(k-2) else 0)≤
      (Fintype.card {T : C // T.hub=u}:ℝ) := by
    split_ifs with h
    · have hh := hpotential u h.1 h.2
      rw [ordinary_isolator_potential_count_eq P F H k θ α x y u σ hroot h.1 h.2] at hh
      exact (le_div_iff₀ hden).mp hh
    · exact Nat.cast_nonneg _
  have hsum := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset U))=>hhub u)
  have hleft : (∑ u : U,if H x u ∧ H y u then c*(Fintype.card V:ℝ)^(k-2) else 0)=
      (Fintype.card {u : U // H x u ∧ H y u}:ℝ)*(c*(Fintype.card V:ℝ)^(k-2)) := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Fintype.card_subtype]
  rw [hleft,← finite_card_eq_sum_fibres (fun T : C=>T.hub)] at hsum
  have hscale := mul_le_mul_of_nonneg_right hhubs (mul_nonneg hc hden.le)
  have hexp : k-1=(k-2)+1 := by omega
  calc
    _ = (η*Fintype.card V)*(c*(Fintype.card V:ℝ)^(k-2)) := by rw [hexp,pow_succ];ring
    _ ≤ _ := hscale.trans hsum

end Oberwolfach
