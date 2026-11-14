module

public import Oberwolfach.OrdinaryIsolatorTotalCounts

@[expose] public section

/-! The normalized isolator sum retains the two root spokes and omits only
the physical root edge. Its lower bound therefore also applies when that
physical edge was not retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

def ordinaryIsolatorPotential (P F : SimpleGraph V) (H : V → U → Prop)
    (k : ℕ) (θ α : ℝ) (x y : V) (σ : Sym2 V → Bool) : ℝ :=
  (∑ u : U,if H x u ∧ H y u then
    rootedInducedSurvivalSum P
      (fun S : OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ else 0)/Fintype.card V

theorem ordinary_isolator_potential_lower (P F : SimpleGraph V) (H : V → U → Prop)
    (k : ℕ) (θ α : ℝ) (x y : V) (σ : Sym2 V → Bool) (hn : 0<Fintype.card V)
    (c η : ℝ) (hc : 0≤c)
    (hhubs : η*Fintype.card V≤(Fintype.card {u : U // H x u ∧ H y u}:ℝ))
    (hpotential : ∀ u,H x u → H y u →
      c≤rootedInducedSurvivalSum P
        (fun S : OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ) :
    c*η≤ordinaryIsolatorPotential P F H k θ α x y σ := by
  unfold ordinaryIsolatorPotential
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
  have hsum := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset U))=>
    show (if H x u ∧ H y u then c else 0)≤
      (if H x u ∧ H y u then rootedInducedSurvivalSum P
        (fun S : OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ else 0) by
      split_ifs with h
      · exact hpotential u h.1 h.2
      · exact le_rfl)
  have he : (∑ u : U,if H x u ∧ H y u then c else 0)=
      (Fintype.card {u : U // H x u ∧ H y u}:ℝ)*c := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Fintype.card_subtype]
  rw [he] at hsum
  have hh := mul_le_mul_of_nonneg_right hhubs hc
  nlinarith only [hsum,hh]

end Oberwolfach
