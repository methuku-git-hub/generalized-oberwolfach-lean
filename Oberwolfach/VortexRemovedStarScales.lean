module

public import Oberwolfach.MarkedProtectedActiveGeometry

@[expose] public section
/-! Removing a bounded fraction from each fixed vortex domain preserves
geometric decay, with the explicitly enlarged ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_sdiff_scales
    (V:ℕ→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    (I T:∀ i,Finset (V i)) (L:ℕ) (θ η:ℝ)
    (hθ0:0≤θ) (hθ1:θ<1) (hη:0≤η)
    (hsub:∀ i,i≤L→T i⊆I i)
    (hsmall:∀ i,i≤L→((T i).card:ℝ)≤θ*(I i).card)
    (hstep:∀ i,i<L→((I (i+1)).card:ℝ)≤η*(I i).card):
    (∀ i,i≤L→(1-θ)*((I i).card:ℝ)≤((I i\T i).card:ℝ)) ∧
    (∀ i,i<L→(((I (i+1))\(T (i+1))).card:ℝ)≤(η/(1-θ))*((I i\T i).card:ℝ)) :=by
  have hden:0<1-θ:=by linarith
  have hlo:∀ i,i≤L→(1-θ)*((I i).card:ℝ)≤((I i\T i).card:ℝ):=by
    intro i hi
    have hn:=Finset.card_sdiff_add_card_eq_card (hsub i hi)
    have he:((I i\T i).card:ℝ)+(T i).card=(I i).card:=by exact_mod_cast hn
    have hs:=hsmall i hi
    nlinarith
  refine ⟨hlo,?_⟩
  intro i hi
  have hnext:(((I (i+1))\(T (i+1))).card:ℝ)≤((I (i+1)).card:ℝ):=by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : (I (i+1)\T (i+1))⊆I (i+1))
  have hcur:=hlo i (Nat.le_of_lt hi)
  have hmul:0≤η*(((I i\T i).card:ℝ)-(1-θ)*((I i).card:ℝ)):=mul_nonneg hη (sub_nonneg.mpr hcur)
  have hscale:η*((I i).card:ℝ)≤(η/(1-θ))*((I i\T i).card:ℝ):=by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith
  exact hnext.trans ((hstep i hi).trans hscale)


theorem vortex_sdiff_ratio_lt_one (θ η:ℝ) (hθ:θ<1) (hη:η<1-θ):
    η/(1-θ)<1:=by
  exact (div_lt_one (by linarith : 0<1-θ)).2 hη

theorem vortex_sdiff_invariant
    (V:ℕ→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    (I T:∀ i,Finset (V i)) (ρ:∀ i,Equiv.Perm (V i)) (L:ℕ)
    (hI:∀ i,i≤L→∀ x,ρ i x∈I i↔x∈I i)
    (hT:∀ i,i≤L→∀ x,ρ i x∈T i↔x∈T i):
    ∀ i,i≤L→∀ x,ρ i x∈I i\T i↔x∈I i\T i:=by
  intro i hi x
  simp only [Finset.mem_sdiff,hI i hi x,hT i hi x]

end Oberwolfach
