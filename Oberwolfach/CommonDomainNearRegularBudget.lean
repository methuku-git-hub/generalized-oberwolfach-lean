module

public import Oberwolfach.RestrictedRegularRootedFactors

@[expose] public section
/-! Two nearly complete neighbourhoods and a bounded forbidden set leave
an induced domain with the relative size needed for degree transfer. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem common_domain_near_regular_budget {V:Type} [Fintype V] [DecidableEq V]
    (A₁ A₂ C:Finset V) (η:ℝ) (hη:0≤η) (hη1:η≤1)
    (h₁:((Finset.univ\A₁).card:ℝ)≤η*Fintype.card V/16)
    (h₂:((Finset.univ\A₂).card:ℝ)≤η*Fintype.card V/16)
    (hC:(C.card:ℝ)≤η*Fintype.card V/16):
    let B:=(A₁∩A₂)\C;
    ((Fintype.card V-B.card:ℕ):ℝ)≤η*B.card:=by
  intro B
  have hs:Finset.univ\B⊆((Finset.univ\A₁)∪(Finset.univ\A₂))∪C:=by
    intro v hv
    have hvnot: v∉B:=(Finset.mem_sdiff.mp hv).2
    by_cases hC':v∈C
    · exact Finset.mem_union_right _ hC'
    · apply Finset.mem_union_left
      by_cases hA₁:v∈A₁
      · apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro hA₂
        exact hvnot (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hA₁,hA₂⟩,hC'⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hA₁⟩)
  have hc:((Finset.univ\B).card:ℝ)≤(Finset.univ\A₁).card+(Finset.univ\A₂).card+C.card:=by
    have hh:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    have hhh:=Finset.card_union_le (Finset.univ\A₁) (Finset.univ\A₂)
    exact_mod_cast (show (Finset.univ\B).card≤(Finset.univ\A₁).card+(Finset.univ\A₂).card+C.card by omega)
  have hB:B.card≤Fintype.card V:=Finset.card_le_univ B
  have hdiff:((Finset.univ\B).card:ℝ)=(Fintype.card V:ℝ)-B.card:=by
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Nat.cast_sub hB]
  have hq:((Fintype.card V-B.card:ℕ):ℝ)=(Fintype.card V:ℝ)-B.card:=by rw [Nat.cast_sub hB]
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hmiss:(Fintype.card V:ℝ)-B.card≤3*η*Fintype.card V/16:=by linarith only [hdiff,hc,h₁,h₂,hC]
  have hηmiss:=mul_le_mul_of_nonneg_left hmiss hη
  have hηsq:η^2≤η:=by nlinarith [mul_nonneg hη (sub_nonneg.mpr hη1)]
  have hηsqn:=mul_le_mul_of_nonneg_right hηsq hn
  rw [hq]
  nlinarith only [hmiss,hηmiss,hηsqn,hη,hn]

end Oberwolfach
