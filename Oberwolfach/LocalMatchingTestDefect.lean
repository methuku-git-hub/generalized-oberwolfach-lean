module

public import Oberwolfach.LongUnusedSpokeLocalIncidence
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem local_matching_test_defect
    {R C:Type} [Fintype C] [DecidableEq R] [DecidableEq C]
    (I:Finset R) (M:Finset C) (Q:C→Finset R) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d))
    (hmass:(1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ))
    (htest:(1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)):
    ((I\M.biUnion Q).card:ℝ)≤(ε+γ)*I.card:=by
  have hdis':∀c∈M,∀d∈M,c≠d→Disjoint (Q c∩I) (Q d∩I):=by
    intro c hc d hd hcd
    exact (hdis c hc d hd hcd).mono Finset.inter_subset_left Finset.inter_subset_left
  have hset:M.biUnion (fun c=>Q c∩I) = I∩M.biUnion Q:=by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_inter]
    aesop
  have hcardNat:(I∩M.biUnion Q).card = ∑c∈M,(Q c∩I).card:=by
    rw [←hset,Finset.card_biUnion]
    intro c hc d hd hcd
    exact hdis' c hc d hd hcd
  have hcard:(↑(I∩M.biUnion Q).card:ℝ)=∑c∈M,((Q c∩I).card:ℝ):=by exact_mod_cast hcardNat
  have hpartition:=Finset.card_sdiff_add_card_inter I (M.biUnion Q)
  have hpartition':((I\M.biUnion Q).card:ℝ)+((I∩M.biUnion Q).card:ℝ)=I.card:=by exact_mod_cast hpartition
  have hmul:=mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hγ1)
  have hI:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  have heγ:0≤γ*ε*(I.card:ℝ):=mul_nonneg (mul_nonneg hγ hε) hI
  nlinarith only [hcard,hpartition',hmul,htest,heγ]
end Oberwolfach
