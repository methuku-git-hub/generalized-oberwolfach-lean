module

public import Oberwolfach.HypergraphWeightMoments
public import Oberwolfach.FiniteUniform

@[expose] public section

/-! Vertex-colouring concentration for actual hyperedge weights. The
variance proxy uses weighted degrees, avoiding a factor equal to the total
number of vertices or hyperedges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    [DecidableEq V] [Nonempty C]

def monochromaticWeightedSum (R : E → Finset V) (w : E → ℝ) (c : C) (σ : V → C) : ℝ :=
  ∑ e,w e*patternValue (R e) (fun _=>c) σ

theorem monochromaticWeightedSum_expectation (R : E → Finset V) (w : E → ℝ)
    (k : ℕ) (hR : ∀ e,(R e).card=k) (c : C) :
    (FiniteLaw.pi (fun _ : V=>FiniteLaw.uniform C)).expectation (monochromaticWeightedSum R w c)=
      (∑ e,w e)/(Fintype.card C:ℝ)^k := by
  unfold monochromaticWeightedSum
  have hh := finiteLaw_expectation_omitted_root_sum (fun _ : V=>FiniteLaw.uniform C)
    Finset.univ R ∅ (fun _ _=>c) w
  simpa only [Finset.sdiff_empty,FiniteLaw.uniform,Finset.prod_const,hR,one_div_pow,
    ← Finset.sum_mul,mul_one_div,← Finset.sum_div,monochromaticWeightedSum] using hh

theorem monochromaticWeightedSum_tail (R : E → Finset V) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (k : ℕ) (hk : 0<k) (hR : ∀ e,(R e).card=k)
    (hW : 0<∑ e,w e) (D : ℝ) (hD : ∀ v,hypergraphWeightedDegree R w v≤D)
    (c : C) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : V=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤|monochromaticWeightedSum R w c σ-(∑ e,w e)/(Fintype.card C:ℝ)^k|)≤
      2*Real.exp (-2*t^2/(D*k*∑ e,w e)) := by
  have hh := finiteLaw_omitted_weighted_tail (fun _ : V=>FiniteLaw.uniform C)
    Finset.univ R ∅ (fun _ _=>c) w (hypergraphWeightedDegree R w)
    (fun e _=>hw e) (by intro v;simp only [Finset.sdiff_empty];exact le_refl _) ht
  have hb : (FiniteLaw.pi (fun _ : V=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤|monochromaticWeightedSum R w c σ-(∑ e,w e)/(Fintype.card C:ℝ)^k|)≤
      2*Real.exp (-2*t^2/(∑ v,(hypergraphWeightedDegree R w v)^2)) := by
    simpa only [Finset.sdiff_empty,FiniteLaw.uniform,Finset.prod_const,hR,one_div_pow,
      ← Finset.sum_mul,mul_one_div,← Finset.sum_div,monochromaticWeightedSum] using hh
  have hpos := hypergraphWeightedDegree_square_sum_pos R w hw k hk hR hW
  have hsq := hypergraphWeightedDegree_square_sum R w hw k hR D hD
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hdiv := div_le_div_of_nonneg_left (show 0≤2*t^2 by positivity) hpos hsq
  simpa only [neg_mul,neg_div] using neg_le_neg hdiv

end Oberwolfach
