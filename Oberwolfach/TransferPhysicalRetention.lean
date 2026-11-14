module

public import Oberwolfach.TransferPhysicalPatterns
public import Oberwolfach.PatternSurvivalMean
public import Oberwolfach.ProductFailureBounds

@[expose] public section

/-! Concentration and a simultaneous lower survival event for the actual
transfer families, with unequal physical-edge retention probabilities allowed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 3 ≤ r) (P F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U)

def transferSurvivalSum (σ : Sym2 V → Bool) : ℝ :=
  ∑ T : OrdinaryTransferConfiguration hr P F H v u u',
    (1/(Fintype.card V:ℝ)^(r^2))*patternValue (transferRequiredEdges T) (fun _=>true) σ

theorem transferSurvivalSum_tail (hn : 0<Fintype.card V)
    (μ : Sym2 V → FiniteLaw Bool) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |transferSurvivalSum r hr P F H v u u' σ-
        ∑ T : OrdinaryTransferConfiguration hr P F H v u u',
          (1/(Fintype.card V:ℝ)^(r^2))*∏ e∈transferRequiredEdges T,(μ e).mass true|)≤
      2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)) := by
  have htotal : (∑ _ : OrdinaryTransferConfiguration hr P F H v u u',1/(Fintype.card V:ℝ)^(r^2))≤1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (div_le_one (by positivity)).mpr (transfer_configuration_total (hr:=hr))
  have hh := independent_pattern_sum_tail μ transferRequiredEdges
    (fun _ : OrdinaryTransferConfiguration hr P F H v u u'=>1/(Fintype.card V:ℝ)^(r^2))
    (by intro T;positivity) (fun _ _=>true)
    ((r:ℝ)^2/Fintype.card V) (((1+2*r)*r:ℕ):ℝ) 1 (by positivity) (by positivity) (by norm_num)
    (by intro T;exact_mod_cast transferRequiredEdges_card T) htotal
    (transfer_required_edge_incidence (hr:=hr) hn) t ht
  have he : ((r:ℝ)^2/Fintype.card V)*(((1+2*r)*r:ℕ):ℝ)*1=
      (r:ℝ)^2*((1+2*r)*r)/Fintype.card V := by push_cast;ring
  simpa only [he,transferSurvivalSum] using hh

theorem transferSurvivalSum_lower_tail (hn : 0<Fintype.card V)
    (μ : Sym2 V → FiniteLaw Bool) (p c t : ℝ) (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : c*(Fintype.card V:ℝ)^(r^2)≤Fintype.card (OrdinaryTransferConfiguration hr P F H v u u')) :
    (FiniteLaw.pi μ).probability (fun σ=>transferSurvivalSum r hr P F H v u u' σ≤p^((1+2*r)*r)*c-t)≤
      2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)) := by
  let w (_ : OrdinaryTransferConfiguration hr P F H v u u') : ℝ := 1/(Fintype.card V:ℝ)^(r^2)
  have hmean := pattern_survival_mean_lower μ transferRequiredEdges w (by intro T;dsimp [w];positivity)
    p hp hp1 ((1+2*r)*r) transferRequiredEdges_card
    (fun T e he=>hprob e (transferRequiredEdges_subset T he))
  have htotal : c≤∑ T,w T := by
    simp only [w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr hmany
  have hmean' := (mul_le_mul_of_nonneg_left htotal (pow_nonneg hp ((1+2*r)*r))).trans hmean
  apply le_trans _ (transferSurvivalSum_tail r hr P F H v u u' hn μ t ht)
  apply finiteLaw_probability_mono
  intro σ hσ
  have ha := neg_le_abs (transferSurvivalSum r hr P F H v u u' σ-
    ∑ T,w T*∏ e∈transferRequiredEdges T,(μ e).mass true)
  change t≤|transferSurvivalSum r hr P F H v u u' σ-∑ T,w T*∏ e∈transferRequiredEdges T,(μ e).mass true|
  linarith only [hσ,hmean',ha]

end Oberwolfach
