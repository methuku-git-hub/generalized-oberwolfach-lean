module

public import Oberwolfach.RootedSetNormalizedLoads
public import Oberwolfach.PatternSurvivalMean

@[expose] public section

/-! Root-omitted induced-set counts under independent physical-edge
retention. The family and its coefficients are fixed before these trials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {k : ℕ}

def rootedInducedSurvivalSum (P : SimpleGraph V) (S : I → FixedSubset V k)
    (root : Sym2 V) (σ : Sym2 V → Bool) : ℝ :=
  ∑ i,(1/(Fintype.card V:ℝ)^(k-2))*
    patternValue (rootOmittedInducedEdges P (S i).val root) (fun _=>true) σ


theorem rootedInducedSurvivalSum_tail (P : SimpleGraph V)
    (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val)
    (μ : Sym2 V → FiniteLaw Bool) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |rootedInducedSurvivalSum P S s(x,y) σ-
        ∑ i,(1/(Fintype.card V:ℝ)^(k-2))*
          ∏ e∈rootOmittedInducedEdges P (S i).val s(x,y),(μ e).mass true|)≤
      2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)) := by
  have hh := independent_pattern_sum_tail μ
    (fun i=>rootOmittedInducedEdges P (S i).val s(x,y))
    (fun _=>1/(Fintype.card V:ℝ)^(k-2)) (by intro i;positivity) (fun _ _=>true)
    (1/Fintype.card V) ((k:ℝ)^2) 1 (by positivity) (by positivity) (by norm_num)
    (by
      intro i
      have hh := rootOmittedInducedEdges_card P (S i).val s(x,y)
      rw [(S i).property] at hh
      exact_mod_cast hh)
    (fixedSetFamily_normalized_total S hinj x y hxy (by omega) hn hroot)
    (fixedSetFamily_normalized_edge_load P S hinj x y hxy hk hn hroot) t ht
  have he : (1/(Fintype.card V:ℝ))*(k:ℝ)^2*1=(k:ℝ)^2/Fintype.card V := by ring
  simpa only [rootedInducedSurvivalSum,he] using hh


theorem rootedInducedSurvivalSum_lower_tail (P : SimpleGraph V)
    (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val)
    (μ : Sym2 V → FiniteLaw Bool) (p c t : ℝ) (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : c*(Fintype.card V:ℝ)^(k-2)≤Fintype.card I) :
    (FiniteLaw.pi μ).probability (fun σ=>rootedInducedSurvivalSum P S s(x,y) σ≤p^(k^2)*c-t)≤
      2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)) := by
  let R (i : I) := rootOmittedInducedEdges P (S i).val s(x,y)
  let w (_ : I) : ℝ := 1/(Fintype.card V:ℝ)^(k-2)
  have hmean := pattern_survival_mean_lower μ R w (by intro i;dsimp [w];positivity) p hp hp1 (k^2)
    (by intro i;simpa only [R,(S i).property] using rootOmittedInducedEdges_card P (S i).val s(x,y))
    (by
      intro i e he
      apply hprob e
      have hh := (Finset.mem_erase.mp he).2
      rw [SimpleGraph.mem_edgeFinset] at hh ⊢
      exact SimpleGraph.edgeSet_mono (spanningRestriction_le P (S i).val) hh)
  have htotal : c≤∑ i,w i := by
    simp only [w,Finset.sum_const,nsmul_eq_mul,mul_one_div]
    exact (le_div_iff₀ (by positivity : (0:ℝ)<(Fintype.card V:ℝ)^(k-2))).mpr hmany
  have hmean' : p^(k^2)*c≤∑ i,w i*∏ e∈R i,(μ e).mass true :=
    (mul_le_mul_of_nonneg_left htotal (pow_nonneg hp _)).trans hmean
  apply le_trans _ (rootedInducedSurvivalSum_tail P S hinj x y hxy hk hn hroot μ t ht)
  apply finiteLaw_probability_mono
  intro σ hσ
  have habs := neg_le_abs (rootedInducedSurvivalSum P S s(x,y) σ-
    ∑ i,w i*∏ e∈R i,(μ e).mass true)
  change t≤|rootedInducedSurvivalSum P S s(x,y) σ-∑ i,w i*∏ e∈R i,(μ e).mass true|
  linarith only [hmean',hσ,habs]

end Oberwolfach
