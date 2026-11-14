module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section

/-! Concentration and means for fixed sums of resource patterns. The
resource supports and coefficients are fixed before the product experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A I E : Type*} [Fintype A] [Fintype I] [Fintype E] [DecidableEq A] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)] {State : A → Type*}

def supportedPatternSum (R : I → Finset A) (w : I → ℝ) (s : I → ∀ a,State a)
    (state : (∀ e,Base e) → ∀ a,State a) (σ : ∀ e,Base e) : ℝ :=
  ∑ i,w i*patternValue (R i) (s i) (state σ)

theorem supportedPatternSum_change
    (R : I → Finset A) (w : I → ℝ) (hw : ∀ i,0≤w i) (s : I → ∀ a,State a)
    (S : A → Finset E) (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (e : E) (σ τ : ∀ e,Base e) (hagree : ∀ f,f≠e → σ f=τ f) :
    |supportedPatternSum R w s state σ-supportedPatternSum R w s state τ|≤
      ∑ a,if e∈S a then ∑ i,if a∈R i then w i else 0 else 0 := by
  let D := Finset.univ.filter (fun a=>e∈S a)
  have hh := weighted_product_stability Finset.univ R s w D (state τ) (state σ)
    (fun i _=>hw i)
    (by
      intro i _ a _ ha
      apply hs a
      intro f hf
      apply Eq.symm (hagree f _)
      intro he;subst f
      exact ha (by simp [D,hf]))
  simpa only [supportedPatternSum,D,Finset.sum_filter] using hh

theorem supportedPatternSum_tail
    (μ : ∀ e,FiniteLaw (Base e)) (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (s : I → ∀ a,State a)
    (S : A → Finset E) (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (B v : ℝ) (hB : 0<B) (hv : 0<v)
    (hread : ∀ a,((S a).card:ℝ)≤B)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (hsq : (∑ a,(∑ i,if a∈R i then w i else 0)^2)≤v)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |supportedPatternSum R w s state σ-(FiniteLaw.pi μ).expectation (supportedPatternSum R w s state)|)≤
      2*Real.exp (-2*t^2/(B^2*v)) := by
  apply finiteLaw_boundedDifferences_variance_bound μ (supportedPatternSum R w s state)
    (fun e=>∑ a,if e∈S a then ∑ i,if a∈R i then w i else 0 else 0)
    (by
      intro e
      apply Finset.sum_nonneg
      intro a _
      split_ifs
      · exact Finset.sum_nonneg (fun i _=>by split_ifs;exact hw i;exact le_refl _)
      · exact le_refl _)
    (B^2*v) (by positivity) _ (supportedPatternSum_change R w hw s S state hs) t ht
  exact (locality_square_sum S B hB.le hread haffect _).trans
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))

theorem supportedPatternSum_expectation
    (μ : ∀ e,FiniteLaw (Base e)) (R : I → Finset A) (w : I → ℝ)
    (s : I → ∀ a,State a) (S : A → Finset E)
    (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (hdisj : ∀ i,∀ a∈R i,∀ b∈R i,a≠b → Disjoint (S a) (S b)) :
    (FiniteLaw.pi μ).expectation (supportedPatternSum R w s state)=
      ∑ i,w i*∏ a∈R i,(FiniteLaw.pi μ).probability (fun σ=>state σ a=s i a) := by
  unfold FiniteLaw.expectation supportedPatternSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hh := finiteLaw_disjoint_supported_family μ S (fun a σ=>state σ a=s i a)
    (fun a σ τ hagree=>by rw [hs a σ τ hagree]) (R i) (hdisj i)
  rw [← hh]
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [patternValue_indicator]
  split_ifs <;> ring

end Oberwolfach
