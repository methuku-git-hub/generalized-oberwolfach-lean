module

public import Oberwolfach.SubsetComplement
public import Oberwolfach.PartitionConcentration
public import Oberwolfach.ProductExchange
public import Oberwolfach.ZeroVariance
public import Oberwolfach.OneSidedExposure

@[expose] public section

/-! The actual uniform sample spaces in `lem:simp:product-sampling`.
A partition is the function assigning each vertex to its unique cell. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

inductive UniformSampleSpec (V : Type*) [Fintype V] where
  | subset (r : ℕ) (hr : r ≤ Fintype.card V)
  | partition (k : ℕ) (d : Fin k → ℕ) (hd : ∑ a, d a = Fintype.card V)

namespace UniformSampleSpec

variable {V : Type*} [Fintype V]

def State : UniformSampleSpec V → Type _
  | .subset r _ => FixedSubset V r
  | .partition k d _ => FixedPartition V k d

instance stateFintype (s : UniformSampleSpec V) : Fintype s.State := by
  cases s <;> dsimp [State] <;> infer_instance

instance stateNonempty (s : UniformSampleSpec V) : Nonempty s.State := by
  cases s with
  | subset r hr => exact fixedSubset_nonempty hr
  | partition k d hd => exact fixedPartition_nonempty d hd

def law (s : UniformSampleSpec V) : FiniteLaw s.State := FiniteLaw.uniform s.State

def exchange : (s : UniformSampleSpec V) → V → V → s.State → s.State
  | .subset _ _, u, v, S => fixedSubsetMap (Equiv.swap u v) S
  | .partition _ _ _, u, v, P => fixedPartitionMap (Equiv.swap u v) P

def exposures : UniformSampleSpec V → ℕ
  | .subset r _ => min r (Fintype.card V - r)
  | .partition _ _ _ => Fintype.card V

theorem mgf (s : UniformSampleSpec V) (f : s.State → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hchange : ∀ x u v, |f x - f (s.exchange u v x)| ≤ b) (t : ℝ) :
    s.law.expectation (fun x => Real.exp (t * (f x - s.law.expectation f))) ≤
      Real.exp (t ^ 2 * ((s.exposures : ℝ) * b ^ 2) / 8) := by
  cases s with
  | subset r hr =>
    let : Nonempty (FixedSubset V r) := fixedSubset_nonempty hr
    simpa only [law, State, exposures, mul_assoc] using fixedSubset_mgf_min hr f hb hchange t
  | partition k d hd =>
    let : Nonempty (FixedPartition V k d) := fixedPartition_nonempty d hd
    simpa only [law, State, exposures, mul_assoc] using fixedPartition_mgf f hb hchange t

theorem mass_pos (s : UniformSampleSpec V) (x : s.State) : 0 < s.law.mass x := by
  change 0 < (1 : ℝ) / Fintype.card s.State
  positivity

end UniformSampleSpec

theorem uniformSamples_mgf
    {m : ℕ} {V : Fin m → Type*} [∀ i, Fintype (V i)]
    (s : ∀ i, UniformSampleSpec (V i)) (f : (∀ i, (s i).State) → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hchange : ∀ i (σ τ : ∀ j, (s j).State),
      (∀ j, j ≠ i → σ j = τ j) → ∀ u v,
      τ i = (s i).exchange u v (σ i) → |f σ - f τ| ≤ b i)
    (t : ℝ) :
    (FiniteLaw.pi (fun i => (s i).law)).expectation
      (fun σ => Real.exp (t * (f σ - (FiniteLaw.pi (fun i => (s i).law)).expectation f))) ≤
      Real.exp (t ^ 2 * (∑ i, ((s i).exposures : ℝ) * (b i) ^ 2) / 8) := by
  refine finiteLaw_product_exchange_mgf (fun i => (s i).law)
    (fun i x y => ∃ u v, y = (s i).exchange u v x)
    (fun i => ((s i).exposures : ℝ)) ?_ f b hb ?_ t
  · intro i g c hc he u
    exact (s i).mgf g hc (fun x v w => he x _ ⟨v,w,rfl⟩) u
  · intro i σ τ hagree hrel
    obtain ⟨u,v,he⟩ := hrel
    exact hchange i σ τ hagree u v he

theorem uniformSamples_absolute_tail
    {m : ℕ} {V : Fin m → Type*} [∀ i, Fintype (V i)]
    (s : ∀ i, UniformSampleSpec (V i)) (f : (∀ i, (s i).State) → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hchange : ∀ i (σ τ : ∀ j, (s j).State),
      (∀ j, j ≠ i → σ j = τ j) → ∀ u v,
      τ i = (s i).exchange u v (σ i) → |f σ - f τ| ≤ b i)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun i => (s i).law)).probability
      (fun σ => t ≤ |f σ - (FiniteLaw.pi (fun i => (s i).law)).expectation f|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i, ((s i).exposures : ℝ) * (b i) ^ 2)) := by
  exact finiteLaw_mgf_absolute_tail _ _
    (Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    (uniformSamples_mgf s f b hb hchange) ht

theorem uniformSamples_one_sided_tails
    {m : ℕ} {V : Fin m → Type*} [∀ i, Fintype (V i)]
    (s : ∀ i, UniformSampleSpec (V i)) (f : (∀ i, (s i).State) → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hchange : ∀ i (σ τ : ∀ j, (s j).State),
      (∀ j, j ≠ i → σ j = τ j) → ∀ u v,
      τ i = (s i).exchange u v (σ i) → |f σ - f τ| ≤ b i)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun i => (s i).law)).probability
      (fun σ => t ≤ f σ - (FiniteLaw.pi (fun i => (s i).law)).expectation f) ≤
      Real.exp (-2 * t ^ 2 / (∑ i, ((s i).exposures : ℝ) * (b i) ^ 2)) ∧
    (FiniteLaw.pi (fun i => (s i).law)).probability
      (fun σ => t ≤ (FiniteLaw.pi (fun i => (s i).law)).expectation f - f σ) ≤
      Real.exp (-2 * t ^ 2 / (∑ i, ((s i).exposures : ℝ) * (b i) ^ 2)) := by
  exact finiteLaw_mgf_one_sided_tails _ _
    (Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    (uniformSamples_mgf s f b hb hchange) ht

theorem uniformSamples_zero_variance
    {m : ℕ} {V : Fin m → Type*} [∀ i, Fintype (V i)]
    (s : ∀ i, UniformSampleSpec (V i)) (f : (∀ i, (s i).State) → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hchange : ∀ i (σ τ : ∀ j, (s j).State),
      (∀ j, j ≠ i → σ j = τ j) → ∀ u v,
      τ i = (s i).exchange u v (σ i) → |f σ - f τ| ≤ b i)
    (hv : ∑ i, ((s i).exposures : ℝ) * (b i) ^ 2 = 0) :
    ∀ σ, f σ = (FiniteLaw.pi (fun i => (s i).law)).expectation f := by
  intro σ
  refine finiteLaw_zero_mgf_constant _ _ ?_ σ ?_
  · intro u
    simpa only [hv] using uniformSamples_mgf s f b hb hchange u
  · change 0 < ∏ i, (s i).law.mass (σ i)
    exact Finset.prod_pos (fun i _ => (s i).mass_pos (σ i))

end Oberwolfach
