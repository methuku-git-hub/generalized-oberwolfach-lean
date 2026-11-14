module

public import Oberwolfach.LongPreparationRetainedLengths

@[expose] public section
/-! Globally retained short lengths are allowed lengths in actual factors;
non-retained lengths carry zero coefficients at every hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_family_retained_lengths {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2) (S:Set ℕ)
    (hS:∀ u,AllowedCycleLengths (F u) S) (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ):
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let retained:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i);
    (∀ i∈retained, (3 : ℕ) ≤ (i.val + 1) ∧ (i.val + 1) ∈ S ∧
      ∃ (u : U) (v : Fin n), Fintype.card ((F u).connectedComponentMk v) = i.val + 1) ∧
    (∀ i∉retained,∀ u,¬θ/(100*(K:ℝ))≤fraction u i):=by
  intro fraction retained
  constructor
  · intro i hi
    obtain ⟨u,hu⟩:=(Finset.mem_filter.mp hi).2
    have hh:=long_preparation_retained_length_allowed hn (F u) (hF u) S (hS u) K hK θ hθ i hu
    exact ⟨hh.1,hh.2.1,u,hh.2.2⟩
  · intro i hi u hu
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,u,hu⟩

/-- The seed theorem requires positive parameters for every index, including
indices which carry no short cycles. -/
theorem long_preparation_seed_indices {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2) (S:Set ℕ)
    (hS:∀ u,AllowedCycleLengths (F u) S) (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ):
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let retained:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let seedLen:=fun i:Fin K=>max 1 (i.val-1);
    (∀ i,1≤seedLen i) ∧
    (∀ i∈retained,seedLen i+2=i.val+1 ∧ seedLen i+2∈S):=by
  intro fraction retained seedLen
  have hret:=long_preparation_family_retained_lengths hn F hF S hS K hK θ hθ
  constructor
  · intro i
    exact le_max_left _ _
  · intro i hi
    have hh:=hret.1 i hi
    have heq:seedLen i+2=i.val+1:=by
      dsimp [seedLen]
      have h : 1 ≤ i.val - 1 := by omega
      rw [max_eq_right h]
      omega
    exact ⟨heq,heq.symm ▸ hh.2.1⟩
end Oberwolfach
