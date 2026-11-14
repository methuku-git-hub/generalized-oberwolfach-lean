module

public import Oberwolfach.CyclicBoundaryJoint
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! Concatenating interval paths with the boundary joint obtained from a
complementary chain. Path identities and their separate weights are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclic_path_weighting_with_formula {k : ℕ} {X : Type*} [Fintype X]
    {P : Fin (k + 2) → Type*} [∀ i, Fintype (P i)]
    (m : Fin (k + 2) → X → ℝ) (K : Fin (k + 2) → X → X → ℝ)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)))
    (c : Fin (k + 2)) (Q : X → X → ℝ)
    (hQ : ∀ x z, Q x z =
      walkTransport m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1) z x)
    (B : ℝ) (hB : 0 < B) (hms : ∀ i, ∑ x, m i x = B)
    (w : ∀ i, P i → ℝ) (hw : ∀ i p, 0 ≤ w i p)
    (hws : ∀ i, ∑ p, w i p = B)
    (f : ∀ i, P i → X × X)
    (hf : ∀ i x z, (∑ p, if f i p = (x, z) then w i p else 0) =
      if i = c then Q x z else K i x z) :
    ∃ ω : (∀ i, P i) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p) = B ∧
      (∀ i q, (∑ p, if p i = q then ω p else 0) = w i q) ∧
      (∀ p, 0 < ω p → ∀ i,
        (f i (p i)).2 = (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) ∧
      (∀ p, (∀ i, (f i (p i)).2 =
          (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) →
        ω p = chainJoint m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1)
          (fun j => (f (cyclicChainOrder c j) (p (cyclicChainOrder c j))).1) *
        ∏ i, w i (p i) / (if i = c then Q (f i (p i)).1 (f i (p i)).2
          else K i (f i (p i)).1 (f i (p i)).2)) := by
  let J := chainJoint m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1)
  have hJ0 (v : Fin (k + 2) → X) : 0 ≤ J v :=
    chainJoint_nonneg m K (finRotate (k + 2)) (fun i x => (hm i x).le)
      (fun i x z => (hK i).1 x z) _ _ v
  have hJs : ∑ v, J v = B := by
    rw [chainJoint_total m K (finRotate (k + 2)) hm hK, hms]
  have hJm (i : Fin (k + 2)) (e : X × X) :
      (∑ v, if cyclicBoundaryPair c i v = e then J v else 0) =
        ∑ p, if f i p = e then w i p else 0 := by
    rcases e with ⟨x, z⟩
    rw [hf i x z]
    exact complementaryBoundaryJoint_marginal m K hm hK c Q hQ i x z
  obtain ⟨W, hW, htotal, hboundary, hpaths, hsupport, hformula⟩ :=
    weighted_conditional_realization_with_formula J w B hB hJ0 hw hJs hws
      (cyclicBoundaryPair c) f (by
        intro i e
        convert hJm i e using 1 <;>
          (apply Finset.sum_congr rfl; intro t _; split_ifs <;> rfl))
  let ω (p : ∀ i, P i) := ∑ v, W ⟨v, p⟩
  refine ⟨ω, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact Finset.sum_nonneg fun v _ => hW ⟨v, p⟩
  · dsimp only [ω]
    rw [Finset.sum_comm, ← Fintype.sum_sigma]
    exact htotal
  · intro i q
    change (∑ p, if p i = q then (∑ v, W ⟨v, p⟩) else 0) = _
    have hid (p : ∀ i, P i) :
        (if p i = q then (∑ v, W ⟨v, p⟩) else 0) =
        ∑ v, if p i = q then W ⟨v, p⟩ else 0 := by
      split_ifs <;> simp
    simp_rw [hid]
    rw [Finset.sum_comm]
    have hh := hpaths i q
    rw [Fintype.sum_sigma] at hh
    exact hh
  · intro p hp i
    by_contra hbad
    have hz (v : Fin (k + 2) → X) : W ⟨v, p⟩ = 0 := by
      by_contra hne
      have hv : 0 < W ⟨v, p⟩ := lt_of_le_of_ne (hW ⟨v, p⟩) (Ne.symm hne)
      have hs := hsupport v p hv
      apply hbad
      rw [hs i, hs (finRotate (k + 2) i)]
      exact cyclicBoundaryPair_consistent c i v
    have hzero : ω p = 0 := Finset.sum_eq_zero fun v _ => hz v
    rw [hzero] at hp
    exact (lt_irrefl 0) hp
  · intro p hp
    let v₀ (j : Fin (k + 2)) := (f (cyclicChainOrder c j) (p (cyclicChainOrder c j))).1
    have hzero (v : Fin (k + 2) → X) (hv : v ≠ v₀) : W ⟨v, p⟩ = 0 := by
      by_contra hne
      have hpos : 0 < W ⟨v, p⟩ := lt_of_le_of_ne (hW ⟨v, p⟩) (Ne.symm hne)
      apply hv
      funext j
      have hh := congrArg Prod.fst (hsupport v p hpos (cyclicChainOrder c j))
      simpa only [cyclicBoundaryPair, Equiv.symm_apply_apply, v₀] using hh.symm
    have hsum : ω p = W ⟨v₀, p⟩ := by
      exact Finset.sum_eq_single v₀ (fun v _ hv => hzero v hv)
        (fun h => False.elim (h (Finset.mem_univ v₀)))
    have hpair (i : Fin (k + 2)) : cyclicBoundaryPair c i v₀ = f i (p i) := by
      apply Prod.ext
      · change (f (cyclicChainOrder c ((cyclicChainOrder c).symm i))
          (p (cyclicChainOrder c ((cyclicChainOrder c).symm i)))).1 = _
        rw [(cyclicChainOrder c).apply_symm_apply i]
      · change (f (cyclicChainOrder c ((cyclicChainOrder c).symm (finRotate (k + 2) i)))
          (p (cyclicChainOrder c ((cyclicChainOrder c).symm (finRotate (k + 2) i))))).1 = _
        rw [(cyclicChainOrder c).apply_symm_apply]
        exact (hp i).symm
    rw [hsum, hformula]
    change J v₀ * _ = J v₀ * _
    apply congrArg (fun z => J v₀ * z)
    apply Finset.prod_congr rfl
    intro i _
    rw [hpair i]
    simp only [ite_true]
    apply congrArg (fun z => w i (p i) / z)
    convert hf i (f i (p i)).1 (f i (p i)).2 using 1 <;>
      (apply Finset.sum_congr rfl; intro q _; split_ifs <;> rfl)

theorem cyclic_path_weighting {k : ℕ} {X : Type*} [Fintype X]
    {P : Fin (k + 2) → Type*} [∀ i, Fintype (P i)]
    (m : Fin (k + 2) → X → ℝ) (K : Fin (k + 2) → X → X → ℝ)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)))
    (c : Fin (k + 2)) (Q : X → X → ℝ)
    (hQ : ∀ x z, Q x z =
      walkTransport m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1) z x)
    (B : ℝ) (hB : 0 < B) (hms : ∀ i, ∑ x, m i x = B)
    (w : ∀ i, P i → ℝ) (hw : ∀ i p, 0 ≤ w i p)
    (hws : ∀ i, ∑ p, w i p = B)
    (f : ∀ i, P i → X × X)
    (hf : ∀ i x z, (∑ p, if f i p = (x, z) then w i p else 0) =
      if i = c then Q x z else K i x z) :
    ∃ ω : (∀ i, P i) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p) = B ∧
      (∀ i q, (∑ p, if p i = q then ω p else 0) = w i q) ∧
      (∀ p, 0 < ω p → ∀ i,
        (f i (p i)).2 = (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) := by
  obtain ⟨ω, hω, ht, hmarg, hs, _⟩ := cyclic_path_weighting_with_formula
    m K hm hK c Q hQ B hB hms w hw hws f hf
  exact ⟨ω, hω, ht, hmarg, hs⟩

end Oberwolfach
