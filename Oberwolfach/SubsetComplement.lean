module

public import Oberwolfach.FixedSubsets

@[expose] public section

/-! Exposing the smaller of a fixed-cardinality subset and its complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fixedSubsetComplEquiv {V : Type*} [Fintype V] {r : ℕ}
    (hr : r ≤ Fintype.card V) : FixedSubset V r ≃ FixedSubset V (Fintype.card V - r) where
  toFun S := ⟨S.1ᶜ, by rw [Finset.card_compl, S.2]⟩
  invFun T := ⟨T.1ᶜ, by simp only [Finset.card_compl, T.2]; omega⟩
  left_inv S := by apply Subtype.ext; exact compl_compl _
  right_inv T := by apply Subtype.ext; exact compl_compl _

theorem fixedSubsetComplEquiv_map {V : Type*} [Fintype V] {r : ℕ}
    (hr : r ≤ Fintype.card V) (e : Equiv.Perm V) (S : FixedSubset V r) :
    fixedSubsetComplEquiv hr (fixedSubsetMap e S) =
      fixedSubsetMap e (fixedSubsetComplEquiv hr S) := by
  apply Subtype.ext
  ext x
  simp only [fixedSubsetComplEquiv, fixedSubsetMap, Equiv.coe_fn_mk,
    Finset.mem_compl, Finset.mem_map_equiv]

theorem fixedSubset_mgf_min
    {r : ℕ} {V : Type*} [Fintype V]
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V)
    (f : FixedSubset V r → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ S u v, |f S - f (fixedSubsetMap (Equiv.swap u v) S)| ≤ b)
    (t : ℝ) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => Real.exp (t * (f S - (FiniteLaw.uniform (FixedSubset V r)).expectation f))) ≤
      Real.exp (t ^ 2 * (min r (Fintype.card V - r) : ℕ) * b ^ 2 / 8) := by
  by_cases hsmall : r ≤ Fintype.card V - r
  · simpa only [min_eq_left hsmall] using fixedSubset_mgf hr f hb hexchange t
  · rw [min_eq_right (le_of_not_ge hsmall)]
    let e := fixedSubsetComplEquiv (V := V) hr
    let : Nonempty (FixedSubset V (Fintype.card V - r)) :=
      fixedSubset_nonempty (Nat.sub_le _ _)
    have hs (S : FixedSubset V (Fintype.card V - r)) (u v : V) :
        e.symm (fixedSubsetMap (Equiv.swap u v) S) =
          fixedSubsetMap (Equiv.swap u v) (e.symm S) := by
      apply e.injective
      rw [e.apply_symm_apply, fixedSubsetComplEquiv_map, e.apply_symm_apply]
    have hchange : ∀ S u v, |f (e.symm S) - f (e.symm (fixedSubsetMap (Equiv.swap u v) S))| ≤ b := by
      intro S u v
      rw [hs]
      exact hexchange _ _ _
    have h := fixedSubset_mgf (Nat.sub_le (Fintype.card V) r) (fun S => f (e.symm S)) hb hchange t
    have he (Y : FixedSubset V r → ℝ) :
        (FiniteLaw.uniform (FixedSubset V (Fintype.card V - r))).expectation (fun S => Y (e.symm S)) =
        (FiniteLaw.uniform (FixedSubset V r)).expectation Y := by
      rw [← finiteLaw_map_expectation, finiteLaw_uniform_map_equiv e.symm]
    rw [he f, he (fun S => Real.exp (t * (f S -
      (FiniteLaw.uniform (FixedSubset V r)).expectation f)))] at h
    exact h

theorem fixedSubset_absolute_tail
    {r : ℕ} {V : Type*} [Fintype V]
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V)
    (f : FixedSubset V r → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ S u v, |f S - f (fixedSubsetMap (Equiv.swap u v) S)| ≤ b)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (FixedSubset V r)).probability
      (fun S => t ≤ |f S - (FiniteLaw.uniform (FixedSubset V r)).expectation f|) ≤
      2 * Real.exp (-2 * t ^ 2 / ((min r (Fintype.card V - r) : ℕ) * b ^ 2)) := by
  apply finiteLaw_mgf_absolute_tail _ _ (by positivity) _ ht
  intro u
  simpa only [mul_assoc] using fixedSubset_mgf_min hr f hb hexchange u

end Oberwolfach
