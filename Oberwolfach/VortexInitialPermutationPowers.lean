module

public import Oberwolfach.VortexInitialPermutation
public import Oberwolfach.PermutationClose

@[expose] public section
/-! Iterates, short cycles and permutation-closeness agree at the initial
full vortex domain under the canonical embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
theorem vortex_initial_permutation_pow (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V) (k:ℕ) (x:Q.vertices 0):
    (((vortexInitialPermutation G D m β ε Q π)^k) x).val=(π^k) x.val := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,vortex_initial_permutation_commutes,ih,pow_succ',Equiv.Perm.mul_apply]

theorem vortex_initial_no_short_cycles (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V) (h:ℕ)
    (hπ:∀ x k,0<k→k<h→(π^k) x≠x):
    ∀ x:Q.vertices 0,∀ k,0<k→k<h→((vortexInitialPermutation G D m β ε Q π)^k) x≠x := by
  intro x k hk hkh heq
  have hh:=congrArg Subtype.val heq
  rw [vortex_initial_permutation_pow] at hh
  exact hπ x.val k hk hkh hh

theorem vortex_initial_permutation_close_iff (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V) (h:ℕ) (x y:Q.vertices 0):
    PermutationClose (vortexInitialPermutation G D m β ε Q π) h x y ↔
      PermutationClose π h x.val y.val := by
  simp only [PermutationClose]
  constructor
  · rintro (hxy | ⟨j,hxy | hyx⟩)
    · exact Or.inl (congrArg Subtype.val hxy)
    · right; refine ⟨j,Or.inl ?_⟩
      simpa only [vortex_initial_permutation_pow] using congrArg Subtype.val hxy
    · right; refine ⟨j,Or.inr ?_⟩
      simpa only [vortex_initial_permutation_pow] using congrArg Subtype.val hyx
  · rintro (hxy | ⟨j,hxy | hyx⟩)
    · exact Or.inl (Subtype.ext hxy)
    · right; refine ⟨j,Or.inl (Subtype.ext ?_)⟩
      simpa only [vortex_initial_permutation_pow] using hxy
    · right; refine ⟨j,Or.inr (Subtype.ext ?_)⟩
      simpa only [vortex_initial_permutation_pow] using hyx
end Oberwolfach
