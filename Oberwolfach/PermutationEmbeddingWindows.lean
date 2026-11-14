module

public import Oberwolfach.PermutationWindows

@[expose] public section

/-! Permutation windows on an invariant embedded vertex domain. No vertices
are skipped when passing to the restricted permutation. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (f : W→V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
  (hcomm : ∀ x,f (ρ x)=π (f x))
include hcomm

theorem permutation_embedding_power (n : ℕ) (x : W) : f ((ρ^n) x)=(π^n) (f x) := by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [pow_succ',Equiv.Perm.mul_apply,hcomm,ih]

theorem permutation_embedding_inverse_power (n : ℕ) (x : W) :
    f ((ρ^n).symm x)=(π^n).symm (f x) := by
  apply (π^n).injective
  rw [← permutation_embedding_power f π ρ hcomm n,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem permutationWindow_image (l r : ℕ) (x : W) :
    (permutationWindow ρ l r x).image f=permutationWindow π l r (f x) := by
  simp only [permutationWindow,Finset.image_image]
  congr 1
  funext i
  simp only [Function.comp_apply,permutation_embedding_power f π ρ hcomm,
    permutation_embedding_inverse_power f π ρ hcomm]

theorem permutationWindow_embedding_mem (hf : Function.Injective f) (l r : ℕ) (x y : W) :
    f y∈permutationWindow π l r (f x) ↔ y∈permutationWindow ρ l r x := by
  rw [← permutationWindow_image f π ρ hcomm l r x,Finset.mem_image]
  constructor
  · rintro ⟨z,hz,hzy⟩;exact hf hzy ▸ hz
  · intro hy;exact ⟨y,hy,rfl⟩

theorem permutationClose_embedding (hf : Function.Injective f) (b : ℕ) (x y : W) :
    PermutationClose π b (f x) (f y) ↔ PermutationClose ρ b x y := by
  simp only [PermutationClose,← permutation_embedding_power f π ρ hcomm,hf.eq_iff]

end Oberwolfach
