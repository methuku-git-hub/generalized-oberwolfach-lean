module

public import Oberwolfach.PermutationEmbeddingWindows

@[expose] public section

/-! Fixed invariant domains remain invariant under a commuting embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Oberwolfach

theorem permutation_invariant_image {V W : Type*} [DecidableEq V]
    (f : W→V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hcomm : ∀ x,f (ρ x)=π (f x)) (A : Finset W) (hA : ∀ x,ρ x∈A ↔ x∈A) :
    ∀ x,π x∈A.image f ↔ x∈A.image f := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hy' : ρ.symm y∈A := (hA (ρ.symm y)).mp (by simpa only [ρ.apply_symm_apply] using hy)
    have he' : f (ρ.symm y)=x := π.injective (by rw [← hcomm,ρ.apply_symm_apply,he])
    exact Finset.mem_image.mpr ⟨ρ.symm y,hy',he'⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨ρ y,(hA y).mpr hy,(hcomm y).trans (congrArg π he)⟩

end Oberwolfach
