module

public import Oberwolfach.FiniteLawComposition

@[expose] public section
/-! Transport a finite law through an equivalence in either direction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_map_equiv_inverse {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (e : A ≃ B)
    (h : μ.map e = ν) : ν.map e.symm = μ := by
  rw [← h, finiteLaw_map_map]
  have he : (fun x => e.symm (e x)) = id := by funext x; exact e.symm_apply_apply x
  rw [he]
  apply finiteLaw_ext
  intro x
  simp [FiniteLaw.map, Finset.sum_ite_eq']
end Oberwolfach
