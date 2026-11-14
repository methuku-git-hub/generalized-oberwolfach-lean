module

public import Oberwolfach.Definitions

@[expose] public section
/-! A decomposition of a positive number of copies yields one actual spanning
copy. This is the last step in the manuscript's density-one reduction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_decomposition_single_copy {n q:ℕ} (hq:0<q)
    (G F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (hdec:HasFactorDecomposition G (fun _:Fin q=>F)):
    ∃ H:SimpleGraph (Fin n),H≤G ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F):=by
  obtain ⟨pieces,hpart,hiso⟩:=hdec
  let i:Fin q:=⟨0,hq⟩
  obtain ⟨e⟩:=hiso i
  refine ⟨pieces i,?_,?_,⟨e⟩⟩
  · intro u v huv
    exact ((hpart u v).1).2 ⟨i,huv⟩
  · intro v
    have h:=e.degree_eq v
    rw [hF (e v)] at h
    exact h.symm
end Oberwolfach
