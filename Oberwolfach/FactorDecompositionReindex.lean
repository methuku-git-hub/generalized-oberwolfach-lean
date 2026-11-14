module

public import Oberwolfach.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem factor_decomposition_reindex
    {n q:ℕ} {U:Type} (e:Fin q≃U) (S:SimpleGraph (Fin n))
    (F pieces:U→SimpleGraph (Fin n))
    (hpartition:∀x y,(S.Adj x y↔∃u,(pieces u).Adj x y) ∧
      ∀u v,(pieces u).Adj x y→(pieces v).Adj x y→u=v)
    (hiso:∀u,Nonempty (pieces u ≃g F u)):
    HasFactorDecomposition S (fun i=>F (e i)) := by
  refine ⟨fun i=>pieces (e i),?_,fun i=>hiso (e i)⟩
  intro x y
  obtain ⟨hcover,hunique⟩:=hpartition x y
  constructor
  · rw [hcover]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨e.symm u,by simpa using hu⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
  · intro i j hi hj
    apply e.injective
    exact hunique (e i) (e j) hi hj
end Oberwolfach
