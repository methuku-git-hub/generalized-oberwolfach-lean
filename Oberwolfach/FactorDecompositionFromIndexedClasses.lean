module

public import Oberwolfach.FactorDecompositionClasses

@[expose] public section
/-! Glue decompositions indexed by finite lists back into the original list
of prescribed factors, without changing their order or isomorphism types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_decomposition_from_indexed_classes
    {n q:ℕ} {J:Type} [DecidableEq J]
    (G:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n))
    (classes:J→SimpleGraph (Fin n)) (colour:Fin q→J)
    (hclasses:∀x y,(G.Adj x y↔∃j,(classes j).Adj x y) ∧
      ∀j k,(classes j).Adj x y→(classes k).Adj x y→j=k)
    (hlocal:∀j,
      let e:=Fintype.equivFin {i:Fin q // colour i=j}
      HasFactorDecomposition (classes j) (fun k=>F (e.symm k).val)):
    HasFactorDecomposition G F :=by
  apply factor_decomposition_from_classes G F classes colour hclasses
  intro j
  let e:=Fintype.equivFin {i:Fin q // colour i=j}
  obtain ⟨pieces,hpart,hiso⟩:=hlocal j
  refine ⟨fun i=>pieces (e i),?_,?_,?_⟩
  · intro x y
    constructor
    · intro h
      obtain ⟨k,hk⟩:=((hpart x y).1.mp h)
      exact ⟨e.symm k,by simpa using hk⟩
    · rintro ⟨i,hi⟩
      exact (hpart x y).1.mpr ⟨e i,hi⟩
  · intro i k x y hi hk
    exact e.injective ((hpart x y).2 (e i) (e k) hi hk)
  · intro i
    have hh:=hiso (e i)
    change Nonempty (pieces (e i) ≃g F (e.symm (e i)).val) at hh
    simpa only [Equiv.symm_apply_apply] using hh
end Oberwolfach
