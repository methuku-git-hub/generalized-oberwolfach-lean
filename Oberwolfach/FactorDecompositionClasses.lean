module

public import Oberwolfach.FactorDecompositionClassGlue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_decomposition_from_classes
    {n q:ℕ} {J:Type} (G:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n))
    (classes:J→SimpleGraph (Fin n)) (colour:Fin q→J)
    (hclasses:∀x y,(G.Adj x y↔∃j,(classes j).Adj x y) ∧
      ∀j k,(classes j).Adj x y→(classes k).Adj x y→j=k)
    (hlocal:∀j,∃pieces:{i:Fin q // colour i=j}→SimpleGraph (Fin n),
      (∀x y,(classes j).Adj x y↔∃i,(pieces i).Adj x y) ∧
      (∀i k x y,(pieces i).Adj x y→(pieces k).Adj x y→i=k) ∧
      (∀i,Nonempty (pieces i ≃g F i.val))):
    HasFactorDecomposition G F := by
  let part:=fun j=>Classical.choose (hlocal j)
  have hpart:∀j,(∀x y,(classes j).Adj x y↔∃i,(part j i).Adj x y) ∧
      (∀i k x y,(part j i).Adj x y→(part j k).Adj x y→i=k) ∧
      (∀i,Nonempty (part j i ≃g F i.val)):=fun j=>Classical.choose_spec (hlocal j)
  let pieces:Fin q→SimpleGraph (Fin n):=fun i=>part (colour i) ⟨i,rfl⟩
  apply factor_decomposition_class_glue G F pieces classes colour hclasses
  · intro j x y
    constructor
    · intro hj
      obtain ⟨⟨i,hi⟩,hpi⟩:=((hpart j).1 x y).mp hj
      refine ⟨i,hi,?_⟩
      subst j
      exact hpi
    · rintro ⟨i,hi,hpi⟩
      subst j
      exact ((hpart (colour i)).1 x y).mpr ⟨⟨i,rfl⟩,hpi⟩
  · intro i k x y hcolour hi hk
    have hk':(part (colour i) ⟨k,hcolour.symm⟩).Adj x y:=by
      have htransport (j:J) (hj:colour k=j):part j ⟨k,hj⟩=pieces k:=by
        cases hj
        rfl
      rw [htransport (colour i) hcolour.symm]
      exact hk
    have heq: (⟨i,rfl⟩:{t:Fin q // colour t=colour i})=⟨k,hcolour.symm⟩:=
      (hpart (colour i)).2.1 ⟨i,rfl⟩ ⟨k,hcolour.symm⟩ x y hi hk'
    exact congrArg Subtype.val heq
  · intro i
    exact (hpart (colour i)).2.2 ⟨i,rfl⟩
end Oberwolfach
