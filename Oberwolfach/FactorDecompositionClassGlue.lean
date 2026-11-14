module

public import Oberwolfach.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem factor_decomposition_class_glue
    {n q:ℕ} {J:Type} (G:SimpleGraph (Fin n)) (F pieces:Fin q→SimpleGraph (Fin n))
    (classes:J→SimpleGraph (Fin n)) (colour:Fin q→J)
    (hclasses:∀x y,(G.Adj x y↔∃j,(classes j).Adj x y) ∧
      ∀j k,(classes j).Adj x y→(classes k).Adj x y→j=k)
    (hcover:∀j x y,(classes j).Adj x y↔∃i,colour i=j ∧ (pieces i).Adj x y)
    (hunique:∀i k x y,colour i=colour k→(pieces i).Adj x y→(pieces k).Adj x y→i=k)
    (hiso:∀i,Nonempty (pieces i ≃g F i)):
    HasFactorDecomposition G F := by
  refine ⟨pieces,?_,hiso⟩
  intro x y
  obtain ⟨hcoverG,huniqueG⟩:=hclasses x y
  constructor
  · rw [hcoverG]
    constructor
    · rintro ⟨j,hj⟩
      obtain ⟨i,hi,hpi⟩:=(hcover j x y).mp hj
      exact ⟨i,hpi⟩
    · rintro ⟨i,hi⟩
      exact ⟨colour i,(hcover (colour i) x y).mpr ⟨i,rfl,hi⟩⟩
  · intro i k hi hk
    have hci:(classes (colour i)).Adj x y:=(hcover (colour i) x y).mpr ⟨i,rfl,hi⟩
    have hck:(classes (colour k)).Adj x y:=(hcover (colour k) x y).mpr ⟨k,rfl,hk⟩
    exact hunique i k x y (huniqueG (colour i) (colour k) hci hck) hi hk
end Oberwolfach
