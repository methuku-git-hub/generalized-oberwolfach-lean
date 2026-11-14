module

public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! Extend one factor's partial vertex map without changing the others. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [DecidableEq I] [DecidableEq X]

def FamilyPartialInjections (A:I→Finset X) (f:I→X→V):Prop:=
  ∀ i,Set.InjOn (f i) (A i)

theorem prescribed_family_update (A:I→Finset X) (f:I→X→V) (k:I)
    (C:Finset X) (g:X→V) (hinj:FamilyPartialInjections A f)
    (hg:Set.InjOn g (↑(A k∪C):Set X)) (hpres:∀ x∈A k,g x=f k x):
    let A':=Function.update A k (A k∪C);
    let f':=Function.update f k g;
    FamilyPartialInjections A' f' ∧
      (∀ i x,x∈A i→f' i x=f i x) ∧
      (∀ i,i≠k→A' i=A i ∧ f' i=f i) := by
  intro A' f'
  constructor
  · intro i
    by_cases hi:i=k
    · subst i;simpa [A',f'] using hg
    · simpa [A',f',Function.update_of_ne hi] using hinj i
  constructor
  · intro i x hx
    by_cases hi:i=k
    · subst i;simpa [f'] using hpres x hx
    · simp [f',Function.update_of_ne hi]
  · intro i hi
    simp [A',f',Function.update_of_ne hi]
end Oberwolfach
