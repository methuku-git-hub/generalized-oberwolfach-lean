module

public import Oberwolfach.PrescribedFamilyUpdate

@[expose] public section
/-! Track the exact assigned domain: prescribed source vertices together with
the free occurrences processed so far. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X:Type} [DecidableEq I] [DecidableEq X]

theorem prescribed_family_domains_update (A A₀:I→Finset X) (T:Finset (I×X)) (k:I) (C:Finset X)
    (hdom:∀ i x,x∈A i ↔ x∈A₀ i ∨ (i,x)∈T):
    let A':=Function.update A k (A k∪C);
    let T':=T∪({k}:Finset I).product C;
    ∀ i x,x∈A' i ↔ x∈A₀ i ∨ (i,x)∈T' := by
  intro A' T' i x
  by_cases hi:i=k
  · subst i
    have hp:((k,x)∈({k}:Finset I).product C) ↔ x∈C:=by
      constructor
      · intro h;exact (Finset.mem_product.mp h).2
      · intro h;exact Finset.mem_product.mpr ⟨by simp,h⟩
    simp only [A',T',Function.update_self,Finset.mem_union]
    rw [hdom k x,hp]
    tauto
  · have hp:(i,x)∉({k}:Finset I).product C:=by
      intro h
      have hh: i∈({k}:Finset I):=(Finset.mem_product.mp h).1
      exact hi (by simpa using hh)
    simp only [A',T',Function.update_of_ne hi,Finset.mem_union,hp,or_false]
    exact hdom i x
end Oberwolfach
