module

public import Oberwolfach.LongEveryClassRetainedGlobalSameDeletion

@[expose] public section
/-! Instantiate the regular-class event with the actual protected inner
pair and the actual matching/absorber resource graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_protected_regular_class_selection
    {n:ℕ} (P Sample Z A:SimpleGraph (Fin n)) (I:Finset (Fin n))
    (k Bpart:ℕ) (ξ:ℝ)
    (hInner:∀x∈I,∀y∈I,x≠y→Z.Adj x y)
    (hA:∀v,A.degree v≤Bpart) (hSample:A≤Sample)
    (hPart:∀T:SimpleGraph (Fin n),(∀v,T.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*k) ∧
        (∀x y,(Z⊔T).Adj x y→(S.Adj x y↔Sample.Adj x y)) ∧
        (∀v,((changed (Sample.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)):
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*k) ∧
      (∀v,((changed (Sample.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n) ∧
      (∀x∈I,∀y∈I,S.Adj x y↔Sample.Adj x y) ∧ A≤S := by
  obtain ⟨S,hSP,hreg,hagree,hedit⟩:=hPart A hA
  refine ⟨S,hSP,hreg,hedit,?_,?_⟩
  · intro x hx y hy
    by_cases hxy:x=y
    · subst y; simp
    · exact hagree x y ((show Z≤Z⊔A from le_sup_left) (hInner x hx y hy hxy))
  · intro x y hxy
    exact (hagree x y ((show A≤Z⊔A from le_sup_right) hxy)).2 (hSample hxy)
end Oberwolfach
