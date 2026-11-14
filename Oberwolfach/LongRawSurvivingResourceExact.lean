module

public import Oberwolfach.LongRawSurvivingResourceState

@[expose] public section
/-! Exact resource membership after deleting physical rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_resource_iff
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (z:LongRawHubResource n U):
    z∈longRawSurvivingResources P π d raw g j F ↔
      z∈bernoulliVertexSet (longRawHubState P π d raw g j) ∧
      ∀edge,typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F :=by
  simp only [longRawSurvivingResources,Finset.mem_filter]
  constructor
  · rintro ⟨hz,h⟩
    refine ⟨hz,?_⟩
    intro edge he
    rw [he] at h
    exact h
  · rintro ⟨hz,h⟩
    refine ⟨hz,?_⟩
    cases hphys:typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z) with
    | inl edge => exact h edge hphys
    | inr spoke => trivial
end Oberwolfach
