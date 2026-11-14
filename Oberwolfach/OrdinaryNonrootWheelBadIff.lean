module

public import Oberwolfach.OrdinaryInducedWheelWeight
public import Oberwolfach.FiniteWeightedPartition

@[expose] public section
/-! Exact parent = induced + excluded wheel-load identities on the same
sample, for rim and spoke edges in adaptive nonroot domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_wheel_bad_iff (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T:Finset V) (W:Finset U) (C:OrdinaryWheel Q F H r):
    ¬((ordinaryWheelRim C).support⊆(↑(Finset.univ\T):Set V) ∧ ordinaryWheelHub C∈Finset.univ\W) ↔
      ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support:=by
  constructor
  · intro hg
    by_cases hu:ordinaryWheelHub C∈W
    · exact Or.inl hu
    · right
      by_contra hn
      apply hg
      constructor
      · intro z hz
        simp only [Finset.coe_sdiff,Finset.coe_univ,Set.mem_sdiff,Set.mem_univ,true_and]
        intro hzT
        exact hn ⟨z,hzT,hz⟩
      · simp [hu]
  · rintro (hu|⟨z,hzT,hz⟩) ⟨hsub,hhub⟩
    · exact (Finset.mem_sdiff.mp hhub).2 hu
    · exact (Finset.mem_sdiff.mp (hsub hz)).2 hzT

end Oberwolfach
