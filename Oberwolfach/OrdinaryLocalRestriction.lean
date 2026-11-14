module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.CandidateResourceRestriction
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! The exact restriction of the local ordinary cycle family. The parent
cycle is unchanged; only its host and the allowed vertex set are restricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

abbrev localOrdinaryRestrictionGood (Q' : SimpleGraph V) (T' : Finset V)
    {Q F : SimpleGraph V} {T : Finset V} (C : LocalOrdinaryCycle Q F T r) : Prop :=
  C.val.val.val≤Q' ∧ localOrdinaryVertices C⊆T'

def localOrdinaryRestrictionParent {Q Q' F : SimpleGraph V} {T T' : Finset V}
    (hQ : Q'≤Q) (hT : T'⊆T) : LocalOrdinaryCycle Q' F T' r ↪ LocalOrdinaryCycle Q F T r where
  toFun C := ⟨⟨C.val.val,C.val.property.trans hQ⟩,
    fun v hv=>hT (C.property.1 v hv),C.property.2⟩
  inj' := by intro C D he;apply Subtype.ext;apply Subtype.ext;exact congrArg (fun C=>C.val.val) he

def localOrdinaryRestrictionEquiv (Q Q' F : SimpleGraph V) (T T' : Finset V)
    (hQ : Q'≤Q) (hT : T'⊆T) : LocalOrdinaryCycle Q' F T' r ≃
      {C : LocalOrdinaryCycle Q F T r // localOrdinaryRestrictionGood Q' T' C} where
  toFun C := ⟨localOrdinaryRestrictionParent hQ hT C,C.val.property,
    fun v hv=>C.property.1 v (Set.mem_toFinset.mp hv)⟩
  invFun C := ⟨⟨C.val.val.val,C.property.1⟩,
    fun v hv=>C.property.2 (Set.mem_toFinset.mpr hv),C.val.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem localOrdinaryRestriction_degree (Q Q' F : SimpleGraph V) (T T' : Finset V)
    (hQ : Q'≤Q) (hT : T'⊆T) (w : LocalOrdinaryCycle Q F T r → ℝ) (v : V) :
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C=>w (localOrdinaryRestrictionParent hQ hT C)) v=
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C=>if localOrdinaryRestrictionGood Q' T' C then w C else 0) v := by
  have hs := (localOrdinaryRestrictionEquiv (r:=r) Q Q' F T T' hQ hT).symm.sum_comp
    (fun C : LocalOrdinaryCycle Q' F T' r=>if v∈localOrdinaryVertices C then
      w (localOrdinaryRestrictionParent hQ hT C) else 0)
  have hh := candidate_resource_degree (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T))
    (localOrdinaryRestrictionGood Q' T') w v
  unfold hypergraphWeightedDegree at *
  calc
    _ = ∑ C : {C : LocalOrdinaryCycle Q F T r // localOrdinaryRestrictionGood Q' T' C},
      if v∈localOrdinaryVertices C.val then w C.val else 0 := hs.symm
    _ = _ := hh

end Oberwolfach
