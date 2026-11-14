module

public import Oberwolfach.OrdinaryLocalRestriction
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Restricting the host to a set containing the entire local domain leaves
the cycle family and all its weighted vertex loads unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_weights_restrict_host
    (Q F:SimpleGraph V) (T X:Finset V) (hTX:T⊆X)
    (w:LocalOrdinaryCycle Q F T r→ℝ):
    ∃w':LocalOrdinaryCycle (spanningRestriction Q X) F T r→ℝ,
      (∀C,w' C=w (localOrdinaryRestrictionParent
        (show spanningRestriction Q X≤Q from fun a b h=>(spanningRestriction_adj Q X a b).mp h |>.1)
        (Finset.Subset.rfl) C)) ∧
      (∀v,hypergraphWeightedDegree localOrdinaryVertices w' v=
        hypergraphWeightedDegree localOrdinaryVertices w v):=by
  let hQ:spanningRestriction Q X≤Q:=fun a b h=>(spanningRestriction_adj Q X a b).mp h |>.1
  let w':LocalOrdinaryCycle (spanningRestriction Q X) F T r→ℝ:=
    fun C=>w (localOrdinaryRestrictionParent hQ (Finset.Subset.rfl) C)
  have hgood (C:LocalOrdinaryCycle Q F T r):
      localOrdinaryRestrictionGood (spanningRestriction Q X) T C:=by
    constructor
    · intro a b hab
      exact (spanningRestriction_adj Q X a b).mpr ⟨C.val.property hab,
        hTX (C.property.1 a hab.mem_support_left), hTX (C.property.1 b hab.mem_support_right)⟩
    · intro a ha
      exact C.property.1 a (Set.mem_toFinset.mp ha)
  refine ⟨w',?_,?_⟩
  · intro C
    rfl
  · intro v
    have hh:=localOrdinaryRestriction_degree Q (spanningRestriction Q X) F T T hQ (Finset.Subset.rfl) w v
    have heq:(fun C:LocalOrdinaryCycle Q F T r=>
        if localOrdinaryRestrictionGood (spanningRestriction Q X) T C then w C else 0)=w:=by
      funext C
      rw [if_pos (hgood C)]
    rw [heq] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
