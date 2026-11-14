module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedReservedStarClearing

@[expose] public section

/-! The remaining finite occurrence sets have empty inner star after
reservation and the prescribed-edge packing, using its exact inner
intersection. This is the support conclusion required by the deep stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
  {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_finite_prescribed_star_clearing
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A DA:Finset (E⊕K)) (S DS:Finset (V×U)) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (hD:markedFiniteResources tail head ktail khead π DA DS⊆
      (markedFiniteResources tail head ktail khead π A S).filter (markedInnerResource I J))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedStarResource T W)):
    let CA:=(A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ((markedFiniteResources tail head ktail khead π
      ((A\KA)\M.biUnion markedWheelArcs) ((S\KS)\M.biUnion markedWheelSpokePairs)).filter
      (markedInnerResource I J)).filter (markedStarResource T W)=∅:=by
  dsimp only
  rw [markedFiniteResources_sdiff tail head ktail khead π hp,
    markedFiniteResources_sdiff tail head ktail khead π hp,
    markedFiniteResources_star tail head ktail khead π _ _ T W hT,
    markedFiniteResources_sdiff tail head ktail khead π hp,
    markedFiniteResources_inner tail head ktail khead π _ _ I J hI,
    markedPackingResources_eq_finite]
  exact (marked_reserved_star_clearing
    (markedFiniteResources tail head ktail khead π A S)
    (markedFiniteResources tail head ktail khead π DA DS)
    (M.biUnion markedWheelPhysicalResources) I T J W hD hM).2

end Oberwolfach
