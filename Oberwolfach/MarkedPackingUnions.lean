module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! Physical rim graphs and actual spoke relations of unions of wheel
families. These identities do not replace edge-disjointness hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem markedPackingRimGraph_union
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    markedPackingRimGraph (M∪N)=markedPackingRimGraph M⊔markedPackingRimGraph N:=by
  ext v w
  simp only [markedPackingRimGraph,markedPackingRims,physicalEdgeGraph,Finset.union_biUnion,
    Finset.mem_union,SimpleGraph.sup_adj]
  tauto

theorem markedPackingSpokes_union
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (v:V) (u:U):
    markedPackingSpokes (M∪N) v u↔markedPackingSpokes M v u∨markedPackingSpokes N v u:=by
  constructor
  · rintro ⟨W,hW,hw⟩
    rcases Finset.mem_union.mp hW with hm|hn
    · exact Or.inl ⟨W,hm,hw⟩
    · exact Or.inr ⟨W,hn,hw⟩
  · rintro (⟨W,hW,hw⟩|⟨W,hW,hw⟩)
    · exact ⟨W,Finset.mem_union_left _ hW,hw⟩
    · exact ⟨W,Finset.mem_union_right _ hW,hw⟩

end Oberwolfach
