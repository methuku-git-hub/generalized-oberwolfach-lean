module

public import Oberwolfach.EndpointCompletedWheels
public import Oberwolfach.RowCoverPackings

@[expose] public section

/-! Convert the exact endpoint factor to a row cover. Both root stars,
all non-root degree bounds and the physical resource partition are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_row_cover (Q H F : SimpleGraph V) (A B X S T : Finset V)
    (hAB : Disjoint A B) (hXA : X⊆A) (x : V)
    (hA : S⊆X) (hB : T⊆B)
    (hS : ∀ a,Q.Adj x a ↔ a∈S) (hT : ∀ u,H.Adj x u ↔ u∈T)
    (hF : ∀ a,Q.Adj x a → ¬F.Adj x a)
    (hfactor : HasResourceDecomposition
      (endpointTriangleVertices (Q:=endpointHostGraph Q H A B) (F:=F)
        (S:=S) (T:=T)) (S∪T)) :
    ∃ M : Finset (OrdinaryWheel Q F H.Adj 3), OrdinaryRowCover M x X 0 := by
  obtain ⟨M,W,hW,hdis,hrim,hspoke,hdeg,hrow,hcol⟩ :=
    endpoint_factor_completed_wheels Q H F A B S T
      hAB (hA.trans hXA) hB x
      (fun a ha=>⟨(hS a).mpr ha,hF a ((hS a).mpr ha)⟩)
      (fun u hu=>(hT u).mpr hu) hfactor
  refine ⟨Finset.univ.image W,ordinaryRowCover_of_family W x X 0 ?_ hdis ?_ ?_ ?_ ?_ hcol⟩
  · intro C a ha
    rw [←Set.mem_toFinset,(hW C).2,Finset.mem_insert] at ha
    exact ha.elim Or.inl (fun h=>Or.inr (hA (Finset.mem_inter.mp h).2))
  · intro a
    constructor
    · intro ha
      obtain ⟨C,hC⟩ := SimpleGraph.iSup_adj.mp ha
      exact (W C).val.1.property hC
    · intro ha
      obtain ⟨C,hC,_⟩ := hrim a ((hS a).mp ha)
      apply SimpleGraph.iSup_adj.mpr
      exact ⟨C,(ordinaryWheelResources_rim (W C) s(x,a)).mp hC⟩
  · intro u
    constructor
    · rintro ⟨C,hu,hx⟩
      exact hu ▸ (W C).property.1 x hx
    · intro hu
      obtain ⟨C,hC,_⟩ := hspoke u ((hT u).mp hu)
      exact ⟨C,(ordinaryWheelResources_spoke (W C) x u).mp hC⟩
  · simpa using hdeg
  · simpa using hrow

end Oberwolfach
