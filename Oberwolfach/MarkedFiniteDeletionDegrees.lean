module

public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedPackingResourceDetermination

@[expose] public section

/-! Degree bounds for the actual graphs deleted by the reserved star and
preceding wheel packing, in the physical representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedFiniteSpokeGraph_same_part (S:Finset (V×U)):
    (∀ x y,¬(markedFiniteSpokeGraph S).Adj (Sum.inl x) (Sum.inl y)) ∧
    (∀ u z,¬(markedFiniteSpokeGraph S).Adj (Sum.inr u) (Sum.inr z)):=by
  constructor
  · intro x y h
    obtain ⟨⟨v,u⟩,_,he⟩:=Finset.mem_image.mp h.2
    have hu:Sum.inr u∈({Sum.inl x,Sum.inl y}:Finset (V⊕U)):=he ▸ (by simp)
    simpa using hu
  · intro u z h
    obtain ⟨⟨x,v⟩,_,he⟩:=Finset.mem_image.mp h.2
    have hx:Sum.inl x∈({Sum.inr u,Sum.inr z}:Finset (V⊕U)):=he ▸ (by simp)
    simpa using hx

theorem markedFiniteSpokeGraph_degree_row (S:Finset (V×U)) (x:V):
    (markedFiniteSpokeGraph S).degree (Sum.inl x)=(Finset.univ.filter (fun u=>(x,u)∈S)).card:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  have he:(markedFiniteSpokeGraph S).neighborFinset (Sum.inl x)=
      (Finset.univ.filter (fun u=>(x,u)∈S)).image Sum.inr:=by
    ext z
    cases z with
    | inl y=>simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image,Finset.mem_filter,
        Finset.mem_univ,true_and,Sum.inr_ne_inl,and_false,exists_false,
        (markedFiniteSpokeGraph_same_part S).1 x y]
    | inr u=>simp only [SimpleGraph.mem_neighborFinset,markedFiniteSpokeGraph_adj,
        Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Sum.inr.injEq,exists_eq_right]
  rw [he,Finset.card_image_of_injective _ Sum.inr_injective]

theorem markedFiniteSpokeGraph_degree_col (S:Finset (V×U)) (u:U):
    (markedFiniteSpokeGraph S).degree (Sum.inr u)=(Finset.univ.filter (fun x=>(x,u)∈S)).card:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  have he:(markedFiniteSpokeGraph S).neighborFinset (Sum.inr u)=
      (Finset.univ.filter (fun x=>(x,u)∈S)).image Sum.inl:=by
    ext z
    cases z with
    | inr v=>simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image,Finset.mem_filter,
        Finset.mem_univ,true_and,Sum.inl_ne_inr,and_false,exists_false,
        (markedFiniteSpokeGraph_same_part S).2 u v]
    | inl x=>
      rw [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm,markedFiniteSpokeGraph_adj]
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Sum.inl.injEq,exists_eq_right]
  rw [he,Finset.card_image_of_injective _ Sum.inl_injective]

theorem markedFiniteSpokeGraph_union (A B:Finset (V×U)):
    markedFiniteSpokeGraph (A∪B)=markedFiniteSpokeGraph A⊔markedFiniteSpokeGraph B:=by
  ext x y
  simp only [markedFiniteSpokeGraph,physicalEdgeGraph,Finset.image_union,Finset.mem_union,SimpleGraph.sup_adj]
  tauto

theorem markedSampleArcSetGraph_union
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (A B):
    markedSampleArcSetGraph P π d σ (A∪B)=markedSampleArcSetGraph P π d σ A⊔markedSampleArcSetGraph P π d σ B:=by
  ext x y
  simp only [markedSampleArcSetGraph,physicalEdgeGraph,Finset.image_union,Finset.mem_union,SimpleGraph.sup_adj]
  tauto

theorem markedSampleArcSetGraph_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop)
    (M:Finset (MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true))):
    markedSampleArcSetGraph P π d σ (M.biUnion markedWheelArcs)=markedPackingRimGraph M:=by
  unfold markedSampleArcSetGraph markedPackingRimGraph markedPackingRims
  congr 1
  rw [Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro W _
  unfold markedWheelArcs markedCyclePhysicalEdges
  rw [Finset.image_image]

theorem markedFiniteSpokeGraph_packing_degrees
    {E K:Type} {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    (∀ x,(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).degree (Sum.inl x)=
      (Finset.univ.filter (markedPackingSpokes M x)).card) ∧
    (∀ u,(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).degree (Sum.inr u)=
      (Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card):=by
  have he (x:V) (u:U):(x,u)∈M.biUnion markedWheelSpokePairs↔markedPackingSpokes M x u:=by
    simp only [Finset.mem_biUnion,markedWheelSpokePairs,Finset.mem_image,Finset.mem_univ,true_and,
      Prod.mk.injEq,markedPackingSpokes,markedWheelRows]
    aesop
  constructor
  · intro x;rw [markedFiniteSpokeGraph_degree_row];simp only [he]
  · intro u;rw [markedFiniteSpokeGraph_degree_col];simp only [he]

end Oberwolfach
