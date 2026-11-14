module

public import Oberwolfach.MarkedBoundaryPhysicalCoordinates
public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedEndpointArcEmbeddings
public import Oberwolfach.MarkedBoundaryEndpointSampling

@[expose] public section

/-! The boundary graph consists of the actual physical rim edges and
spokes crossing the fixed inner pair. Permutation invariance of the row
set equates physical crossing with crossing of auxiliary endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

theorem marked_boundary_physical_coin_mem (tail head:E→V) (ktail khead:K→V)
    (π:Equiv.Perm V) (H₀ HK:V→U→Prop) (Q:SimpleGraph V)
    (hE:∀ e,Q.Adj (tail e) (head e)) (hK:∀ e,Q.Adj (ktail e) (π (khead e)))
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)):
    markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val∈
      (ordinaryBoundaryGraph Q (fun v u=>H₀ v u∨HK v u) X Z).edgeSet:=by
  rcases a with ⟨(e|e)|e,ha⟩
  · change (ordinaryBoundaryGraph Q _ X Z).Adj (Sum.inl (tail e)) (Sum.inl (head e))
    rw [ordinaryBoundaryGraph_adj]
    refine ⟨hE e,?_⟩
    simpa only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,and_comm] using ha
  · change (ordinaryBoundaryGraph Q _ X Z).Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))
    rw [ordinaryBoundaryGraph_adj]
    refine ⟨hK e,?_⟩
    simpa only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.elim_inr,
      ordinaryInnerVertices_left,hX,and_comm] using ha
  · change (ordinaryBoundaryGraph Q _ X Z).Adj (Sum.inl e.val.1) (Sum.inr e.val.2)
    rw [ordinaryBoundaryGraph_adj]
    refine ⟨e.property,?_⟩
    simpa only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inr,and_comm] using ha

variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color] [LinearOrder V]

theorem marked_sample_boundary_physical_coin_mem (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop)
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail (H false) (H true))
      (markedActiveAuxHead head khead (H false) (H true)) (ordinaryInnerVertices X Z),
    markedActivePhysicalCoin tail head ktail khead π (H false) (H true) a.val∈
      (ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ Finset.univ)
        (fun v u=>H false v u∨H true v u) X Z).edgeSet:=by
  intro E K tail head ktail khead a
  apply marked_boundary_physical_coin_mem tail head ktail khead π (H false) (H true)
    (markedSampleArcSetGraph P π d σ Finset.univ) _ _ X Z hX a
  · intro e
    exact SimpleGraph.mem_edgeFinset.mp
      ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _))
  · intro e
    exact SimpleGraph.mem_edgeFinset.mp
      ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _))

theorem marked_sample_endpoint_coin_mem_boundary (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop)
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (mark incoming:Bool) (x:V) (hx:x∉X) (v:V)
    (hv:v∈markedEndpointLabels P π d X (mark,incoming,x) σ):
    markedBoundaryEndpointCoin (U:=U) π mark incoming x (Sum.inl v)∈
      (ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ Finset.univ)
        (fun v u=>H false v u∨H true v u) X Z).edgeSet:=by
  have hvX:v∈X:=by
    rw [marked_endpoint_labels_actual] at hv
    exact (Finset.mem_filter.mp hv).1
  let e:=markedEndpointArcEmbedding P π d X mark incoming x σ ⟨v,hv⟩
  have he:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark
      (if incoming then v else x) (if incoming then x else v)=1:=e.property
  rw [marked_boundary_endpoint_rim_coin]
  cases mark <;> cases incoming
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at he ⊢
  all_goals rw [SimpleGraph.mem_edgeSet,ordinaryBoundaryGraph_adj]
  all_goals constructor
  · exact SimpleGraph.mem_edgeFinset.mp ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ
      (Sum.inl ⟨(x,v),he⟩)).mpr (Finset.mem_univ _))
  · simp [ordinaryInnerVertices_left,hx,hvX]
  · exact SimpleGraph.mem_edgeFinset.mp ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ
      (Sum.inl ⟨(v,x),he⟩)).mpr (Finset.mem_univ _))
  · simp [ordinaryInnerVertices_left,hx,hvX]
  · exact SimpleGraph.mem_edgeFinset.mp ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ
      (Sum.inr ⟨(x,v),he⟩)).mpr (Finset.mem_univ _))
  · simp [ordinaryInnerVertices_left,hX,hx,hvX]
  · exact SimpleGraph.mem_edgeFinset.mp ((markedSampleArcSetGraph_coordinate P π d σ Finset.univ
      (Sum.inr ⟨(v,x),he⟩)).mpr (Finset.mem_univ _))
  · simp [ordinaryInnerVertices_left,hX,hx,hvX]

end Oberwolfach
