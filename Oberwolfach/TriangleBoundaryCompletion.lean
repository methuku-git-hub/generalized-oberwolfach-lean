module

public import Oberwolfach.PhysicalTriangleWheels
public import Oberwolfach.RootCompletedCliques
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Convert the selected inner triangles into actual ordinary three-wheels.
The exact internal edge identity and all outside-root incidences are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_boundary_completion
    {V U I:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype I]
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset (V⊕U))
    (x:I→V⊕U) (T:I→Finset (V⊕U)) (rim:I→Finset V) (hub:I→U)
    (hx:∀ i,x i∉A) (hT:∀ i,T i⊆A) (hrim:∀ i,(rim i).card=3)
    (hvertices:∀ i,insert (x i) (T i)=(rim i).image Sum.inl∪{Sum.inr (hub i)})
    (hclique:∀ i,∀ v∈insert (x i) (T i),∀ w∈insert (x i) (T i),v≠w→
      (ordinaryPhysicalGraph Q H).Adj v w)
    (hF:∀ i,∀ v∈rim i,∀ w∈rim i,¬F.Adj v w)
    (hinner:∀ i j,i≠j→Disjoint (spanningRestriction (⊤:SimpleGraph (V⊕U)) (T i))
      (spanningRestriction ⊤ (T j)))
    (hsame:∀ i j,i≠j→x i=x j→Disjoint (T i) (T j)):
    ∃ W:I→OrdinaryWheel Q F H 3,
      (∀ i,(ordinaryWheelRim (W i)).support.toFinset=rim i ∧ ordinaryWheelHub (W i)=hub i) ∧
      (∀ i,ordinaryWheelPhysicalGraph (W i)=spanningRestriction ⊤ (insert (x i) (T i))) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) 3 ∧
      spanningRestriction (⨆ i,ordinaryWheelPhysicalGraph (W i)) A=
        (⨆ i,spanningRestriction (⊤:SimpleGraph (V⊕U)) (T i)) ∧
      (∀ z∉A,∀ v,(⨆ i,ordinaryWheelPhysicalGraph (W i)).Adj z v↔∃ i,x i=z ∧ v∈T i):=by
  have hex (i:I):∃ W:OrdinaryWheel Q F H 3,
      (ordinaryWheelRim W).support.toFinset=rim i ∧ ordinaryWheelHub W=hub i ∧
      ordinaryWheelPhysicalGraph W=spanningRestriction ⊤ (insert (x i) (T i)):=by
    have hh:=physical_triangle_wheel Q F H (rim i) (hub i) (hrim i)
      (by simpa only [←hvertices i] using hclique i) (hF i)
    simpa only [←hvertices i] using hh
  choose W hW using hex
  have hdis (i j:I) (hij:i≠j):Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j)):=by
    have hg:Disjoint (ordinaryWheelPhysicalGraph (W i)) (ordinaryWheelPhysicalGraph (W j)):=by
      rw [(hW i).2.2,(hW j).2.2]
      exact root_completed_cliques_disjoint A (T i) (T j) (x i) (x j)
        (hT i) (hT j) (hx i) (hx j) (hinner i j hij) (hsame i j hij)
    have he:=SimpleGraph.disjoint_edgeFinset.mpr hg
    rw [ordinaryWheelPhysicalGraph_edges,ordinaryWheelPhysicalGraph_edges] at he
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Finset.disjoint_left.mp he (Finset.mem_image.mpr ⟨e,hei,rfl⟩) (Finset.mem_image.mpr ⟨e,hej,rfl⟩)
  have heq:(⨆ i,ordinaryWheelPhysicalGraph (W i))=
      (⨆ i,spanningRestriction (⊤:SimpleGraph (V⊕U)) (insert (x i) (T i))):=
    iSup_congr (fun i=>(hW i).2.2)
  refine ⟨W,fun i=>⟨(hW i).1,(hW i).2.1⟩,fun i=>(hW i).2.2,hdis,
    wheelFamily_decomposition W hdis,?_,?_⟩
  · rw [heq];exact root_completed_cliques_inner A x T hx hT
  · intro z hz v;rw [heq];exact root_completed_cliques_at_root A x T hx hT z v hz

end Oberwolfach
