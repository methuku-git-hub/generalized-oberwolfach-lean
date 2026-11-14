module

public import Oberwolfach.MarkedEndpointBoundarySupport
public import Oberwolfach.EmbeddedBoundaryHubClasses
public import Oberwolfach.PermutationInvariantImage
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section

/-! The actual remaining endpoint and hub classes are supported on the
remaining physical boundary graph. No new sample is taken. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_actual_boundary_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (CR DR:SimpleGraph V) (CH DH:V→U→Prop):
    let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ Finset.univ)
      (fun x u=>H false x u∨H true x u) X Z
    let C:=ordinaryPhysicalGraph CR CH
    let D:=ordinaryPhysicalGraph DR DH
    let τ:=fun e:Sym2 (V⊕U)=>decide (e∈((G\C)\D).edgeSet)
    let σ':=rawMarkedDeleteRims σ (CR⊔DR).edgeFinset
    let H':=markedDeletePhysicalSpokes H (C⊔D)
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    (∀ b incoming x,x∉X→markedEndpointLabels P π d X (b,incoming,x) σ'⊆
      markedBoundaryRimNeighbours (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K=>e.val.1) (fun e:K=>e.val.2) π X τ x)∧
    (∀ b x,x∉X→Z.filter (H' b x)⊆markedBoundarySpokeHubs (H false) (H true) Z τ x)∧
    (∀ u,u∉Z→X.filter (fun x=>(H false x u∨H true x u)∧¬(C⊔D).Adj (Sum.inl x) (Sum.inr u))=
      markedBoundarySpokeRows (H false) (H true) X τ u):=by
  intro G C D τ σ' H' E K
  have hrem:G\(C⊔D)=(G\C)\D:=by
    ext x y
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  have hCD:ordinaryPhysicalGraph (CR⊔DR) (fun x u=>CH x u∨DH x u)=C⊔D:=ordinaryPhysicalGraph_sup _ _ _ _
  refine ⟨?_,?_,?_⟩
  · intro b incoming x hx
    have he:=marked_remaining_endpoint_class P π d σ H X Z hX (CR⊔DR)
      (fun x u=>CH x u∨DH x u) b incoming x hx
    dsimp only at he
    rw [hCD] at he
    have he0:markedEndpointLabels P π d X (b,incoming,x) σ'=
        (markedEndpointLabels P π d X (b,incoming,x) σ).filter
          (fun v=>markedBoundaryEndpointCoin π b incoming x (Sum.inl v)∈(G\(C⊔D)).edgeSet):=by
      convert he using 1 <;> congr!
    have he':markedEndpointLabels P π d X (b,incoming,x) σ'=
        (markedEndpointLabels P π d X (b,incoming,x) σ).filter
          (fun v=>τ (markedBoundaryEndpointCoin π b incoming x (Sum.inl v))=true):=by
      simpa only [τ,decide_eq_true_eq,hrem] using he0
    rw [he']
    exact marked_endpoint_class_boundary_support P π d σ X τ b incoming x
  · intro b x hx
    have he:=marked_remaining_spoke_class (markedSampleArcSetGraph P π d σ Finset.univ) H X Z (C⊔D) b x hx
    have he0:Z.filter (H' b x)=(Z.filter (H b x)).filter (fun u=>(G\(C⊔D)).Adj (Sum.inl x) (Sum.inr u)):=by
      convert he using 1 <;> congr!
    have he':Z.filter (H' b x)=(Z.filter (H b x)).filter (fun u=>τ s(Sum.inl x,Sum.inr u)=true):=by
      simpa only [τ,decide_eq_true_eq,hrem,SimpleGraph.mem_edgeSet] using he0
    rw [he']
    exact marked_spoke_class_boundary_support H Z τ b x
  · intro u hu
    have he:=marked_remaining_spoke_column (markedSampleArcSetGraph P π d σ Finset.univ) H X Z (C⊔D) u hu
    have he0:X.filter (fun x=>(H false x u∨H true x u)∧¬(C⊔D).Adj (Sum.inl x) (Sum.inr u))=
        (X.filter (fun x=>H false x u∨H true x u)).filter (fun x=>(G\(C⊔D)).Adj (Sum.inl x) (Sum.inr u)):=by
      convert he using 1 <;> congr!
    rw [he0]
    ext x
    simp only [markedBoundarySpokeRows,Finset.mem_filter,τ,decide_eq_true_eq,hrem,SimpleGraph.mem_edgeSet]
    tauto
end Oberwolfach
