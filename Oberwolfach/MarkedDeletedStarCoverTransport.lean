module

public import Oberwolfach.MarkedSamplePhysicalDeletionLift
public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section

/-! Express the deep-stage star cover in the original physical coordinates.
Both types and directions are inherited from the unchanged original state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_star_cover_transport
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (T:Finset V) (W:Finset U) (F:Finset (Finset V⊕(V×U))):
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (∀ a:E⊕K,markedStarResource T W (Sum.inl (markedPhysicalEdge
      (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π a))→
      Sum.inl (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π a)∈F)→
    (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→Sum.inr (x,u)∈F)→
    (∀ j x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬DR.Adj x (if j then π y else y)→
      markedStarResource T W (Sum.inl ({x,if j then π y else y}:Finset V))→
      Sum.inl ({x,if j then π y else y}:Finset V)∈F)∧
    (∀ j x u,H j x u→¬DS.Adj (Sum.inl x) (Sum.inr u)→
      markedStarResource T W (Sum.inr (x,u))→Sum.inr (x,u)∈F):=by
  intro σ' H' E K hr hs
  constructor
  · intro j x y hxy hD hstar
    have hdel:markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) j x y=1:=by
      apply (markedPhysicalRim_delete_iff P π d σ DR.edgeFinset j x y).mpr
      exact ⟨hxy,by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hD⟩
    cases j
    · exact hr (Sum.inl ⟨(x,y),hdel⟩) hstar
    · exact hr (Sum.inr ⟨(x,y),hdel⟩) hstar
  · intro j x u hH hD hstar
    apply hs x u _ hstar
    cases j
    · exact Or.inl ⟨hH,hD⟩
    · exact Or.inr ⟨hH,hD⟩

end Oberwolfach
