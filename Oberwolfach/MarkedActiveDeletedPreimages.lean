module

public import Oberwolfach.MarkedActiveSamplePackingLift

@[expose] public section

/-! A surviving ambient arc or spoke outside the removed rows and hubs
has an actual preimage in the restricted deleted sample. In particular,
the marked arc uses the same successor and the same physical state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Γ Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_active_deleted_rim_preimage
    (f:A↪oV) (g:B↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (T:Finset V) (hfX:Finset.univ.image f=Finset.univ\T)
    (j:Bool) (x y:V) (hx:x∉T) (hy:y∉T)
    (hxy:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1)
    (hD:¬DR.Adj x (if j then π y else y)):
    ∃ a:MarkedSampleArc (P.comap f) ρ (3*d)
      (fun e=>rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inl e)) j,
      f a.val.1=x∧f a.val.2=y:=by
  have hxmem:x∈Finset.univ.image f:=by rw [hfX];simp [hx]
  have hymem:y∈Finset.univ.image f:=by rw [hfX];simp [hy]
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hxmem
  obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hymem
  have hdeleted:markedPhysicalRim P π (3*d)
      (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) j x y=1:=by
    apply (markedPhysicalRim_delete_iff P π d σ DR.edgeFinset j x y).mpr
    exact ⟨hxy,by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hD⟩
  have hpre:markedPhysicalRim (P.comap f) ρ (3*d)
      (fun e=>rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inl e)) j a b=1:=by
    apply (markedPhysicalRim_orderEmbedding f π ρ hf P (3*d)
      (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) j a b).mpr
    simpa only [ha,hb] using hdeleted
  exact ⟨⟨(a,b),hpre⟩,ha,hb⟩

theorem marked_active_deleted_spoke_preimage
    (f:A↪oV) (g:B↪U) (H:Bool→V→U→Prop) (DS:SimpleGraph (V⊕U))
    (T:Finset V) (W:Finset U)
    (hfX:Finset.univ.image f=Finset.univ\T) (hgX:Finset.univ.image g=Finset.univ\W)
    (j:Bool) (x:V) (u:U) (hx:x∉T) (hu:u∉W)
    (hH:H j x u) (hD:¬DS.Adj (Sum.inl x) (Sum.inr u)):
    ∃ a:A,∃ b:B,f a=x∧g b=u∧markedDeletePhysicalSpokes H DS j (f a) (g b):=by
  have hxmem:x∈Finset.univ.image f:=by rw [hfX];simp [hx]
  have humem:u∈Finset.univ.image g:=by rw [hgX];simp [hu]
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hxmem
  obtain ⟨b,_,hb⟩:=Finset.mem_image.mp humem
  exact ⟨a,b,ha,hb,by simpa only [ha,hb,markedDeletePhysicalSpokes] using And.intro hH hD⟩

end Oberwolfach
