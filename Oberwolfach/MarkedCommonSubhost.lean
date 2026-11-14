module

public import Oberwolfach.MarkedRimCommonSubhost
public import Oberwolfach.MarkedSpokeCommonSubhost

@[expose] public section
/-! A common typed subhost of the original sample and a later modified
host, obtained by physical deletions on the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_subhost_physical_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U)
    (hrim:∀ x y,x∈I→y∈I→σ (Sum.inl s(x,y))=τ (Sum.inl s(x,y)))
    (hsp:∀ b v u,v∈I→u∈J→(H b v u↔H' b v u))
    (htypes:∀ v u,¬(H false v u∧H true v u)):
    ∃ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      DR≤P ∧
      (∀ x∈I,∀ y∈I,¬DR.Adj x y) ∧
      (∀ v∈I,∀ u∈J,¬DS.Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀ x,DR.degree x=(Finset.univ.filter (fun y=>P.Adj x y∧
        σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y)))).card) ∧
      (∀ v,DS.degree (Sum.inl v)=(Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ u,DS.degree (Sum.inr u)=(Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1 →
        markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
        markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1) ∧
      (∀ b v u,markedDeletePhysicalSpokes H DS b v u↔H b v u∧H' b v u) :=by
  obtain ⟨DR,hP,_,hinnerR,hdegR,hsubR⟩:=marked_rim_common_subhost_deletion P π d σ τ I hrim
  obtain ⟨DS,hsubS,hinnerS,hdegS,hdegU⟩:=marked_spoke_common_subhost_deletion H H' I J htypes hsp
  exact ⟨DR,DS,hP,hinnerR,hinnerS,hdegR,hdegS,hdegU,hsubR,hsubS⟩
end Oberwolfach
