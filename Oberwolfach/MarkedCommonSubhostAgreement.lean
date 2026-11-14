module

public import Oberwolfach.MarkedCommonSubhost

@[expose] public section
/-! The deleted common host retains the whole protected typed inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_subhost_agrees_on_inner
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (hπ:∀ v,π v∈I↔v∈I)
    (hrim:∀ x y,x∈I→y∈I→σ (Sum.inl s(x,y))=τ (Sum.inl s(x,y)))
    (hsp:∀ b v u,v∈I→u∈J→(H b v u↔H' b v u))
    (htypes:∀ v u,¬(H false v u∧H true v u)):
    ∃ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      DR≤P ∧
      (∀ x,DR.degree x=(Finset.univ.filter (fun y=>P.Adj x y∧
        σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y)))).card) ∧
      (∀ v,DS.degree (Sum.inl v)=(Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ u,DS.degree (Sum.inr u)=(Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1 →
        markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
        markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1) ∧
      (∀ b v u,markedDeletePhysicalSpokes H DS b v u↔H b v u∧H' b v u) ∧
      (∀ mark x y,x∈I→y∈I→
        markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=
        markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y) ∧
      (∀ b v u,v∈I→u∈J→(markedDeletePhysicalSpokes H DS b v u↔H b v u)) :=by
  obtain ⟨DR,DS,hP,hinnerR,hinnerS,hdegR,hdegS,hdegU,hsubR,hsubS⟩:=
    marked_common_subhost_physical_deletions P π d σ τ H H' I J hrim hsp htypes
  refine ⟨DR,DS,hP,hdegR,hdegS,hdegU,hsubR,hsubS,?_,?_⟩
  · intro mark x y hx hy
    have hy':(if mark then π y else y)∈I:=by cases mark <;> simp [hπ,hy]
    have hn: s(x,if mark then π y else y)∉DR.edgeFinset:=by
      intro he
      exact hinnerR x hx (if mark then π y else y) hy' (SimpleGraph.mem_edgeFinset.mp he)
    simp only [markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation,rawMarkedDeleteRims,hn,ite_false]
  · intro b v u hv hu
    rw [hsubS b v u,hsp b v u hv hu]
    simp
end Oberwolfach
