module

public import Oberwolfach.MarkedPhysicalDeletionComposition
public import Oberwolfach.MarkedDecompositionHostTransfer

@[expose] public section
/-! If a physical deletion avoids the reserved rim pairs and spokes, all
ordinary and marked arc directions and both spoke types used by the
reservoir remain present. No global deletion-degree bound is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_resources_survive_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y)
    (hS:∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u)):
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E',e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K',e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H' b v u) :=by
  intro σ' H' E K E' K'
  refine ⟨?_,?_,?_⟩
  · intro e he
    have hd:s(e.val.1,e.val.2)∉DR.edgeFinset:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR e.val.1 e.val.2 he
    have ho:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) false e.val.1 e.val.2).mp e.property
    have hn:markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) false e.val.1 e.val.2=1:=by
      rw [markedPhysicalRim_eq_one_iff]
      refine ⟨ho.1,ho.2.1,?_⟩
      simpa [σ',rawMarkedDeleteRims,hd] using ho.2.2
    exact ⟨⟨e.val,hn⟩,rfl⟩
  · intro e he
    have hd:s(e.val.1,π e.val.2)∉DR.edgeFinset:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR e.val.1 (π e.val.2) he
    have ho:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) true e.val.1 e.val.2).mp e.property
    have hn:markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) true e.val.1 e.val.2=1:=by
      rw [markedPhysicalRim_eq_one_iff]
      refine ⟨ho.1,ho.2.1,?_⟩
      simpa [σ',rawMarkedDeleteRims,hd] using ho.2.2
    exact ⟨⟨e.val,hn⟩,rfl⟩
  · intro b v u hc hh
    exact ⟨hh,hS v u hc⟩

/-- Preserve the same typed resources through both stages. -/
theorem marked_reserved_resources_survive_two_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (R₁ R₂:SimpleGraph V) (S₁ S₂:SimpleGraph (V⊕U))
    (hR₁:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬R₁.Adj x y)
    (hR₂:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬R₂.Adj x y)
    (hS₁:∀ v u,Sum.inr (v,u)∈C→¬S₁.Adj (Sum.inl v) (Sum.inr u))
    (hS₂:∀ v u,Sum.inr (v,u)∈C→¬S₂.Adj (Sum.inl v) (Sum.inr u)):
    let σ':=rawMarkedDeleteRims (rawMarkedDeleteRims σ R₁.edgeFinset) R₂.edgeFinset
    let H':=markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H S₁) S₂
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E',e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K',e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H' b v u) :=by
  intro σ' H' E K E' K'
  have hr:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬(R₁⊔R₂).Adj x y:=by
    intro x y hc
    simpa only [SimpleGraph.sup_adj,not_or] using And.intro (hR₁ x y hc) (hR₂ x y hc)
  have hs:∀ v u,Sum.inr (v,u)∈C→¬(S₁⊔S₂).Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc
    simpa only [SimpleGraph.sup_adj,not_or] using And.intro (hS₁ v u hc) (hS₂ v u hc)
  have h:=marked_reserved_resources_survive_physical_deletion P π d σ H C (R₁⊔R₂) (S₁⊔S₂) hr hs
  dsimp only [σ',H',E',K'] at h ⊢
  rw [rawMarkedDeleteRims_sup,markedDeletePhysicalSpokes_sup]
  convert h using 1 <;> congr!
end Oberwolfach
