module

public import Oberwolfach.OrdinaryTwoDomainChangeBounds
public import Oberwolfach.OrdinaryRestrictedSpokeEdit

@[expose] public section
/-! Restricting a neighborhood to a fixed domain cannot increase its
symmetric change. This supplies the fixed-domain triangle edit hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem changed_inter_card_le {X:Type} [DecidableEq X] (A S T:Finset X):
    (changed (A∩S) (A∩T)).card≤(changed S T).card:=by
  apply Finset.card_le_card
  intro x hx
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at hx ⊢
  tauto

theorem ordinary_restricted_row_column_changes (H J:V→U→Prop) (A:Finset V) (B:Finset U) (L:ℝ)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    (∀v,((changed (B.filter (H v)) (B.filter (J v))).card:ℝ)≤L) ∧
    (∀u,((changed (A.filter (fun v=>H v u)) (A.filter (fun v=>J v u))).card:ℝ)≤L):=by
  constructor
  · intro v
    have hh:=changed_inter_card_le B (Finset.univ.filter (H v)) (Finset.univ.filter (J v))
    have he:B∩Finset.univ.filter (H v)=B.filter (H v):=by ext u;simp
    have hf:B∩Finset.univ.filter (J v)=B.filter (J v):=by ext u;simp
    rw [he,hf] at hh
    exact (Nat.cast_le.mpr hh).trans (hrow v)
  · intro u
    have hh:=changed_inter_card_le A (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))
    have he:A∩Finset.univ.filter (fun v=>H v u)=A.filter (fun v=>H v u):=by ext v;simp
    have hf:A∩Finset.univ.filter (fun v=>J v u)=A.filter (fun v=>J v u):=by ext v;simp
    rw [he,hf] at hh
    exact (Nat.cast_le.mpr hh).trans (hcol u)
end Oberwolfach
