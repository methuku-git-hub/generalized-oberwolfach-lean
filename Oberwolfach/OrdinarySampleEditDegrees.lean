module

public import Oberwolfach.GraphDifferenceChangedDegree
public import Oberwolfach.TransferCandidates
public import Oberwolfach.OrdinaryPotentialDegreeStability

@[expose] public section
/-! Symmetric sample edits bound lost rim edges and lost spoke rows and
columns. Completing the transfer root costs at most one extra spoke per column. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_lost_rim_degree_from_sample_edit (Q₀ Q F:SimpleGraph V) (d:ℝ)
    (h:∀v,((changed (Q₀.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d):
    ∀v,(((Q₀\F)\Q).degree v:ℝ)≤d:=by
  intro v
  have hsub:(Q₀\F)\Q≤Q₀\Q:=by intro a b hab;exact ⟨hab.1.1,hab.2⟩
  have hd:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have hc:=graph_difference_degree_le_changed Q₀ Q v
  have he:((changed (Q.neighborFinset v) (Q₀.neighborFinset v)).card:ℝ)≤d:=by
    simpa [changed,Finset.union_comm] using h v
  have hh:(((Q₀\F)\Q).degree v:ℝ)≤((changed (Q.neighborFinset v) (Q₀.neighborFinset v)).card:ℝ):=by
    exact_mod_cast hd.trans hc
  exact hh.trans he

theorem ordinary_lost_spoke_rows_from_sample_edit (H₀ H:V→U→Prop) (d:ℝ)
    (h:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d):
    ∀v,(∑u,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d:=by
  intro v
  have hsub:(Finset.univ.filter (fun u=>H₀ v u∧¬H v u))⊆changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v)):=by
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl ⟨hu.1,hu.2⟩
  have hc:((Finset.univ.filter (fun u=>H₀ v u∧¬H v u)).card:ℝ)≤
      (changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:=by exact_mod_cast Finset.card_le_card hsub
  have hh:=hc.trans (h v)
  have he:((Finset.univ.filter (fun u=>H₀ v u∧¬H v u)).card:ℝ)=
      ∑u,bipAdj (fun v u=>H₀ v u∧¬H v u) v u:=by
    simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    congr! 8 <;> exact Subsingleton.elim _ _
  exact he ▸ hh

theorem ordinary_lost_spoke_columns_from_sample_edit (H₀ H:V→U→Prop) (d:ℝ)
    (h:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d):
    ∀u,(∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d:=by
  intro u
  have hsub:(Finset.univ.filter (fun v=>H₀ v u∧¬H v u))⊆changed
      (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u)):=by
    intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl ⟨hv.1,hv.2⟩
  have hc:((Finset.univ.filter (fun v=>H₀ v u∧¬H v u)).card:ℝ)≤
      (changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:=by exact_mod_cast Finset.card_le_card hsub
  have hh:=hc.trans (h u)
  have he:((Finset.univ.filter (fun v=>H₀ v u∧¬H v u)).card:ℝ)=
      ∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u:=by
    simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    congr! 8 <;> exact Subsingleton.elim _ _
  exact he ▸ hh

theorem ordinary_completed_root_lost_spoke_column (H₀ H:V→U→Prop) (d:ℝ)
    (h:∀u,(∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d):
    ∀x u,(∑v,bipAdj (fun v u=>transferRootCompletedSpokes H₀ x v u∧¬H v u) v u)≤d+1:=by
  intro x u
  let A:=Finset.univ.filter (fun v=>H₀ v u∧¬H v u)
  let B:=Finset.univ.filter (fun v=>transferRootCompletedSpokes H₀ x v u∧¬H v u)
  have hsub:B⊆insert x A:=by
    intro v hv
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and,transferRootCompletedSpokes] at hv
    simp only [Finset.mem_insert,A,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hv.1 with hvx|hv0
    · exact Or.inl hvx
    · exact Or.inr ⟨hv0,hv.2⟩
  have hc:B.card≤A.card+1:=(Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hc':(B.card:ℝ)≤(A.card:ℝ)+1:=by exact_mod_cast hc
  have heA:(A.card:ℝ)=∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u:=by
    dsimp [A]
    simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    congr! 8 <;> exact Subsingleton.elim _ _
  have ha:(A.card:ℝ)≤d:=heA.symm ▸ h u
  have hb:(∑v,bipAdj (fun v u=>transferRootCompletedSpokes H₀ x v u∧¬H v u) v u)=(B.card:ℝ):=by
    dsimp [B]
    simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    congr! 8 <;> exact Subsingleton.elim _ _
  rw [hb]
  linarith
end Oberwolfach
