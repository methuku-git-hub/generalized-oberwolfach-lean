module

public import Oberwolfach.OrdinaryRestrictedChanges
public import Oberwolfach.OrdinaryEmbeddedGraphChanges

@[expose] public section
/-! The original symmetric rim, spoke-row and spoke-column bounds supply
all seven edit hypotheses of the robust triangle event on the sum domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_two_domain_big_edit_bounds (R Q:SimpleGraph V) (H J:V→U→Prop)
    (A:Finset V) (B:Finset U) (L:ℝ) (hL:0≤L)
    (hR:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=B.image (Sum.inr:U→V⊕U)
    let H₀:=fun v u=>u∈B∧H v u
    let J₀:=fun v u=>u∈B∧J v u
    let R':=R.map e
    let Q':=Q.map e
    let H':=ordinaryPhysicalSpokeGraph H₀
    let J':=ordinaryPhysicalSpokeGraph J₀;
    (∀z,((changed (A'∩R'.neighborFinset z) (A'∩Q'.neighborFinset z)).card:ℝ)≤L) ∧
    (∀z,((changed (B'∩H'.neighborFinset z) (B'∩J'.neighborFinset z)).card:ℝ)≤L) ∧
    (∀z∈B',((changed (A'∩H'.neighborFinset z) (A'∩J'.neighborFinset z)).card:ℝ)≤L) ∧
    (∀z,((R'\Q').degree z:ℝ)≤L) ∧ (∀z,((Q'\R').degree z:ℝ)≤L) ∧
    (∀z,((H'\J').degree z:ℝ)≤L) ∧ (∀z,((J'\H').degree z:ℝ)≤L):=by
  intro e A' B' H₀ J₀ R' Q' H' J'
  have hRA:∀v,((changed (A∩R.neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L:=by
    intro v
    have hh:=changed_inter_card_le A (R.neighborFinset v) (Q.neighborFinset v)
    exact (Nat.cast_le.mpr hh).trans (hR v)
  have hrest:=ordinary_restricted_row_column_changes H J A B L hrow hcol
  have hr:∀v,((changed (B.filter (H₀ v)) (B.filter (J₀ v))).card:ℝ)≤L:=by
    intro v
    have he:B.filter (H₀ v)=B.filter (H v):=by ext u;simp [H₀]
    have hf:B.filter (J₀ v)=B.filter (J v):=by ext u;simp [J₀]
    rw [he,hf];exact hrest.1 v
  have hc:∀u∈B,((changed (A.filter (fun v=>H₀ v u)) (A.filter (fun v=>J₀ v u))).card:ℝ)≤L:=by
    intro u hu
    have he:A.filter (fun v=>H₀ v u)=A.filter (fun v=>H v u):=by ext v;simp [H₀,hu]
    have hf:A.filter (fun v=>J₀ v u)=A.filter (fun v=>J v u):=by ext v;simp [J₀,hu]
    rw [he,hf];exact hrest.2 u
  have hres:=ordinary_two_domain_restricted_change_bounds R Q H₀ J₀ A B L hL hRA
    (by intro v;convert hr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u hu;convert hc u hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hrim:=ordinary_embedded_graph_difference_bounds e R Q L hL hR
  have hspoke:=ordinary_restricted_spoke_edit_degree_bounds H J B L hL hrest.1 (fun u _=>hcol u)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro z;convert hres.1 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert hres.2.1 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z hz;convert hres.2.2 z hz using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert hrim.1 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert hrim.2 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert hspoke.1 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert hspoke.2 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
