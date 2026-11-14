module

public import Oberwolfach.BoundarySupportEvent
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Boundary sets after the approximate packing and the subsequent covering.
The error is bounded by the actual leftover and covering degrees, without
multiplication by the probability used to reserve boundary edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem boundary_after_packing_changed (G R C D:SimpleGraph V)
    (hR:R≤G) (hCR:Disjoint C R) (v:V):
    changed (R.neighborFinset v) (((G\C)\D).neighborFinset v) ⊆
      (((G\R)\C).neighborFinset v) ∪ D.neighborFinset v:=by
  intro w hw
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
    SimpleGraph.sdiff_adj] at hw ⊢
  have hdis:¬(C.Adj v w ∧ R.Adj v w):=by
    rintro ⟨hc,hr⟩
    exact disjoint_graphs_no_common_edge C R hCR v w hc hr
  rcases hw with hw|hw
  · right
    by_contra hd
    exact hw.2 ⟨⟨hR hw.1,fun hc=>hdis ⟨hc,hw.1⟩⟩,hd⟩
  · left
    exact ⟨⟨hw.1.1.1,hw.2⟩,hw.1.1.2⟩

theorem boundary_after_packing_change_degree (G R C D:SimpleGraph V)
    (hR:R≤G) (hCR:Disjoint C R) (v:V):
    (changed (R.neighborFinset v) (((G\C)\D).neighborFinset v)).card ≤
      ((G\R)\C).degree v+D.degree v:=by
  exact (Finset.card_le_card (boundary_after_packing_changed G R C D hR hCR v)).trans
    (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      Finset.card_union_le (((G\R)\C).neighborFinset v) (D.neighborFinset v))

theorem boundary_after_packing_support_change (G R C D:SimpleGraph V)
    (hR:R≤G) (hCR:Disjoint C R) (A:Finset V) (v:V):
    (changed (A∩R.neighborFinset v) (A∩((G\C)\D).neighborFinset v)).card ≤
      ((G\R)\C).degree v+D.degree v:=by
  have hs:changed (A∩R.neighborFinset v) (A∩((G\C)\D).neighborFinset v) ⊆
      changed (R.neighborFinset v) (((G\C)\D).neighborFinset v):=by
    intro w hw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at hw ⊢
    tauto
  exact (Finset.card_le_card hs).trans (boundary_after_packing_change_degree G R C D hR hCR v)

theorem boundary_after_packing_estimates (P G R C D G':SimpleGraph V) (hrem:G'=(G\C)\D) (A Z:Finset V)
    (τ ε ℓ d:ℝ) (hR:R≤G) (hCR:Disjoint C R)
    (hleft:∀ v,(((G\R)\C).degree v:ℝ)≤ℓ) (hcover:∀ v,(D.degree v:ℝ)≤d)
    (hrow:∀ x,|((A∩R.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε)
    (hpair:∀ x y,x≠y→
      |(((A∩R.neighborFinset x)∩(A∩R.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε)
    (hcol:∀ v∈A,|((Z.filter (fun x=>v∈A∩R.neighborFinset x)).card:ℝ)-
      τ*(Z∩P.neighborFinset v).card|≤ε):
    (∀ x,|((A∩G'.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε+ℓ+d) ∧
    (∀ x y,x≠y→
      |(((A∩G'.neighborFinset x)∩(A∩G'.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε+2*(ℓ+d)) ∧
    (∀ v∈A,|((Z.filter (fun x=>v∈A∩G'.neighborFinset x)).card:ℝ)-
      τ*(Z∩P.neighborFinset v).card|≤ε+ℓ+d):=by
  have hc (v:V):((changed (R.neighborFinset v) (G'.neighborFinset v)).card:ℝ)≤ℓ+d:=by
    have hh:((changed (R.neighborFinset v) (G'.neighborFinset v)).card:ℝ)≤
      ((G\R)\C).degree v+D.degree v:=by
      have he:changed (R.neighborFinset v) (G'.neighborFinset v)=
          changed (R.neighborFinset v) (((G\C)\D).neighborFinset v):=by
        ext w;simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,hrem]
      rw [he]
      exact_mod_cast boundary_after_packing_change_degree G R C D hR hCR v
    linarith [hleft v,hcover v]
  simpa only [add_assoc] using boundary_support_estimates_after_changes P R G' A Z
    τ ε (ℓ+d) hc hrow hpair hcol

end Oberwolfach
