module

public import Oberwolfach.OrdinaryPackingPhysicalRemainder
public import Oberwolfach.OrdinaryWheelRemainders
public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.OrdinaryPhysicalGraphDeletion
public import Oberwolfach.RowCoverUnion

@[expose] public section
/-! An actual packing in the unreserved host avoids the inner pair and
reserve, and its uncovered incidence is the actual physical remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryUnreservedRim (Q:SimpleGraph V) (X:Finset V) (R:SimpleGraph (V⊕U)):SimpleGraph V:=
  (Q\spanningRestriction Q X)\R.comap Sum.inl

def ordinaryUnreservedSpokes (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)):V→U→Prop:=
  fun v u=>H v u∧¬(v∈X∧u∈Z)∧¬R.Adj (Sum.inl v) (Sum.inr u)

theorem ordinary_unreserved_physical_graph (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)):
    ordinaryPhysicalGraph (ordinaryUnreservedRim Q X R) (ordinaryUnreservedSpokes H X Z R)=
      (ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))\R:=by
  ext a b
  cases a with
  | inl v=>
    cases b with
    | inl w=>simp [ordinaryPhysicalGraph,ordinaryUnreservedRim,spanningRestriction_adj,ordinaryInnerVertices_left]
    | inr u=>simp [ordinaryPhysicalGraph,ordinaryUnreservedSpokes,spanningRestriction_adj,
        ordinaryInnerVertices_left,ordinaryInnerVertices_right] <;> tauto
  | inr u=>
    cases b with
    | inl v=>
      simp only [ordinaryPhysicalGraph,ordinaryUnreservedSpokes,SimpleGraph.sdiff_adj,spanningRestriction_adj,
        ordinaryInnerVertices_left,ordinaryInnerVertices_right]
      have he:R.Adj (Sum.inr u) (Sum.inl v)↔R.Adj (Sum.inl v) (Sum.inr u):=R.adj_comm _ _
      rw [he]
      tauto
    | inr u'=>simp [ordinaryPhysicalGraph]

theorem ordinary_unreserved_packing_certificate
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ)
    (M:Finset (OrdinaryWheel (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R) r))
    (hM:∀A∈M,∀B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (τ:ℝ) (hleft:∀w:V⊕U,((ordinaryIncidentEdges (ordinaryUnreservedRim Q X R)
      (ordinaryUnreservedSpokes H X Z R) w\M.biUnion ordinaryActiveResources).card:ℝ)≤τ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let C:=ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M);
    let Q':=Q\ordinaryWheelRimGraph M;
    let H':=fun v u=>H v u∧¬ordinaryPackingSpokes M v u;
    Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)) ∧
    Disjoint C R ∧
    (∀w,((((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H)
      (ordinaryInnerVertices X Z))\R)\C).degree w:ℝ)≤τ) ∧
    ordinaryPhysicalGraph Q' H'=ordinaryPhysicalGraph Q H\C ∧
    (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card):=by
  intro C Q' H'
  have hrim:ordinaryWheelRimGraph M≤ordinaryUnreservedRim Q X R:=ordinaryWheelRimGraph_subhost M
  have hsp:∀v u,ordinaryPackingSpokes M v u → ordinaryUnreservedSpokes H X Z R v u:=by
    intro v u hvu
    obtain ⟨W,hW,hu,hv⟩:=hvu
    rw [←hu]
    exact W.property.1 v hv
  have hCQ:C≤ordinaryPhysicalGraph (ordinaryUnreservedRim Q X R) (ordinaryUnreservedSpokes H X Z R):=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact hrim hab
      | inr u=>exact hsp v u hab
    | inr u=>cases b with
      | inl v=>exact hsp v u hab
      | inr u'=>exact hab.elim
  rw [ordinary_unreserved_physical_graph] at hCQ
  have hi:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (hCQ hab.1).1.2 hab.2
  have hR:Disjoint C R:=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (hCQ hab.1).2 hab.2
  have hrem:∀w,((((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H)
      (ordinaryInnerVertices X Z))\R)\C).degree w:ℝ)≤τ:=by
    intro w
    have hh:=ordinary_packing_leftover_physical_degree M w
    have he:=ordinary_physical_graph_after_deletion (ordinaryUnreservedRim Q X R)
      (ordinaryUnreservedSpokes H X Z R) C
    change ordinaryPhysicalGraph (ordinaryUnreservedRim Q X R\ordinaryWheelRimGraph M)
      (fun v u=>ordinaryUnreservedSpokes H X Z R v u∧¬ordinaryPackingSpokes M v u)=_ at he
    rw [ordinary_unreserved_physical_graph] at he
    rw [he] at hh
    have hh':= (Nat.cast_le (α:=ℝ)).mpr (le_of_eq hh)
    have hb:=hh'.trans (hleft w)
    convert hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hpost:ordinaryPhysicalGraph Q' H'=ordinaryPhysicalGraph Q H\C:=by
    ext a b
    cases a with
    | inl v=>cases b with
      | inl w=>rfl
      | inr u=>rfl
    | inr u=>cases b with
      | inl v=>
        change (H v u∧¬ordinaryPackingSpokes M v u)↔(H v u∧¬ordinaryPackingSpokes M v u)
        rfl
      | inr u'=>simp [ordinaryPhysicalGraph]
  have hrimQ:ordinaryWheelRimGraph M≤Q:=hrim.trans (sdiff_le.trans sdiff_le)
  have hspH:∀v u,ordinaryPackingSpokes M v u→H v u:=fun v u h=>(hsp v u h).1
  have hd:=ordinary_decomposition_remainder_balance Q (ordinaryWheelRimGraph M) H (ordinaryPackingSpokes M) r
    hrimQ hspH hbal hdiv (ordinaryPacking_decomposition M hM)
  exact ⟨hi,hR,hrem,hpost,hd.1,hd.2⟩
end Oberwolfach
