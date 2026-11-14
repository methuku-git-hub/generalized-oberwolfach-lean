module

public import Oberwolfach.OrdinaryTrianglePrescribedAssemblyWithUnion
public import Oberwolfach.OrdinaryInnerUnionDegree
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Keep the free-vertex physical degree bounds when the prescribed-edge
    and deep-root wheel packings are recombined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z:Type} [Fintype V] [Fintype U] [Fintype Z] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop}

theorem ordinary_triangle_prescribed_union_outer_bounds
    (C:Z→OrdinaryWheel Q F H 3)
    (M:Finset (OrdinaryWheel (Q\wheelFamilyRim C) F (fun v u=>H v u∧¬wheelFamilySpokes C v u) 3))
    (R:Finset (OrdinaryWheel Q F H 3)) (I:Finset V) (J:Finset U) (a:ℝ) (nh nr:ℕ)
    (hR:ordinaryWheelRimGraph R=wheelFamilyRim C⊔ordinaryWheelRimGraph M)
    (hS:∀v u,ordinaryPackingSpokes R v u↔wheelFamilySpokes C v u∨ordinaryPackingSpokes M v u)
    (hCr:∀v,((wheelFamilyRim C).degree v:ℝ)≤12*a*Fintype.card V)
    (hCs:∀v,((Finset.univ.filter (wheelFamilySpokes C v)).card:ℝ)≤6*a*Fintype.card V)
    (hCc:∀u,((Finset.univ.filter (fun v=>wheelFamilySpokes C v u)).card:ℝ)≤9*a*Fintype.card V)
    (hMr:∀v∉I,(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr)
    (hMs:∀v∉I,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr)
    (hMc:∀u∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v u)).card≤3*nr):
    (∀v∉I,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
      18*a*Fintype.card V+3*((nh:ℝ)+nr)) ∧
    (∀u∉J,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
      9*a*Fintype.card V+3*(nr:ℝ)):=by
  have hphys:ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)=
      ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)⊔
      ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M):=by
    ext x y
    cases x with
    | inl v=>cases y with
      | inl w=>simpa only [ordinaryPhysicalGraph,SimpleGraph.sup_adj] using iff_of_eq (congrArg (fun G:SimpleGraph V=>G.Adj v w) hR)
      | inr u=>simpa only [ordinaryPhysicalGraph,SimpleGraph.sup_adj] using hS v u
    | inr u=>cases y with
      | inl v=>simpa only [ordinaryPhysicalGraph,SimpleGraph.sup_adj] using hS v u
      | inr u'=>simp [ordinaryPhysicalGraph]
  have hsum (x:V⊕U):((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree x:ℝ)≤
      ((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)).degree x:ℝ)+
      ((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x:ℝ):=by
    have hh:=graph_degree_sup_le (ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C))
      (ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)) x
    have hn:(((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)⊔
        ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x):ℝ)≤
        ((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)).degree x:ℝ)+
        ((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x:ℝ):=by exact_mod_cast hh
    convert hn using 1 <;> congr! 8 <;> first | exact hphys | exact Subsingleton.elim _ _
  constructor
  · intro v hv
    have hc:((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)).degree (Sum.inl v):ℝ)≤18*a*Fintype.card V:=by
      rw [ordinary_physical_degree_row,Nat.cast_add]
      linarith [hCr v,hCs v]
    have hm:((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        3*((nh:ℝ)+nr):=by
      rw [ordinary_physical_degree_row,Nat.cast_add]
      have hr:(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr:=hMr v hv
      have hs:(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr:=hMs v hv
      have hr':((ordinaryWheelRimGraph M).degree v:ℝ)≤2*nh+2*nr:=by exact_mod_cast hr
      have hs':((Finset.univ.filter (ordinaryPackingSpokes M v)).card:ℝ)≤(nh:ℝ)+nr:=by exact_mod_cast hs
      linarith
    exact (hsum (Sum.inl v)).trans (add_le_add hc hm)
  · intro u hu
    have hc:((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)).degree (Sum.inr u):ℝ)≤9*a*Fintype.card V:=by
      rw [ordinary_physical_degree_column]
      exact hCc u
    have hm:((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤3*(nr:ℝ):=by
      rw [ordinary_physical_degree_column]
      exact_mod_cast hMc u hu
    exact (hsum (Sum.inr u)).trans (add_le_add hc hm)
end Oberwolfach
