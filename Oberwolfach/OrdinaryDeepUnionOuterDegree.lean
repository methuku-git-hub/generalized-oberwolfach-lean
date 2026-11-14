module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.OrdinaryInnerUnionDegree
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Physical outer-degree bounds are preserved when prescribed and deep
    wheel packings of any permitted length are glued. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_deep_union_outer_degree
    (PE:Finset (OrdinaryWheel Q F H r))
    (M:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph PE) F (fun v u=>H v u∧¬ordinaryPackingSpokes PE v u) r))
    (R:Finset (OrdinaryWheel Q F H r)) (I:Finset V) (J:Finset U) (a:ℝ) (nh nr K:ℕ)
    (hR:ordinaryWheelRimGraph R=ordinaryWheelRimGraph PE⊔ordinaryWheelRimGraph M)
    (hS:∀v u,ordinaryPackingSpokes R v u↔ordinaryPackingSpokes PE v u∨ordinaryPackingSpokes M v u)
    (hCr:∀v,((ordinaryWheelRimGraph PE).degree v:ℝ)≤12*a*Fintype.card V)
    (hCs:∀v,((Finset.univ.filter (ordinaryPackingSpokes PE v)).card:ℝ)≤6*a*Fintype.card V)
    (hCc:∀u,((Finset.univ.filter (fun v=>ordinaryPackingSpokes PE v u)).card:ℝ)≤3*a*Fintype.card V*r)
    (hMr:∀v∉I,(ordinaryWheelRimGraph M).degree v≤2*nh+nr*(2*(K+1)))
    (hMs:∀v∉I,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr*(K+1))
    (hMc:∀u∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v u)).card≤nr*r) :
    (∀v∉I,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
      18*a*Fintype.card V+3*((nh:ℝ)+(K+1)*nr)) ∧
    (∀u∉J,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
      3*a*Fintype.card V*r+(nr:ℝ)*r) := by
  have hphys:ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)=
      ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)⊔
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
      ((ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree x:ℝ)+
      ((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x:ℝ):=by
    have hh:=graph_degree_sup_le (ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE))
      (ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)) x
    have hn:(((ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)⊔
        ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x):ℝ)≤
        ((ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree x:ℝ)+
        ((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree x:ℝ):=by exact_mod_cast hh
    convert hn using 1 <;> congr! 8 <;> first | exact hphys | exact Subsingleton.elim _ _
  constructor
  · intro v hv
    have hc:((ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree (Sum.inl v):ℝ)≤18*a*Fintype.card V:=by
      rw [ordinary_physical_degree_row,Nat.cast_add]
      linarith [hCr v,hCs v]
    have hm:((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        3*((nh:ℝ)+(K+1)*nr):=by
      rw [ordinary_physical_degree_row,Nat.cast_add]
      have hr:((ordinaryWheelRimGraph M).degree v:ℝ)≤(2*nh+nr*(2*(K+1)):ℕ):=by exact_mod_cast hMr v hv
      have hs:((Finset.univ.filter (ordinaryPackingSpokes M v)).card:ℝ)≤(nh+nr*(K+1):ℕ):=by exact_mod_cast hMs v hv
      push_cast at hr hs
      nlinarith
    exact (hsum (Sum.inl v)).trans (add_le_add hc hm)
  · intro u hu
    have hc:((ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree (Sum.inr u):ℝ)≤3*a*Fintype.card V*r:=by
      rw [ordinary_physical_degree_column]
      exact hCc u
    have hm:((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤(nr:ℝ)*r:=by
      rw [ordinary_physical_degree_column]
      exact_mod_cast hMc u hu
    exact (hsum (Sum.inr u)).trans (add_le_add hc hm)
end Oberwolfach
