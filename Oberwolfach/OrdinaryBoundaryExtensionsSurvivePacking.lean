module

public import Oberwolfach.OrdinaryBoundaryExtensionRetention
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! A packing that avoids both the fresh boundary reserve and the protected
inner pair leaves every fully sampled extension intact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sampled_inner_incident_edge_survives
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hreserve:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ))
    (a b:V⊕U) (hab:(ordinaryPhysicalGraph Q H).Adj a b)
    (hinside:a∈ordinaryInnerVertices X Z∨b∈ordinaryInnerVertices X Z)
    (hcoin:σ s(a,b)=true):
    (ordinaryPhysicalGraph Q H\C).Adj a b:=by
  refine ⟨hab,?_⟩
  intro hc
  by_cases ha:a∈ordinaryInnerVertices X Z
  · by_cases hb:b∈ordinaryInnerVertices X Z
    · have hi:(spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)).Adj a b:=
        (spanningRestriction_adj _ _ _ _).mpr ⟨hab,ha,hb⟩
      exact (disjoint_iff_inf_le.mp hinner) (v:=a) (w:=b) ⟨hc,hi⟩
    · have hbnd:(ordinaryBoundaryGraph Q H X Z).Adj a b:=
        (ordinaryBoundaryGraph_adj Q H X Z a b).mpr ⟨hab,Or.inr ⟨hb,ha⟩⟩
      have hr:(retainedGraph (ordinaryBoundaryGraph Q H X Z) σ).Adj a b:=⟨hbnd,hcoin⟩
      exact (disjoint_iff_inf_le.mp hreserve) (v:=a) (w:=b) ⟨hc,hr⟩
  · have hb:b∈ordinaryInnerVertices X Z:=hinside.resolve_left ha
    have hbnd:(ordinaryBoundaryGraph Q H X Z).Adj a b:=
      (ordinaryBoundaryGraph_adj Q H X Z a b).mpr ⟨hab,Or.inl ⟨ha,hb⟩⟩
    have hr:(retainedGraph (ordinaryBoundaryGraph Q H X Z) σ).Adj a b:=⟨hbnd,hcoin⟩
    exact (disjoint_iff_inf_le.mp hreserve) (v:=a) (w:=b) ⟨hc,hr⟩

theorem ordinary_retained_extensions_survive_packing
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (b:ℝ)
    (hinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hreserve:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ))
    (hkeep:ordinaryPhysicalGraph Q H\C≤ordinaryPhysicalGraph Q' H')
    (hgood:∀a c u,b≤((retainedPatternSet (X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u))
      (markedBoundaryJoinCoins a c u) σ).card:ℝ)):
    ∀u a c,b≤(((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ):=by
  intro u a c
  let A:=retainedPatternSet (X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u))
    (markedBoundaryJoinCoins a c u) σ
  have hsub:A⊆(X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c:=by
    intro v hv
    have hv':v∈X ∧ (Q.Adj a v∧Q.Adj v c∧H v u) ∧
        ∀e∈markedBoundaryJoinCoins a c u v,σ e=true:=by
      have hh : (v∈X ∧ Q.Adj a v∧Q.Adj v c∧H v u) ∧
          ∀e∈markedBoundaryJoinCoins a c u v,σ e=true:=by
        simpa [A,retainedPatternSet] using hv
      exact ⟨hh.1.1,hh.1.2,hh.2⟩
    have hi:Sum.inl v∈ordinaryInnerVertices X Z:=by simpa [ordinaryInnerVertices_left] using hv'.1
    have h1:σ s(Sum.inl a,Sum.inl v)=true:=hv'.2.2 _ (by simp [markedBoundaryJoinCoins])
    have h2:σ s(Sum.inl v,Sum.inl c)=true:=hv'.2.2 _ (by simp [markedBoundaryJoinCoins])
    have h3:σ s(Sum.inl v,Sum.inr u)=true:=hv'.2.2 _ (by simp [markedBoundaryJoinCoins])
    have he1:=ordinary_sampled_inner_incident_edge_survives Q H X Z C σ hinner hreserve
      (Sum.inl a) (Sum.inl v) hv'.2.1.1 (Or.inr hi) h1
    have he2:=ordinary_sampled_inner_incident_edge_survives Q H X Z C σ hinner hreserve
      (Sum.inl v) (Sum.inl c) hv'.2.1.2.1 (Or.inl hi) h2
    have he3:=ordinary_sampled_inner_incident_edge_survives Q H X Z C σ hinner hreserve
      (Sum.inl v) (Sum.inr u) hv'.2.1.2.2 (Or.inl hi) h3
    have ha:Q'.Adj a v:=hkeep he1
    have hc:Q'.Adj c v:=(show Q'.Adj v c from hkeep he2).symm
    have hu:H' v u:=hkeep he3
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hv'.1,hu⟩,
      (Q'.mem_neighborFinset a v).mpr ha⟩,(Q'.mem_neighborFinset c v).mpr hc⟩
  exact (hgood a c u).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
end Oberwolfach
