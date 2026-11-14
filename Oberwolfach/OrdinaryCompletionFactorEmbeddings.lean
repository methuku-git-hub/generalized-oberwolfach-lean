module

public import Oberwolfach.OrdinaryReservedWheelMatching
public import Oberwolfach.OrdinaryReservedComponentsGlue
public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly

@[expose] public section
/-! Reconstruct all prescribed factors from their already embedded
complements and an ordinary completion on the remaining spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completion_factor_embeddings {n r:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop) (hQ:Q≤G) (hr:0<r)
    (hdec:HasOrdinaryWheelDecomposition Q H r)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hspokes:∀u,(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
      G.Adj (fC u x) (fC u y) ∧ ¬Q.Adj (fC u x) (fC u y))
    (havoid:∀u (x:{x:Fin n // (F u).connectedComponentMk x∉C u}),¬H (fC u x) u)
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))):
    ∃f:∀u,Fin n↪Fin n,
      (∀u x (hx:(F u).connectedComponentMk x∉C u),f u x=fC u ⟨x,hx⟩) ∧
      (∀u x y,(F u).Adj x y→G.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (Fin n) (F u) (f u))
        (partialFactorPhysicalEdgesPoly (Fin n) (F v) (f v))) :=by
  obtain ⟨M,W,hWinj,hWmem,hWspoke,hWdis,hWsupport⟩:=ordinary_reserved_wheel_matching Q H hr hdec F C hspokes
  have hEach:∀u,∃f:Fin n↪Fin n,
      (∀x (hx:(F u).connectedComponentMk x∉C u),f x=fC u ⟨x,hx⟩) ∧
      (∀x y,(F u).Adj x y→G.Adj (f x) (f y)) ∧
      (∀c:↥(C u),Set.range (fun x:c.val=>f x.val)=(ordinaryWheelRim (W u c)).support) ∧
      (∀c:↥(C u),∀x y:c.val,(F u).Adj x.val y.val→(ordinaryWheelRim (W u c)).Adj (f x.val) (f y.val)):=by
    intro u
    apply ordinary_reserved_components_glue (F u) G (hF u) (C u) (W u) (hsize u)
    · intro c
      exact ((hWmem u c).2.2).trans hQ
    · exact hWsupport u
    · intro x y hxy
      exact (hC u x y hxy).1
    · intro x c hx
      exact havoid u x (hWspoke u c (fC u x) hx)
  choose f hOff hGraph hRange hSelected using hEach
  have hCase:∀u x y,(F u).Adj x y→
      (∃c:↥(C u),(ordinaryWheelRim (W u c)).Adj (f u x) (f u y)) ∨
      (∃(hx:(F u).connectedComponentMk x∉C u) (hy:(F u).connectedComponentMk y∉C u),
        (f u x=fC u ⟨x,hx⟩) ∧ (f u y=fC u ⟨y,hy⟩)):=by
    intro u x y hxy
    have heq:(F u).connectedComponentMk y=(F u).connectedComponentMk x:=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    by_cases hx:(F u).connectedComponentMk x∈C u
    · left
      let c:↥(C u):=⟨(F u).connectedComponentMk x,hx⟩
      have hxc:x∈c.val.supp:=by simp [c]
      have hyc:y∈c.val.supp:=by change (F u).connectedComponentMk y=(F u).connectedComponentMk x;exact heq
      exact ⟨c,hSelected u c ⟨x,hxc⟩ ⟨y,hyc⟩ hxy⟩
    · right
      have hy:(F u).connectedComponentMk y∉C u:=by simpa only [heq] using hx
      exact ⟨hx,hy,hOff u x hx,hOff u y hy⟩
  refine ⟨f,hOff,hGraph,?_⟩
  intro u v huv
  apply Set.disjoint_left.mpr
  intro e heu hev
  obtain ⟨x,y,hxy,he⟩:=heu
  obtain ⟨z,t,hzt,he'⟩:=hev
  have hsym:s(f u x,f u y)=s(f v z,f v t):=he.symm.trans he'
  rcases hCase u x y hxy with ⟨c,huc⟩ | ⟨hx,hy,hux,huy⟩ <;>
    rcases hCase v z t hzt with ⟨d,hvd⟩ | ⟨hz,ht,hvz,hvt⟩
  · have hu:Sum.inl e∈ordinaryWheelResources (W u c):=by
      rw [he,ordinaryWheelResources_rim]
      exact huc
    have hv:Sum.inl e∈ordinaryWheelResources (W v d):=by
      rw [he',ordinaryWheelResources_rim]
      exact hvd
    exact Finset.disjoint_left.mp (hWdis u v c d huv) hu hv
  · have hQedge:Q.Adj (f u x) (f u y):=(hWmem u c).2.2 huc
    have hNo:¬Q.Adj (f v z) (f v t):=by
      rw [hvz,hvt]
      exact (hC v ⟨z,hz⟩ ⟨t,ht⟩ hzt).2
    have heQ:s(f u x,f u y)∈Q.edgeSet:=hQedge
    rw [hsym] at heQ
    exact hNo heQ
  · have hQedge:Q.Adj (f v z) (f v t):=(hWmem v d).2.2 hvd
    have hNo:¬Q.Adj (f u x) (f u y):=by
      rw [hux,huy]
      exact (hC u ⟨x,hx⟩ ⟨y,hy⟩ hxy).2
    have heQ:s(f v z,f v t)∈Q.edgeSet:=hQedge
    rw [←hsym] at heQ
    exact hNo heQ
  · have hu:e∈partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u):=by
      refine ⟨⟨x,hx⟩,⟨y,hy⟩,hxy,?_⟩
      simpa only [←hux,←huy] using he
    have hv:e∈partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v):=by
      refine ⟨⟨z,hz⟩,⟨t,ht⟩,hzt,?_⟩
      simpa only [←hvz,←hvt] using he'
    exact Set.disjoint_left.mp (hCC u v huv) hu hv
end Oberwolfach
