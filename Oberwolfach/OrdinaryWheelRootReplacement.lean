module

public import Oberwolfach.GraphRootReplacement
public import Oberwolfach.OrdinaryWheelResources

@[expose] public section

/-! Construct the paired wheel by replacing one rim root and optionally
its hub. The signed rim and spoke identities are proved for the exact
selected cycle; no new cycle is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_wheel_root_replacement (W:OrdinaryWheel Q F H r) (x y:V) (u':U)
    (hx:x∈(ordinaryWheelRim W).support) (hy:y∉(ordinaryWheelRim W).support)
    (hQ:∀ v,(ordinaryWheelRim W).Adj x v→Q.Adj y v)
    (hF:∀ v∈(ordinaryWheelRim W).support,v≠x→¬F.Adj y v)
    (hHy:H y u') (hH:∀ v∈(ordinaryWheelRim W).support,v≠x→H v u'):
    ∃ W':OrdinaryWheel Q F H r,
      ordinaryWheelRim W'=(ordinaryWheelRim W).map (Equiv.swap x y).toEmbedding ∧
      ordinaryWheelHub W'=u' ∧
      (∀ v,v∈(ordinaryWheelRim W').support↔v=y∨(v∈(ordinaryWheelRim W).support∧v≠x)) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
        (if e∈graphRootEdges (ordinaryWheelRim W) x x then 1 else 0)-
          (if e∈graphRootEdges (ordinaryWheelRim W) x y then 1 else 0)) ∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources W' then 1 else 0)=
        (if v=x∧z=ordinaryWheelHub W then 1 else 0)-(if v=y∧z=u' then 1 else 0)+
        (if v∈(ordinaryWheelRim W).support∧v≠x∧z=ordinaryWheelHub W then 1 else 0)-
          (if v∈(ordinaryWheelRim W).support∧v≠x∧z=u' then 1 else 0)):=by
  let C:=(ordinaryWheelRim W).map (Equiv.swap x y).toEmbedding
  have hC:IsEmbeddedCycle C r:=(W.val.1.val.property).map (Equiv.swap x y).toEmbedding
  have hCQ:C≤Q:=graph_swap_root_subgraph _ Q x y W.val.1.property hy hQ
  have hs (v:V):v∈C.support↔v=y∨(v∈(ordinaryWheelRim W).support∧v≠x):=
    graph_swap_root_support _ x y hx hy v
  have hCH:∀ v∈C.support,H v u':=by
    intro v hv
    rcases (hs v).mp hv with rfl|⟨hv,hvx⟩
    · exact hHy
    · exact hH v hv hvx
  have hCF:∀ v∈C.support,∀ w∈C.support,¬F.Adj v w:=by
    intro v hv w hw
    rcases (hs v).mp hv with hve|hvrest <;> rcases (hs w).mp hw with hwe|hwrest
    · rw [hve,hwe];exact F.loopless.irrefl _
    · rw [hve];exact hF w hwrest.1 hwrest.2
    · rw [hwe];exact fun h=>hF v hvrest.1 hvrest.2 h.symm
    · exact W.property.2 v hvrest.1 w hwrest.1
  let W':OrdinaryWheel Q F H r:=⟨(⟨⟨C,hC⟩,hCQ⟩,u'),hCH,hCF⟩
  have hWC:ordinaryWheelRim W'=C:=rfl
  refine ⟨W',rfl,rfl,hs,?_,?_⟩
  · intro e
    simp only [ordinaryWheelResources_rim,hWC]
    simpa only [SimpleGraph.mem_edgeFinset] using
      graph_swap_root_indicator (ordinaryWheelRim W) x y hy e
  · intro v z
    have hxy:x≠y:=fun h=>hy (h ▸ hx)
    simp only [ordinaryWheelResources_spoke,show ordinaryWheelHub W'=u' from rfl]
    rw [hWC]
    simp only [hs]
    by_cases hvx:v=x <;> by_cases hvy:v=y <;>
      by_cases hv:v∈(ordinaryWheelRim W).support <;>
      by_cases hz:z=ordinaryWheelHub W <;> by_cases hz':z=u'
    all_goals simp_all only [eq_comm,true_and,and_true,false_and,and_false,
      true_or,or_true,false_or,or_false,not_true_eq_false,not_false_eq_true,ite_true,ite_false]
    all_goals simp_all
    all_goals simp [Ne.symm hvx]

end Oberwolfach
