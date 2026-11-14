module

public import Oberwolfach.OrdinaryWheelRootReplacement
public import Oberwolfach.GraphTwoRootReplacement
public import Oberwolfach.RootWheelCaps
public import Oberwolfach.PathCycleSupport

@[expose] public section

/-! The spoke-edge and vertex-wheel pairs use an already selected common
path. Their precise path set is retained for the later hub-switch identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_one_root_path_wheels (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (hr:3≤r) (x y a b:V) (u u':U) (p:Q.Walk a b)
    (hp:p.IsPath) (hlen:p.length=r-2) (hxy:x≠y)
    (hxa:Q.Adj x a) (hxb:Q.Adj x b) (hya:Q.Adj y a) (hyb:Q.Adj y b)
    (havoid:∀ v∈p.support,v≠x∧v≠y)
    (hF:∀ v∈insert x (insert y p.support.toFinset),
      ∀ w∈insert x (insert y p.support.toFinset),¬F.Adj v w)
    (hH:H x u∧H y u') (hHp:∀ v∈p.support,H v u∧H v u'):
    ∃ W W':OrdinaryWheel Q F H r,
      ordinaryWheelHub W=u ∧ ordinaryWheelHub W'=u' ∧
      (∀ v,v∈(ordinaryWheelRim W).support↔v=x∨v∈p.support) ∧
      (∀ v,v∈(ordinaryWheelRim W').support↔v=y∨v∈p.support) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
        (if e=s(x,a) then 1 else 0)+(if e=s(x,b) then 1 else 0)-
          (if e=s(y,a) then 1 else 0)-(if e=s(y,b) then 1 else 0)) ∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources W' then 1 else 0)=
        (if v=x∧z=u then 1 else 0)-(if v=y∧z=u' then 1 else 0)+
        (if v∈p.support∧z=u then 1 else 0)-(if v∈p.support∧z=u' then 1 else 0)):=by
  have hxp:x∉p.support:=fun h=>(havoid x h).1 rfl
  let q:Q.Walk x b:=p.cons hxa
  have hq:q.IsPath:=SimpleGraph.Walk.IsPath.cons hp hxp
  have hqLen:q.length=r-1:=by simp only [q,SimpleGraph.Walk.length_cons,hlen];omega
  obtain ⟨C,hC,hCQ,hCxb,hCs,hsteps⟩:=embedded_cycle_from_path_with_support Q r hr x b q hq hqLen hxb
  have hs (v:V):v∈C.support↔v=x∨v∈p.support:=by
    rw [hCs];simp only [q,SimpleGraph.Walk.support_cons,List.mem_cons]
  have hCxa:C.Adj x a:=by
    have hh:=hsteps 0 (by rw [hqLen];omega)
    simpa [q] using hh
  have hab:a≠b:=by
    intro he
    subst b
    have hz:=SimpleGraph.Walk.isPath_iff_eq_nil.mp hp
    rw [hz,SimpleGraph.Walk.length_nil] at hlen
    omega
  have hin (v:V) (hv:v∈C.support):v∈insert x (insert y p.support.toFinset):=by
    rcases (hs v).mp hv with rfl|hv <;> simp [hv]
  let W:OrdinaryWheel Q F H r:=⟨(⟨⟨C,hC⟩,hCQ⟩,u),
    (fun v hv=>by rcases (hs v).mp hv with rfl|hv;exact hH.1;exact (hHp v hv).1),
    (fun v hv w hw=>hF v (hin v hv) w (hin w hw))⟩
  have hyC:y∉C.support:=by
    intro hy
    rcases (hs y).mp hy with he|hy
    · exact hxy he.symm
    · exact (havoid y hy).2 rfl
  have hneigh:C.neighborFinset x={a,b}:=ordinaryWheel_root_neighbors W x a b hab hCxa hCxb
  have hnew:∀ v,C.Adj x v→Q.Adj y v:=by
    intro v hv
    have hm:v∈C.neighborFinset x:=(C.mem_neighborFinset x v).mpr hv
    rw [hneigh] at hm
    rcases Finset.mem_insert.mp hm with rfl|hm
    · exact hya
    · exact Finset.mem_singleton.mp hm ▸ hyb
  obtain ⟨W',hWr,hWu,hWs,hrim,hsp⟩:=ordinary_wheel_root_replacement W x y u'
    hCxa.mem_support_left hyC hnew (fun v hv _=>hF y (by simp) v (hin v hv)) hH.2
    (fun v hv hvx=>by
      have hpv: v∈p.support:=((hs v).mp hv).resolve_left hvx
      exact (hHp v hpv).2)
  have hs' (v:V):v∈(ordinaryWheelRim W').support↔v=y∨v∈p.support:=by
    rw [hWs,show ordinaryWheelRim W=C from rfl,hs]
    constructor
    · rintro (he|⟨he|hv,hvx⟩)
      · exact Or.inl he
      · exact (hvx he).elim
      · exact Or.inr hv
    · rintro (he|hv)
      · exact Or.inl he
      · exact Or.inr ⟨Or.inr hv,(havoid v hv).1⟩
  refine ⟨W,W',rfl,hWu,hs,hs',?_,?_⟩
  · intro e
    have hge (z:V):graphRootEdges C x z={s(z,a),s(z,b)}:=by
      unfold graphRootEdges;rw [hneigh];simp
    have hh:=hrim e
    change (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-
      (if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
      (if e∈graphRootEdges C x x then 1 else 0)-(if e∈graphRootEdges C x y then 1 else 0) at hh
    rw [hge,hge,int_indicator_pair e _ _ (fun h=>hab (sym2_fixed_endpoint_injective x h)),
      int_indicator_pair e _ _ (fun h=>hab (sym2_fixed_endpoint_injective y h))] at hh
    linarith only [hh]
  · intro v z
    have he:(v∈C.support∧v≠x)↔v∈p.support:=by
      rw [hs]
      constructor
      · rintro ⟨he|hv,hvx⟩
        · exact (hvx he).elim
        · exact hv
      · intro hv
        exact ⟨Or.inr hv,(havoid v hv).1⟩
    simpa only [show ordinaryWheelRim W=C from rfl,show ordinaryWheelHub W=u from rfl,
      and_assoc,←and_assoc,he] using hsp v z

end Oberwolfach
