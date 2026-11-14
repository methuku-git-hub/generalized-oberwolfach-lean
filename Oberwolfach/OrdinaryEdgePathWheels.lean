module

public import Oberwolfach.OrdinaryWheelTwoRootReplacement
public import Oberwolfach.PathCycleSupport

@[expose] public section

/-! An actual simple path constructs the paired rim-edge wheels in the
transformer. The roots and path are retained exactly, including the root
edge and the two attachment edges in the signed identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edge_path_wheels (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (hr:3≤r) (x y x' y' a b:V) (u:U) (p:Q.Walk a b)
    (hp:p.IsPath) (hlen:p.length=r-3)
    (hxy:Q.Adj x y) (hxa:Q.Adj x a) (hyb:Q.Adj y b)
    (hxy':Q.Adj x' y') (hxa':Q.Adj x' a) (hyb':Q.Adj y' b)
    (hx'x:x'≠x) (hx'y:x'≠y) (hy'x:y'≠x) (hy'y:y'≠y)
    (havoid:∀ v∈p.support,v∉({x,y,x',y'}:Finset V))
    (hF:∀ v∈insert x (insert y (insert x' (insert y' p.support.toFinset))),
      ∀ w∈insert x (insert y (insert x' (insert y' p.support.toFinset))),¬F.Adj v w)
    (hH:∀ v∈insert x (insert y (insert x' (insert y' p.support.toFinset))),H v u):
    ∃ W W':OrdinaryWheel Q F H r,
      ordinaryWheelHub W=u ∧ ordinaryWheelHub W'=u ∧
      (∀ v,v∈(ordinaryWheelRim W).support↔v=x∨v=y∨v∈p.support) ∧
      (∀ v,v∈(ordinaryWheelRim W').support↔v=x'∨v=y'∨v∈p.support) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
        (if e=s(x,y) then 1 else 0)+(if e=s(x,a) then 1 else 0)+(if e=s(y,b) then 1 else 0)-
          (if e=s(x',y') then 1 else 0)-(if e=s(x',a) then 1 else 0)-(if e=s(y',b) then 1 else 0)) ∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources W' then 1 else 0)=
        (if v=x∧z=u then 1 else 0)+(if v=y∧z=u then 1 else 0)-
          (if v=x'∧z=u then 1 else 0)-(if v=y'∧z=u then 1 else 0)):=by
  have hout (v:V) (hv:v∈p.support):v≠x∧v≠y∧v≠x'∧v≠y':=by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using havoid v hv
  have hxp:x∉p.support:=fun h=>(hout x h).1 rfl
  have hyp:y∉p.support:=fun h=>(hout y h).2.1 rfl
  let q:Q.Walk x y:=(p.cons hxa).concat hyb.symm
  have hq:q.IsPath:=by
    apply (SimpleGraph.Walk.IsPath.cons hp hxp).concat
    · simp only [SimpleGraph.Walk.support_cons,List.mem_cons,not_or]
      exact ⟨hxy.ne.symm,hyp⟩
  have hqlen:q.length=r-1:=by
    simp only [q,SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_cons,hlen]
    omega
  obtain ⟨C,hC,hCQ,hCxy,hCs,hsteps⟩:=embedded_cycle_from_path_with_support Q r (by omega) x y q hq hqlen hxy
  have hsupport (v:V):v∈C.support↔v=x∨v=y∨v∈p.support:=by
    rw [hCs]
    simp only [q,SimpleGraph.Walk.support_concat,SimpleGraph.Walk.support_cons,
      List.mem_append,List.mem_cons,List.mem_singleton]
    tauto
  have hCxa:C.Adj x a:=by
    have hh:=hsteps 0 (by rw [hqlen];omega)
    simpa [q] using hh
  have hCyb:C.Adj y b:=by
    have hqb:q.getVert (p.length+1)=b:=by
      simp [q,SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.getVert_cons_succ]
    have hqy:q.getVert (p.length+1+1)=y:=by
      have he:p.length+1+1=q.length:=by simp [q]
      rw [he,q.getVert_length]
    have hh:=hsteps (p.length+1) (by simp [q])
    rw [hqb,hqy] at hh
    exact hh.symm
  have hin (v:V) (hv:v∈C.support):v∈insert x (insert y (insert x' (insert y' p.support.toFinset))):=by
    rcases (hsupport v).mp hv with rfl|rfl|hv <;> simp [hv]
  let W:OrdinaryWheel Q F H r:=⟨(⟨⟨C,hC⟩,hCQ⟩,u),
    (fun v hv=>hH v (hin v hv)),(fun v hv w hw=>hF v (hin v hv) w (hin w hw))⟩
  have hx'out:x'∉C.support:=by
    intro h
    rcases (hsupport x').mp h with h|h|h
    · exact hx'x h
    · exact hx'y h
    · exact (hout x' h).2.2.1 rfl
  have hy'out:y'∉C.support:=by
    intro h
    rcases (hsupport y').mp h with h|h|h
    · exact hy'x h
    · exact hy'y h
    · exact (hout y' h).2.2.2 rfl
  obtain ⟨W',_hW'r,hW'u,hW's,hrim,hspoke⟩:=ordinary_wheel_two_root_replacement W x y x' y' a b
    hCxy hCxa hCyb (hout a p.start_mem_support).2.1.symm (hout b p.end_mem_support).1.symm
    hx'out hy'out hxy'.ne hxy' hxa' hyb' ⟨hH x' (by simp),hH y' (by simp)⟩
    (hF x' (by simp) y' (by simp))
    (fun v hv _ _=>⟨hF x' (by simp) v (hin v hv),hF y' (by simp) v (hin v hv)⟩)
  refine ⟨W,W',rfl,hW'u,hsupport,?_,hrim,hspoke⟩
  intro v
  rw [hW's,show ordinaryWheelRim W=C from rfl,hsupport]
  constructor
  · rintro (h|h|⟨h|h|h,hvx,hvy⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (hvx h).elim
    · exact (hvy h).elim
    · exact Or.inr (Or.inr h)
  · rintro (h|h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Or.inr (Or.inr h),(hout v h).1,(hout v h).2.1⟩)

end Oberwolfach
