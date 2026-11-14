module

public import Oberwolfach.OrdinaryVertexWheelPairs
public import Oberwolfach.TriangleSupportEdges

@[expose] public section

/-! Triangular vertex wheels need no additional internal path. Their two
non-root vertices may be reused in another wheel; disjointness is checked
at the family level rather than imposed on these supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_wheel (Q F:SimpleGraph V) (H:V→U→Prop)
    (x a b:V) (u:U) (hxa:Q.Adj x a) (hxb:Q.Adj x b) (hab:Q.Adj a b)
    (hH:H x u∧H a u∧H b u)
    (hF:∀ v∈({x,a,b}:Finset V),∀ w∈({x,a,b}:Finset V),¬F.Adj v w):
    ∃ C:OrdinaryWheel Q F H 3,ordinaryWheelHub C=u ∧
      (∀ v,v∈(ordinaryWheelRim C).support↔v∈({x,a,b}:Finset V)) ∧
      (ordinaryWheelRim C).Adj x a ∧ (ordinaryWheelRim C).Adj x b ∧
      (ordinaryWheelRim C).Adj a b:=by
  obtain ⟨C,hC⟩:=triangle_cycle_from_vertices_support Q x a b hxa.ne hxb.ne hab.ne hxa hxb hab
  have hs (v:V):v∈C.val.val.support↔v∈({x,a,b}:Finset V):=by
    rw [←Set.mem_toFinset,hC]
  have hh:∀ v∈C.val.val.support,H v u:=by
    intro v hv
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using (hs v).mp hv : v=x∨v=a∨v=b) with rfl|rfl|rfl
    · exact hH.1
    · exact hH.2.1
    · exact hH.2.2
  let W:OrdinaryWheel Q F H 3:=⟨(C,u),hh,fun v hv w hw=>hF v ((hs v).mp hv) w ((hs w).mp hw)⟩
  have he (v w:V):C.val.val.Adj v w↔v∈({x,a,b}:Finset V)∧w∈({x,a,b}:Finset V)∧v≠w:=by
    rw [C.val.property.triangle_adj,hs,hs]
  exact ⟨W,rfl,hs,(he x a).mpr ⟨by simp,by simp,hxa.ne⟩,
    (he x b).mpr ⟨by simp,by simp,hxb.ne⟩,(he a b).mpr ⟨by simp,by simp,hab.ne⟩⟩

theorem triangular_vertex_wheel_pair (Q F:SimpleGraph V) (H:V→U→Prop)
    (x y a b:V) (u:U) (hxy:x≠y)
    (hxa:Q.Adj x a) (hxb:Q.Adj x b) (hya:Q.Adj y a) (hyb:Q.Adj y b) (hab:Q.Adj a b)
    (hH:H x u∧H y u∧H a u∧H b u)
    (hF:∀ v∈({x,a,b}:Finset V),∀ w∈({x,a,b}:Finset V),¬F.Adj v w)
    (hFy:¬F.Adj y a∧¬F.Adj y b):
    ∃ D:OrdinaryVertexWheelPair Q F H 3 x y a b u,
      (∀ v,v∈(ordinaryWheelRim D.first).support↔v∈({x,a,b}:Finset V)) ∧
      (∀ v,v∈(ordinaryWheelRim D.second).support↔v∈({y,a,b}:Finset V)) ∧
      rootWheelInternal D.first x a b=∅:=by
  obtain ⟨C,hCu,hCs,hCxa,hCxb,_⟩:=ordinary_triangle_wheel Q F H x a b u hxa hxb hab
    ⟨hH.1,hH.2.2.1,hH.2.2.2⟩ hF
  have hy:y∉(ordinaryWheelRim C).support:=by
    rw [hCs]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨hxy.symm,hya.ne,hyb.ne⟩
  have hneighbors (v:V) (hv:(ordinaryWheelRim C).Adj x v):v=a∨v=b:=by
    have hm: v∈(ordinaryWheelRim C).neighborFinset x:=((ordinaryWheelRim C).mem_neighborFinset x v).mpr hv
    rw [ordinaryWheel_root_neighbors C x a b hab.ne hCxa hCxb] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hremaining (v:V) (hv:v∈(ordinaryWheelRim C).support) (hvx:v≠x):v=a∨v=b:=by
    have hm: v=x∨v=a∨v=b:=by simpa only [Finset.mem_insert,Finset.mem_singleton] using (hCs v).mp hv
    exact hm.resolve_left hvx
  obtain ⟨C',hmap,hC'u,hs,hrim,hsp⟩:=ordinary_wheel_root_replacement C x y u hCxa.mem_support_left hy
    (fun v hv=>(hneighbors v hv).elim (fun h=>h ▸ hya) (fun h=>h ▸ hyb))
    (fun v hv hvx=>(hremaining v hv hvx).elim (fun h=>h ▸ hFy.1) (fun h=>h ▸ hFy.2)) hH.2.1
    (fun v hv hvx=>(hremaining v hv hvx).elim (fun h=>h ▸ hH.2.2.1) (fun h=>h ▸ hH.2.2.2))
  have hnew (v:V) (hv:(ordinaryWheelRim C).Adj x v):(ordinaryWheelRim C').Adj y v:=by
    have hvy:v≠y:=fun he=>hy (he ▸ hv.mem_support_right)
    rw [hmap,graph_swap_adj,Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hv.ne.symm hvy]
    exact hv
  have hedge (z:V):graphRootEdges (ordinaryWheelRim C) x z={s(z,a),s(z,b)}:=by
    unfold graphRootEdges
    rw [ordinaryWheel_root_neighbors C x a b hab.ne hCxa hCxb]
    simp
  let D:OrdinaryVertexWheelPair Q F H 3 x y a b u:=
    ⟨C,C',hCu,hC'u,hCxa,hCxb,hnew a hCxa,hnew b hCxb,hmap,hs,
      fun e=>by simpa only [hedge] using hrim e,
      fun v z=>by have hh:=hsp v z;rw [hCu] at hh;omega⟩
  refine ⟨D,hCs,?_,?_⟩
  · intro v
    change v∈(ordinaryWheelRim C').support↔v∈({y,a,b}:Finset V)
    rw [hs,hCs]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro (he|⟨he|he|he,hne⟩)
      · exact Or.inl he
      · exact (hne he).elim
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr he)
    · rintro (rfl|rfl|rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr (Or.inl rfl),hxa.ne.symm⟩
      · exact Or.inr ⟨Or.inr (Or.inr rfl),hxb.ne.symm⟩
  · ext v
    simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.notMem_empty,iff_false]
    exact fun hv=>hv.2 ((hCs v).mp hv.1)

end Oberwolfach
