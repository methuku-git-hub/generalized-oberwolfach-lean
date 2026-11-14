module

public import Oberwolfach.OrdinaryWheelRootReplacement
public import Oberwolfach.SparseRootWheels
public import Oberwolfach.RootWheelCaps

@[expose] public section

/-! Construct both root replacements from common-neighbour counts. The
two wheels use the same internal path. Neither a conflict-free pair of
roots nor cross-spokes at the wrong hub are assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_paired_root_wheels (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W Ω:Finset V) (hAΩ:A⊆Ω) (x y v w:V) (u u':U)
    (hxy:x≠y) (hvw:v≠w) (hvΩ:v∈Ω) (hwΩ:w∈Ω)
    (hxv:Q.Adj x v) (hxw:Q.Adj x w) (hyv:Q.Adj y v) (hyw:Q.Adj y w)
    (hFroot:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (hFy:¬F.Adj y v∧¬F.Adj y w)
    (hHroot:H x u∧H y u'∧H v u∧H w u∧H v u'∧H w u')
    (hHA:∀ a∈A,H a u∧H a u')
    (r:ℕ) (hr:4≤r) (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ a∈Ω,∀ c∈Ω,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:W.card+((r:ℝ)+4)*(L+1)<b):
    ∃ C C':OrdinaryWheel Q F H r,
      ordinaryWheelHub C=u ∧ ordinaryWheelHub C'=u' ∧
      (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
      (ordinaryWheelRim C').Adj y v ∧ (ordinaryWheelRim C').Adj y w ∧
      ordinaryWheelRim C'=(ordinaryWheelRim C).map (Equiv.swap x y).toEmbedding ∧
      (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V)∨a∈A∧a∉W∧a≠y) ∧
      (∀ a,a∈(ordinaryWheelRim C').support↔a=y∨(a∈(ordinaryWheelRim C).support∧a≠x)) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources C then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources C' then 1 else 0)=
        (if e∈({s(x,v),s(x,w)}:Finset (Sym2 V)) then 1 else 0)-
          (if e∈({s(y,v),s(y,w)}:Finset (Sym2 V)) then 1 else 0)) ∧
      (∀ a z,
        (if Sum.inr (a,z)∈ordinaryWheelResources C then (1:ℤ) else 0)-
          (if Sum.inr (a,z)∈ordinaryWheelResources C' then 1 else 0)=
        (if a=x∧z=u then 1 else 0)-(if a=y∧z=u' then 1 else 0)+
        (if a∈(ordinaryWheelRim C).support∧a≠x∧z=u then 1 else 0)-
          (if a∈(ordinaryWheelRim C).support∧a≠x∧z=u' then 1 else 0)):=by
  let W₀:=W∪insert y (F.neighborFinset y)
  have hW₀:(W₀.card:ℝ)≤W.card+L+1:=by
    have hh:W₀.card≤W.card+(F.neighborFinset y).card+1:=by
      have hi:=Finset.card_insert_le y (F.neighborFinset y)
      exact (Finset.card_union_le _ _).trans (by omega)
    have hh':(W₀.card:ℝ)≤W.card+F.degree y+1:=by exact_mod_cast hh
    linarith only [hh',hF y]
  obtain ⟨C,hCu,hCxv,hCxw,hCs⟩:=ordinary_root_wheel_from_common_counts_within Q F H A W₀ Ω hAΩ x v w
    hvΩ hwΩ u hvw hxv hxw hFroot ⟨hHroot.1,hHroot.2.2.1,hHroot.2.2.2.1⟩
    (fun a ha=>(hHA a ha).1) r hr L b hL hF hcount (by nlinarith only [hW₀,hbudget])
  have hyC:y∉(ordinaryWheelRim C).support:=by
    intro hy
    rcases hCs y hy with hy|hy
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with hy|hy|hy
      · exact hxy hy.symm
      · exact hyv.ne hy
      · exact hyw.ne hy
    · exact hy.2 (by simp [W₀])
  have hCy:∀ a,(ordinaryWheelRim C).Adj x a→Q.Adj y a:=by
    intro a ha
    have hm: a∈(ordinaryWheelRim C).neighborFinset x:=((ordinaryWheelRim C).mem_neighborFinset x a).mpr ha
    rw [ordinaryWheel_root_neighbors C x v w hvw hCxv hCxw] at hm
    rcases Finset.mem_insert.mp hm with rfl|hm
    · exact hyv
    · exact Finset.mem_singleton.mp hm ▸ hyw
  have hCFy:∀ a∈(ordinaryWheelRim C).support,a≠x→¬F.Adj y a:=by
    intro a ha hax
    rcases hCs a ha with ha|ha
    · simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with ha|rfl|rfl
      · exact (hax ha).elim
      · exact hFy.1
      · exact hFy.2
    · intro he
      exact ha.2 (Finset.mem_union_right _ (Finset.mem_insert_of_mem ((F.mem_neighborFinset y a).mpr he)))
  have hCH':∀ a∈(ordinaryWheelRim C).support,a≠x→H a u':=by
    intro a ha hax
    rcases hCs a ha with ha|ha
    · simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with ha|rfl|rfl
      · exact (hax ha).elim
      · exact hHroot.2.2.2.2.1
      · exact hHroot.2.2.2.2.2
    · exact (hHA a ha.1).2
  obtain ⟨C',hC'r,hC'u,hC's,hrim,hsp⟩:=ordinary_wheel_root_replacement C x y u'
    hCxv.mem_support_left hyC hCy hCFy hHroot.2.1 hCH'
  have hnew (a:V) (ha:(ordinaryWheelRim C).Adj x a):
      (ordinaryWheelRim C').Adj y a:=by
    have hay:a≠y:=fun h=>hyC (h ▸ ha.mem_support_right)
    rw [hC'r,graph_swap_adj,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne ha.ne.symm hay]
    exact ha
  refine ⟨C,C',hCu,hC'u,hCxv,hCxw,hnew v hCxv,hnew w hCxw,hC'r,?_,hC's,?_,?_⟩
  · intro a ha
    rcases hCs a ha with ha|ha
    · exact Or.inl ha
    · refine Or.inr ⟨ha.1,fun h=>ha.2 (Finset.mem_union_left _ h),?_⟩
      intro h;exact ha.2 (by simp [W₀,h])
  · intro e
    have hedge (z:V):graphRootEdges (ordinaryWheelRim C) x z={s(z,v),s(z,w)}:=by
      unfold graphRootEdges
      rw [ordinaryWheel_root_neighbors C x v w hvw hCxv hCxw]
      simp
    simpa only [hedge] using hrim e
  · intro a z;simpa only [hCu] using hsp a z

end Oberwolfach
