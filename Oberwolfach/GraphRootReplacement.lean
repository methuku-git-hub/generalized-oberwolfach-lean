module

public import Oberwolfach.FractionalRelabeling
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Relabel one supported vertex to an unused label. The exact changes
are its incident edges; all other edges are retained with multiplicity one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def graphRootEdges (C:SimpleGraph V) (x z:V):Finset (Sym2 V):=
  (C.neighborFinset x).image (fun v=>s(z,v))

theorem graphRootEdges_mem (C:SimpleGraph V) (x z a b:V):
    s(a,b)∈graphRootEdges C x z↔(a=z∧C.Adj x b)∨(b=z∧C.Adj x a):=by
  simp only [graphRootEdges,Finset.mem_image,SimpleGraph.mem_neighborFinset,Sym2.eq_iff]
  constructor
  · rintro ⟨v,hv,(⟨hza,hvb⟩|⟨hzb,hva⟩)⟩
    · subst a;subst b;exact Or.inl ⟨rfl,hv⟩
    · subst b;subst a;exact Or.inr ⟨rfl,hv⟩
  · rintro (⟨rfl,hb⟩|⟨rfl,ha⟩)
    · exact ⟨b,hb,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨a,ha,Or.inr ⟨rfl,rfl⟩⟩

theorem graph_swap_adj (C:SimpleGraph V) (x y a b:V):
    (C.map (Equiv.swap x y).toEmbedding).Adj a b↔
      C.Adj (Equiv.swap x y a) (Equiv.swap x y b):=by
  have h:=SimpleGraph.map_adj_apply (G:=C) (f:=(Equiv.swap x y).toEmbedding)
    (a:=Equiv.swap x y a) (b:=Equiv.swap x y b)
  simpa only [Equiv.toEmbedding_apply,Equiv.swap_apply_self] using h

theorem graph_swap_root_support (C:SimpleGraph V) (x y:V)
    (hx:x∈C.support) (hy:y∉C.support) (v:V):
    v∈(C.map (Equiv.swap x y).toEmbedding).support↔
      v=y∨(v∈C.support∧v≠x):=by
  have hxy:x≠y:=fun h=>hy (h ▸ hx)
  rw [SimpleGraph.support_map]
  constructor
  · rintro ⟨a,ha,rfl⟩
    by_cases hax:a=x
    · subst a;simp
    · have hay:a≠y:=fun h=>hy (h ▸ ha)
      rw [Equiv.toEmbedding_apply,Equiv.swap_apply_of_ne_of_ne hax hay]
      exact Or.inr ⟨ha,hax⟩
  · rintro (rfl|⟨hv,hvx⟩)
    · exact ⟨x,hx,by simp⟩
    · exact ⟨v,hv,Equiv.swap_apply_of_ne_of_ne hvx (fun h=>hy (h ▸ hv))⟩

theorem graph_swap_root_indicator (C:SimpleGraph V) (x y:V) (hy:y∉C.support)
    (e:Sym2 V):
    (if e∈C.edgeFinset then (1:ℤ) else 0)-
      (if e∈(C.map (Equiv.swap x y).toEmbedding).edgeFinset then 1 else 0)=
    (if e∈graphRootEdges C x x then 1 else 0)-
      (if e∈graphRootEdges C x y then 1 else 0):=by
  have hno (v:V):¬C.Adj y v:=fun h=>hy h.mem_support_left
  have hno' (v:V):¬C.Adj v y:=fun h=>hy h.mem_support_right
  induction e using Sym2.ind with
  | _ a b=>
    simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,graph_swap_adj,graphRootEdges_mem]
    by_cases hax:a=x <;> by_cases hay:a=y <;> by_cases hbx:b=x <;> by_cases hby:b=y
    all_goals subst_vars
    all_goals simp_all [Equiv.swap_apply_def,SimpleGraph.adj_comm]
    all_goals exact fun h=>hno _ h.symm

theorem graph_swap_root_subgraph (C Q:SimpleGraph V) (x y:V) (hCQ:C≤Q)
    (hy:y∉C.support) (hadj:∀ v,C.Adj x v→Q.Adj y v):
    C.map (Equiv.swap x y).toEmbedding≤Q:=by
  intro a b hab
  obtain ⟨v,w,hvw,rfl,rfl⟩:=(SimpleGraph.map_adj _ _ _ _).mp hab
  have hvy:v≠y:=fun h=>hy (h ▸ hvw.mem_support_left)
  have hwy:w≠y:=fun h=>hy (h ▸ hvw.mem_support_right)
  simp only [Equiv.toEmbedding_apply]
  by_cases hvx:v=x
  · subst v
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hvw.ne.symm hwy]
    exact hadj w hvw
  · by_cases hwx:w=x
    · subst w
      rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hvx hvy]
      exact (hadj v hvw.symm).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy,Equiv.swap_apply_of_ne_of_ne hwx hwy]
      exact hCQ hvw

end Oberwolfach
