module

public import Oberwolfach.PrescribedSourceEdgeUpdate

@[expose] public section
/-! Maintain the exact relation between tracked source edges and physical
edges across a whole-family component update. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype X] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_source_edge_update
    (A:I→Finset X) (f:I→X→V) (Q:I→SimpleGraph X)
    (R:I→Finset (Sym2 X)) (E:I→Finset (Sym2 V))
    (hrepr:∀ i,E i=(R i).image (Sym2.map (f i)))
    (hsource:∀ i,R i⊆(Q i).edgeFinset)
    (hends:∀ i e,e∈R i→∀ x∈e.toFinset,x∈A i)
    (k:I) (C:Finset X) (g:X→V) (D:Finset (Sym2 X))
    (hpres:∀ x∈A k,g x=f k x) (hnewsub:D⊆(Q k).edgeFinset)
    (hnewends:∀ e∈D,∀ x∈e.toFinset,x∈A k∪C):
    let A':=Function.update A k (A k∪C);
    let f':=Function.update f k g;
    let R':=Function.update R k (R k∪D);
    let E':=Function.update E k (E k∪D.image (Sym2.map g));
    (∀ i,E' i=(R' i).image (Sym2.map (f' i))) ∧
    (∀ i,R' i⊆(Q i).edgeFinset) ∧
    (∀ i e,e∈R' i→∀ x∈e.toFinset,x∈A' i) := by
  intro A' f' R' E'
  constructor
  · intro i
    by_cases hi:i=k
    · subst i
      simp only [E',R',f',Function.update_self]
      rw [hrepr k]
      exact (prescribed_source_edge_update (A k) (f k) g hpres (R k) D (hends k)).symm
    · simpa only [E',R',f',Function.update_of_ne hi] using hrepr i
  constructor
  · intro i
    by_cases hi:i=k
    · subst i
      simp only [R',Function.update_self]
      exact Finset.union_subset (hsource k) hnewsub
    · simpa only [R',Function.update_of_ne hi] using hsource i
  · intro i e he x hx
    by_cases hi:i=k
    · subst i
      have he':e∈R k∪D:=by simpa only [R',Function.update_self] using he
      have hx':x∈A k∪C:=by
        rcases Finset.mem_union.mp he' with he'|he'
        · exact Finset.mem_union_left C (hends k e he' x hx)
        · exact hnewends e he' x hx
      simpa only [A',Function.update_self] using hx'
    · have he':e∈R i:=by simpa only [R',Function.update_of_ne hi] using he
      have hx':x∈A i:=hends i e he' x hx
      simpa only [A',Function.update_of_ne hi] using hx'
end Oberwolfach
