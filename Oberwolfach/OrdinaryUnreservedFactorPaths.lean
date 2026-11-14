module

public import Oberwolfach.OrdinaryComplementPieceDegree

@[expose] public section
/-! Removing whole reserved components leaves a two-regular induced factor.
Every source path and cycle avoiding those components lifts to this factor,
with its length, support and path/cycle property preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_factor_paths
    {n:ℕ} (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (Cres:Finset F.ConnectedComponent):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    (F.induce S).IsRegularOfDegree 2 ∧
    (∀(a b:Fin n) (p:F.Walk a b) (hp:p.IsPath) (hmem:∀x∈p.support,x∈S),
      let q:=p.induce S hmem;
      q.length=p.length ∧ q.IsPath ∧ q.support.map Subtype.val=p.support) ∧
    (∀(a:Fin n) (p:F.Walk a a) (hp:p.IsCycle) (hmem:∀x∈p.support,x∈S),
      let q:=p.induce S hmem;
      q.length=p.length ∧ q.IsCycle ∧ q.support.map Subtype.val=p.support) :=by
  intro S
  have hreg:(F.induce S).IsRegularOfDegree 2:=by
    intro x
    have hs:F.neighborSet x.val⊆S:=by
      intro y hxy
      change F.connectedComponentMk y∉Cres
      have heq:F.connectedComponentMk y=F.connectedComponentMk x.val:=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
      have hx:F.connectedComponentMk x.val∉Cres:=x.property
      simpa only [heq] using hx
    simpa only [hF x.val] using (F.degree_induce_of_neighborSet_subset hs)
  refine ⟨hreg,?_,?_⟩
  · intro a b p hp hmem q
    have hmap:=p.map_induce hmem
    have hlen:=congrArg SimpleGraph.Walk.length hmap
    have hpath:(q.map (SimpleGraph.Embedding.induce S).toHom).IsPath:=by rw [hmap];exact hp
    have hsupp:=congrArg SimpleGraph.Walk.support hmap
    refine ⟨?_,hpath.of_map,?_⟩
    · simpa only [SimpleGraph.Walk.length_map] using hlen
    · rw [SimpleGraph.Walk.support_map] at hsupp
      change (p.induce S hmem).support.map Subtype.val=p.support at hsupp
      exact hsupp
  · intro a p hp hmem q
    have hmap:=p.map_induce hmem
    have hlen:=congrArg SimpleGraph.Walk.length hmap
    have hcycle:(q.map (SimpleGraph.Embedding.induce S).toHom).IsCycle:=by rw [hmap];exact hp
    have hsupp:=congrArg SimpleGraph.Walk.support hmap
    refine ⟨?_,hcycle.of_map,?_⟩
    · simpa only [SimpleGraph.Walk.length_map] using hlen
    · rw [SimpleGraph.Walk.support_map] at hsupp
      change (p.induce S hmem).support.map Subtype.val=p.support at hsupp
      exact hsupp
end Oberwolfach
