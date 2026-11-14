module

public import Oberwolfach.OrdinaryTransformerEdgePaths

@[expose] public section

/-! Endpoints of the actual disjoint paths are distinct occurrences.
This records the injectivity used when pairing rim-path and spoke-path
endpoints at every old vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] {Q:SimpleGraph V}

 def graphPathEndpoint (p:Σ a:V,Σ b:V,Q.Walk a b) (i:Fin 2):V:=if i=0 then p.1 else p.2.1

 theorem graphPathEndpoint_mem (p:Σ a:V,Σ b:V,Q.Walk a b) (i:Fin 2):
    graphPathEndpoint p i∈p.2.2.support:=by
  unfold graphPathEndpoint
  split_ifs
  · exact p.2.2.start_mem_support
  · exact p.2.2.end_mem_support

 theorem graphPathEndpoint_injective (p:Σ a:V,Σ b:V,Q.Walk a b)
    (hp:p.2.2.IsPath) (hlen:0<p.2.2.length):Function.Injective (graphPathEndpoint p):=by
  have hab:p.1≠p.2.1:=by
    rcases p with ⟨a,b,p⟩
    intro he
    dsimp only at he hp hlen
    subst b
    have hz:=SimpleGraph.Walk.isPath_iff_eq_nil.mp hp
    rw [hz,SimpleGraph.Walk.length_nil] at hlen
    omega
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [graphPathEndpoint]

 theorem disjoint_path_endpoint_injective (p:I→(Σ a:V,Σ b:V,Q.Walk a b))
    (hp:∀ i,(p i).2.2.IsPath) (hlen:∀ i,0<(p i).2.2.length)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset):
    Function.Injective (fun z:I×Fin 2=>graphPathEndpoint (p z.1) z.2):=by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  change graphPathEndpoint (p i) a=graphPathEndpoint (p j) b at he
  have hij:i=j:=by
    by_contra hn
    have hi:=List.mem_toFinset.mpr (graphPathEndpoint_mem (p i) a)
    have hj:=List.mem_toFinset.mpr (graphPathEndpoint_mem (p j) b)
    exact Finset.disjoint_left.mp (hdis i j hn) hi (he.symm ▸ hj)
  subst j
  exact Prod.ext rfl (graphPathEndpoint_injective (p i) (hp i) (hlen i) he)

 theorem paired_endpoint_sets_disjoint {K:Type} [DecidableEq K]
    (a b:K→V) (ha:Function.Injective a) (hb:Function.Injective b)
    (hab:∀ i j,a i≠b j):
    (∀ i,a i≠b i) ∧ ∀ i j,i≠j→Disjoint ({a i,b i}:Finset V) {a j,b j}:=by
  refine ⟨fun i=>hab i i,?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv hv'
  rcases hv with hv|hv <;> rcases hv' with hv'|hv'
  · exact hij (ha (hv.symm.trans hv'))
  · exact hab i j (hv.symm.trans hv')
  · exact hab j i (hv'.symm.trans hv)
  · exact hij (hb (hv.symm.trans hv'))

end Oberwolfach
