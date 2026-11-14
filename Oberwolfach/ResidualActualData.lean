module

public import Oberwolfach.ResidualActualEmbeddingOverlap
public import Oberwolfach.ResidualSubtypeGlueInputs

@[expose] public section
/-! Data of the actual selected paths and cycles.  These definitions record
one fixed deletion; no random sampling or new source orientation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]

structure ActualResidualData (F:SimpleGraph V) where
  s₁ : Finset K
  s₂ : Finset K
  hs : Disjoint s₁ s₂
  u : K→V
  v : K→V
  P : ∀i,F.Walk (u i) (v i)
  hp : ∀i∈s₁∪s₂,(P i).IsPath
  hP : (↑(s₁∪s₂):Set K).PairwiseDisjoint (fun i=>(P i).support.toFinset)
  c : ℕ
  d : ℕ
  hc : 3≤c
  hd : 0<d
  hlen : ∀i∈s₁∪s₂,(P i).length=c*d+4
  T : K→Finset ℕ
  hT : ∀i,T i⊆Finset.range d
  t : Finset J
  root : J→V
  C : ∀j,F.Walk (root j) (root j)
  hcycle : ∀j∈t,(C j).IsCycle
  hC : (↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset)
  hcross : ∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset
  Cembed : Finset V
  hEmbed : Cembed⊆t.biUnion (fun j=>(C j).support.toFinset)

namespace ActualResidualData
variable {F:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) F)
def Z:=DeletedPathIndex a.s₁ a.s₂ a.d a.T
instance : Fintype a.Z := by unfold Z; infer_instance
def start (z:a.Z):V:=deletedPathStart F a.s₁ a.s₂ a.u a.v a.P a.c a.d a.T z
def finish (z:a.Z):V:=deletedPathEnd F a.s₁ a.s₂ a.u a.v a.P a.c a.d a.T z
def path (z:a.Z):F.Walk (a.start z) (a.finish z):=
  deletedPathWalk F a.s₁ a.s₂ a.u a.v a.P a.c a.d a.T (fun i _=>a.hT i) z
def deletedVertices:Finset V:=a.t.biUnion (fun j=>(a.C j).support.toFinset) ∪
  Finset.univ.biUnion (fun z:a.Z=>(a.path z).support.toFinset\{a.start z,a.finish z})
def deletedEdges:Finset (Sym2 V):=a.t.biUnion (fun j=>(a.C j).edges.toFinset) ∪
  Finset.univ.biUnion (fun z:a.Z=>(a.path z).edges.toFinset)
abbrev graph:SimpleGraph V:=F.deleteEdges (a.deletedEdges:Set (Sym2 V))
def remaining:Finset V:=Finset.univ\a.deletedVertices
def prescribed:Finset V:=(a.s₁.biUnion (fun i=>{(a.P i).getVert 2,(a.P i).getVert (2+a.c*a.d)})) ∪
  (a.remaining ∩ a.s₂.biUnion (fun i=>(Finset.range (a.d+1)).image (fun j=>(a.P i).getVert (2+a.c*j))))
def additionalSelectedInteriors:Finset V:=Finset.univ.biUnion (fun i:{i // i∈a.s₁}=>
  (a.path (.inl i)).support.toFinset\{a.start (.inl i),a.finish (.inl i)})
def oldDomain:Finset V:=(a.prescribed ∪
  (Finset.univ.biUnion (fun r:SelectedRunIndex a.s₂ a.d a.T=>(a.path (.inr r)).support.toFinset)) ∪ a.Cembed) ∪ a.additionalSelectedInteriors

theorem graph_facts (hF:F.IsRegularOfDegree 2):
    a.graph≤F ∧ a.prescribed⊆a.remaining ∧
    (∀x∈a.prescribed,∀y∈a.prescribed,¬a.graph.Adj x y) ∧
    a.remaining.card≤a.graph.edgeFinset.card+a.prescribed.card ∧
    (∀x,x∉a.remaining→∀y,¬a.graph.Adj x y) ∧
    a.oldDomain∩a.remaining=a.prescribed := by
  have h:=residual_actual_graph_and_prescriptions F hF a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d a.hc a.hd a.hlen a.T a.hT a.t a.root a.C a.hcycle a.hC a.hcross
  have ho:=residual_actual_embedding_overlap F hF a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d a.hc a.hd a.hlen a.T a.hT a.t a.root a.C a.hcycle a.hC a.hcross a.Cembed a.hEmbed
  have hExtra:a.additionalSelectedInteriors⊆a.deletedVertices:=by
    intro x hx
    obtain ⟨i,_,hxi⟩:=Finset.mem_biUnion.mp hx
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨.inl i,Finset.mem_univ _,hxi⟩
  have hExtraR:a.additionalSelectedInteriors∩a.remaining=∅:=by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (hExtra hx)
  have ho':a.oldDomain∩a.remaining=a.prescribed:=by
    rw [oldDomain,Finset.union_inter_distrib_right,hExtraR,Finset.union_empty]
    exact ho
  dsimp only [graph,remaining,prescribed,deletedVertices,deletedEdges,path,start,finish,Z] at h ho' ⊢
  refine ⟨F.deleteEdges_le _,h.1,h.2.1,?_,?_,ho'⟩
  · exact h.2.2.2.2.1
  · intro x hx y
    apply h.2.2.2.2.2
    simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hx
theorem old_domain_union_remaining
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed):
    a.oldDomain∪a.remaining=Finset.univ:=by
  ext x
  simp only [Finset.mem_union,Finset.mem_univ,iff_true]
  by_cases hx:x∈a.remaining
  · exact Or.inr hx
  · left
    have hxDel:x∈a.deletedVertices:=by
      simpa only [remaining,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hx
    obtain hxCycle|hxPaths:=Finset.mem_union.mp hxDel
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hCycle hxCycle))
    · obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hxPaths
      cases z with
      | inl i =>
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hz⟩)
      | inr r =>
        have hxs:x∈(a.path (.inr r)).support.toFinset:=(Finset.mem_sdiff.mp hz).1
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hxs⟩)))
end ActualResidualData
end Oberwolfach
