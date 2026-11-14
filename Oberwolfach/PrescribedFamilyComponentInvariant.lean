module

public import Oberwolfach.PrescribedFamilyUpdate
public import Oberwolfach.PrescribedActualLoadStep
public import Oberwolfach.PrescribedEmbeddingPhysicalStep

@[expose] public section
/-! One factor-level update preserves partial injections, all old images,
the actual free-occurrence load bound, and the physical-edge invariants. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

def familyVertexImage (f:I→X→V) (p:I×X):V:=f p.1 p.2

theorem prescribed_family_component_invariant
    (A:I→Finset X) (f:I→X→V) (T:Finset (I×X)) (k:I) (C:Finset X) (g:X→V) (t:ℝ)
    (hinj:FamilyPartialInjections A f)
    (hT:∀ p∈T,p.2∈A p.1) (hC:Disjoint C (A k))
    (hg:Set.InjOn g (↑(A k∪C):Set X)) (hpres:∀ x∈A k,g x=f k x)
    (hbound:∀ v,((T.filter (fun p=>familyVertexImage f p=v)).card:ℝ)≤t+1)
    (havoid:∀ x∈C,g x∉Finset.univ.filter (fun v=>(t:ℝ)≤(T.filter (fun p=>familyVertexImage f p=v)).card))
    (E:I→Finset (Sym2 V)) (added:Finset (Sym2 V)) (F J:SimpleGraph V)
    (hpair:PairwisePhysicalDisjoint E) (hcover:∀ j,E j⊆F.edgeFinset)
    (hJ:J.edgeFinset⊆F.edgeFinset) (hedges:Disjoint added F.edgeFinset):
    let A':=Function.update A k (A k∪C);
    let f':=Function.update f k g;
    let T':=T∪({k}:Finset I).product C;
    FamilyPartialInjections A' f' ∧
    (∀ i x,x∈A i→f' i x=f i x) ∧
    (∀ p∈T',p.2∈A' p.1) ∧
    (∀ v,((T'.filter (fun p=>familyVertexImage f' p=v)).card:ℝ)≤t+1) ∧
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset := by
  intro A' f' T'
  have hfam:=prescribed_family_update A f k C g hinj hg hpres
  have hTdis:Disjoint T (({k}:Finset I).product C):=by
    apply Finset.disjoint_left.mpr
    intro p hp hprod
    have hh:=Finset.mem_product.mp hprod
    have hk:p.1=k:=by simpa using hh.1
    have hAssigned:=hT p hp
    rw [hk] at hAssigned
    exact (Finset.disjoint_left.mp hC) hh.2 hAssigned
  have hpresAll:∀ p∈T,familyVertexImage f' p=familyVertexImage f p:=by
    intro p hp
    exact hfam.2.1 p.1 p.2 (hT p hp)
  have hnewinj:Set.InjOn (familyVertexImage f') (↑(({k}:Finset I).product C):Set (I×X)):=by
    intro p hp q hq he
    have hp':=Finset.mem_product.mp hp
    have hq':=Finset.mem_product.mp hq
    have hpk:p.1=k:=by simpa using hp'.1
    have hqk:q.1=k:=by simpa using hq'.1
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    simp only at hpk hqk
    subst i
    subst j
    simp only [familyVertexImage,f',Function.update_self] at he
    have hxy:x=y:=hg (by simp [hp'.2]) (by simp [hq'.2]) he
    subst y
    rfl
  have hnewavoid:∀ p∈(({k}:Finset I).product C),familyVertexImage f' p∉
      Finset.univ.filter (fun v=>(t:ℝ)≤(T.filter (fun q=>familyVertexImage f q=v)).card):=by
    intro p hp
    have hh:=Finset.mem_product.mp hp
    have hk:p.1=k:=by simpa using hh.1
    change f' p.1 p.2 ∉ _
    rw [hk]
    simpa only [f',Function.update_self] using havoid p.2 hh.2
  have hload:=prescribed_actual_component_load_step T (({k}:Finset I).product C)
    (familyVertexImage f) (familyVertexImage f') t hTdis hpresAll hnewinj hbound hnewavoid
  have hed:=prescribed_embedding_physical_step E k added F J hpair hcover hJ hedges
  refine ⟨hfam.1,hfam.2.1,?_,hload,hed.1,hed.2⟩
  intro p hp
  change p∈T∪({k}:Finset I).product C at hp
  rcases Finset.mem_union.mp hp with hp|hp
  · have hOld:=hT p hp
    by_cases hi:p.1=k
    · have hOldK:p.2∈A k:=by simpa only [hi] using hOld
      have hmem:p.2∈A k∪C:=Finset.mem_union_left C hOldK
      simpa only [hi,A',Function.update_self] using hmem
    · simpa [A',Function.update_of_ne hi] using hOld
  · have hh:=Finset.mem_product.mp hp
    have hk:p.1=k:=by simpa using hh.1
    rw [hk]
    simpa only [A',Function.update_self] using Finset.mem_union_right (A k) hh.2
end Oberwolfach
