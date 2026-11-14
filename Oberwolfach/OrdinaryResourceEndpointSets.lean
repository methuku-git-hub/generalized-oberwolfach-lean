module

public import Oberwolfach.OrdinaryTransformerForbiddenEdges

@[expose] public section

/-! Endpoint sets of finite physical edge sets, retaining the distinct
row and hub types. These identities control the successive transformer budget. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinaryResourceRows_subset (K:Finset (Sym2 V⊕(V×U))) (N:Finset V)
    (hr:∀ v w,Sum.inl s(v,w)∈K→v∈N∧w∈N)
    (hs:∀ v u,Sum.inr (v,u)∈K→v∈N) : ordinaryResourceRows K⊆N := by
  intro v hv
  obtain ⟨e,he,hv⟩:=Finset.mem_biUnion.mp hv
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ a b=>
      have hv':v=a∨v=b:=by simpa using hv
      rcases hv' with h|h
      · rw [h];exact (hr a b he).1
      · rw [h];exact (hr a b he).2
  | inr p=>
    have hv':v=p.1:=by simpa using hv
    rw [hv'];exact hs p.1 p.2 he

theorem ordinaryResourceHubs_subset (K:Finset (Sym2 V⊕(V×U))) (B:Finset U)
    (h:∀ v u,Sum.inr (v,u)∈K→u∈B) : ordinaryResourceHubs K⊆B := by
  intro u hu
  obtain ⟨e,he,hu⟩:=Finset.mem_biUnion.mp hu
  cases e with
  | inl e=>simp at hu
  | inr p=>
    have hu':u=p.2:=by simpa using hu
    rw [hu'];exact h p.1 p.2 he

theorem ordinaryResourceRows_union (K L:Finset (Sym2 V⊕(V×U))) :
    ordinaryResourceRows (K∪L)=ordinaryResourceRows K∪ordinaryResourceRows L := by
  exact Finset.union_biUnion

theorem ordinaryResourceHubs_union (K L:Finset (Sym2 V⊕(V×U))) :
    ordinaryResourceHubs (K∪L)=ordinaryResourceHubs K∪ordinaryResourceHubs L := by
  exact Finset.union_biUnion

theorem ordinaryResourceRows_biUnion [DecidableEq I] (s:Finset I) (K:I→Finset (Sym2 V⊕(V×U))) :
    ordinaryResourceRows (s.biUnion K)=s.biUnion (fun i=>ordinaryResourceRows (K i)) := by
  exact Finset.biUnion_biUnion _ _ _

theorem ordinaryResourceHubs_biUnion [DecidableEq I] (s:Finset I) (K:I→Finset (Sym2 V⊕(V×U))) :
    ordinaryResourceHubs (s.biUnion K)=s.biUnion (fun i=>ordinaryResourceHubs (K i)) := by
  exact Finset.biUnion_biUnion _ _ _

theorem ordinaryResourceRows_mono {K L:Finset (Sym2 V⊕(V×U))} (h:K⊆L) :
    ordinaryResourceRows K⊆ordinaryResourceRows L := by
  intro x hx
  obtain ⟨e,he,hx⟩:=Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨e,h he,hx⟩

theorem ordinaryResourceHubs_mono {K L:Finset (Sym2 V⊕(V×U))} (h:K⊆L) :
    ordinaryResourceHubs K⊆ordinaryResourceHubs L := by
  intro x hx
  obtain ⟨e,he,hx⟩:=Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨e,h he,hx⟩

end Oberwolfach
