module

public import Oberwolfach.PrescribedPositionSelectionNodup

@[expose] public section
/-! An oriented matching, listed in any order, has a vertex list with no
repetitions and whose set is its endpoint set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

def prescribedMatchingEndpoints (M:Finset (V×V)):Finset V:=
  M.biUnion (fun e=>{e.1,e.2})

def IsPrescribedOrientedMatching (M:Finset (V×V)):Prop:=
  (∀e∈M,e.1≠e.2) ∧
  (∀e∈M,∀f∈M,e≠f→Disjoint ({e.1,e.2}:Finset V) ({f.1,f.2}:Finset V))

theorem prescribed_target_matching_list_nodup (M:Finset (V×V)) (hM:IsPrescribedOrientedMatching M):
    (M.toList.flatMap prescribedPairVertices).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    have he':e∈M:=by simpa using he
    simp [prescribedPairVertices,hM.1 e he']
  · apply (Finset.nodup_toList M).pairwise_of_forall_ne
    intro e he f hf hne
    have he':e∈M:=by simpa using he
    have hf':f∈M:=by simpa using hf
    have hdis:=hM.2 e he' f hf' hne
    apply List.disjoint_left.mpr
    intro x hx hy
    apply (Finset.disjoint_left.mp hdis)
    · simpa [prescribedPairVertices] using hx
    · simpa [prescribedPairVertices] using hy

theorem prescribed_target_matching_list_endpoints (M:Finset (V×V)):
    (M.toList.flatMap prescribedPairVertices).toFinset=prescribedMatchingEndpoints M := by
  ext x
  simp only [prescribedMatchingEndpoints,List.mem_toFinset,List.mem_flatMap,Finset.mem_biUnion]
  constructor
  · rintro ⟨e,he,hx⟩
    refine ⟨e,by simpa using he,?_⟩
    simpa [prescribedPairVertices] using hx
  · rintro ⟨e,he,hx⟩
    refine ⟨e,by simpa using he,?_⟩
    simpa [prescribedPairVertices] using hx
end Oberwolfach
