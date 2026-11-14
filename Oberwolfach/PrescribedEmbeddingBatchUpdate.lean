module

public import Oberwolfach.PrescribedEmbeddingInjectiveUpdate
public import Oberwolfach.PrescribedEmbeddingUpdatePreserves

@[expose] public section
/-! Extend a partial injection by a finite list of distinct source-target
pairs while keeping every earlier image fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

def updatePairedImages (f:X→V):List (X×V)→(X→V)
  | []=>f
  | (x,z)::ps=>updatePairedImages (Function.update f x z) ps

theorem prescribed_embedding_batch_update (ps:List (X×V)):
    ∀ (A:Finset X) (f:X→V),
    (ps.map Prod.fst).Nodup→(ps.map Prod.snd).Nodup→
    (∀ p∈ps,p.1∉A)→(∀ p∈ps,p.2∉A.image f)→Set.InjOn f A→
    Set.InjOn (updatePairedImages f ps) (↑(A∪(ps.map Prod.fst).toFinset):Set X) ∧
    (∀ a∈A,updatePairedImages f ps a=f a) ∧
    (∀ p∈ps,updatePairedImages f ps p.1=p.2) := by
  induction ps with
  | nil =>
    intro A f ha hb hdom himg hinj
    refine ⟨?_,?_,?_⟩
    · simpa [updatePairedImages] using hinj
    · intro a ha; rfl
    · simp
  | cons p ps ih =>
    rcases p with ⟨x,z⟩
    intro A f hsrc htgt hdom himg hinj
    have hsrc':(ps.map Prod.fst).Nodup:=by simpa using (List.nodup_cons.mp (by simpa using hsrc)).2
    have htgt':(ps.map Prod.snd).Nodup:=by simpa using (List.nodup_cons.mp (by simpa using htgt)).2
    have hxnot:x∉ps.map Prod.fst:=(List.nodup_cons.mp (by simpa using hsrc)).1
    have hznot:z∉ps.map Prod.snd:=(List.nodup_cons.mp (by simpa using htgt)).1
    have hxA:x∉A:=hdom (x,z) (by simp)
    have hzA:z∉A.image f:=himg (x,z) (by simp)
    let f':=Function.update f x z
    let A':=insert x A
    have hinj':Set.InjOn f' A':=prescribed_embedding_injective_update A f x z hinj hzA
    have hp:=prescribed_embedding_update_preserves A f x z hxA
    have hdom':∀ q∈ps,q.1∉A':=by
      intro q hq
      have hqA:=hdom q (by simp [hq])
      have hqx:q.1≠x:=by
        intro he
        apply hxnot
        exact List.mem_map.mpr ⟨q,hq,he⟩
      simpa [A',hqA,hqx] 
    have himg':∀ q∈ps,q.2∉A'.image f':=by
      intro q hq
      have hqA:=himg q (by simp [hq])
      have hqz:q.2≠z:=by
        intro he
        apply hznot
        exact List.mem_map.mpr ⟨q,hq,he⟩
      rw [show A'.image f'=insert z (A.image f) from hp.2]
      simp [hqA,hqz]
    obtain ⟨hinj'',hold,hnew⟩:=ih A' f' hsrc' htgt' hdom' himg' hinj'
    have hsets:A'∪(ps.map Prod.fst).toFinset=A∪(((x,z)::ps).map Prod.fst).toFinset:=by
      ext a
      simp [A',or_assoc,or_left_comm,or_comm]
    constructor
    · change Set.InjOn (updatePairedImages f' ps) (↑(A∪(((x,z)::ps).map Prod.fst).toFinset):Set X)
      rw [←hsets]
      exact hinj''
    constructor
    · intro a ha
      change updatePairedImages f' ps a=f a
      have ha':a∈A':=by simp [A',ha]
      rw [hold a ha']
      exact hp.1 a ha
    · intro q hq
      change updatePairedImages f' ps q.1=q.2
      simp only [List.mem_cons] at hq
      rcases hq with rfl|hq
      · have hx':x∈A':=by simp [A']
        rw [hold x hx']
        simp [f']
      · exact hnew q hq
end Oberwolfach
