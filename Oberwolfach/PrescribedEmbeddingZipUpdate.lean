module

public import Oberwolfach.PrescribedEmbeddingBatchUpdate

@[expose] public section
/-! Apply a component's ordered target list to its ordered source list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_embedding_zip_update (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup)
    (A:Finset X) (f:X→V) (hinj:Set.InjOn f A)
    (hsource:∀ x∈as,x∉A) (htarget:∀ z∈bs,z∉A.image f):
    let g:=updatePairedImages f (as.zip bs);
    Set.InjOn g (↑(A∪as.toFinset):Set X) ∧
    (∀ a∈A,g a=f a) ∧ (∀ p∈as.zip bs,g p.1=p.2) := by
  let ps:=as.zip bs
  have hfst:ps.map Prod.fst=as:=List.map_fst_zip hlen.le
  have hsnd:ps.map Prod.snd=bs:=List.map_snd_zip hlen.ge
  have hsrc:(ps.map Prod.fst).Nodup:=by rw [hfst];exact ha
  have htgt:(ps.map Prod.snd).Nodup:=by rw [hsnd];exact hb
  have hdom:∀ p∈ps,p.1∉A:=by
    intro p hp
    exact hsource p.1 (List.of_mem_zip hp).1
  have himg:∀ p∈ps,p.2∉A.image f:=by
    intro p hp
    exact htarget p.2 (List.of_mem_zip hp).2
  have hh:=prescribed_embedding_batch_update ps A f hsrc htgt hdom himg hinj
  simpa only [hfst] using hh
end Oberwolfach
