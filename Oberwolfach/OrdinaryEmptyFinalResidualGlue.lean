module

public import Oberwolfach.ResidualActualEmbeddingGlue
public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! When the actual final index is empty, a compatible simultaneous residual
placement glues directly to an embedding of every whole unreserved source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem empty_final_dependent_residual_glue
    {U V:Type} [DecidableEq V] [Nonempty V]
    {X A K J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    (hempty:∀u,IsEmpty (A u)) (len:∀u,A u→ℕ)
    (inner:∀u (i:A u),Fin (len u i+1)↪X u)
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (Old:∀u,Finset (X u))
    (hOldEq:∀u,Old u=(data u).oldDomain\bufferedPathStrictInterior (len u) (inner u))
    (ψ:∀u,X u→V) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (B:∀u,Finset {x // x∈(data u).remaining})
    (g Φ:∀u,{x // x∈(data u).remaining}→V) (L C:U→Finset V)
    (hA:∀u,residualSubtypeSet (data u).remaining (data u).prescribed⊆B u)
    (hΦ:∀u,Function.Injective (Φ u))
    (hg:∀u x,x∈residualSubtypeSet (data u).remaining (data u).prescribed→ g u x=ψ u x.1)
    (hΦg:∀u x,x∈B u→Φ u x=g u x)
    (himage:∀u,(B u).image (g u)=
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪C u)
    (hOldC:∀u,Disjoint ((Old u).image (ψ u)) (C u))
    (hfree:∀u x,x∉B u→Φ u x∈L u)
    (hL:∀u,Disjoint (L u) ((Old u).image (ψ u))):
    ∃f:∀u,X u↪V,
      (∀u x,x∈(data u).oldDomain→f u x=ψ u x) ∧
      (∀u (x:{x // x∈(data u).remaining}),f u x.1=Φ u x):=by
  have hInt:∀u,bufferedPathStrictInterior (len u) (inner u)=∅:=by
    intro u
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact (hempty u).false i
  have hOld:∀u,Old u=(data u).oldDomain:=by
    intro u
    rw [hOldEq u,hInt u]
    simp
  have hex:∀u,∃f:X u→V,Function.Injective f ∧
      (∀x,x∈(data u).oldDomain→f x=ψ u x) ∧
      (∀x:{x // x∈(data u).remaining},f x.1=Φ u x):=by
    intro u
    apply actual_residual_embedding_glues_to_factor (data u) (hF u) (hCycle u) (ψ u)
      (by simpa only [hOld u] using hψ u) (B u) (g u) (Φ u) (L u) (C u) ∅
      (hA u) (hΦ u) (hg u) (hΦg u)
      (by simpa only [Finset.union_empty] using himage u)
      (by simpa only [hOld u] using hOldC u) (by simp) (hfree u)
      (by simpa only [hOld u] using hL u)
  let f:∀u,X u↪V:=fun u=>⟨Classical.choose (hex u),(Classical.choose_spec (hex u)).1⟩
  refine ⟨f,?_,?_⟩
  · intro u x hx
    exact (Classical.choose_spec (hex u)).2.1 x hx
  · intro u x
    exact (Classical.choose_spec (hex u)).2.2 x
end Oberwolfach
