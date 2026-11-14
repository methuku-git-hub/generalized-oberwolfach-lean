module

public import Oberwolfach.OrdinaryEmptyFinalResidualGlue

@[expose] public section
/-! Glue residual embeddings with extra prescribed targets and retain their
    coverage in the full unreserved factor embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem empty_final_dependent_residual_glue_with_forced_targets
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
    (g Φ:∀u,{x // x∈(data u).remaining}→V) (L Ends T:U→Finset V)
    (hA:∀u,residualSubtypeSet (data u).remaining (data u).prescribed⊆B u)
    (hΦ:∀u,Function.Injective (Φ u))
    (hg:∀u x,x∈residualSubtypeSet (data u).remaining (data u).prescribed → g u x=ψ u x.1)
    (hΦg:∀u x,x∈B u→Φ u x=g u x)
    (himage:∀u,(B u).image (g u)=
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪Ends u∪
        ((T u\(Old u).image (ψ u))\Ends u))
    (hOldEnds:∀u,Disjoint ((Old u).image (ψ u)) (Ends u))
    (hcover:∀u v,v∈T u→v∈(Old u).image (ψ u) ∨ ∃x,Φ u x=v)
    (hfree:∀u x,x∉B u→Φ u x∈L u)
    (hL:∀u,Disjoint (L u) ((Old u).image (ψ u))):
    ∃f:∀u,X u↪V,
      (∀u x,x∈(data u).oldDomain→f u x=ψ u x) ∧
      (∀u (x:{x // x∈(data u).remaining}),f u x.1=Φ u x) ∧
      (∀u v,v∈T u→∃x,f u x=v):=by
  let Z:=fun u=>(T u\(Old u).image (ψ u))\Ends u
  have hOldZ:∀u,Disjoint ((Old u).image (ψ u)) (Z u):=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv hz
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hv
  have hOldC:∀u,Disjoint ((Old u).image (ψ u)) (Ends u∪Z u):=by
    intro u
    exact Finset.disjoint_union_right.mpr ⟨hOldEnds u,hOldZ u⟩
  have hImage':∀u,(B u).image (g u)=
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪(Ends u∪Z u):=by
    intro u
    simpa only [Z,Finset.union_assoc] using himage u
  obtain ⟨f,hOld,hRem⟩:=empty_final_dependent_residual_glue hempty len inner F hF data hCycle Old hOldEq ψ hψ B g Φ L
    (fun u=>Ends u∪Z u) hA hΦ hg hΦg hImage' hOldC hfree hL
  refine ⟨f,hOld,hRem,?_⟩
  intro u v hv
  rcases hcover u v hv with hvOld|⟨x,hx⟩
  · obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hvOld
    have hxOld:x∈(data u).oldDomain:=by
      rw [hOldEq u] at hx
      exact (Finset.mem_sdiff.mp hx).1
    exact ⟨x,hOld u x hxOld⟩
  · exact ⟨x.1,(hRem u x).trans hx⟩
end Oberwolfach
