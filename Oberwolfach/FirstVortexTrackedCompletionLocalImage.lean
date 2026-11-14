module

public import Oberwolfach.FirstVortexResidualCompletionOrientedTracked
public import Oberwolfach.CompletionProtectedImageMatchingBound

@[expose] public section
/-! The actual completion maps inherit a local image estimate on a protected
set, with the same assigned-edge cap used when the maps were constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexTrackedCompletionLocalImageFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_tracked_completion_local_image
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Dsrc:U→Fin n→Fin n→Prop)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (Interiors:U→Finset (Fin n)) (ψ:U→Fin n→Fin n)
    (Kbad Jbad:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n))
    (Dfree Dstar:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
    (Lists:U→Finset (Fin n)) (FinalEdges:U→Finset (Sym2 (Fin n))) (δ α:ℝ)
    (I:Finset (Fin n)) (havoid:∀w,Disjoint (Lists w) I)
    (hcompletion:FirstVortexResidualCompletionOrientedTracked F Dsrc K J a Interiors ψ Kbad Jbad Lbad Bad Z
      Dfree Dstar Pack Lists FinalEdges δ α):
    ∃ (Φ:∀w,{x // x∈(a w).remaining}→Fin n) (fC:∀w,{x // x∉Interiors w}↪Fin n),
      (∀w (x:{x // x∉Interiors w}),x.val∈(a w).oldDomain→fC w x=ψ w x.val) ∧
      (∀w (x:{x // x∈(a w).remaining}) (hx:x.val∉Interiors w),fC w ⟨x.val,hx⟩=Φ w x) ∧
      (∀w,(((Finset.univ.image (Φ w))∩I).card)≤
        (residualSubtypeSet (a w).remaining (a w).prescribed).card+
          2*⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊+(Z w).card) :=by
  rcases hcompletion with ⟨pieces,hgraph,harcs,assign,orient,B,g,Φ,fC,hOrient,hMcap,hOld,hΦ,hB,hbad,hlist,hfixed,hZ,hfree,hD,hpair,hcover,hJ,hPack,hdis,hload,hunion,hdegree⟩
  refine ⟨Φ,fC,hOld,hΦ,?_⟩
  intro w
  have hh:=completion_protected_image_matching_bound I (B w) (Φ w) (g w) (Lists w)
    ((residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1))
    (Z w) (prescribedAssignedArcs Kbad assign orient w) (hfixed w) (hfree w) (havoid w) (hB w).2.2
  have hp:=Finset.card_image_le (s:=residualSubtypeSet (a w).remaining (a w).prescribed) (f:=fun x=>ψ w x.1)
  have hm:=hMcap w
  omega
end Oberwolfach
