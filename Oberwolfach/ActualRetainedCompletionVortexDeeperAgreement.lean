module

public import Oberwolfach.ActualRetainedCompletionInnerAgreement
public import Oberwolfach.MarkedVortexActualResidualDeeperEquality

@[expose] public section
/-! The actual completion and encoded rim correction agree with the same
retained sample on all deeper vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

theorem actual_retained_completion_vortex_deeper_agreement
    (π:Equiv.Perm V) (d c:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (F:U→SimpleGraph V) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K L:U→Type) [∀u,DecidableEq (K u)] [∀u,DecidableEq (L u)]
    (data:∀u,ActualResidualData (K:=K u) (J:=L u) (F u))
    (inner:∀u,retainedMarkedIndex π d σ false t Jret u→Fin (c*d+1)↪V)
    (ψ:U→V→V) (I:Finset V) (J:Finset U) (absorber:U→Finset V)
    (Kbad:SimpleGraph V) (assign:Sym2 V→U) (orient:Sym2 V→V×V)
    (BB:∀u,Finset {x // x∈(data u).remaining}) (g Φ:∀u,{x // x∈(data u).remaining}→V)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}↪V)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (hDR:∀u,Disjoint (bufferedPathStrictInterior (fun _=>c*d) (inner u)) (data u).remaining)
    (hC:∀u (x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}),x.val∈(data u).oldDomain→fC u x=ψ u x.val)
    (hR:∀u (x:{x // x∈(data u).remaining}) (hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨x.val,hx⟩=Φ u x)
    (hStart:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩=i.val)
    (hEnd:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩=(π^d) i.val)
    (hOld:∀u,Disjoint (((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u))
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u)))
    (hAbs:∀u∈J,Disjoint (absorber u) I)
    (hBB:∀u,(BB u).image (g u)=
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1) ∪
      prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient u) ∪
      innerRequiredTargets J I (fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u))
        (retainedFinalMarkedAt π d σ t Jret) absorber (fun u=>((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u)) u)
    (hEndList:∀u v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient u)→
      ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ u∈protectedPairEdgeHubs (rawReservedSpokeList π d σ) J e)
    (hag:∀u x,x∈BB u→Φ u x=g u x)
    (hfree:∀u x,x∉BB u→Φ u x∈rawReservedSpokeList π d σ u\(I∪retainedFinalMarkedAt π d σ t Jret u))
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (hI:I=Q.extendedVertices 1) (hJ:J=Q.extendedIndices 1)
    (σglobal τglobal:RawMarkedOutcome V U Bool Bool)
    (hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→σglobal (Sum.inl e)=τglobal (Sum.inl e))
    (hinterval:∀e,σglobal (Sum.inr e)=τglobal (Sum.inr e)):
    let R:=fun u=>Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪
      Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val))
    let H:=retainedRawMarkedSpokes π d σ false t Jret false false
    let H':Bool→V→U→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d σ false t Jret false false true v u
      else v∈R u\markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val;
    ∀ (i:ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τglobal ∧
      (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)):=by
  intro R H H'
  have hfirst:=actual_retained_completion_inner_agreement π d c hd σ t Jret F hF K L data inner ψ I J absorber Kbad assign orient BB g Φ fC
    hCycle hDR hC hR hStart hEnd hOld hAbs hBB hEndList hag hfree
  subst I
  subst J
  exact marked_vortex_actual_residual_deeper_equality Q π d σ t Jret σglobal τglobal R hrim hinterval hfirst
end Oberwolfach
