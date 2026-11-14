module

public import Oberwolfach.LongSelectedClassDynamicSameBalancedImageLoad
public import Oberwolfach.LongSelectedClassDynamicHostSameEmbeddingImageLoad
public import Oberwolfach.LongSelectedClassDynamicSourceHostSameEmbedding
public import Oberwolfach.LongSelectedClassDynamicSourceSameBalanced
public import Oberwolfach.LongSelectedClassDynamicSourceHostSpokes
public import Oberwolfach.LongSelectedClassDynamicSourceBalancedDegrees
public import Oberwolfach.LongSelectedClassOrientedSourceBalancedDegrees
public import Oberwolfach.LongSelectedOrientedSourceHostComplement
public import Oberwolfach.LongSelectedClassOrientedSourceHostSpokes
public import Oberwolfach.LongSelectedOrientedSourceSpokes
public import Oberwolfach.LongSelectedOrientedSourceComplement
public import Oberwolfach.LongSelectedProtectedSourceComplement
public import Oberwolfach.LongSelectedProtectedSourceSpokes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longClassDynamicSameBalancedImageLoadProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_class_dynamic_same_balanced_degrees_image_load
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Sclass:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hDhostM:∀x y,Dhost x y→Mhost x y=1)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,Mhost v w)=Fintype.card U ∧ (∑w,Mhost w v)=Fintype.card U):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedClassDynamicSourceHostSameEmbeddingImageLoad hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Dhost Extra ρ₀ θ δglobal M →
    LongSelectedClassDynamicSourceSameBalancedImageLoad hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedClassDynamicHostSameEmbeddingImageLoadFin n = longClassDynamicSameBalancedImageLoadProofFin n := Subsingleton.elim _ _
  have hdec0K : selectedClassDynamicHostSameEmbeddingImageLoadFin K = longClassDynamicSameBalancedImageLoadProofFin K := Subsingleton.elim _ _
  have hdec1 : selectedClassDynamicSameBalancedImageLoadFin n = longClassDynamicSameBalancedImageLoadProofFin n := Subsingleton.elim _ _
  have hdec1K : selectedClassDynamicSameBalancedImageLoadFin K = longClassDynamicSameBalancedImageLoadProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hsource
  try rw [hdec0K] at hsource
  try rw [hdec1]
  try rw [hdec1K]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,hDirected,hHost,hPacked,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
  have hEnds:∀w,
      (∀i (hp:inner w i 0∉Interiors w),fC w ⟨inner w i 0,hp⟩=i.val) ∧
      (∀i (hp:inner w i (Fin.last ((m+1)*d))∉Interiors w),fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val):=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    have he:=actual_sum_buffered_endpoint_agreement (hF w) (data w) (m+1) d hc hd' hs1 (ext w) (inner w) hsupp hinner hdis π Subtype.val (ψ w)
      (by intro a j hj;simpa only [retainedAndRawIntervalRoot] using hmarker (.inl a) j hj) (fC w) (hC w)
    constructor
    · intro i hp
      simpa only [bufferedInitialEndpointInComplement] using he.1 i
    · intro i hp
      simpa only [bufferedEndpointInComplement] using he.2 i
  have hSpokes:∀w,
      let B:=Finset.univ.image (fun i:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) i.val)
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪ B)
      Y w⊆R ∧ R.card=(m+1)*(Y w).card ∧ Disjoint (R\Y w) ((Y w).image π):=by
    intro w B R
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    let extA:=fun i=>ext w (.inl i)
    have hdisA:∀i j,i≠j→Disjoint (Finset.univ.image (extA i)) (Finset.univ.image (extA j)):=by
      intro i j hij
      exact hdis (.inl i) (.inl j) (by simpa using hij)
    have hfinish:∀i,fC w (bufferedEndpointInComplement (fun _=>(m+1)*d) extA (inner w) hinner hdisA i)=(π^d) i.val:=by
      intro i
      exact (hEnds w).2 i _
    exact retained_spoke_identities_from_complement π (m+1) d hd hnoshort (fun e=>raw (Sum.inr e)) false t Jret w
      extA (inner w) hinner hdisA (fC w) rfl hfinish (hYavoid w)
  have hsourceTail:∀w,((Finset.univ\bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))∪
      bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w)).image (factorCycleOrientation (F w) (E w)) =
      (Finset.univ\bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))∪Finset.univ.image (fun i=>inner w i 0):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,hinner,_,_,_,_,_,_,_,_,_,_,_,_,_,hdis,_,hDirection,_⟩
    exact actual_buffered_orientation_complement (F w) (E w) (m+1) d (by omega) (by omega) (ext w) (inner w) hinner hdis hDirection
  have hCover:=actual_inner_targets_covered_by_complement
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    F data Interiors ψ fC Φ (fun w=>(hprops w).2.2.2.2.2.2.2.2.1) hC hR H A
    (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber hZ
  let extA:=fun w i=>ext w (.inl i)
  have hinnerA:∀w i p,inner w i p=extA w i ⟨p.val+2,by omega⟩:=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,hh,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    exact hh
  have hdisA:∀w i j,i≠j→Disjoint (Finset.univ.image (extA w i)) (Finset.univ.image (extA w j)):=by
    intro w i j hij
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_,_,_⟩
    exact hh (.inl i) (.inl j) (by simpa using hij)
  have hσ:∀w,(complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
      (bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w))).image (factorCycleOrientation (F w) (E w))=
      complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
        (bufferedInitialEndpoints (fun _=>(m+1)*d) (inner w)):=by
    intro w
    simpa only [complementTailDomain,bufferedInitialEndpoints] using hsourceTail w
  have hbegin:∀w i,fC w (bufferedInitialEndpointInComplement (fun _=>(m+1)*d) (extA w) (inner w) (hinnerA w) (hdisA w) i)=i.val:=by
    intro w i
    exact (hEnds w).1 i _
  have hend:∀w i,fC w (bufferedEndpointInComplement (fun _=>(m+1)*d) (extA w) (inner w) (hinnerA w) (hdisA w) i)=(π^d) i.val:=by
    intro w i
    exact (hEnds w).2 i _
  have hDirected':∀w x y,(F w).Adj x.1 y.1→Dsrc w x.1 y.1→Mhost (fC w x) (fC w y)=1:=by
    intro w x y ha hd
    exact hDhostM _ _ (hDirected w x y ha hd)
  have hdegrees:=residual_degrees_from_retained_balanced_complement_explicit π (m+1) d (by omega) hnoshort
    (fun e=>raw (Sum.inr e)) false t Jret F hF E Dsrc hAlign extA inner hinnerA hdisA hσ fC hbegin hend
    Sclass Mhost hphysical hbalance hDirected' hPacked
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,fun w=>(hEnds w).1,fun w=>(hEnds w).2,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,⟨hinnerA,hdisA,hσ,hdegrees⟩,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
end Oberwolfach
