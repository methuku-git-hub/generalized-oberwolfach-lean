module

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
local instance longProtectedSourceSpokesFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_protected_source_spokes
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedProtectedSourceWithComplement hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M →
    LongSelectedProtectedSourceWithSpokes hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedProtectedSourceComplementFin n = longProtectedSourceSpokesFin n := Subsingleton.elim _ _
  have hdec0K : selectedProtectedSourceComplementFin K = longProtectedSourceSpokesFin K := Subsingleton.elim _ _
  have hdec1 : selectedProtectedSourceSpokesFin n = longProtectedSourceSpokesFin n := Subsingleton.elim _ _
  have hdec1K : selectedProtectedSourceSpokesFin K = longProtectedSourceSpokesFin K := Subsingleton.elim _ _
  try rw [hdec0] at hsource
  try rw [hdec0K] at hsource
  try rw [hdec1]
  try rw [hdec1K]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,Φ,fC,hC,hR,hZ,hYavoid,hHost,hPacked⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
  have hEnds:∀w,
      (∀i (hp:inner w i 0∉Interiors w),fC w ⟨inner w i 0,hp⟩=i.val) ∧
      (∀i (hp:inner w i (Fin.last ((m+1)*d))∉Interiors w),fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val):=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid⟩
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
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid⟩
    let extA:=fun i=>ext w (.inl i)
    have hdisA:∀i j,i≠j→Disjoint (Finset.univ.image (extA i)) (Finset.univ.image (extA j)):=by
      intro i j hij
      exact hdis (.inl i) (.inl j) (by simpa using hij)
    have hfinish:∀i,fC w (bufferedEndpointInComplement (fun _=>(m+1)*d) extA (inner w) hinner hdisA i)=(π^d) i.val:=by
      intro i
      exact (hEnds w).2 i _
    exact retained_spoke_identities_from_complement π (m+1) d hd hnoshort (fun e=>raw (Sum.inr e)) false t Jret w
      extA (inner w) hinner hdisA (fC w) rfl hfinish (hYavoid w)
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,Φ,fC,hC,hR,hZ,hYavoid,fun w=>(hEnds w).1,fun w=>(hEnds w).2,hSpokes,hHost,hPacked⟩
end Oberwolfach
