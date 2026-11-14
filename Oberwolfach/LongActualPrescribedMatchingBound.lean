module

public import Oberwolfach.LongActualMissingSpokeDefect
public import Oberwolfach.LongTrueSpokeDefectFromMatching
public import Oberwolfach.ActualPrescribedFromBoundarySpokeDefects
public import Oberwolfach.ActualPrescribedMarkerImageGeometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longActualPrescribedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_prescribed_from_matching_and_boundary
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m c:ℕ) (hd:1≤d) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) {J:U→Type} [∀w,DecidableEq (J w)]
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})
      (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
    (hc:∀w,(data w).c=c) (hdd:∀w,(data w).d=d)
    (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (hT:∀w i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
      (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w
      (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (H:Finset U) (A:Finset (Fin n)) (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v∈A,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ)),
    ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)≤
      4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ)+2*(max a γ*n):=by
  intro σ R T S hST q Q M F J _ data ext ψ hc hdd hs₂ hsupp hmarker hT H A a γ hγ hu hmatch hboundary v hv
  let root:=fun w i=>retainedAndRawIntervalRoot π d σ false true t Jret w i
  let colour:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Bool :=
    fun w i=>match i with | Sum.inl _=>false | Sum.inr _=>true
  let Defect:=fun x w=>∃z∈longRawIncidenceSet S (.inr (true,.inl x))\M.biUnion Q,z.1=Sum.inr (true,x,w)
  have hroot:∀w i,i∈(data w).s₁∪(data w).s₂→ rawIntervalColouredStart π d (fun e=>σ (w,e)) (root w i) (colour w i):=by
    intro w i hi
    cases i with
    | inl b => exact b.property.1
    | inr b => exact b.property
  have hgeom:∀w i,i∈(data w).s₁∪(data w).s₂→∀j≤d,
      ((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed→
      ψ w ((data w).P i |>.getVert (2+(data w).c*j))=(π^j) (root w i):=by
    intro w
    exact actual_prescribed_marker_image_geometry (data w) c d (hc w) (hdd w) (ext w) (ψ w) π (root w) (hsupp w) (hmarker w)
  have hfirst:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert 2)∈(data w).prescribed→
      ψ w ((data w).P i |>.getVert 2)=root w i:=by
    intro w i hi hp
    simpa only [Nat.mul_zero,Nat.add_zero,pow_zero,Equiv.Perm.one_apply] using hgeom w i hi 0 (by omega) (by simpa using hp)
  have hlast:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed→
      ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))=(π^d) (root w i):=by
    intro w i hi hp
    simpa only [hdd w] using hgeom w i hi d (le_refl d) (by simpa only [hdd w] using hp)
  have hmiss:∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→Defect ((π^j) (root w i)) w:=by
    exact long_actual_missing_positions_are_spoke_defects P π d m hd ℓ raw Del t Jret M F data hs₂ hT
  have hdef:=long_true_spoke_defect_count_from_matching S (M.biUnion Q) H a γ hγ hu hmatch
  have hdef₀:((H.filter (fun w=>Defect v w)).card:ℝ)≤max a γ*n:=by
    simpa only [Defect] using hdef v
  have hdef₁:((H.filter (fun w=>Defect (π.symm v) w)).card:ℝ)≤max a γ*n:=by
    simpa only [Defect] using hdef (π.symm v)
  have h:=actual_prescribed_multiplicity_from_boundary_spoke_defects π d σ F data ψ root colour H hroot hfirst hlast Defect hdd
    (by intro w i hi;exact hgeom w i (Finset.mem_union_right _ hi)) hmiss v
    (4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ)) (max a γ*n) (max a γ*n) (hboundary v hv)
      (by
        apply le_trans ?_ hdef₀
        exact_mod_cast (Finset.card_le_card (by intro w hw; simpa only [Finset.mem_filter] using hw)))
      (by
        apply le_trans ?_ hdef₁
        exact_mod_cast (Finset.card_le_card (by intro w hw; simpa only [Finset.mem_filter] using hw)))
  linarith only [h]
end Oberwolfach
