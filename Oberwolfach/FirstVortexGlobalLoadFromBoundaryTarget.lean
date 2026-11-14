module

public import Oberwolfach.LongActualPrescribedMatchingLoad
public import Oberwolfach.PartitionMargins

@[expose] public section
/-! Global prescribed load from matching boundary starts and an already
established target-occurrence budget, with no cycle-length lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstGlobalBoundaryTargetFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_global_load_from_boundary_and_target_budget
    (δ θ:ℝ) (d:ℕ) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀(n K:ℕ),N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m c:ℕ) (hd:1≤d) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t),
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
    (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n))
    (hscale:max a γ*n≤(θ/4096)*n) (hbad:∀v,(Kbad.degree v:ℝ)≤δ*n/4)
    (hZ:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n/4),
    ∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n:=by
  obtain ⟨N,hN⟩:=eventually_sublinear_le_linear (p:=3/4) (ε:=δ/32) (by norm_num) (by positivity)
  refine ⟨max N 1,?_⟩
  intro n K hn U _ _ P π m c hd ℓ raw Del t Jret σ R T S hST q Q M F J _ data ext ψ hc hdd hs₂ hsupp hmarker hT a γ hγ hu hmatch hboundary Kbad Z hscale hbad hZ
  have hnN:N≤n:=(le_max_left _ _).trans hn
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hpow: (n:ℝ)^(3/4:ℝ)≤(δ/32)*n:=hN n hnN
  have hN':4*(n:ℝ)^(3/4:ℝ)≤δ*n/8:=by linarith
  have hD:4/(d:ℝ)≤δ/8:=by
    have hh:4/(d:ℝ)=4*(1/(d:ℝ)):=by ring
    rw [hh]
    nlinarith
  have hH:((Finset.univ:Finset U).card:ℝ)≤((Finset.univ:Finset (Fin n)).card:ℝ):=by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hu
  have hbnd:∀v∈(Finset.univ:Finset (Fin n)),
      ((rawIntervalBoundaryHubSet π d σ (Finset.univ:Finset U) v).card:ℝ)≤
        4*((Finset.univ:Finset U).card:ℝ)/d+4*((Finset.univ:Finset (Fin n)).card:ℝ)^(3/4:ℝ):=by
    simpa only [Finset.card_univ,Fintype.card_fin] using (fun v _=>hboundary v)
  have hb':∀v∈(Finset.univ:Finset (Fin n)),(Kbad.degree v:ℝ)≤δ*((Finset.univ:Finset (Fin n)).card:ℝ)/4:=by
    simpa only [Finset.card_univ,Fintype.card_fin] using (fun v _=>hbad v)
  have hz':∀v∈(Finset.univ:Finset (Fin n)),((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*((Finset.univ:Finset (Fin n)).card:ℝ)/4:=by
    simpa only [Finset.card_univ,Fintype.card_fin] using (fun v _=>hZ v)
  have hm':2*(max a γ*n)≤δ*((Finset.univ:Finset (Fin n)).card:ℝ)/4:=by
    simp only [Finset.card_univ,Fintype.card_fin]
    have hh:=mul_le_mul_of_nonneg_right hθδ hn0
    nlinarith
  have hn':4*((Finset.univ:Finset (Fin n)).card:ℝ)^(3/4:ℝ)≤δ*((Finset.univ:Finset (Fin n)).card:ℝ)/8:=by simpa using hN'
  have hout:=long_actual_prescribed_load_from_matching_and_boundary P π d m c hd ℓ raw Del t Jret M F data ext ψ hc hdd hs₂ hsupp hmarker hT
    (Finset.univ:Finset U) (Finset.univ:Finset (Fin n)) a γ hγ hu hmatch hbnd Kbad Z δ hH hD hn' hm' hb' hz'
  intro v
  simpa using hout v (Finset.mem_univ v)
end Oberwolfach
