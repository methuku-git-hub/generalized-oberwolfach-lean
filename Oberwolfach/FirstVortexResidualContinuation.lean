module

public import Oberwolfach.LongSelectedAlignedSourceResidualCompletion
public import Oberwolfach.FirstVortexPrescribedAssignmentOutcome

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexResidualContinuationFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_residual_continuation
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P DelG:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (F:U→SimpleGraph (Fin n)) (H:Finset U) (A:Finset (Fin n))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δlocal ρ₀ θ ε lam α b βfinal δglobal:ℝ)
    (hρ₀:0<ρ₀) (hb:0≤b) (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hθδ:10*θ≤δglobal) (hεδ:ε≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hU:0<Fintype.card U):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:=Function.Embedding.subtype (·∈T)
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬DelG.Adj x y
    let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
      (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
    (∀w,IsExtendingList Dfree (Lists w) βfinal)→
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedAlignedSourceWithGlobalLoadCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δlocal
      (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P DelG Used Kbad A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M →
    LongSelectedAlignedSourceWithResidualCompletion hU F P π d m ℓ raw t Jret σE H A Kbad Used DelG absorber δlocal
      (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P DelG Used Kbad A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M :=by
  intro raw T e Dfree Lists hext M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let occupied:=fun w=>((data w).oldDomain\Interiors w).image (ψ w)
  let Z:=innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
  let Jbad:=spanningRestriction (P\Used) A\Kbad
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
  let FinalEdges:=fun w=>Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset)
  have hOutcome:=hExtra.1
  obtain ⟨hKdeg,hKcard,hKPack,hJdeg,hKJ,hUsedJ,hOutside,hShield,hLbad,hBad,hAssignment⟩:=hOutcome
  have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
    intro w
    rw [(hprops w).2.2.2.1]
  have hDR:∀w,Disjoint (Interiors w) (data w).remaining:=by
    intro w
    exact (hprops w).2.2.2.2.2.2.2.2.1
  have hInj:∀w,Set.InjOn (ψ w) (↑((data w).oldDomain\Interiors w):Set (Fin n)):=by
    intro w
    exact (hprops w).2.2.2.2.2.2.2.2.2.1
  have hOldReserved:∀w,Disjoint (Lists w) (occupied w):=by
    intro w
    have hh:=((hprops w).2.2.2.2.2.2.2.2.2.2.2.1).symm
    exact (Finset.disjoint_left.mpr (by
      intro x hx hy
      exact (Finset.disjoint_left.mp hh) (Finset.mem_sdiff.mp hx).1 hy))
  have hZprops:=inner_required_targets_properties H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
  have hSize:∀w,(Fintype.card {x // x∈(data w).remaining}:ℝ)≤δglobal*Fintype.card (Fin n):=by
    intro w
    simp only [Fintype.card_coe,Fintype.card_fin]
    have hn0:(0:ℝ)≤n:=by positivity
    have hh:=mul_le_mul_of_nonneg_right hθδ hn0
    nlinarith [hupper w]
  have hDegree:∀v,(Kbad.degree v:ℝ)≤b*Fintype.card (Fin n):=by
    intro v
    simp only [Fintype.card_fin]
    have hh:=mul_le_mul_of_nonneg_right hαb (Nat.cast_nonneg n)
    exact (hKdeg v).trans hh
  letI : DecidableRel Jbad.Adj := fun x y=>Classical.propDecidable _
  have hJ:∀v,(Jbad.degree v:ℝ)≤δglobal*Fintype.card (Fin n):=by
    intro v
    simp only [Fintype.card_fin]
    have hh:=mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg n)
    have hJdeg':(Jbad.degree v:ℝ)≤ε*n:=by
      convert hJdeg v using 1 <;> congr 2 <;> exact Subsingleton.elim _ _
    exact hJdeg'.trans hh
  letI : Fintype Jbad.edgeSet := Jbad.fintypeEdgeSet
  have hKJ':Disjoint Kbad.edgeFinset Jbad.edgeFinset:=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    apply Finset.disjoint_left.mp hKJ hx
    simpa only [SimpleGraph.mem_edgeFinset] using hy
  have hαCap:0<((ρ₀/4)/40000):=by positivity
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  have hI:(Fintype.card U:ℝ)≤Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using (show (Fintype.card U:ℝ)≤n by exact_mod_cast hu)
  obtain ⟨pieces',hgraph',harcs',hcont⟩:=hLate _ _ data
  have hcompletion:FirstVortexResidualCompletion F Dsrc _ _ data Interiors ψ Kbad Jbad Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δglobal:=by
    refine ⟨pieces',hgraph',harcs',?_⟩
    apply hcont hCycle Interiors hDR ψ hInj Kbad Jbad Lbad Bad H Z
      (fun e _=>hOutside e) hZprops.2.2.1 hZprops.1 hShield ((ρ₀/4)/40000) b hαCap hb hbsmall hnV
      (by simpa only [Fintype.card_fin] using hLbad) (by simpa only [Fintype.card_fin] using hBad) hDegree
      (by simpa only [Fintype.card_fin] using hcapacity) βfinal δglobal hβ hβ1 hδ hδbound
      (by simpa only [Fintype.card_fin] using hnβ) (by simpa only [Fintype.card_fin] using hnδ) hI hSize
      (by simpa only [Fintype.card_fin] using hglobal) hJ hKJ' Dfree Dstar (fun x y h=>Or.inl h)
      (fun x y h=>Or.inl (Or.inr h)) Pack hKPack (fun x y h=>hSelected x y h.1) Lists hext hOldReserved FinalEdges hOldDisj hOldPack
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion⟩
end Oberwolfach
