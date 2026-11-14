module

public import Oberwolfach.LongEncodedResidualReferenceChangeOnRoots
public import Oberwolfach.LongEncodedResidualSpokeOutsideControl
public import Oberwolfach.LongPartitionedResidualDivisible
public import Oberwolfach.MarkedFullBalanceFromReferenceTests
public import Oberwolfach.LongEncodedResidualReferenceChange
public import Oberwolfach.LongEncodedResidualSpokeGraphByAgreement
public import Oberwolfach.LongResidualArcPairInjective
public import Oberwolfach.LongFactorResidualSpokePartition

@[expose] public section
/-! Form the directed rim and spoke change graphs for the same corrected
factor-complement witness and the same retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sameSampleBalancedExactChangeGraphsLocalFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance sameSampleBalancedExactChangeGraphsLocalArc {n:ℕ} (P:Fin n×Fin n→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_same_sample_balanced_exact_change_graphs_with_local_control
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (F:U→SimpleGraph (Fin n)) (G S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (M:Fin n→Fin n→ℕ) (I:Finset (Fin n)) (t:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n))
    (R:U→Finset (Fin n)) (θ δ ηphys ηdel ηtype lossRow lossCol ε ζ:ℝ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,M x y=1→G.Adj x y)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hI:∀v,π v∈I↔v∈I)
    (hprov:LongFactorComplementProvenance F S G π d m raw t J Pack Enew A R)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    (C:U→Finset (Fin n)) (ζret load ηLocal δLocal χLocal:ℝ) (hζret:0≤ζret) (hU:Fintype.card U≤n)
    :
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let ρ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d ρ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d ρ false t J false true true
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    ∀T:Finset {e:Fin n×Fin n // P e},
    ∀τtarget:RawMarkedOutcome (Fin n) U Bool Bool,
    (∀e,τtarget (Sum.inr e)=σ (Sum.inr e))→
    (∀e:Sym2 (Fin n),e.toFinset⊆I→τtarget (Sum.inl e)=σ (Sum.inl e))→
    (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τtarget (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y)→
    (∀e∈T,longMarkedArcEligible π d e.val)→(∀e,e∉T→longOrdinaryArcEligible π d e.val)→
    (∀mark x y,x∈I→y∈I→
      (markedPhysicalRim G π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y))→
    MarkedRemainderDivisible (fun e:residualOrdinaryArc P T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P T=>e.val.val.1) (fun e=>π.symm e.val.val.2) HK Finset.univ
      (Finset.univ.filter (fun z:Fin n×U=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    MarkedRestrictedBalanceWithSpokes G π d m Finset.univ Finset.univ ε σ H→
    (∀v,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤ηphys)→
    (∀v,(Del.degree v:ℝ)≤ηdel)→
    (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤ηtype)→
    (∀v,v∉I→((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤ηLocal)→
    (∀v,v∉I→(Del.degree v:ℝ)≤δLocal)→
    (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤χLocal)→
    RetainedRestrictionGood π d ρ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret J→
    (∀w v,v∈rawReservedSpokeList π d ρ w→v∉C w→v∈R w\Y w)→
    (∀v,v∉I→((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤ζ*n→
    2*(lossCol+10*θ*n)+ε≤ζ*n→
    ∃(FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)),
      (∀e,τtarget (Sum.inr e)=σ (Sum.inr e)) ∧
      (∀e:Sym2 (Fin n),e.toFinset⊆I→τtarget (Sum.inl e)=σ (Sum.inl e)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τtarget (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
      (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τtarget a)→markedPairPhysical π a∈FR.edgeFinset) ∧
      (∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype) ∧
      (∀v,v∉I→(FR.degree v:ℝ)≤ηLocal+δLocal+χLocal) ∧
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      (∀z,(FS.degree z:ℝ)≤ζ*n) ∧
      ∀B:Finset U,∀v,v∉I→(∑w∈B,if ¬(H false v w↔H' false v w) then (1:ℝ) else 0)≤
        2*(ζret*n+load)+(ε+2*(ηLocal+δLocal+χLocal)):=by
  intro Small P T₁ σ ρ Y H H₀ HK H' T τtarget hTargetInterval hTargetInner hTargetCode hMarked hOrd hInner hdiv hbal hChange hDel hType hChangeLocal hDelLocal hTypeLocal hgood hprotect hload hRetRow hRetCol hBudgetRow hBudgetCol
  have hstd6 : sameSampleBalancedExactChangeGraphsLocalFin 6 = instDecidableEqFin 6 := Subsingleton.elim _ _
  rw [hstd6] at hcorrect
  let Roots:Finset (Fin n):=Finset.univ\I
  obtain ⟨τ,FR,hinterval,hinner,hRims,hRimChange,hFR,hFRlocal⟩:=long_encoded_residual_reference_change_on_roots G S Del Small π d ω M I ηphys ηdel ηtype
    hphysical hhost hcorrect hI Roots ηLocal δLocal χLocal T hMarked hOrd hInner
    (by intro v; convert hChange v using 1 <;> congr!) hDel
    (by intro v; convert hType v using 1 <;> congr!)
    (by intro v hv; convert hChangeLocal v (Finset.mem_sdiff.mp hv).2 using 1 <;> congr!)
    (by intro v hv; exact hDelLocal v (Finset.mem_sdiff.mp hv).2)
    (by intro v hv; convert hTypeLocal v (Finset.mem_sdiff.mp hv).2 using 1 <;> congr!)
  have hdis:=long_factor_residual_spoke_partition F S G π d m hd hnoshort raw t J Pack Enew A R hprov
  have hinj:=long_residual_arc_pair_injective S Small M π T
  obtain ⟨FS,hSpokeChange,hFS,hSpokeLocal⟩:=long_encoded_residual_spoke_change_graph_with_outside_control G π d m raw σ τ t J R θ δ lossRow lossCol ε
    (ηphys+ηdel+ηtype) ζ (fun e:residualOrdinaryArc P T=>e.val.val.1) (fun e=>e.val.val.2)
    (fun e:residualMarkedArc P T=>e.val.val.1) (fun e=>π.symm e.val.val.2) hinj.1 hinj.2 hcontrol I C ζret load (ηLocal+δLocal+χLocal) hζret hU
    (by intro v w hh;exact (hdis.2.2 w v hh.2) hh.1) hdiv hbal hRims FR hRimChange hFR hI hgood hprotect hload
    (by intro v hv;exact hFRlocal v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩))
    hRetRow hRetCol hBudgetRow hBudgetCol
  have hTargetRim:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τtarget a)→markedPairPhysical π a∈FR.edgeFinset:=by
    intro a ha
    apply hRimChange a
    intro h
    apply ha
    apply h.trans
    cases a with
    | inl xy => exact (hRims false xy.1 xy.2).trans (hTargetCode false xy.1 xy.2).symm
    | inr xy => exact (hRims true xy.1 xy.2).trans (hTargetCode true xy.1 xy.2).symm
  refine ⟨FR,FS,hTargetInterval,hTargetInner,hTargetCode,hTargetRim,hFR,?_,hSpokeChange,hFS,hSpokeLocal⟩
  intro v hv
  exact hFRlocal v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩)
end Oberwolfach
