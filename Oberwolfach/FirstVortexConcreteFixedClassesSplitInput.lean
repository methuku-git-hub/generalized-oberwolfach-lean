module

public import Oberwolfach.FirstVortexConcreteProtectedSplitInput
public import Oberwolfach.FirstVortexConcreteProtectedFixedClasses

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexConcreteFixedSplitInputFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_concrete_fixed_classes_split_input
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hδ1:δold≤1) (hθ:0<θ) (hepsPos:0<eps)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀hi:ρ₀≤1) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hprecise:ε≤((ρ₀/4)/40000)/8192)
    (ξCap:ℝ) (hξPartCap:ξPart≤ξCap)
    (hCap:∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ))
    (hlamθ:lam≤θ) (hdlarge:(r+4)+2≤d)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hεα:ε≤α/1000) (hlamhi:lam≤α/128)
    (a γ ρ Δ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξ) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr)
,
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner →
    ∀(γLoss σLoss:ℝ) (size a₀ b₀ e₀ f₀ L Bpart:ℕ) (εAbs ζCorr ξCorr:ℝ),
    (hsize:2*mm≤size)→(hL:L+1=Vort.length)→
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i)→
    0≤ξCorr→6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (γLoss*n) (σLoss*n)→
    ε≤εAbs→e₀≤Bpart→
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξPart z
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w→
    (let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
     let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
     MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
        (Vort.extendedVertices 1) (Vort.extendedIndices 1))→
    ∀(αAssign ρreserve:ℝ), αAssign/2=α → (e₀:ℝ)≤ρreserve*n →
    ∃D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)),
    ∃CReserve:Finset (Finset (Fin n)⊕(Fin n×U)),
    (D₀.Valid (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false)
      (r+4) (Vort.extendedVertices 1) (Vort.extendedIndices 1) (γLoss*n) (σLoss*n) ∧
    CReserve.card≤e₀ ∧ Disjoint D₀.removed CReserve ∧
    MarkedFixedTerminalAbsorber P π d (r+4) (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false)
      CReserve (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1))) ∧
    markedResourceRimGraph CReserve≤longSelectedPhysicalGraph P π d z.1 ∧
    (CReserve.card:ℝ)≤ρreserve*n ∧
    ∀Sclass:SimpleGraph (Fin n),Sclass≤P → Sclass.IsRegularOfDegree (2*Fintype.card U) →
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξPart*n) →
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,Sclass.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) →
      markedResourceRimGraph CReserve≤Sclass →
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→Sclass.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ CReserve Sclass M Del ∧
        FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) bmatch ρ₀ ξ Δ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 :=by
  obtain ⟨N,hN⟩:=first_vortex_protected_fixed_classes_from_concrete_boundary_event α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r
    hα hlam hε hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
    hρ₀hi hδglobal hθglobal hprecise ξCap hξPartCap hCap hlamθ hdlarge Nret hNret
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
  intro γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected αAssign ρreserve hαAssign hReserveScale
  have hp:=hN n hn
  have hdec:firstVortexProtectedFixedClassesFin n=firstVortexConcreteFixedSplitInputFin n:=Subsingleton.elim _ _
  have hdecK:firstVortexProtectedFixedClassesFin K=firstVortexConcreteFixedSplitInputFin K:=Subsingleton.elim _ _
  try rw [hdec] at hp
  try rw [hdecK] at hp
  obtain ⟨D₀,C,hValid,hCard,hDisjoint,hAbs,hReserve,hSelected⟩:=hp U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected
  have hCardReal:(C.card:ℝ)≤ρreserve*n:=
    (show (C.card:ℝ)≤e₀ by exact_mod_cast hCard).trans hReserveScale
  refine ⟨D₀,C,⟨hValid,hCard,hDisjoint,hAbs⟩,hReserve,hCardReal,?_⟩
  simpa only [hαAssign] using hSelected
end Oberwolfach
