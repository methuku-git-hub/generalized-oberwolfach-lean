module

public import Oberwolfach.LongClassProtectedCorrectionUniformSpacing
public import Oberwolfach.SuppliedVortexRegularClassBalancedDegreesForEveryProtection
public import Oberwolfach.SuppliedVortexClassBalancedProtectedCorrection
public import Oberwolfach.SuppliedVortexRegularClassBalancedDegreesForEveryProtection
public import Oberwolfach.SuppliedVortexClassBalancedProtectedCorrection
public import Oberwolfach.LongClassProtectedCorrectionAndDeletion
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedComplement
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedResidual
public import Oberwolfach.FirstVortexPreparedProtectedComplementProof
public import Oberwolfach.SuppliedVortexOutcomePreparedFirstComplement
public import Oberwolfach.FirstVortexPreparedComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedClassFullyUniformCorrectionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_prepare_class_balanced_correction_fully_uniform
    (αRef ρ₀ δcorr:ℝ) (hαRef:0<αRef) (hρ₀:0<ρ₀) (hδcorr:0<δcorr):
    ∃c:ℝ,0<c ∧ ∀(ξPart:ℝ),0≤ξPart→
    ξPart≤min (min (c/4) (δcorr/16)) (αRef*(ρ₀/200)^2/4)→
    ∀d:ℕ, ∃N:ℕ,1≤N ∧
    ∀(r k₀ K:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d)
    (sstar γRich tstar kstar θ ρ D eps lam ζret alpha γ:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ ξ Δ τ:ℝ) (fprot:ℝ) (hfprot:0≤fprot)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (n:ℕ),N≤n→∀(hn:1≤n)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsize:ρ*D=2*Fintype.card U) (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (π:Equiv.Perm (Fin n))
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (δlocal δglobal αMatch bmatch lamAssign:ℝ)
    (hmpart:mpart 0=Fintype.card U)
    (hfbound:fprot≤(αRef*(ρ₀/200)^2/16)*n)
    (hdegree:∀v,(P.degree v:ℝ)=D)
    (hmin:∀v,(1/2+αRef)*(n:ℝ)≤P.degree v),
    SuppliedVortexRegularClassBalancedDegreesForEveryProtection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign →
    SuppliedVortexClassBalancedProtectedCorrection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr fprot :=by
  obtain ⟨c,hc,hN⟩:=long_class_protected_correction_uniform_spacing αRef ρ₀ δcorr hαRef hρ₀ hδcorr
  refine ⟨c,hc,?_⟩
  intro ξPart hξ0 hξ d
  obtain ⟨N,hNpos,hN⟩:=hN d
  refine ⟨N,hNpos,?_⟩
  intro r k₀ K hr hK hm hd sstar γRich tstar kstar θ ρ D eps lam ζret alpha γ hθpos hθ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ ξ Δ τ fprot hfprot size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hnN hn U _ _ F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign hmpart hfbound hdegree hmin hout
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  unfold SuppliedVortexRegularClassBalancedDegreesForEveryProtection at hout
  have hdec : referenceWitnessFinDecidable n = suppliedClassFullyUniformCorrectionFin n := Subsingleton.elim _ _
  have hdecK : referenceWitnessFinDecidable K = suppliedClassFullyUniformCorrectionFin K := Subsingleton.elim _ _
  have hdec6 : referenceWitnessFinDecidable 6 = suppliedClassFullyUniformCorrectionFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hout
  try rw [hdecK] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexClassBalancedProtectedCorrection
  try rw [hdec]
  try rw [hdecK]
  try rw [hdec6]
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hmass,hclasses,hPrior,hClass,hBoundaryGlobal,hBalanced,hColourDegrees,hrow,hlocalRow,hfixed,hcolumn,hextLocal,hboundary,hrows,hglobalRet,hunassigned,hcolumnAll,hprotected,hglobalBound,hpair,hselected1,hselected2,hpaths,hrest⟩:=hz
  refine ⟨levelWeight,hweight,z,hmass,?_,hkeep.2.2⟩
  intro Aprotect hAprotect hforbid
  obtain ⟨Sclass,hSP,hregS,hprotect,hedit,hPrepared⟩:=hclasses Aprotect hAprotect
  refine ⟨Sclass,hSP,hregS,hprotect,hedit,hPrepared,?_⟩
  have hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  letI : DecidableRel (Zpart⊔Aprotect).Adj := fun x y=>Classical.propDecidable _
  have hforbid' : ∀v,((Zpart⊔Aprotect).degree v:ℝ)≤fprot := by
    intro v
    convert hforbid v using 1
    congr 1
    simp only [← SimpleGraph.ncard_neighborSet]
  have hN':=hN n hnN P Sclass (Zpart⊔Aprotect) ⊥ π (mpart 0) z.1 ρ D ((1/100:ℝ)/((r+4:ℕ):ℝ)) 0 ξPart fprot 0
    (longAssignedApproxMarkedWeight F hF K (r+4) θ) (longAssignedApproxOrdinaryWeight F hF K (r+4) θ)
  have hdecC : classUniformSpacingCorrectionFin n = suppliedClassFullyUniformCorrectionFin n := Subsingleton.elim _ _
  have hdecC6 : classUniformSpacingCorrectionSix = suppliedClassFullyUniformCorrectionFin 6 := Subsingleton.elim _ _
  try rw [hdecC] at hN'
  try rw [hdecC6] at hN'
  have hhosterr:∀v,|(P.degree v:ℝ)-D|≤(0:ℝ)*n:=by intro v; rw [hdegree v]; simp
  have hcol:∀j v,|((∑w,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j v w:ℕ):ℝ)-
    markedExpandedPhysicalProbability (ρ*(1/100)/2) (ρ*((1/100:ℝ)/((r+4:ℕ):ℝ))/2)
      ((∑u,longAssignedApproxOrdinaryWeight F hF K (r+4) θ u)/D)
      ((∑u,longAssignedApproxMarkedWeight F hF K (r+4) θ u)/D)
      (2*(∑u,(1-1/100-(1/100:ℝ)/((r+4:ℕ):ℝ)-longAssignedApproxMarkedWeight F hF K (r+4) θ u-longAssignedApproxOrdinaryWeight F hF K (r+4) θ u))/D) j/2*P.degree v|≤(n:ℝ)^(3/5:ℝ):=by
    intro j v
    exact (hColourDegrees j v).1.le
  obtain ⟨Mhost,Del,hphysical,hbalance,hD0,hedits,hcorrect,hdelDegree,hdelProtect,hfree,hS,hhost,harc⟩:=hN' hρlo hρ1 hD hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 (by norm_num) (by linarith) hξ0 hξ hfprot hfbound hregS hsize hmpart hSP hhosterr hcol hedit hprotect hforbid' (by intro v; simp) (by intro x y h; exact False.elim h) hmin hpaths
  refine ⟨Mhost,Del,hphysical,?_,hedits,hcorrect,?_,hdelProtect⟩
  · simpa [hmpart] using hbalance
  · simpa only [zero_add] using hdelDegree
end Oberwolfach
