module

public import Oberwolfach.SuppliedVortexRegularClassPreparedCapacity
public import Oberwolfach.SuppliedVortexRegularClassPreparedGlobal
public import Oberwolfach.FirstVortexClassPreparedGlobalBoundaryProof
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedGlobal
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedCapacity
public import Oberwolfach.FirstVortexPreparedProtectedGlobalProof
public import Oberwolfach.SuppliedVortexOutcomePreparedFirstGlobal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedClassPreparedGlobalFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_regular_class_prepared_global
    (r k₀ K d:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d) (hd3:3≤d) (hdlarge:(r+4)+2≤d)
    (αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ:ℝ)
    (δlocal δglobal αMatch bmatch εQ ξ lamAssign ξPart:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρ₀max:ρ₀≤1)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hα:0<αMatch) (hlam:0<lam) (hε:0<εQ) (hδ:0<δlocal) (hδglobal:0<δglobal)
    (hbmatch:0<bmatch) (hαb:(2*αMatch)/16≤bmatch)
    (hαsmall:(2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024) (hαglobal:2*αMatch≤4*δglobal)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:εQ≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δglobal) (hθlocal:θ≤δlocal/32)
    (hlamlocal:lam≤δlocal*εQ/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (C₀:ℝ) (hC:1≤C₀) (hehi:εQ≤αMatch/(1000*C₀)) (hlamhi:lam≤αMatch/128) (hlamθ:lam≤θ)
    (hγ:0≤γ) (hγε:γ≤eps) (heps1:eps≤1) (ha:alpha≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (ρscale:ℝ) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
    (hcutHost:5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hDv:0<Dnat) (hρhi:initialIndexDensity U Dnat≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dnat) (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hvsize:0<vsize)
    (hsize:initialIndexDensity U Dnat*(Dnat:ℝ)=2*Fintype.card U)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hscale:max alpha γ*n≤ρscale*(Q.extendedVertices 1).card)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ Δ τ:ℝ) (hτ:0≤τ)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (τWeight Asrc:ℝ) (hBM:0<BM)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dnat τWeight Asrc BM weight)
    (hBO:∀i,0<BO i) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)),
    ∀(hn:1≤n) (hDvR:0<(Dnat:ℝ)),
    SuppliedVortexRegularClassPreparedCapacity r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch lamAssign →
    SuppliedVortexRegularClassPreparedGlobal r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign :=by
  obtain ⟨N,hN⟩:=first_vortex_class_prepared_oriented_with_boundary_global_load εQ θ δglobal ρ₀ lam lamAssign ζret (r+4) d (by omega) hdlarge hε hθpos (by linarith) hδglobal hθδ Nret hNret hρ₀max hεsmall hlam.le (by linarith) (by omega) hspacing
  refine ⟨max N 1,?_⟩
  intro n hnN U _ _ F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR hout
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  unfold SuppliedVortexRegularClassPreparedCapacity at hout
  have hdec : referenceWitnessFinDecidable n = suppliedClassPreparedGlobalFin n := Subsingleton.elim _ _
  have hdecK : referenceWitnessFinDecidable K = suppliedClassPreparedGlobalFin K := Subsingleton.elim _ _
  have hdec6 : referenceWitnessFinDecidable 6 = suppliedClassPreparedGlobalFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hout
  try rw [hdecK] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexRegularClassPreparedGlobal
  have hdec' : referenceWitnessFinDecidable n = suppliedClassPreparedGlobalFin n := Subsingleton.elim _ _
  have hdecK' : referenceWitnessFinDecidable K = suppliedClassPreparedGlobalFin K := Subsingleton.elim _ _
  have hdec6' : referenceWitnessFinDecidable 6 = suppliedClassPreparedGlobalFin 6 := Subsingleton.elim _ _
  try rw [hdec']
  try rw [hdecK']
  try rw [hdec6']
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hmass,⟨Sclass,hSP,hregS,hprotect,hedit,hPrepared⟩,hPrior,hClass,hBoundaryGlobal,hBalanced,hColourDegrees,hrow,hlocalRow,hfixed,hcolumn,hextLocal,hboundary,hrows,hglobalRet,hunassigned,hcolumnAll,hprotected,hglobalBound,hpair,hselected1,hselected2,hpaths,hstarts,hres,hfixedSelection,hspoke,hcount,hmark,hord,hload,hmasspost,hbudget,hmatch⟩:=hz
  refine ⟨levelWeight,hweight,z,hmass,⟨Sclass,hSP,hregS,hprotect,hedit,?_⟩,hkeep.2.2⟩
  have hlocal:=first_vortex_common_event_local_tests P Dnat vsize βQ εQ Q π d
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
    (fun e=>z.1 (Sum.inr e)) z.2 (longAssignedIntervalProbability F hF K (r+4) θ)
    (longAssignedSpokeProbability F hF K (r+4) θ) ζret hfixed hcolumn hboundary hrows
  have hN':=hN n K (le_trans (le_max_left _ _) hnN) hK
  have hdecN : firstVortexClassPreparedGlobalBoundaryFin n = suppliedClassPreparedGlobalFin n := Subsingleton.elim _ _
  have hdecNK : firstVortexClassPreparedGlobalBoundaryFin K = suppliedClassPreparedGlobalFin K := Subsingleton.elim _ _
  have hdecN6 : firstVortexClassPreparedGlobalBoundaryFin 6 = suppliedClassPreparedGlobalFin 6 := Subsingleton.elim _ _
  try rw [hdecN] at hN'
  try rw [hdecNK] at hN'
  try rw [hdecN6] at hN'
  exact hN' U P Sclass π Dnat vsize βQ Q hreg hDv hρhi hvsize F hF δlocal αMatch bmatch eps ξ Δ alpha γ ρscale
    hθ (le_trans hγ hγε) hρ₀ hα hlamθ heps hαsmall hαglobal hγ ha hγrate hζ hζ0 hρscale hρscale0 hscale hnoshort weight w z.1 _ z.2
    hlocal.2.2.2 hlocal.1 hlocal.2.1 hstarts hglobalRet hBoundaryGlobal hPrepared
end Oberwolfach
