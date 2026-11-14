module

public import Oberwolfach.SuppliedVortexClassChosenCorrectionProof
public import Oberwolfach.SuppliedVortexClassBalancedFullyUniform
public import Oberwolfach.FirstVortexClassDualDeletionBudgets

@[expose] public section
/-! All class-correction tolerances and both matching budgets are chosen before
spacing and order, uniformly for the later host and class density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedClassOrderedFullFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_class_fully_uniform_ordered_budgets
    (αRef αMatch ρ₀ εV ΔBudget ξBudget δold δlocal lamAssign lamMatch:ℝ)
    (hαRef:0<αRef) (hαMatch:0<αMatch) (hρ₀:0<ρ₀) (hεV:0<εV)
    (hΔ:0<ΔBudget) (hξ:0<ξBudget) (hgap:δold<δlocal) (hlam:lamMatch<lamAssign):
    ∃δcorr:ℝ,0<δcorr ∧ ∃c:ℝ,0<c ∧ ∃ξPart:ℝ,0<ξPart ∧
    ξPart+δcorr≤ΔBudget ∧ ξPart+δcorr≤ξBudget ∧ ξPart≤(2*αMatch)/32 ∧
    ξPart/2≤(lamAssign-lamMatch)*εV ∧
    (∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β εV m),0<m→
      ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
    ∀d:ℕ, ∃N:ℕ,1≤N ∧
    ∀(r k₀ K:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d)
    (sstar γRich tstar kstar θ ρ D eps ζret alpha γ:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ τ:ℝ) (fprot:ℝ) (hfprot:0≤fprot)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (n:ℕ),N≤n→∀(hn:1≤n)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsize:ρ*D=2*Fintype.card U) (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (π:Equiv.Perm (Fin n))
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Dnat vsize:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εV vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (δglobal bmatch:ℝ)
    (hmpart:mpart 0=Fintype.card U)
    (hfbound:fprot≤(αRef*(ρ₀/200)^2/16)*n)
    (hdegree:∀v,(P.degree v:ℝ)=D)
    (hmin:∀v,(1/2+αRef)*(n:ℝ)≤P.degree v),
    SuppliedVortexRegularClassBalancedDegreesForEveryProtection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lamMatch ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξBudget ΔBudget τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εV Q hpres δlocal δglobal αMatch bmatch lamAssign →
    SuppliedVortexClassAtChosenCorrection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lamMatch ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξBudget ΔBudget τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εV Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr fprot :=by
  obtain ⟨δcorr,hδ,hchoose⟩:=first_vortex_class_dual_deletion_budgets αRef (2*αMatch) ρ₀ εV ΔBudget ξBudget δold δlocal lamAssign lamMatch hαRef (by positivity) hρ₀ hεV hΔ hξ hgap hlam
  obtain ⟨c,hc,hN⟩:=supplied_vortex_prepare_class_balanced_correction_fully_uniform αRef ρ₀ δcorr hαRef hρ₀ hδ
  obtain ⟨ξPart,hξPart,hΔbudget,hξbudget,hbound,hassign,hedges,hload⟩:=hchoose c hc
  refine ⟨δcorr,hδ,c,hc,ξPart,hξPart,?_,?_,hassign,hedges,hload,?_⟩
  · linarith
  · linarith
  intro d
  have hN':=hN ξPart hξPart.le hbound d
  have hdec:suppliedClassFullyUniformCorrectionFin=suppliedClassOrderedFullFin:=by funext n; exact Subsingleton.elim _ _
  try rw [hdec] at hN'
  obtain ⟨N,hNpos,hN'⟩:=hN'
  refine ⟨N,hNpos,?_⟩
  intro r k₀ K hr hK hm hd sstar γRich tstar kstar θ ρ D eps ζret alpha γ hθpos hθ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ τ fprot hfprot size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hnN hn U _ _ F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart π weight w Dnat vsize βQ Q hpres δglobal bmatch hmpart hfbound hdegree hmin hout
  have hbalanced:=hN' r k₀ K hr hK hm hd sstar γRich tstar kstar θ ρ D eps lamMatch ζret alpha γ hθpos hθ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ ξBudget ΔBudget τ fprot hfprot size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hnN hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart π weight w Dnat vsize βQ εV Q hpres δlocal δglobal αMatch bmatch lamAssign hmpart hfbound hdegree hmin hout
  have hchosen:=supplied_vortex_class_at_chosen_correction r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lamMatch ζret alpha γ hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ ξBudget ΔBudget τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εV Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr fprot (by linarith) (by linarith)
  have hdecC : suppliedClassChosenCorrectionFin n = suppliedClassOrderedFullFin n := Subsingleton.elim _ _
  have hdecCK : suppliedClassChosenCorrectionFin K = suppliedClassOrderedFullFin K := Subsingleton.elim _ _
  try rw [hdecC] at hchosen
  try rw [hdecCK] at hchosen
  exact hchosen hbalanced
end Oberwolfach
