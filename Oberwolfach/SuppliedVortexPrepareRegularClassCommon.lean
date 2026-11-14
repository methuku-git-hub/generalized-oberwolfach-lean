module

public import Oberwolfach.SuppliedVortexRegularBoundaryOrderedOutcome
public import Oberwolfach.SuppliedVortexRegularClassPreparedOutcome
public import Oberwolfach.FirstVortexClassPrepareFromCommonTests
public import Oberwolfach.SuppliedVortexOutcomeBalancedDegreeMatchingGlobalBoundary
public import Oberwolfach.SuppliedVortexOutcomePreparedBalancedDegreeMatchingGlobalBoundary
public import Oberwolfach.FirstVortexPrepareOrientedCommonTests
public import Oberwolfach.SuppliedVortexOutcomePreparedOrientedMatching
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedMatching
public import Oberwolfach.FirstVortexPrepareProtectedCommonTests
public import Oberwolfach.SuppliedVortexOutcomePreparedFirstMatching

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedRegularClassPrepareFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_prepare_regular_class_from_common_event
    (r k₀ K d:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d) (hd3:3≤d)
    (αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ:ℝ)
    (δold δlocal αMatch bmatch εQ ξ lamAssign ξPart:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hα:0<αMatch) (hlam:0<lam) (hε:0<εQ) (hδ:0<δold)
    (hbmatch:0<bmatch) (hαb:(2*αMatch)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:εQ≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32)
    (hlamlocal:lam≤δold*εQ/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (C₀:ℝ) (hC:1≤C₀) (hehi:εQ≤αMatch/(1000*C₀)) (hlamhi:lam≤αMatch/128) (hlamθ:lam≤θ)
    (hγ:0≤γ) (ha0:0≤alpha) (hγε:γ≤eps) (heps1:eps≤1) (ha:alpha≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (ρscale:ℝ) (hρscale:ρscale≤θ/4096)
    (hξdeg:ξPart≤(2*αMatch)/32) (hξedges:ξPart/2≤(lamAssign-lam)*εQ)
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
    (hmargin:ξPart*n≤(δlocal-δold)*(Q.extendedVertices 1).card)
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
    SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres →
    SuppliedVortexRegularClassPreparedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch lamAssign :=by
  obtain ⟨N,hN⟩:=first_vortex_class_prepare_from_common_tests αMatch lam lamAssign εQ δold δlocal θ eps ξ ρ₀ bmatch ξPart d K (r+4) hα hlam hε hδ hθpos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθ hlamlocal hspacing hd3 hK hm heps hξ hξ0
  refine ⟨max N 1,?_⟩
  intro n hnN U _ _ F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR hout
  unfold SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome at hout
  have hdec : referenceWitnessFinDecidable n = suppliedRegularClassPrepareFin n := Subsingleton.elim _ _
  have hdec6 : referenceWitnessFinDecidable 6 = suppliedRegularClassPrepareFin 6 := Subsingleton.elim _ _
  have hdecK : referenceWitnessFinDecidable K = suppliedRegularClassPrepareFin K := Subsingleton.elim _ _
  try rw [hdecK] at hout
  try rw [hdec] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexRegularClassPreparedOutcome
  have hdec' : referenceWitnessFinDecidable n = suppliedRegularClassPrepareFin n := Subsingleton.elim _ _
  have hdec6' : referenceWitnessFinDecidable 6 = suppliedRegularClassPrepareFin 6 := Subsingleton.elim _ _
  try rw [hdec']
  try rw [hdec6']
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hmass,hPrior,hClass,hBoundaryGlobal,hBalanced,hColourDegrees,hrow,hlocalRow,hfixed,hcolumn,hextLocal,hboundary,hrows,hglobalRet,hunassigned,hcolumnAll,hprotected,hglobalBound,hpair,hselected1,hselected2,hpaths,hstarts,hres,hfixedSelection,hspoke,hcount,hmark,hord,hload,hmasspost,hbudget,hmatch⟩:=hz
  refine ⟨levelWeight,hweight,z,hmass,?_,hkeep.2⟩
  obtain ⟨Sclass,hSP,hregS,hprotect,hedit⟩:=hClass ⊥ (by intro v; simp)
  refine ⟨Sclass,hSP,hregS,?_,hedit,?_⟩
  · intro x y hxy
    exact hprotect x y (Or.inl hxy)
  have hN':=hN n (le_trans (le_max_left _ _) hnN)
  have hdecN : firstVortexClassPrepareCommonTestsFin n = suppliedRegularClassPrepareFin n := Subsingleton.elim _ _
  have hdecN6 : firstVortexClassPrepareCommonTestsFin 6 = suppliedRegularClassPrepareFin 6 := Subsingleton.elim _ _
  try rw [hdecN] at hN'
  try rw [hdecN6] at hN'
  apply hN' U P Sclass π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ alpha γ ζret ρscale Δ hγ ha0 hγε heps1 ha hγrate hζ hρscale hζ0 hscale τWeight Asrc BM hBM weight hw BO hBO w hw0 hwupper z.1 _ z.2 t₀ τ hτ hSP hedit hξdeg hξedges hmargin hrow hfixed hcolumn hboundary hrows hpair hglobalBound hstarts hcount hload hbudget
  intro Del δDel hDel hΔ S e T q selected Hret Qres
  obtain ⟨M,hpos,hdisj,hrim,hinc,hincLarge,hlow,hup,hphysical,hremaining⟩:=hmatch Del δDel hDel hΔ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,?_⟩
  intro Reserve X Z habs
  obtain ⟨assign,C,hC,hcount,_,herr,_⟩:=hremaining Reserve X Z habs
  exact ⟨assign,C,hC,hcount,herr⟩
end Oberwolfach
