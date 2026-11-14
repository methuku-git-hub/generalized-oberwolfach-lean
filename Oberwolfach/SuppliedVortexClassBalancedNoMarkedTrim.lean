module

public import Oberwolfach.FirstVortexReservedListsNoMarkedTrim
public import Oberwolfach.SuppliedVortexRegularClassGlobalForEveryProtection
public import Oberwolfach.SuppliedVortexRegularClassBalancedDegreesForEveryProtection
public import Oberwolfach.SuppliedVortexRegularClassBalancedDegreesForEveryProtection
public import Oberwolfach.FirstVortexClassPreparedBalancedHostProof
public import Oberwolfach.FirstVortexClassPreparedBalancedDegreesProof
public import Oberwolfach.SuppliedVortexRegularClassGlobalForEveryProtection
public import Oberwolfach.SuppliedVortexRegularClassPreparedResidual
public import Oberwolfach.FirstVortexClassPreparedResidualProof
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedResidual
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedGlobal
public import Oberwolfach.FirstVortexPreparedProtectedResidualProof
public import Oberwolfach.SuppliedVortexOutcomePreparedFirstResidual
public import Oberwolfach.FirstVortexPreparedResidual
public import Oberwolfach.FirstVortexReservedListsEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedClassNoMarkedTrimFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_class_every_protection_balanced_no_marked_trim
    (r k₀ K d:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d)
    (αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ ξ Δ τ:ℝ)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n:ℕ) (hn:1≤n)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsize:ρ*D=2*Fintype.card U) (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (ξPart:ℝ) (π:Equiv.Perm (Fin n))
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (δlocal δglobal αMatch bmatch lamAssign:ℝ)
    (βlist lamList ζList βfinal γList pstar:ℝ)
    (hn2:2≤n) (hu:Fintype.card U≤n) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hεQ:0≤εQ)
    (hb:0≤bmatch) (hbsmall:bmatch≤((ρ₀/4)/40000)/16) (hαb:(2*αMatch)/16≤bmatch)
    (hθδ:10*θ≤δglobal) (hεδ:εQ≤δglobal) (hβfinal:0<βfinal) (hβfinal1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ))
    (hγList:0≤γList) (hpstar:0≤pstar) (hp:pstar≤ρ*(1/100)/2)
    (hβlist:0≤βlist) (hlamList:0≤lamList) (hζList:0≤ζList) (hΔζ:Δ≤ζList)
    (hP:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n)
    (hmargin:βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ))
    (hlistBudget:(lamList+2*ζList)*n≤βlist*n)
    (htrim:βfinal+εQ≤lamList)
:
    SuppliedVortexRegularClassGlobalForEveryProtection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign →
    SuppliedVortexRegularClassBalancedDegreesForEveryProtection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign :=by
  intro hout
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  unfold SuppliedVortexRegularClassGlobalForEveryProtection at hout
  have hdec : referenceWitnessFinDecidable n = suppliedClassNoMarkedTrimFin n := Subsingleton.elim _ _
  have hdecK : referenceWitnessFinDecidable K = suppliedClassNoMarkedTrimFin K := Subsingleton.elim _ _
  have hdec6 : referenceWitnessFinDecidable 6 = suppliedClassNoMarkedTrimFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hout
  try rw [hdecK] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexRegularClassBalancedDegreesForEveryProtection
  have hdec' : referenceWitnessFinDecidable n = suppliedClassNoMarkedTrimFin n := Subsingleton.elim _ _
  have hdecK' : referenceWitnessFinDecidable K = suppliedClassNoMarkedTrimFin K := Subsingleton.elim _ _
  have hdec6' : referenceWitnessFinDecidable 6 = suppliedClassNoMarkedTrimFin 6 := Subsingleton.elim _ _
  try rw [hdec']
  try rw [hdecK']
  try rw [hdec6']
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hmass,hclasses,hPrior,hClass,hBoundaryGlobal,hBalanced,hColourDegrees,hrow,hlocalRow,hfixed,hcolumn,hextLocal,hboundary,hrows,hglobalRet,hunassigned,hcolumnAll,hprotected,hglobalBound,hpair,hselected1,hselected2,hpaths,hstarts,hres,hfixedSelection,hspoke,hcount,hmark,hord,hload,hmasspost,hbudget,hmatch⟩:=hz
  refine ⟨levelWeight,hweight,z,hmass,?_,hkeep.2.2⟩
  intro Aprotect hAprotect
  obtain ⟨Sclass,hSP,hregS,hprotect,hedit,hPrepared⟩:=hclasses Aprotect hAprotect
  refine ⟨Sclass,hSP,hregS,hprotect,hedit,?_⟩
  have hneighbour:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ):=by
    simpa only [longAssignedSpokeProbability,Bool.false_eq_true,ite_false] using hselected2
  have hdecL : instDecidableEqFin n = suppliedClassNoMarkedTrimFin n := Subsingleton.elim _ _
  have hdecLK : instDecidableEqFin K = suppliedClassNoMarkedTrimFin K := Subsingleton.elim _ _
  have hList:=@first_vortex_reserved_lists_without_marked_loss n U _ _
  try rw [hdecL] at hList
  try rw [hdecLK] at hList
  have hext:=hList hn2 F hF K (r+4) d (by omega) (by omega)
    θ hθpos.le (by linarith) P π Dnat vsize βQ εQ Q hεQ z.1 γList pstar (ρ*(1/100)/2) βlist lamList ζList Δ
    hγList hpstar hp hβlist hlamList hζList hP herror hpaths hneighbour hmargin hlistBudget hΔζ _ z.2
    βfinal hβfinal.le htrim
  have hhost:=first_vortex_class_prepared_balanced_host_completion P Sclass π Dnat vsize d (r+4) βQ εQ Q F hF θ lamAssign eps δlocal δglobal αMatch bmatch ρ₀ ξ Δ alpha γ βfinal weight w z.1 _ z.2
    hρ₀ hb hbsmall hαb hθδ hεδ hβfinal hβfinal1 hδ hδbound hSP (by omega) hnβ hnδ hu
  have hdecR : firstVortexClassPreparedBalancedHostProofFin n = suppliedClassNoMarkedTrimFin n := Subsingleton.elim _ _
  have hdecRK : firstVortexClassPreparedBalancedHostProofFin K = suppliedClassNoMarkedTrimFin K := Subsingleton.elim _ _
  try rw [hdecR] at hhost
  try rw [hdecRK] at hhost
  have hhost' := hhost hext hPrepared
  have hdegrees:=first_vortex_class_prepared_balanced_degrees P Sclass π Dnat vsize d (r+4) βQ εQ Q F hF θ lamAssign eps δlocal δglobal αMatch bmatch ρ₀ ξ Δ alpha γ weight w z.1 _ z.2 hd hnoshort hSP
  have hdecD : firstVortexClassPreparedBalancedDegreesProofFin n = suppliedClassNoMarkedTrimFin n := Subsingleton.elim _ _
  have hdecDK : firstVortexClassPreparedBalancedDegreesProofFin K = suppliedClassNoMarkedTrimFin K := Subsingleton.elim _ _
  try rw [hdecD] at hdegrees
  try rw [hdecDK] at hdegrees
  exact hdegrees hhost'

end Oberwolfach
