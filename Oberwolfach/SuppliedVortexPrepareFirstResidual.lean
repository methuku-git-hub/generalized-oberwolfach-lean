module

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
local instance suppliedPrepareFirstResidualFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_prepare_first_residual
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
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (δlocal αMatch bmatch:ℝ)
    (βlist lamList ζList βfinal η γList pstar:ℝ)
    (hn2:2≤n) (hu:Fintype.card U≤n) (hεQ:0≤εQ)
    (hb:0≤bmatch) (hbsmall:bmatch≤((ρ₀/4)/40000)/16) (hαb:αMatch/16≤bmatch)
    (hθδ:10*θ≤δlocal) (hεδ:εQ≤δlocal) (hβfinal:0<βfinal) (hβfinal1:βfinal≤1)
    (hδ:0<δlocal) (hδbound:δlocal≤(βfinal/100)^2)
    (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δlocal≤(n:ℝ))
    (hγList:0≤γList) (hpstar:0≤pstar) (hp:pstar≤ρ*(1/100)/2)
    (hβlist:0≤βlist) (hlamList:0≤lamList) (hζList:0≤ζList) (hΔζ:Δ≤ζList)
    (hP:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n)
    (hmargin:βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ))
    (hlistBudget:(lamList+2*ζList)*n≤βlist*n)
    (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (htrim:βfinal+εQ+1/(100*((r+4:ℕ):ℝ))+η≤lamList)
:
    SuppliedVortexOutcomeWithPreparedFirstGlobal r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch →
    SuppliedVortexOutcomeWithPreparedFirstResidual r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch :=by
  intro hout
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  unfold SuppliedVortexOutcomeWithPreparedFirstGlobal at hout
  have hdec : suppliedPreparedGlobalFin n = suppliedPrepareFirstResidualFin n := Subsingleton.elim _ _
  have hdecK : suppliedPreparedGlobalFin K = suppliedPrepareFirstResidualFin K := Subsingleton.elim _ _
  have hdec6 : suppliedPreparedGlobalFin 6 = suppliedPrepareFirstResidualFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hout
  try rw [hdecK] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexOutcomeWithPreparedFirstResidual
  have hdec' : suppliedPreparedResidualFin n = suppliedPrepareFirstResidualFin n := Subsingleton.elim _ _
  have hdecK' : suppliedPreparedResidualFin K = suppliedPrepareFirstResidualFin K := Subsingleton.elim _ _
  have hdec6' : suppliedPreparedResidualFin 6 = suppliedPrepareFirstResidualFin 6 := Subsingleton.elim _ _
  try rw [hdec']
  try rw [hdecK']
  try rw [hdec6']
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hInputs,hPrepared,hmass,hPrior,hrow,hlocalRow,hfixed,hcolumn,hextLocal,hboundary,hrows,hglobalRet,hunassigned,hcolumnAll,hprotected,hglobalBound,hpair,hselected1,hselected2,hpaths,hstarts,hres,hfixedSelection,hspoke,hcount,hmark,hord,hload,hmasspost,hbudget,hmatch⟩:=hz
  refine ⟨levelWeight,hweight,z,hInputs,?_,hkeep.2.2⟩
  have hneighbour:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ):=by
    simpa only [longAssignedSpokeProbability,Bool.false_eq_true,ite_false] using hselected2
  have hdecL : instDecidableEqFin n = suppliedPrepareFirstResidualFin n := Subsingleton.elim _ _
  have hdecLK : instDecidableEqFin K = suppliedPrepareFirstResidualFin K := Subsingleton.elim _ _
  have hList:=@first_vortex_reserved_lists_from_event_tests n U _ _
  try rw [hdecL] at hList
  try rw [hdecLK] at hList
  have hext:=hList hn2 F hF K (r+4) d (by omega) (by omega)
    θ hθpos.le (by linarith) P π Dnat vsize βQ εQ Q hεQ z.1 γList pstar (ρ*(1/100)/2) βlist lamList ζList Δ
    hγList hpstar hp hβlist hlamList hζList hP herror hpaths hneighbour hmargin hlistBudget hΔζ _ z.2
    (fun u=>hstarts u false) βfinal η hβfinal.le hsub htrim
  have hresidual:=first_vortex_prepared_residual_completion P π Dnat vsize d (r+4) βQ εQ Q F hF θ lam eps δlocal δlocal αMatch bmatch ρ₀ ξ Δ alpha γ βfinal weight w z.1 _ z.2
    hρ₀ hb hbsmall hαb hθδ hεδ hβfinal hβfinal1 hδ hδbound (by omega) hnβ hnδ hu
  have hdecR : firstVortexPreparedResidualFin n = suppliedPrepareFirstResidualFin n := Subsingleton.elim _ _
  have hdecRK : firstVortexPreparedResidualFin K = suppliedPrepareFirstResidualFin K := Subsingleton.elim _ _
  try rw [hdecR] at hresidual
  try rw [hdecRK] at hresidual
  exact hresidual hext hPrepared
end Oberwolfach
