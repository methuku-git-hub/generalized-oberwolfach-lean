module

public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedSpokes
public import Oberwolfach.FirstVortexPreparedProtectedSpokesProof
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
local instance suppliedPrepareProtectedSpokesFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_prepare_protected_spokes
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
    (δlocal αMatch bmatch:ℝ) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x):
    SuppliedVortexOutcomeWithPreparedProtectedComplement r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch →
    SuppliedVortexOutcomeWithPreparedProtectedSpokes r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres δlocal αMatch bmatch :=by
  intro hout
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  unfold SuppliedVortexOutcomeWithPreparedProtectedComplement at hout
  have hdec : suppliedPreparedProtectedComplementFin n = suppliedPrepareProtectedSpokesFin n := Subsingleton.elim _ _
  have hdecK : suppliedPreparedProtectedComplementFin K = suppliedPrepareProtectedSpokesFin K := Subsingleton.elim _ _
  have hdec6 : suppliedPreparedProtectedComplementFin 6 = suppliedPrepareProtectedSpokesFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hout
  try rw [hdecK] at hout
  try rw [hdec6] at hout
  unfold SuppliedVortexOutcomeWithPreparedProtectedSpokes
  have hdec' : suppliedPreparedProtectedSpokesFin n = suppliedPrepareProtectedSpokesFin n := Subsingleton.elim _ _
  have hdecK' : suppliedPreparedProtectedSpokesFin K = suppliedPrepareProtectedSpokesFin K := Subsingleton.elim _ _
  have hdec6' : suppliedPreparedProtectedSpokesFin 6 = suppliedPrepareProtectedSpokesFin 6 := Subsingleton.elim _ _
  try rw [hdec']
  try rw [hdecK']
  try rw [hdec6']
  obtain ⟨levelWeight,hweight,z,hz⟩:=hout
  have hkeep:=hz
  obtain ⟨hInputs,hPrepared,hmass,hPrior,hrest⟩:=hz
  refine ⟨levelWeight,hweight,z,hInputs,?_,hkeep.2.2⟩
  have hnew:=first_vortex_prepared_protected_spokes P π Dnat vsize d (r+4) βQ εQ Q F hF θ lam eps δlocal δlocal αMatch bmatch ρ₀ ξ Δ alpha γ weight w z.1 _ z.2 hd hnoshort
  have hdecC : firstVortexPreparedProtectedSpokesProofFin n = suppliedPrepareProtectedSpokesFin n := Subsingleton.elim _ _
  have hdecCK : firstVortexPreparedProtectedSpokesProofFin K = suppliedPrepareProtectedSpokesFin K := Subsingleton.elim _ _
  try rw [hdecC] at hnew
  try rw [hdecCK] at hnew
  exact hnew hPrepared
end Oberwolfach
