module

public import Oberwolfach.SuppliedVortexRegularBoundaryOrderedOutcome

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
theorem supplied_vortex_regular_boundary_outcome_deletion_cap
    (r k₀ K d:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d)
    (αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ ξ Δ Δsmall τ:ℝ)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n:ℕ) (hn:1≤n)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsize:ρ*D=2*Fintype.card U) (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (ξPart:ℝ) (π:Equiv.Perm (Fin n))
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (hcap:Δsmall≤Δ):
    SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass
      P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres →
    SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ ρ D eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρ1 hD hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δsmall τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass
      P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres :=by
  intro hout
  have hbound:Δsmall*(n:ℝ)≤Δ*n:=mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg n)
  unfold SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome at hout ⊢
  obtain ⟨levelWeight,hweights,z,hrest⟩:=hout
  refine ⟨levelWeight,hweights,z,?_⟩
  repeat' first
    | exact hrest
    | (rcases hrest with ⟨hfirst,hrest⟩
       refine ⟨?_,?_⟩
       first
       | exact hfirst
       | (intro Del δ hdeg hδ; exact hfirst Del δ hdeg (hδ.trans hbound)))
  intro Del δ hdeg hδ
  exact hrest Del δ hdeg (hδ.trans hbound)
end Oberwolfach
