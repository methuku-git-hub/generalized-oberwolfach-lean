module

public import Oberwolfach.ExpandedSamplePhysicalClassLaw
public import Oberwolfach.ProtectedFactorPreparation

@[expose] public section
/-! A protected-preparation lower bound for the same expanded sample gives
the exact independent-retention lower bound needed by the class partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance expandedPrepTransferAlignedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) expandedPrepTransferAlignedSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem expanded_sample_preparation_probability_transfer_aligned
    {n m:ℕ} {U Γ Color:Type} [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ) (F:Fin m→SimpleGraph (Fin n))
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (b:ℝ)
    (h: b≤((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>ProtectedFactorPreparation P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ B F)):
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u)
      (by positivity) hsum)).probability (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  rw [←expanded_sample_physical_class_probability P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun S=>ProtectedFactorPreparation P S I ξ B F)]
  exact h
end Oberwolfach
