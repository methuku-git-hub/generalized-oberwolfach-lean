module

public import Oberwolfach.OrdinaryFixedCorrectedReservoirSpokeLabels
public import Oberwolfach.OrdinaryCorrectedReservoirSpokeLabels
public import Oberwolfach.OrdinaryReservedTrimBudget

@[expose] public section
/-! The actual bounded reservoir supplies the absorber row and column budgets
needed for reserved lists and required-edge assignment at large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_corrected_reservoir_label_budgets_eventually
    (r m t a b:ℕ) (lam ε bRate:ℝ) (hlam:0<lam) (hε:ε≤lam/4) (hb:0<bRate):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (ξ:ℝ) (Q F:SimpleGraph (Fin n)) (A Z Wterm Inner:Finset (Fin n)) (Bterm B:Finset U),
    (Inner.card:ℝ)≤ε*n→
    ∀(K:Finset (Sym2 (Fin n)⊕(Fin n×U))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a b ξ Q F
      (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false) A Z Wterm Bterm B K JQ JH→
      (∀u,ordinaryReservoirSpokeLabels K u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
      (∀u,(lam/2)*n+Inner.card+(ordinaryReservoirSpokeLabels K u).card≤lam*n) ∧
      (∀v,((Finset.univ.filter (fun u=>v∈ordinaryReservoirSpokeLabels K u)).card:ℝ)≤bRate*n) :=by
  obtain ⟨Nr,hr⟩:=ordinary_reserved_trim_budget_eventually lam ε (2^(t*t)*a) hlam hε
  obtain ⟨Nc,hc⟩:=ordinary_constant_eventually_below_linear_rate bRate (2^(t*t)*b) hb
  refine ⟨max Nr Nc,?_⟩
  intro n hn U _ _ π d σ ξ Q F A Z Wterm Inner Bterm B hInner K JQ JH hW
  obtain ⟨hsub,hrow,hcol⟩:=ordinary_fixed_corrected_reservoir_spoke_labels π d σ r m t a b ξ Q F A Z Wterm Bterm B K JQ JH hW
  refine ⟨hsub,?_,?_⟩
  · intro u
    exact hr n (by omega) Inner.card (ordinaryReservoirSpokeLabels K u).card hInner (hrow u)
  · intro v
    have hc':((Finset.univ.filter (fun u=>v∈ordinaryReservoirSpokeLabels K u)).card:ℝ)≤(2^(t*t)*b:ℕ):=by exact_mod_cast hcol v
    have hc'' : ((2^(t*t)*b:ℕ):ℝ)≤bRate*n:=by
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hc n (by omega)
    exact hc'.trans hc''
end Oberwolfach
