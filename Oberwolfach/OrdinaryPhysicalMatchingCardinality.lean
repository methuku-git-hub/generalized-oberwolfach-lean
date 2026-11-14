module

public import Oberwolfach.OrdinaryPhysicalMatchingRows
public import Oberwolfach.PhysicalMatchingLargeRows
public import Oberwolfach.OrdinaryAssignedRetainedHubTests

@[expose] public section
/-! The actual physical ground, retained tests and large degree rows fit a
fixed cubic cardinality bound once the host dominates the fixed cutoff. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_matching_cardinality
    (hn:2≤n) (hK:K≤n) (hU:Fintype.card U≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ)
    (φ:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Sym2 (Fin n)⊕(Fin n×U))
    (σ:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (S:OrdinaryPhysicalRowIndex (Fin n) U→Finset (PhysicalSampledActive φ σ)) (α:ℝ):
    Fintype.card (PhysicalSampledActive φ σ)≤n^3 ∧
    Fintype.card (OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ)≤n^3 ∧
    Fintype.card (LargeMatchingRow S n α)≤n^3 :=by
  have hsym:Fintype.card (Sym2 (Fin n))≤n*n:=by
    have hsurj:Function.Surjective (fun xy:Fin n×Fin n=>s(xy.1,xy.2)):=by
      intro e
      induction e using Sym2.ind with
      | _ x y=>exact ⟨(x,y),rfl⟩
    have hh:=Fintype.card_le_of_surjective (fun xy:Fin n×Fin n=>s(xy.1,xy.2)) hsurj
    simpa only [Fintype.card_prod,Fintype.card_fin] using hh
  have hphys:Fintype.card (Sym2 (Fin n)⊕(Fin n×U))≤2*(n*n):=by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have hm:=Nat.mul_le_mul_left n hU
    nlinarith
  have h2sq:2*(n*n)≤n^3:=by
    have hh:=Nat.mul_le_mul_left (n*n) hn
    nlinarith [hh]
  have h3:3*n≤n^3:=by
    have hs:3≤n*n:=by nlinarith
    have hh:=Nat.mul_le_mul_right n hs
    nlinarith [hh]
  constructor
  · have hh:=Fintype.card_le_of_injective (Subtype.val:PhysicalSampledActive φ σ→Sym2 (Fin n)⊕(Fin n×U)) Subtype.val_injective
    exact hh.trans (hphys.trans h2sq)
  constructor
  · have hh:=Fintype.card_le_of_injective (Subtype.val:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ→Fin K×U) Subtype.val_injective
    have hp:Fintype.card (Fin K×U)≤n*n:=by
      simp only [Fintype.card_prod,Fintype.card_fin]
      exact (Nat.mul_le_mul hK hU)
    have hs:n*n≤n^3:=by nlinarith [h2sq]
    exact hh.trans (hp.trans hs)
  · have hh:=Fintype.card_le_of_injective (Subtype.val:LargeMatchingRow S n α→OrdinaryPhysicalRowIndex (Fin n) U) Subtype.val_injective
    have hr:Fintype.card (OrdinaryPhysicalRowIndex (Fin n) U)≤3*n:=by
      simpa only [Fintype.card_fin] using ordinary_physical_row_index_card_le (V:=Fin n) (by simpa using hU)
    exact hh.trans (hr.trans h3)
end Oberwolfach
