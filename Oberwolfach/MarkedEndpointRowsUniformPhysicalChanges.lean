module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! Transfer endpoint row and index counts on their fixed restricted
domains, retaining the original parent-order error scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_endpoint_rows_uniform_physical_changes
    (h:ℕ) (x:ℝ) (hx:0<x):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (B:Finset U)
      (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
      (errR errI:ℝ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0≤errR → 0≤errI → errR≤(x/4)*Fintype.card V → errI≤(x/4)*Fintype.card V →
    MarkedRowsWithSpokes P π d h A p k q s a j errR σ H →
    MarkedIndicesWithSpokes π d h B q s a j errI σ H →
    (∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d τ e)→markedPairPhysical π e∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    ∃ errR' errI':ℝ,0≤errR' ∧ 0≤errI' ∧ errR'≤(x/2)*Fintype.card V ∧ errI'≤(x/2)*Fintype.card V ∧
      MarkedRowsWithSpokes P π d h A p k q s a j errR' τ H' ∧
      MarkedIndicesWithSpokes π d h B q s a j errI' τ H' := by
  let ζcap:=x/(16*((h:ℝ)+1))
  have hcap:0<ζcap:=by dsimp [ζcap];positivity
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d A B p k q s a j errR errI σ τ H H' FR FS
    heR heI hrBound hiBound hrows hindices hR hS hFR hFS
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hδ:0≤ζ*Fintype.card V:=mul_nonneg hζ hn
  have hcap':ζ*(16*((h:ℝ)+1))≤x:=(le_div_iff₀ (by positivity)).mp hζcap
  have hh:(0:ℝ)≤h:=Nat.cast_nonneg _
  have hchange:=marked_neighbourhoods_after_physical_change P π d h A B p k q s a j
    errR errI (ζ*Fintype.card V) (ζ*Fintype.card V) (ζ*Fintype.card V) hδ hδ hδ
    σ τ H H' hrows hindices FR FS hR hS hFR (fun v=>hFS (Sum.inl v)) (fun u=>hFS (Sum.inr u))
  refine ⟨errR+h*(ζ*Fintype.card V+ζ*Fintype.card V),errI+h*(ζ*Fintype.card V),
    by positivity,by positivity,?_,?_,hchange⟩
  · nlinarith [mul_le_mul_of_nonneg_right hcap' hn,mul_nonneg hδ hh]
  · nlinarith [mul_le_mul_of_nonneg_right hcap' hn,mul_nonneg hδ hh]
end Oberwolfach
