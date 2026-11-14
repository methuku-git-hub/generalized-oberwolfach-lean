module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! The neighbourhood fields of the reference level after the actual
physical rim and spoke changes, on the original ambient domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_changed_neighbourhoods
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (rho t kappa ζ errR errI:ℝ)
    (hζ:0≤ζ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)):
    let n:ℝ:=Fintype.card V
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ);
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s a c errR σ H→
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s a c errI σ H→
    (∀ z,¬(rawMarkedPairRims P π d σ z↔rawMarkedPairRims P π d τ z)→
      markedPairPhysical π z∈FR.edgeFinset)→
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ v,(FR.degree v:ℝ)≤ζ*n)→(∀ z,(FS.degree z:ℝ)≤ζ*n)→
    errR+(r+12:ℝ)*(ζ*n+ζ*n)≤(kappa/4)*n→
    errI+(r+12:ℝ)*(ζ*n)≤(kappa/4)*n→
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s a c ((kappa/4)*n) τ H' ∧
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s a c ((kappa/4)*n) τ H' :=by
  intro n p k hrows hindices hrim hspoke hdegR hdegS hbudgetR hbudgetI
  have hnonneg:0≤ζ*n:=mul_nonneg hζ (Nat.cast_nonneg _)
  obtain ⟨hrow,hindex⟩:=marked_neighbourhoods_after_physical_change P π d (r+12)
    Finset.univ Finset.univ p k q s a c errR errI (ζ*n) (ζ*n) (ζ*n) hnonneg hnonneg hnonneg
    σ τ H H' hrows hindices FR FS hrim hspoke hdegR
    (fun v=>hdegS (Sum.inl v)) (fun u=>hdegS (Sum.inr u))
  constructor
  · intro S T J hS hT hJ hinj
    exact (hrow S T J hS hT hJ hinj).trans_le (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudgetR)
  · intro J hJ hsep
    exact (hindex J hJ hsep).trans_le (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudgetI)
end Oberwolfach
