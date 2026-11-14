module

public import Oberwolfach.MarkedRowsPhysicalChange
public import Oberwolfach.MarkedLocalChangeDegreeScale
public import Oberwolfach.MarkedPhysicalChangesRestrict

@[expose] public section
/-! Preserve the active row counts on their fixed outer domain, even when
the eligible hub domain is larger than the active vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_rows_uniform_physical_changes
    (tstar iota:ℝ) (ht:0<tstar) (hi:0 < iota):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U W Z Γ Color:Type) [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
      [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z],
    ∀ (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
      (hcomm:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
      (t p k:ℝ) (q:Z→Γ→ℝ) (s:Z→Color→ℝ) (a:Γ) (j:Color)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    iota*Fintype.card V≤(Fintype.card W:ℝ) → tstar≤t →
    (∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d τ e)→markedPairPhysical π e∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    let σloc:=rawMarkedRestrictPair f g σ
    let τloc:=rawMarkedRestrictPair f g τ
    let Hloc:=fun b v u=>H b (f v) (g u)
    let Hloc':=fun b v u=>H' b (f v) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a j ((tstar/16)*Fintype.card W) σloc Hloc →
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a j ((t/8)*Fintype.card W) τloc Hloc' := by
  let ζlocal:=tstar/32
  let ζcap:=iota*ζlocal
  have hlocal:0<ζlocal:=by dsimp [ζlocal];positivity
  have hcap:0<ζcap:=mul_pos hi hlocal
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U W Z Γ Color _ _ _ _ _ _ _ _ _ _ f g π ρ hcomm P d t p k q s a j σ τ H H' FR FS
    hsize htt hR hS hFR hFS σloc τloc Hloc Hloc' hrows
  let fg:W⊕Z↪V⊕U:=Function.Embedding.sumMap f.toEmbedding g
  obtain ⟨hRloc,hSloc⟩:=marked_physical_changes_restrict f g π ρ hcomm P d σ τ H H' FR FS hR hS
  obtain ⟨hFRloc,hFSloc⟩:=marked_local_change_degree_scale f.toEmbedding fg FR FS iota ζ ζlocal hlocal.le hsize hζcap hFR hFS
  have hn:(0:ℝ)≤Fintype.card W:=Nat.cast_nonneg _
  have hδ:0≤ζlocal*Fintype.card W:=mul_nonneg hlocal.le hn
  have hh:=marked_rows_after_physical_change (P.comap f) ρ d 1 Finset.univ p k q s a j
    ((tstar/16)*Fintype.card W) (ζlocal*Fintype.card W) (ζlocal*Fintype.card W) hδ hδ
    σloc τloc Hloc Hloc' hrows (FR.comap f) (FS.comap fg) hRloc hSloc hFRloc (fun u=>hFSloc (Sum.inr u))
  have hBudget:(tstar/16)*Fintype.card W+1*(ζlocal*Fintype.card W+ζlocal*Fintype.card W)≤
      (t/8)*Fintype.card W:=by
    dsimp [ζlocal]
    nlinarith [mul_le_mul_of_nonneg_right htt hn]
  intro S T J hS hT hJ hinj
  exact (hh S T J hS hT hJ hinj).trans_le (by simpa only [Nat.cast_one] using hBudget)
end Oberwolfach
