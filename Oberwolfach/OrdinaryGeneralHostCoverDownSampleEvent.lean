module

public import Oberwolfach.OrdinaryPackingCleanupSameSampleCapped
public import Oberwolfach.OrdinaryHostCoverDownFromFinish

@[expose] public section
/-! Conditional high-probability packing and sparse cleanup on the same
sample, with the packing constructed before cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_host_coverdown_on_sample_event_capped (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν cap:ℝ,0<p→0<βe→0<βh→0<ν→0<cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (σ:Ω→Sym2 (V⊕U)→Bool)
      (β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit:ℝ),
    hpack≤h-ξ-ζ→
    (∀a,E a→OrdinaryPackingCleanupSampleInputs (m+1) (by omega) k d α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε b c
      pR pH density tR tH Ledit βe βh L (P a) (Q a) (F a) (H a) π (X a) (Z a) s j (raw a) (σ a))→
    ∀(Kcap Dmax:ℕ) (ρ:ℝ),
    (∀a,E a→
      let R:=retainedGraph (ordinaryBoundaryGraph (Q a) (H a) (X a) (Z a)) (σ a);
      ∀(M:OrdinaryUnreservedPackingData (Q a) (F a) (H a) (X a) (Z a) R (m+1) (τ*Fintype.card (V⊕U))),
      let C:=ordinaryPackingUsedGraph (Q a) (F a) (H a) (X a) (Z a) R (m+1) (τ*Fintype.card (V⊕U)) M;
      let Q₁:=ordinaryPackingPostRim (Q a) (F a) (H a) (X a) (Z a) R (m+1) (τ*Fintype.card (V⊕U)) M;
      let H₁:=ordinaryPackingPostSpokes (Q a) (F a) (H a) (X a) (Z a) R (m+1) (τ*Fintype.card (V⊕U)) M;
      ∀(K:OrdinaryOutsideCleanupData Q₁ (F a) H₁ (X a) (Z a) C (m+1) (ν*Fintype.card (V⊕U))),
      let Q₂:=ordinaryCleanupPostRim Q₁ (F a) H₁ (X a) (Z a) C (m+1) (ν*Fintype.card (V⊕U)) K;
      let H₂:=ordinaryCleanupPostSpokes Q₁ (F a) H₁ (X a) (Z a) C (m+1) (ν*Fintype.card (V⊕U)) K;
      OrdinaryGeneralFinishHostResult Q₂ (F a) H₂ (X a) (Z a) m Kcap Dmax ρ)→
    1-e≤μ.probability (fun a=>E a ∧
      OrdinaryGeneralHostCoverDownResult (Q a) (F a) (H a) (X a) (Z a) (m+1)
        (ν*Fintype.card (V⊕U)+2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  obtain ⟨N,hN⟩:=ordinary_packing_cleanup_on_sample_event_capped (m+1) (by omega) α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hε,hmain⟩:=hN k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro p βe βh ν cap hp hβe hβh hν hcap
  obtain ⟨τ,hτ,hτcap,hmain⟩:=hmain p βe βh ν cap hp hβe hβh hν hcap
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨η,hη,n₀,hmain⟩:=hmain L hL
  refine ⟨η,hη,n₀,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e hE P Q F H π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinputs Kcap Dmax ρ hfinish
  have hh:=hmain V U Γ Color Ω hn μ E e hE P Q F H π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinputs
  apply hh.trans
  apply finiteLaw_probability_mono
  intro a ha
  obtain ⟨ha,M,⟨K⟩⟩:=ha
  have hdata:=hinputs a ha
  exact ⟨ha,ordinary_host_coverdown_from_packing_cleanup_finish m (Q a) (F a) (H a) (X a) (Z a)
    (retainedGraph (ordinaryBoundaryGraph (Q a) (H a) (X a) (Z a)) (σ a))
    (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) ρ Kcap Dmax hdata.balanced hdata.divisible M K
    (hfinish a ha M K)⟩
end Oberwolfach
