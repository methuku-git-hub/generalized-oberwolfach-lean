module

public import Oberwolfach.OrdinaryPackingCleanupSampleInputs

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

theorem ordinary_packing_cleanup_on_sample_event (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν:ℝ,0<p→0<βe→0<βh→0<ν→
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (σ:Ω→Sym2 (V⊕U)→Bool)
      (β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit:ℝ),
    hpack≤h-ξ-ζ→
    (∀a,E a→OrdinaryPackingCleanupSampleInputs r hr k d α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε b c
      pR pH density tR tH Ledit βe βh L (P a) (Q a) (F a) (H a) π (X a) (Z a) s j (raw a) (σ a))→
    1-e≤μ.probability (fun a=>E a ∧
      let R:=retainedGraph (ordinaryBoundaryGraph (Q a) (H a) (X a) (Z a)) (σ a);
      ∃M:OrdinaryUnreservedPackingData (Q a) (F a) (H a) (X a) (Z a) R r (τ*Fintype.card (V⊕U)),
      Nonempty (OrdinaryOutsideCleanupData
        (ordinaryPackingPostRim (Q a) (F a) (H a) (X a) (Z a) R r (τ*Fintype.card (V⊕U)) M) (F a)
        (ordinaryPackingPostSpokes (Q a) (F a) (H a) (X a) (Z a) R r (τ*Fintype.card (V⊕U)) M) (X a) (Z a)
        (ordinaryPackingUsedGraph (Q a) (F a) (H a) (X a) (Z a) R r (τ*Fintype.card (V⊕U)) M) r
        (ν*Fintype.card (V⊕U)))):=by
  obtain ⟨N,hN⟩:=ordinary_unreserved_near_balance_packing r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hε,hpack_rule⟩:=hN k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro p βe βh ν hp hβe hβh hν
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_sampled_cleanup_after_packing r hr p βe βh ν hp hβe hβh hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨Nclean,hclean⟩:=hcleanup L hL
  obtain ⟨η,hη,Npack,hpack'⟩:=hpack_rule τ hτ
  refine ⟨η,hη,max Nclean Npack,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e hE P Q F H π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinputs
  have hnV:Npack≤Fintype.card V:=by omega
  have hnW:Nclean≤Fintype.card (V⊕U):=by
    have hh:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    omega
  apply hE.trans
  apply finiteLaw_probability_mono
  intro a ha
  have hdata:=hinputs a ha
  obtain ⟨parent⟩:=hdata.parent
  obtain ⟨D⟩:=ordinary_unreserved_packing_data_fixed_cut r hr k α ω β₀ β bminus bplus h hpack δ
    ε₀ εstar η ξ ζ p ε b c (P a) (Q a) (F a) (H a) (X a) (Z a) (σ a) hcut parent
  obtain ⟨M⟩:=hpack' V U hnV (P a) (Q a) (F a) (H a) (X a) (Z a)
    (retainedGraph (ordinaryBoundaryGraph (Q a) (H a) (X a) (Z a)) (σ a)) D
  have hc:=hclean V U Γ Color hnW (P a) (Q a) (F a) (H a) π d (X a) (Z a) pR pH density tR tH Ledit
    s j (raw a) (σ a) hdata.cleanup_profile hdata.conflict_degree hdata.balanced hdata.divisible
    hdata.extensions hdata.hub_pairs M
  exact ⟨ha,M,hc⟩
end Oberwolfach
