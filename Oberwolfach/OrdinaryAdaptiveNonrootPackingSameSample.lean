module

public import Oberwolfach.OrdinaryUnreservedNearParentFixedCut

@[expose] public section
/-! Apply near-balance packing on domains selected from the same outcome.
The domain types themselves may depend on the sampled root sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_nonroot_packing_on_parent_event (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀γ:ℝ,0<γ→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(T:Ω→Finset V) (W:Ω→Finset U),
    let Vf:=fun s=>↥(Finset.univ\T s);let Uf:=fun s=>↥(Finset.univ\W s);
    ∀(P Q F:∀s,SimpleGraph (Vf s)) (H:∀s,Vf s→Uf s→Prop)
      (X:∀s,Finset (Vf s)) (Z:∀s,Finset (Uf s)) (σ:∀s,Sym2 (Vf s⊕Uf s)→Bool)
      (β₀ h ε₀ ξ ζ p ε f b c:ℝ),
    hpack≤h-ξ-ζ→
    (∀s,E s→n₀≤Fintype.card (Vf s))→
    (∀s,E s→Nonempty (OrdinaryUnreservedNearParentData r hr k α ω β₀ β bminus bplus h δ
      ε₀ εstar η ξ ζ p ε f b c (P s) (Q s) (F s) (H s) (X s) (Z s) (σ s)))→
    1-e≤μ.probability (fun s=>E s ∧
      Nonempty (OrdinaryUnreservedPackingData (Q s) (F s) (H s) (X s) (Z s)
        (retainedGraph (ordinaryBoundaryGraph (Q s) (H s) (X s) (Z s)) (σ s)) r
        (γ*Fintype.card (Vf s⊕Uf s)))):=by
  obtain ⟨N,hN⟩:=ordinary_unreserved_near_balance_packing r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hε,hpack_rule⟩:=hN k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro γ hγ
  obtain ⟨η,hη,n₀,hn₀⟩:=hpack_rule γ hγ
  refine ⟨η,hη,n₀,?_⟩
  intro V U Ω _ _ _ _ _ μ E e hE T W Vf Uf P Q F H X Z σ β₀ h ε₀ ξ ζ p ε f b c hcut hsize hparent
  apply hE.trans
  apply finiteLaw_probability_mono
  intro s hs
  obtain ⟨d⟩:=hparent s hs
  obtain ⟨D⟩:=ordinary_unreserved_near_parent_packing_data_fixed_cut r hr k α ω β₀ β bminus bplus h hpack δ
    ε₀ εstar η ξ ζ p ε f b c (P s) (Q s) (F s) (H s) (X s) (Z s) (σ s) hcut d
  exact ⟨hs,hn₀ (Vf s) (Uf s) (hsize s hs) (P s) (Q s) (F s) (H s) (X s) (Z s)
    (retainedGraph (ordinaryBoundaryGraph (Q s) (H s) (X s) (Z s)) (σ s)) D⟩
end Oberwolfach
