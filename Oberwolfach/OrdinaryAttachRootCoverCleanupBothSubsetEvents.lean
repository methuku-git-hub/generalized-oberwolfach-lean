module

public import Oberwolfach.OrdinaryAttachRootCoverCleanupSubsetEvents
public import Oberwolfach.OrdinaryRootCoverSubsetCounts
public import Oberwolfach.OrdinaryBoundaryLocalEvents
public import Oberwolfach.FiniteLawAttachConditionalEvent

@[expose] public section
/-! Attach the adaptive post-cover cleanup tests to an existing event on
the very same ambient physical-edge coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_root_cover_cleanup_both_subset_events (βe βh p:ℝ)
    (hβe:0<βe) (hβh:0<βh) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃N:ℕ,∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (B:(Σ _ : Ω, Sym2 (V⊕U)→Bool)→Prop),
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-e≤(μ.sigma (fun _=>ν)).probability B→(∀z,B z→E z.1)→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (r:ℕ) (η ell:ℝ)
      (D:∀a,OrdinaryRootCoverData (Q a) (F a) (H a) (X a) (T a) (Z a) (W a) r η ell)
      (pR pH density tR tH L βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    (∀a,E a→((T a).card:ℝ)≤(βe/2)*Fintype.card (V⊕U))→
    (∀a,E a→OrdinaryCleanupParentProfiles (P a) (Q a) (F a) (H a) π d (X a) (Z a)
      pR pH density tR tH L βe₀ βh₀ s j (raw a))→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    1-(e+3/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>ν)).probability (fun z=>
      (B z ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1\T z.1) (βe/2) p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2) ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1\W z.1) (βh/2) p z.2):=by
  obtain ⟨N₁,hN₁⟩:=ordinary_attach_root_cover_cleanup_subset_events βe βh p hβe hβh hp hp1 q
  obtain ⟨N₂,hN₂⟩:=ordinary_boundary_hub_pair_retention_event (βh/2) p (by positivity) hp hp1 q
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e B ν hB hBE P Q F H π d X T Z W r η ell D
    pR pH density tR tH L βe₀ βh₀ s j raw hT hprofile hmE hmH
  let B' := fun z:(Σ _ : Ω, Sym2 (V⊕U)→Bool)=> B z ∧
    OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
      (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1\T z.1) (βe/2) p z.2 ∧
    OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2
  let G := fun a σ=>OrdinaryBoundaryHubPairGood
    (fun v u=>H a v u∧¬(D a).spokes v u) (Z a\W a) (βh/2) p σ
  have hB':1-(e+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>ν)).probability B':=by
    exact hN₁ V U Γ Color Ω (le_trans (le_max_left _ _) hn) μ E e B hB hBE P Q F H π d X T Z W r η ell D
      pR pH density tR tH L βe₀ βh₀ s j raw hT hprofile hmE hmH
  have hG:∀a,E a→1-1/(Fintype.card (V⊕U):ℝ)^q≤ν.probability (G a):=by
    intro a _
    exact hN₂ V U (le_trans (le_max_right _ _) hn)
      (fun v u=>H a v u∧¬(D a).spokes v u) (Z a\W a)
  have hh:=finiteLaw_attach_conditional_event μ (fun _=>ν) E B' G
    (e+2/(Fintype.card (V⊕U):ℝ)^q) (1/(Fintype.card (V⊕U):ℝ)^q)
    (by positivity) hB' (by intro z hz; exact hBE z hz.1) hG
  convert hh using 1 <;> ring
end Oberwolfach
