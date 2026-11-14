module

public import Oberwolfach.OrdinaryAttachRootCoverCleanupBothSubsetEvents
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

theorem ordinary_attach_root_cover_cleanup_both_subset_events_at_rate (βe βh p:ℝ)
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
    1-(e+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>ν)).probability (fun z=>
      (B z ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1\T z.1) (βe/2) p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2) ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1\W z.1) (βh/2) p z.2):=by
  obtain ⟨N,hN⟩:=ordinary_attach_root_cover_cleanup_both_subset_events βe βh p hβe hβh hp hp1 (q+1)
  refine ⟨max 2 N,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e B ν hB hBE P Q F H π d X T Z W r η ell D
    pR pH density tR tH L βe₀ βh₀ s j raw hT hprofile hmE hmH
  have hn2:(2:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast (le_trans (le_max_left 2 N) hn)
  have hnpos:0<(Fintype.card (V⊕U):ℝ):=by linarith
  have hpw:0<(Fintype.card (V⊕U):ℝ)^q:=pow_pos hnpos _
  have hfrac:3/(Fintype.card (V⊕U):ℝ)^(q+1)≤2/(Fintype.card (V⊕U):ℝ)^q:=by
    rw [pow_succ]
    apply (div_le_div_iff₀ (mul_pos hpw hnpos) hpw).2
    have hm:=mul_le_mul_of_nonneg_left (show (3:ℝ)≤2*Fintype.card (V⊕U) by linarith) hpw.le
    nlinarith only [hm]
  have hh:=hN V U Γ Color Ω (le_trans (le_max_right 2 N) hn) μ E e B hB hBE
    P Q F H π d X T Z W r η ell D pR pH density tR tH L βe₀ βh₀ s j raw hT hprofile hmE hmH
  linarith only [hh,hfrac]
end Oberwolfach
