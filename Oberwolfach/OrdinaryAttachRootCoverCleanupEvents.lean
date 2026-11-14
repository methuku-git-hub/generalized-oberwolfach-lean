module

public import Oberwolfach.OrdinaryRootCoverCleanupParentCounts
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

theorem ordinary_attach_root_cover_cleanup_events (βe βh p:ℝ)
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
    (∀a,E a→OrdinaryCleanupParentProfiles (P a) (Q a) (F a) (H a) π d (X a) (Z a)
      pR pH density tR tH L βe₀ βh₀ s j (raw a))→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    1-(e+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>ν)).probability (fun z=>B z ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_local_events_high_probability βe βh p hβe hβh hp hp1 q
  refine ⟨N,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e B ν hB hBE P Q F H π d X T Z W r η ell D
    pR pH density tR tH L βe₀ βh₀ s j raw hprofile hmE hmH
  let δ:ℝ:=2/(Fintype.card (V⊕U):ℝ)^q
  let Good:=fun a σ=>OrdinaryBoundaryExtensionGood (Q a\(D a).rim)
      (fun v u=>H a v u∧¬(D a).spokes v u) (X a) βe p σ ∧
    OrdinaryBoundaryHubPairGood (fun v u=>H a v u∧¬(D a).spokes v u) (Z a) βh p σ
  have hconditional:∀a,E a→1-δ≤ν.probability (Good a):=by
    intro a ha
    have hcounts:=ordinary_root_cover_cleanup_parent_counts (P a) (Q a) ⊥ (F a) (H a) π d
      (X a) (T a) (Z a) (W a) r η ell (D a) pR pH density tR tH L βe₀ βh₀ βe βh s j (raw a)
      (hprofile a ha) bot_le hmE hmH
    apply hN V U hn (Q a\(D a).rim) (fun v u=>H a v u∧¬(D a).spokes v u) (X a) (Z a)
    intro x y u
    convert hcounts.1 x y u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact finiteLaw_attach_conditional_event μ (fun _=>ν) E B Good e δ (by positivity) hB hBE hconditional
end Oberwolfach
