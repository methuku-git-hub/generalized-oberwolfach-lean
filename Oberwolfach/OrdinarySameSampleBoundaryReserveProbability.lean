module

public import Oberwolfach.OrdinarySameSampleBoundaryReserve
public import Oberwolfach.OrdinaryAdaptiveBoundaryReserve

@[expose] public section
/-! After the original sample and its edited completion host are chosen,
the fresh boundary reserve is good with high probability on that same
outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_boundary_reserve_high_probability
    (q₀:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E →
    ∀(P F:SimpleGraph V) (Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
      (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (J:Finset U)
      (pR pH tR tH e L:ℝ) (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hL:0≤L)
      (s:U→Color→ℝ) (j:Color) (sample:Ω→RawWheelOutcome V U Γ Color),
    (∀ω,E ω→RawOrdinaryRows P π d 2 I pR s j tR (sample ω)) →
    (∀ω,E ω→RawOrdinaryDomainIndices F π d 3 J pH j tH (sample ω)) →
    (∀v,|pR*(P.neighborFinset v∩I).card-2*pH*J.card|≤e) →
    (∀ω,E ω→∀v,((changed ((Q ω).neighborFinset v) ((rawWheelGraph P (sample ω)).neighborFinset v)).card:ℝ)≤L) →
    (∀ω,E ω→∀v,((changed (Finset.univ.filter (H ω v)) (Finset.univ.filter (rawWheelSpokes π d (sample ω) j v))).card:ℝ)≤L) →
    (∀ω,E ω→∀v,(Q ω).degree v=2*(Finset.univ.filter (H ω v)).card) →
    ∀(τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
    1-(e₀+1/(Fintype.card (V⊕U):ℝ)^q₀)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        OrdinaryBoundaryReserveReadyProperty (Q z.1) (H z.1) I J τ ε (e+tR+2*tH+3*L) (e+tR+2*tH+3*L) z.2):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_boundary_reserve_high_probability q₀ ε hε
  refine ⟨N,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e₀ hE P F Q H π d I J pR pH tR tH e L htR htH he hL s j sample
    hrows hcols hparent hrim hspoke hQbal τ hτ hτ1 ν
  have h:=hN V U Ω hn μ E e₀ hE Q H (fun _=>I) (fun _=>J) τ hτ hτ1
  apply h.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  exact ordinary_same_sample_profiles_boundary_reserve P F (Q z.1) (H z.1) π d I J pR pH tR tH e L
    htR htH he hL s j (sample z.1) (hrows z.1 hz.1) (hcols z.1 hz.1) hparent
    (hrim z.1 hz.1) (hspoke z.1 hz.1) (hQbal z.1 hz.1) τ ε hτ z.2 hz.2
end Oberwolfach
