module

public import Oberwolfach.OrdinaryAdaptiveReserveExtraEvent
public import Oberwolfach.BoundaryReserveSupportEvent

@[expose] public section
/-! The adaptive reserve, its support concentration, and a further
conditionally likely event use the same fresh physical-edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_reserve_support_and_extra (q:ℕ) (ε εs:ℝ) (hε:0<ε) (hεs:0<εs):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),
      1-e₀≤μ.probability E →
      ∀(Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (I:Ω→Finset V) (J:Ω→Finset U)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      ∀(Extra:Ω→(Sym2 (V⊕U)→Bool)→Prop) (δ:ℝ),0≤δ→
      (∀ω,E ω→1-δ≤ν.probability (Extra ω))→
      1-(e₀+2/(Fintype.card (V⊕U):ℝ)^q+δ)≤
        (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
          OrdinaryBoundaryReserveGood (Q z.1) (H z.1) (I z.1) (J z.1) τ ε z.2 ∧
          BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q z.1) (H z.1) (I z.1) (J z.1)) τ εs z.2 ∧ Extra z.1 z.2):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_boundary_reserve_with_extra_event q ε hε
  obtain ⟨Ns,hNs⟩:=boundary_reserve_support_high_probability εs hεs q
  refine ⟨max N Ns,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E e₀ hE Q H I J τ hτ hτ1 ν Extra δ hδ hExtra
  let δs:ℝ:=1/(Fintype.card (V⊕U):ℝ)^q
  have hδs:0≤δs:=by dsimp [δs];positivity
  let Extra':Ω→(Sym2 (V⊕U)→Bool)→Prop:=fun ω σ=>
    BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q ω) (H ω) (I ω) (J ω)) τ εs σ ∧ Extra ω σ
  have hc:∀ω,E ω→1-(δs+δ)≤ν.probability (Extra' ω):=by
    intro ω hω
    have ha:=hNs (V⊕U) (by omega) (ordinaryBoundaryGraph (Q ω) (H ω) (I ω) (J ω)) τ hτ hτ1
    have hb:=hExtra ω hω
    have hi:=finiteLaw_good_intersection ν
      (BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q ω) (H ω) (I ω) (J ω)) τ εs) (Extra ω) δ hb
    change 1-δs≤_ at ha
    change _≤ν.probability (Extra' ω) at hi
    linarith
  have hh:=hN V U Ω (by omega) μ E e₀ hE Q H I J τ hτ hτ1 Extra' (δs+δ) (by linarith) hc
  have heq:2/(Fintype.card (V⊕U):ℝ)^q=δs+δs:=by dsimp [δs];ring
  rw [heq]
  convert hh using 1 <;> try ring
end Oberwolfach
