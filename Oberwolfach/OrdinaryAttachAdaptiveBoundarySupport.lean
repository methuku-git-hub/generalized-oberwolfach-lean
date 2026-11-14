module

public import Oberwolfach.BoundaryReserveSupportEvent
public import Oberwolfach.FiniteLawAttachConditionalEvent
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Attach uniform boundary-reserve support tests to any existing event
on the same ambient coins, after the boundary host has been chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_adaptive_boundary_support (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
      (B:(Σ _ : Ω,Sym2 (V⊕U)→Bool)→Prop) (Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
      (X:Ω→Finset V) (Z:Ω→Finset U) (p:ℝ) (hp:0≤p) (hp1:p≤1),
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1);
    1-e≤(μ.sigma (fun _=>law)).probability B→(∀z,B z→E z.1)→
    1-(e+1/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>law)).probability
      (fun z=>B z∧BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q z.1) (H z.1) (X z.1) (Z z.1)) p ε z.2):=by
  obtain ⟨N,hN⟩:=boundary_reserve_support_high_probability ε hε q
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E e B Q H X Z p hp hp1 law hB hBE
  let δ:ℝ:=1/(Fintype.card (V⊕U):ℝ)^q
  let Good:=fun s σ=>BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q s) (H s) (X s) (Z s)) p ε σ
  have hs:∀s,E s→1-δ≤law.probability (Good s):=by
    intro s _
    exact hN (V⊕U) hn (ordinaryBoundaryGraph (Q s) (H s) (X s) (Z s)) p hp hp1
  exact finiteLaw_attach_conditional_event μ (fun _=>law) E B Good e δ (by positivity) hB hBE hs
end Oberwolfach
