module

public import Oberwolfach.BoundarySupportEvent

@[expose] public section
/-! Uniform physical neighborhood and codegree concentration on the fresh
reserve sample, with the whole physical vertex set as both fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

def BoundaryReserveSupportGood (G:SimpleGraph W) (τ ε:ℝ) (σ:Sym2 W→Bool):Prop:=
  (∀x,|(((Finset.univ:Finset W)∩(retainedGraph G σ).neighborFinset x).card:ℝ)-
      τ*((Finset.univ:Finset W)∩G.neighborFinset x).card|<ε*Fintype.card W) ∧
  (∀x y,x≠y→
    |((((Finset.univ:Finset W)∩(retainedGraph G σ).neighborFinset x)∩
      ((Finset.univ:Finset W)∩(retainedGraph G σ).neighborFinset y)).card:ℝ)-
      τ^2*(((Finset.univ:Finset W)∩G.neighborFinset x)∩
        ((Finset.univ:Finset W)∩G.neighborFinset y)).card|<ε*Fintype.card W) ∧
  (∀v∈(Finset.univ:Finset W),|(((Finset.univ:Finset W).filter
      (fun x=>v∈(Finset.univ:Finset W)∩(retainedGraph G σ).neighborFinset x)).card:ℝ)-
      τ*((Finset.univ:Finset W)∩G.neighborFinset v).card|<ε*Fintype.card W)

theorem boundary_reserve_support_high_probability (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃N:ℕ,∀(W:Type) [Fintype W] [DecidableEq W],N≤Fintype.card W→
      ∀(G:SimpleGraph W) (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      1-1/(Fintype.card W:ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 W=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
          (BoundaryReserveSupportGood G τ ε):=by
  obtain ⟨N,hN⟩:=fresh_boundary_support_common_event ε hε q
  exact ⟨N,fun W _ _ hn G τ hτ hτ1=>hN W hn G Finset.univ Finset.univ τ hτ hτ1⟩
end Oberwolfach
