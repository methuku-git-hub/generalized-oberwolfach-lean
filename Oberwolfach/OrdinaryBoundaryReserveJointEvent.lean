module

public import Oberwolfach.OrdinaryBoundaryReserveBalance
public import Oberwolfach.BoundaryReserveMaximumDegree
public import Oberwolfach.TwoCommonEvents

@[expose] public section
/-! The boundary reserve simultaneously has controlled total degree and
controlled rim/spoke balance on one independent physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryBoundaryReserveGood (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (τ ε:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop:=
  let B:=ordinaryBoundaryGraph Q H I J;
  let R:=retainedGraph B σ;
  (∀x,|((R.degree x):ℝ)-τ*B.degree x|<ε*Fintype.card (V⊕U)) ∧
  (∀v:V,|(((R.comap Sum.inl).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card)-
      τ*((B.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card)|
        <3*ε*Fintype.card (V⊕U))

theorem ordinary_boundary_reserve_joint_high_probability (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (OrdinaryBoundaryReserveGood Q H I J τ ε):=by
  obtain ⟨N₁,h₁⟩:=retained_graph_degrees_common_event (q+1) ε hε
  obtain ⟨N₂,h₂⟩:=ordinary_boundary_reserve_balance_high_probability (q+1) ε hε
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U _ _ _ _ hn Q H I J τ hτ hτ1
  let G:=ordinaryBoundaryGraph Q H I J
  let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)
  let E:=fun σ:Sym2 (V⊕U)→Bool=>∀x,|(((retainedGraph G σ).degree x):ℝ)-τ*G.degree x|<ε*Fintype.card (V⊕U)
  let D:=fun σ:Sym2 (V⊕U)→Bool=>∀v:V,|((((retainedGraph G σ).comap Sum.inl).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>(retainedGraph G σ).Adj (Sum.inl v) (Sum.inr u))).card)-
      τ*((G.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).card)|
        <3*ε*Fintype.card (V⊕U)
  have hpE:1-1/(Fintype.card (V⊕U):ℝ)^(q+1)≤μ.probability E:=h₁ (V⊕U) (by omega) G τ hτ hτ1
  have hpD:1-1/(Fintype.card (V⊕U):ℝ)^(q+1)≤μ.probability D:=h₂ V U (by omega) Q H I J τ hτ hτ1
  have hi:=finiteLaw_good_intersection μ E D (1/(Fintype.card (V⊕U):ℝ)^(q+1)) hpD
  have hnpos:0<Fintype.card (V⊕U):=by omega
  have hb:=scaled_inverse_power_le (Fintype.card (V⊕U)) q hnpos 2
    (by exact_mod_cast (show 2≤Fintype.card (V⊕U) by omega))
  have hb':2*(1/(Fintype.card (V⊕U):ℝ)^(q+1))≤1/(Fintype.card (V⊕U):ℝ)^q:=by convert hb using 1 <;> ring
  have hgood:1-1/(Fintype.card (V⊕U):ℝ)^q≤μ.probability (fun σ=>E σ∧D σ):=by linarith only [hi,hpE,hb']
  exact hgood
end Oberwolfach
