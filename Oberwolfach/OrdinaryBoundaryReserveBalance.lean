module

public import Oberwolfach.BoundaryReserveDegreeEvent
public import Oberwolfach.OrdinaryPhysicalDegreeDomains

@[expose] public section
/-! Fresh physical boundary-edge retention preserves all rim/spoke balance
errors up to a uniform additive deviation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_reserve_balance_high_probability (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    let G:=ordinaryBoundaryGraph Q H I J;
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (fun σ=>let G':=retainedGraph G σ;
          ∀v:V,|(((G'.comap Sum.inl).degree v:ℝ)-
            2*(Finset.univ.filter (fun u=>G'.Adj (Sum.inl v) (Sum.inr u))).card)-
            τ*((G.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).card)|
              <3*ε*Fintype.card (V⊕U)):=by
  obtain ⟨N,hN⟩:=retained_degree_domains_common_event q ε hε
  refine ⟨max 2 N,?_⟩
  intro V U _ _ _ _ hn Q H I J τ hτ hτ1 G
  let A:Fin 2→Finset (V⊕U):=fun i=>if i=0 then ordinaryPhysicalRimDomain else ordinaryPhysicalHubDomain
  have hsize:2≤Fintype.card (V⊕U):=by omega
  have h:=hN (V⊕U) (by omega) G 2 hsize A τ hτ hτ1
  apply h.trans
  apply finiteLaw_probability_mono
  intro σ hσ G' v
  have hleft:=hσ (0:Fin 2) (Sum.inl v)
  have hright:=hσ (1:Fin 2) (Sum.inl v)
  simp only [A,ite_true,show (1:Fin 2)≠0 by decide,ite_false] at hleft hright
  rw [ordinary_physical_left_degree,ordinary_physical_left_degree] at hleft
  rw [ordinary_physical_right_degree,ordinary_physical_right_degree] at hright
  let x:ℝ:=((G'.comap Sum.inl).degree v:ℝ)-τ*(G.comap Sum.inl).degree v
  let y:ℝ:=((Finset.univ.filter (fun u=>G'.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)-
    τ*(Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).card
  have htri:|x-2*y|≤|x|+2*|y|:=by
    have ht:=abs_sub x (2*y)
    simpa only [abs_mul,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)] using ht
  have hbound:|x-2*y|<3*ε*Fintype.card (V⊕U):=by
    dsimp [x,y] at *
    linarith only [htri,hleft,hright]
  have heq:(((G'.comap Sum.inl).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>G'.Adj (Sum.inl v) (Sum.inr u))).card)-
      τ*((G.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).card)=x-2*y:=by
    dsimp [x,y];ring
  rw [heq]
  exact hbound
end Oberwolfach
