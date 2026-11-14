module

public import Oberwolfach.MarkedRimCapacityEvent

@[expose] public section

/-! The order threshold precedes the graph, reference degree and actual
sampling densities. The exponential constant is fixed by their positive
lower bounds and the prescribed error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRim_uniform_capacity_event
    (ε γ pstar : ℝ) (hε : 0<ε) (hγ : 0<γ) (hpstar : 0<pstar) (b : ℕ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V)
      (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p →
    ∀ D δP : ℝ,0≤δP → δP≤ε/4 →
      (∀ x,|(P.degree x:ℝ)-D|≤δP*Fintype.card V) →
      (∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ)) →
    1-20*(Fintype.card V:ℝ)^2*Real.exp (-min (ε^2/2) (γ^2*pstar^4/16)*Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>(∀ a x,
        |((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
        |((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V) ∧
        ∀ x y,x≠y →3/2*γ*p^2*Fintype.card V≤
        ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π b σ false x z ∧
          0<markedPhysicalRim P π b σ false z y)).card:ℝ)) := by
  let N := max 1 (max (Nat.ceil (4*(2*(b:ℝ)+1)/ε))
    (Nat.ceil (8*(2*(b:ℝ)+1)/(γ*pstar^2))))
  refine ⟨N,?_⟩
  intro V _ _ hn P π p k hp hk hsum hlo D δP hδ hδε hPreg hP
  have hn1 : 1≤Fintype.card V := by dsimp [N] at hn;omega
  have hD : 4*(2*(b:ℝ)+1)/ε≤(Fintype.card V:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (4*(2*(b:ℝ)+1)/ε)≤Fintype.card V by dsimp [N] at hn;omega))
  have hR : 8*(2*(b:ℝ)+1)/(γ*pstar^2)≤(Fintype.card V:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (8*(2*(b:ℝ)+1)/(γ*pstar^2))≤Fintype.card V by dsimp [N] at hn;omega))
  have hD' := (div_le_iff₀ hε).mp hD
  have hR' := (div_le_iff₀ (by positivity : 0<γ*pstar^2)).mp hR
  exact markedPhysicalRim_capacity_event P π b p k hp hk hsum D ε δP γ pstar
    hε.le hδ hδε hγ.le hpstar.le hlo hn1 hPreg hP (by linarith only [hD']) (by linarith only [hR'])

end Oberwolfach
