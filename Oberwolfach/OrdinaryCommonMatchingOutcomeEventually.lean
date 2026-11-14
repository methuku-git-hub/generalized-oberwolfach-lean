module

public import Oberwolfach.OrdinaryCombinedFailureEventually
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! The complete displayed error budget permits a single positive-mass
    outcome once the two domains are sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_common_matching_outcome_eventually
    (K B t εprior ζ : ℝ) (d : ℕ) (hK : 0≤K) (hB : 0<B) (ht : 0<t)
    (hbudget : εprior+ζ<1) :
    ∃ N : ℕ, ∀ n m u : ℕ, N≤n → N≤m → (u:ℝ)≤K*m →
    ∀ (Ω : Type) [Fintype Ω] (μ : FiniteLaw Ω) (E : Ω→Prop),
      1-εprior-ζ-((1/(n:ℝ)+3/(n:ℝ)^2)+3/(m:ℝ)+1/(n:ℝ)+1/(m:ℝ)+
        1/(n:ℝ)+(1/(n:ℝ)+2/(n:ℝ)^2)+
        (m:ℝ)*u*(2*Real.exp (-2*t^2 /
          ((4*(d:ℝ)+3)^2*((3:ℝ)^4*B/m)*(2*3)*((3:ℝ)^2*B))))) ≤ μ.probability E →
      ∃z,0<μ.mass z ∧ E z := by
  have hε : 0<1-(εprior+ζ) := by linarith
  obtain ⟨N,hN⟩:=ordinary_combined_failure_eventually_small K B t (1-(εprior+ζ)) d hK hB ht hε
  refine ⟨N,?_⟩
  intro n m u hn hm hu Ω _ μ E hprob
  have hfail:=hN n m u hn hm hu
  apply finiteLaw_positive_event_exists μ E
  linarith
end Oberwolfach
