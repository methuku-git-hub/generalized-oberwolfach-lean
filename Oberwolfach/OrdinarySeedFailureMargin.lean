module

public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! The explicit ordinary seed concentration failure tends to zero for
fixed parameters, uniformly over hub sets of size at most n. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach

theorem eventually_ordinary_seed_failure_below
    (d m:ℕ) (B t δ:ℝ) (hB:0<B) (ht:0<t) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
    (Fintype.card ((Fin n×Fin n)⊕(Fin n×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))<δ:=by
  let A:ℝ:=(8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)
  have hA:0<A:=by dsimp [A];positivity
  let c:ℝ:=2*t^2/A
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_any_polynomial_exponential_failure_below 2 c δ 3 hc hδ
  refine ⟨max N 4,?_⟩
  intro n hn U _ hu
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn4:4≤n:=le_trans (le_max_right _ _) hn
  have hnpos:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hcard:(Fintype.card ((Fin n×Fin n)⊕(Fin n×U)):ℝ)≤(n:ℝ)^3:=by
    have hnat:Fintype.card ((Fin n×Fin n)⊕(Fin n×U))≤n^3:=by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      nlinarith
    exact_mod_cast hnat
  have hexp:-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)) = -c*(n:ℝ):=by
    dsimp [c,A]
    field_simp
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right hcard (show 0≤2*Real.exp (-c*(n:ℝ)) by positivity)
  have hh:=hN n hnN
  nlinarith
end Oberwolfach
