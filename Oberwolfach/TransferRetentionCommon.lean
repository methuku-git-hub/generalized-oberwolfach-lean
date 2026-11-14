module

public import Oberwolfach.TransferPhysicalRetention
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! The physical survival event is simultaneous over a fixed family of
potential roots, even when the candidate graphs depend on a first exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U J : Type*} [Fintype V] [DecidableEq V] [Fintype J]

theorem transferSurvivalSum_common_event
    (r : ℕ) (hr : 3 ≤ r) (P F : SimpleGraph V) (H : J → V → U → Prop)
    (v : J → V) (u u' : J → U) (hn : 0<Fintype.card V)
    (μ : Sym2 V → FiniteLaw Bool) (p t : ℝ) (c : J → ℝ)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : ∀ j,c j*(Fintype.card V:ℝ)^(r^2)≤
      Fintype.card (OrdinaryTransferConfiguration hr P F (H j) (v j) (u j) (u' j))) :
    1-Fintype.card J*(2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ j,
        p^((1+2*r)*r)*c j-t<transferSurvivalSum r hr P F (H j) (v j) (u j) (u' j) σ) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) (Finset.univ : Finset J)
    (fun j σ=>transferSurvivalSum r hr P F (H j) (v j) (u j) (u' j) σ≤p^((1+2*r)*r)*c j-t)
    (fun _=>2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)))
    (fun j _=>transferSurvivalSum_lower_tail r hr P F (H j) (v j) (u j) (u' j) hn μ p (c j) t hp hp1 ht hprob (hmany j))
  simpa only [Finset.mem_univ,forall_const,not_le,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] using hh

theorem transferSurvivalSum_two_exposures {Ω : Type*} [Fintype Ω]
    (r : ℕ) (hr : 3 ≤ r) (P F : SimpleGraph V) (H : Ω → J → V → U → Prop)
    (v : J → V) (u u' : J → U) (hn : 0<Fintype.card V)
    (ν : FiniteLaw Ω) (Good : Ω → Prop) (b : ℝ) (hgood : 1-b≤ν.probability Good)
    (μ : Sym2 V → FiniteLaw Bool) (p t : ℝ) (c : J → ℝ)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : ∀ ω,Good ω → ∀ j,c j*(Fintype.card V:ℝ)^(r^2)≤
      Fintype.card (OrdinaryTransferConfiguration hr P F (H ω j) (v j) (u j) (u' j))) :
    1-b-Fintype.card J*(2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)))≤
      (ν.prod (FiniteLaw.pi μ)).probability (fun z=>Good z.1 ∧ ∀ j,
        p^((1+2*r)*r)*c j-t<transferSurvivalSum r hr P F (H z.1 j) (v j) (u j) (u' j) z.2) := by
  have hh := finiteLaw_product_good_lower ν (FiniteLaw.pi μ) Good
    (fun ω σ=>∀ j,p^((1+2*r)*r)*c j-t<transferSurvivalSum r hr P F (H ω j) (v j) (u j) (u' j) σ)
    b (Fintype.card J*(2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V))))
    (by positivity) hgood
    (fun ω hω=>transferSurvivalSum_common_event r hr P F (H ω) v u u' hn μ p t c hp hp1 ht hprob (hmany ω hω))
  convert hh using 1 <;> congr!

end Oberwolfach
