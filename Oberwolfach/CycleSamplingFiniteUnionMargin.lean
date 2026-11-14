module

public import Oberwolfach.CycleSamplingTailMargins

@[expose] public section
/-! The fixed family of vertex and ordered-pair tests has a small total
failure bound once each displayed pointwise estimate is available. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_sampling_finite_union_margin (c b:ℝ) (hc:0<c) (hb:0<b):
    ∃ N:ℕ,∀ (V:Type) [Fintype V],N≤Fintype.card V→
    ∀ (S:Finset (V×V)) (errV:V→ℝ) (errP:V×V→ℝ),
    (∀ v,errV v≤2*Real.exp (-c*(Fintype.card V:ℝ)^2))→
    (∀ z∈S,errP z≤Real.exp (-b*Fintype.card V))→
    (∑ v,errV v)+(∑ z∈S,errP z)<1 := by
  obtain ⟨N,hN⟩:=cycle_sampling_union_error_small c b hc hb
  refine ⟨N,?_⟩
  intro V _ hn S errV errP hV hP
  have hv: (∑ v,errV v)≤2*(Fintype.card V:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^2):=by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun v _=>hV v)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hh
  have hs:(S.card:ℝ)≤(Fintype.card V:ℝ)^2:=by
    have hh:S.card≤Fintype.card (V×V):=Finset.card_le_univ S
    simp only [Fintype.card_prod] at hh
    have hc':(S.card:ℝ)≤(Fintype.card V:ℝ)*(Fintype.card V:ℝ):=by exact_mod_cast hh
    simpa only [pow_two] using hc'
  have hp:(∑ z∈S,errP z)≤(Fintype.card V:ℝ)^2*Real.exp (-b*Fintype.card V):=by
    have hh:=Finset.sum_le_sum (s:=S) hP
    have hh':(∑ z∈S,errP z)≤(S.card:ℝ)*Real.exp (-b*Fintype.card V):=by
      simpa only [Finset.sum_const,nsmul_eq_mul] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)
  have hf:=hN (Fintype.card V) hn
  linarith only [hv,hp,hf]
end Oberwolfach
