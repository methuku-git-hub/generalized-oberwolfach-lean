module

public import Oberwolfach.SignedDemandNormalization

@[expose] public section

/-! Real signed corrections with exactly prescribed zero-total degree changes.
The correction is carried by actual edge occurrences and is uniformly bounded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem signedCorrection_marginal {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (q : E → ℝ) (Δ : V → ℝ) (s B : ℝ)
    (hs : 0<s) (hB : 0<B)
    (hq : ∀ v,(∑ e,if f e=v then q e else 0)=(s*occurrenceDegree f v+Δ v)/(B*s))
    (v : V) :
    (∑ e,if f e=v then B*s*q e-s else 0)=Δ v := by
  have he (e : E) : (if f e=v then B*s*q e-s else 0)=
      B*s*(if f e=v then q e else 0)-s*(if f e=v then 1 else 0) := by
    split_ifs <;> ring
  have hD : (∑ e,if f e=v then (1:ℝ) else 0)=occurrenceDegree f v := by
    unfold occurrenceDegree
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,hq,hD]
  change B*s*((s*occurrenceDegree f v+Δ v)/(B*s))-s*occurrenceDegree f v=Δ v
  field_simp [hs.ne',hB.ne']
  <;> ring

set_option maxHeartbeats 800000 in
theorem bounded_signed_degree_correction
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (Δp Δm : V → ℝ)
    (hΔp : ∑ v,Δp v=0) (hΔm : ∑ v,Δm v=0)
    (s B δ ε r h : ℝ) (hs : 0<s) (hB : 1≤B)
    (hn : 0<Fintype.card V) (hδ : 0≤δ) (hδsmall : δ<1/4)
    (hdegp : ∀ v,|occurrenceDegree tail v-(Fintype.card E : ℝ)/Fintype.card V|≤ε)
    (hdegm : ∀ v,|occurrenceDegree head v-(Fintype.card E : ℝ)/Fintype.card V|≤ε)
    (herrorp : ∀ v,|Δp v|≤r) (herrorm : ∀ v,|Δm v|≤r)
    (hsmall : s*ε+r ≤ δ*s*((Fintype.card E : ℝ)/Fintype.card V))
    (hMC : (Fintype.card E : ℝ)/B ≤ h*Fintype.card V*Fintype.card V/2)
    (hlarge : ∀ (S T : Finset V),
      1-2*δ < (S.card : ℝ)/Fintype.card V+(T.card : ℝ)/Fintype.card V →
      h*Fintype.card V*Fintype.card V*
        min ((S.card : ℝ)/Fintype.card V) ((T.card : ℝ)/Fintype.card V) ≤
        ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card : ℝ)) :
    ∃ u : E → ℝ,(∀ e,|u e|≤B*s) ∧
      (∀ v,(∑ e,if tail e=v then u e else 0)=Δp v) ∧
      (∀ v,(∑ e,if head e=v then u e else 0)=Δm v) := by
  let f (v : V) := (s*occurrenceDegree tail v+Δp v)/(B*s)
  let g (v : V) := (s*occurrenceDegree head v+Δm v)/(B*s)
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hf (v : V) := normalized_signed_demand_bounds (occurrenceDegree tail v) (Δp v)
    (Fintype.card E) (Fintype.card V) s B δ ε r (Nat.cast_nonneg _) hnr hs hB hδ hδsmall
    (hdegp v) (herrorp v) hsmall
  have hg (v : V) := normalized_signed_demand_bounds (occurrenceDegree head v) (Δm v)
    (Fintype.card E) (Fintype.card V) s B δ ε r (Nat.cast_nonneg _) hnr hs hB hδ hδsmall
    (hdegm v) (herrorm v) hsmall
  obtain ⟨q,hq,hqt,hqh⟩ := bipartite_nearUniformFractionalDegrees tail head f g hn hn hδ le_rfl hδsmall
    (div_nonneg (Nat.cast_nonneg _) hBp.le) hMC
    (normalized_signed_demand_total tail Δp hΔp s B hs)
    (normalized_signed_demand_total head Δm hΔm s B hs)
    (fun v => (hf v).1) (fun v => (hg v).1) (fun v => (hf v).2) (fun v => (hg v).2) hlarge
  refine ⟨fun e => B*s*q e-s,?_,signedCorrection_marginal tail q Δp s B hs hBp hqt,
    signedCorrection_marginal head q Δm s B hs hBp hqh⟩
  intro e
  rw [abs_le]
  have hlo := mul_nonneg (mul_pos hBp hs).le (hq e).1
  have hup := mul_le_of_le_one_right (mul_pos hBp hs).le (hq e).2
  have hBs : s≤B*s := by nlinarith
  constructor <;> linarith

end Oberwolfach
