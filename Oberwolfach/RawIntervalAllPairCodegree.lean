module

public import Oberwolfach.RawIntervalAllPairLabelProbability
public import Oberwolfach.RawIntervalLabelCounts
public import Oberwolfach.RawMarkedHubCounts

@[expose] public section
/-! Lower codegree estimates hold simultaneously for all distinct pairs,
including pairs whose interval windows meet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_interval_label_pair_expectation_lower
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (x y:V) (hxy:x≠y) (j:Color) (s₀:ℝ) (hs₀:0≤s₀) (hsl:∀u,s₀≤s u j):
    (5/8:ℝ)*s₀^2*Fintype.card U≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).expectation
       (fun σ=>rawIntervalLabelCount π d σ j {x,y}):=by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hterm (u:U): (5/8:ℝ)*s₀^2≤μ.probability
      (fun σ=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
              rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j)):=by
    have hp:=raw_interval_two_labels_probability_lower π d hd (q u) (hq u) (hQ u)
      (s u) (hs u) (hS u) hnoshort x y hxy j
    have hsq:s₀^2≤(s u j)^2:=by nlinarith [hsl u,hs u j]
    apply (mul_le_mul_of_nonneg_left hsq (by norm_num:(0:ℝ)≤5/8)).trans
    unfold μ rawIntervalFamilyState
    rw [rawIntervalFamily_column_event d hd q hq hQ s hs hS u
      (fun τ=>rawIntervalState π d τ x=some (Sum.inr j) ∧ rawIntervalState π d τ y=some (Sum.inr j))]
    exact hp
  have he : μ.expectation (fun σ=>rawIntervalLabelCount π d σ j {x,y})=
      ∑u:U,μ.probability (fun σ=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
              rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j)):=by
    unfold FiniteLaw.expectation rawIntervalLabelCount FiniteLaw.probability
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
    split_ifs <;> simp
  rw [he]
  calc
    (5/8:ℝ)*s₀^2*Fintype.card U = ∑ _u:U,(5/8:ℝ)*s₀^2 := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun u _=>hterm u)


theorem raw_interval_all_pair_spoke_codegree_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hm:0<Fintype.card U) (j:Color) (s₀:ℝ) (hs₀:0≤s₀) (hsl:∀u,s₀≤s u j)
    (t:ℝ) (ht:0<t):
    1-(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀x y:V,x≠y→(5/8:ℝ)*s₀^2*Fintype.card U-t≤
        (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
          rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j))).card:ℝ)):=by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let I:Type:={z:V×V // z.1≠z.2}
  let T (i:I):Finset V:={i.val.1,i.val.2}
  have htail (i:I): μ.probability (fun σ=>t≤
      |rawIntervalLabelCount π d σ j (T i)-μ.expectation (fun τ=>rawIntervalLabelCount π d τ j (T i))|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))):=by
    have hh:=rawIntervalLabelCount_tail π d hd q hq hQ s hs hS hm j (T i)
      (by exact ⟨i.val.1,by simp [T]⟩) t ht
    have hc:(T i).card=2:=by simp [T,i.property]
    simpa only [hc,Nat.cast_ofNat] using hh
  have hh:=finiteLaw_common_event_lower μ Finset.univ
    (fun i:I=>fun σ=>t≤|rawIntervalLabelCount π d σ j (T i)-μ.expectation (fun τ=>rawIntervalLabelCount π d τ j (T i))|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))
    (fun i _=>htail i)
  have hcard:(Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^2:=by
    exact_mod_cast (show Fintype.card I≤Fintype.card V^2 from
      (Fintype.card_subtype_le _).trans_eq (by simp [pow_two]))
  have hbudget: (Fintype.card I:ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
      (Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U)))):=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hh
  apply ((sub_le_sub_left hbudget 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy
  have hcount:=hσ ⟨(x,y),hxy⟩
  have hmean:=raw_interval_label_pair_expectation_lower π d hd q hq hQ s hs hS hnoshort x y hxy j s₀ hs₀ hsl
  have heq:(((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
          rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j))).card:ℝ)=rawIntervalLabelCount π d σ j {x,y}:=by
    rw [Finset.card_filter,Nat.cast_sum]
    simp only [rawIntervalLabelCount,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [heq]
  dsimp only [T] at hcount
  linarith [neg_abs_le (rawIntervalLabelCount π d σ j {x,y}-μ.expectation (fun τ=>rawIntervalLabelCount π d τ j {x,y}))]
end Oberwolfach
