module

public import Oberwolfach.CapacityPositionSplitting
public import Oberwolfach.CapacitySplittingScales
public import Oberwolfach.WeightedOccurrenceDegrees
public import Oberwolfach.OccurrenceCapacityMatrix
public import Oberwolfach.EqualPartCutNormalization

@[expose] public section

/-! The position-splitting construction with the manuscript's graph inputs.
The accuracy constants precede the graph, its size, the degree target and the
weights. The edge types are separate finite types throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w

theorem occurrenceSumLinear_total {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (f : E → V) (w : E → ℝ) : (∑ v,occurrenceSumLinear f w v)=∑ e,w e := by
  change (∑ v,∑ e,if f e=v then w e else 0)=_
  rw [Finset.sum_comm]
  simp

theorem injective_occurrence_head {V E : Type*} (tail head : E → V)
    (hinj : Function.Injective (fun e => (tail e,head e))) :
    Function.Injective (fun e => (head e,tail e)) := by
  intro e f h
  exact hinj (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))

set_option maxHeartbeats 1800000 in
theorem marked_capacity_position_splitting
    (k : ℕ) (hk : 0<k) (δ dmin h : ℝ)
    (hδ : 0<δ) (hδsmall : δ<1/4) (hdmin : 0<dmin) (hh : 0<h) :
    ∃ ε κ : ℝ,0<ε ∧ 0<κ ∧ κ≤1/2 ∧
    ∀ (V : Type u) (E : Type v) (K : Type w)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V],
    ∀ (tail head : E → V) (ktail khead : K → V),
    Function.Injective (fun e => (tail e,head e)) →
    Function.Injective (fun e => (ktail e,khead e)) →
    0<Fintype.card V →
    ∀ z : ℝ,dmin*Fintype.card V/(k+1:ℝ)≤z →
    (∀ v,|occurrenceDegree tail v-(k+1)*z|≤ε*Fintype.card V) →
    (∀ v,|occurrenceDegree head v-(k+1)*z|≤ε*Fintype.card V) →
    (∀ v,|occurrenceDegree ktail v-z|≤ε*Fintype.card V) →
    (∀ v,|occurrenceDegree khead v-z|≤ε*Fintype.card V) →
    (∀ S T : Finset V,(1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
      h*Fintype.card V*min (S.card:ℝ) T.card ≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ (w : E → ℝ) (wK : K → ℝ),
    (∀ e,|w e-1|≤κ) → (∀ e,|wK e-1|≤κ) →
    (∀ v,occurrenceSumLinear tail w v+occurrenceSumLinear ktail wK v=
      occurrenceSumLinear head w v+occurrenceSumLinear khead wK v) →
    (∑ e,w e)=(k+1)*(∑ e,wK e) →
    ∃ (d : Fin (k+2) → V → ℝ) (f : Fin (k+1) → E → ℝ),
      (∀ v,d 0 v=occurrenceSumLinear khead wK v) ∧
      (∀ v,d (Fin.last (k+1)) v=occurrenceSumLinear ktail wK v) ∧
      (∀ j,(∑ v,d j v)=∑ e,wK e) ∧
      (∀ j v,(9/10)*z≤d j v ∧ d j v≤(11/10)*z) ∧
      (∀ e,(∑ j,f j e)=w e) ∧
      (∀ j v,occurrenceSumLinear tail (f j) v=d j.castSucc v) ∧
      (∀ j v,occurrenceSumLinear head (f j) v=d j.succ v) ∧
      (∀ j e,1/(2*(k+1:ℝ))≤f j e ∧ f j e≤2/(k+1:ℝ)) := by
  let A := max 1 (24/(δ*dmin))
  let B := max 1 (2/h)
  have hA : 0<A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 1≤B := le_max_left _ _
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hq : 0<dmin/(k+1:ℝ) := by positivity
  obtain ⟨ε,κ,hε,hκ,hεsmall,hκsmall,hρsmall,hbudget⟩ :=
    exists_capacity_splitting_parameters k δ dmin (dmin/(k+1:ℝ)) A B hδ hdmin hq hA hBp
  refine ⟨ε,κ,hε,hκ,hκsmall,?_⟩
  intro V E K instV instE instK instDec tail head ktail khead hinj hkinj hn z hz hdt hdh hdkt hdkh hcut w wK hw hwK hbalance htotal
  classical
  let n : ℝ := Fintype.card V
  let ρ := ε+κ
  have hnreal : 0<n := Nat.cast_pos.mpr hn
  have hρ : 0<ρ := add_pos hε hκ
  let O := occurrenceSumLinear tail w
  let I := occurrenceSumLinear head w
  let p := occurrenceSumLinear khead wK
  let q := occurrenceSumLinear ktail wK
  let M := ∑ e,wK e
  have hO : (∑ v,O v)=(k+1)*M := (occurrenceSumLinear_total tail w).trans htotal
  have hp : (∑ v,p v)=M := occurrenceSumLinear_total khead wK
  have hq : (∑ v,q v)=M := occurrenceSumLinear_total ktail wK
  have hbal (v : V) : O v-I v=p v-q v := by
    have hh := hbalance v
    change O v+q v=I v+p v at hh
    linarith
  have hOt (v : V) : |O v-(k+1)*z|≤ρ*n :=
    weighted_occurrence_degree_near tail w κ ε n ((k+1)*z) hκ.le hw v
      (injective_occurrence_degree_bound tail head hinj v) (hdt v)
  have hIt (v : V) : |I v-(k+1)*z|≤ρ*n :=
    weighted_occurrence_degree_near head w κ ε n ((k+1)*z) hκ.le hw v
      (injective_occurrence_degree_bound head tail (injective_occurrence_head tail head hinj) v) (hdh v)
  have hpt (v : V) : |p v-z|≤ρ*n :=
    weighted_occurrence_degree_near khead wK κ ε n z hκ.le hwK v
      (injective_occurrence_degree_bound khead ktail (injective_occurrence_head ktail khead hkinj) v) (hdkh v)
  have hqt (v : V) : |q v-z|≤ρ*n :=
    weighted_occurrence_degree_near ktail wK κ ε n z hκ.le hwK v
      (injective_occurrence_degree_bound ktail khead hkinj v) (hdkt v)
  have hmean : dmin*n/2≤(Fintype.card E:ℝ)/Fintype.card V := by
    have hm := (abs_le.mp (occurrence_degree_mean_near tail ((k+1)*z) (ε*n) hn hdt)).1
    have hz' : dmin*n≤z*(k+1:ℝ) := (div_le_iff₀ (by positivity)).mp hz
    have heps : ε≤dmin/2 := by nlinarith
    nlinarith
  have hsmall := marked_position_signed_scale ε ρ δ dmin A n
    ((Fintype.card E:ℝ)/Fintype.card V) hρ hδ hdmin (le_max_right _ _) hnreal hεsmall hmean
  have hMC : (Fintype.card E:ℝ)/B≤h*Fintype.card V*Fintype.card V/2 := by
    apply normalized_correction_mass_bound _ n B h _ hBp hh (le_max_right _ _)
    dsimp only [n]
    exact_mod_cast injective_occurrence_card_bound tail head hinj
  have hbudget' : κ/(k+1:ℝ)+k*(B*(A*ρ))≤1/(2*(k+1:ℝ)) := by
    simpa only [ρ,mul_assoc] using hbudget
  obtain ⟨f,hf,hfr,hfc,hfb⟩ := capacity_position_splitting tail head k hk w p q O I M z (ρ*n)
    (mul_pos hρ hnreal).le (fun _ => rfl) (fun _ => rfl) hbal hp hq hO hpt hqt hOt hIt
    κ (A*ρ) B δ (2*(ε*n)) h hw (mul_pos hA hρ) hB hn hδ.le hδsmall
    (occurrence_degree_near_mean tail ((k+1)*z) (ε*n) hn hdt)
    (occurrence_degree_near_mean head ((k+1)*z) (ε*n) hn hdh)
    (by convert hsmall using 1 <;> ring) hMC
    (equal_part_cut_normalization tail head δ h hn hcut) hbudget'
  let d (j : Fin (k+2)) (v : V) := capacityPositionDemands k (p v) (q v) (O v) j
  refine ⟨d,f,?_,?_,?_,?_,hf,hfr,hfc,hfb⟩
  · intro v
    exact capacityPositionDemands_first k (p v) (q v) (O v)
  · intro v
    exact capacityPositionDemands_last k (p v) (q v) (O v)
  · intro j
    exact capacityPositionDemands_total k hk p q O M hp hq hO j
  · intro j v
    have he := capacityPositionDemands_error k hk (p v) (q v) (O v) z (ρ*n)
      (mul_pos hρ hnreal).le (hpt v) (hqt v) (hOt v) j
    have hs := mul_le_mul_of_nonneg_right hρsmall hnreal.le
    have hz' : (dmin/(k+1:ℝ))*n≤z := by convert hz using 1 <;> ring
    obtain ⟨hl,hu⟩ := abs_le.mp he
    change (9/10)*z≤capacityPositionDemands k (p v) (q v) (O v) j ∧
      capacityPositionDemands k (p v) (q v) (O v) j≤(11/10)*z
    constructor <;> dsimp only [ρ] at * <;> nlinarith

end Oberwolfach
