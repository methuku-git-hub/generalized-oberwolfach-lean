module

public import Oberwolfach.MarkedCapacityPositionSplitting
public import Oberwolfach.LongMarkedCopiedWeights
public import Oberwolfach.ApproximateMarkedCycleWeights
public import Oberwolfach.MarkedBalanceInputs

@[expose] public section

/-! The complete approximation step from the original degree, path-count and
large-cut hypotheses. Constants are uniform in the density and separation
parameter; the explicit approximation error records the latter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000 in
theorem marked_capacity_approximation (α p₀ : ℝ) (hα : 0<α) (hαmax : α≤1)
    (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (t k : ℕ)
    (ht : 1+3*⌈Real.log (10*(100/p₀+1))/(-Real.log (1-α/200))⌉₊≤t)
    (hc : 12*t+4≤k+2) :
    ∃ ε κ B : ℝ,0<ε ∧ 0<κ ∧ κ≤1/2 ∧ 0<B ∧
    ∀ (V : Type u) (E : Type v) (K : Type w)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V],
    ∀ (tail head : E → V) (ktail khead : K → V),
    Function.Injective (fun e => (tail e,head e)) →
    Function.Injective (fun e => (ktail e,khead e)) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → 0<Fintype.card V → 10/p₀≤(Fintype.card V:ℝ) →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ (π : Equiv.Perm V) (b : ℕ),
    (∀ e,¬PermutationClose π b (tail e) (head e)) →
    (∀ e,¬PermutationClose π b (ktail e) (khead e)) →
    ∀ w : E⊕K → ℝ,w∈markedBalanceSubspace tail head ktail khead (k+1) →
    ‖w-(fun _ => (1:ℝ))‖≤κ →
    ∃ q : MarkedCycleTuple tail head ktail khead (k+1) π b → ℝ,
      (∀ C,0≤q C ∧ q C≤B/(Fintype.card V:ℝ)^k) ∧
      ‖(∑ C,q C • markedCycleIncidence tail head ktail khead (k+1) C.val)-w‖≤
        (k+1:ℝ)*((k+2:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ) := by
  have hk : 0<k := by omega
  let δ := min (α/16) (p₀/128)
  have hδ : 0<δ := by dsimp [δ];positivity
  have hδsmall : δ<1/4 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨ε,κ,hε,hκ,hκsmall,hsplit⟩ := marked_capacity_position_splitting k hk δ (p₀/2) (α*p₀/16)
    hδ hδsmall (by positivity) (by positivity)
  obtain ⟨b₀,B,hb₀,hB,hcopied⟩ := long_marked_copied_weights α p₀ hα hαmax hp₀ hp₀max t k ht hc
  refine ⟨ε,κ,B,hε,hκ,hκsmall,hB,?_⟩
  intro V E K instV instE instK instDec tail head ktail khead hinj hkinj p D hp hpmax hn hsize hDlo hDhi hdt hdh hdkt hdkh hcommon hcut π b hsep hksep w hw hwclose
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  let wO (e : E) := w (Sum.inl e)
  let wK (e : K) := w (Sum.inr e)
  have hwO (e : E) : |wO e-1|≤κ := edge_weight_error_of_norm w κ hwclose (Sum.inl e)
  have hwK (e : K) : |wK e-1|≤κ := edge_weight_error_of_norm w κ hwclose (Sum.inr e)
  have hwKb (e : K) : 1/2≤wK e ∧ wK e≤3/2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp (hwK e)
    constructor <;> linarith
  obtain ⟨hbal,htotal⟩ := markedBalanceSubspace_inputs tail head ktail khead (k+1) w hw
  have htotal' : (∑ e,wO e)=(k+1:ℝ)*(∑ e,wK e) := by
    simpa only [Nat.cast_add,Nat.cast_one] using htotal
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hpp : 0<p := hp₀.trans_le hp
  have hDp : 0<D := by linarith
  have hz : (p₀/2)*Fintype.card V/(k+1:ℝ)≤p*D/(k+1:ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hp hDp.le
    nlinarith
  have heq : (k+1:ℝ)*(p*D/(k+1:ℝ))=p*D := by field_simp
  obtain ⟨d,f,hd0,hdlast,hdtotal,hd,hfs,hfr,hfc,hfb⟩ := hsplit V E K tail head ktail khead hinj hkinj hn
    (p*D/(k+1:ℝ)) hz (by simpa only [heq] using hdt) (by simpa only [heq] using hdh) hdkt hdkh
    (marked_graph_cut_uniform tail head α p p₀ hα.le hp hcut) wO wK hwO hwK hbal htotal'
  have hdtotal' (j : Fin (k+2)) : (∑ x,d j x)=∑ x,d 0 x := (hdtotal j).trans (hdtotal 0).symm
  obtain ⟨u,hu,he,hub,hul⟩ := hcopied V E K tail head ktail khead hinj hkinj p D hp hpmax hn hsize hDlo hDhi
    f wK d hfb hwKb hd hdtotal' hfr hfc (fun x => (hdlast x).symm) (fun x => (hd0 x).symm) hcommon
  obtain ⟨q,hq,hqerror⟩ := approximate_marked_cycle_coefficients tail head ktail khead hinj hkinj
    (k+1) (by omega) π b hsep hksep f wO wK hfs
    (by simpa only [Nat.cast_add,Nat.cast_one] using hfb) hwKb u hu he B hB.le
    (by simpa only [Nat.add_sub_cancel] using hub)
  have hwident : Sum.elim wO wK=w := by funext e;cases e <;> rfl
  refine ⟨q,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using hq
  · simpa only [hwident,Nat.cast_add,Nat.cast_one,show (k:ℝ)+1+1=k+2 by ring] using hqerror

end Oberwolfach
