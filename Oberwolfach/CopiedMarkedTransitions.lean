module

public import Oberwolfach.CopiedMarkedCapacities
public import Oberwolfach.MarkedTransitionScales
public import Oberwolfach.OrdinaryTransitionMixing
public import Oberwolfach.CyclicCapacityProfiles

@[expose] public section

/-! Verification of the long-cycle theorem's transition hypotheses for the
actual copied marked graph. The single exceptional interface is its marked one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

set_option maxHeartbeats 1200000 in
theorem copied_marked_transition_hypotheses
    {V E K : Type*} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (k : ℕ) (f : Fin (k+1) → E → ℝ) (wK : K → ℝ) (d : Fin (k+2) → V → ℝ)
    (α p p₀ D : ℝ) (hα : 0<α) (hp₀ : 0<p₀) (hp : p₀≤p) (hpmax : p≤1/2)
    (hn : 0<Fintype.card V) (hsize : 10/p₀≤(Fintype.card V:ℝ))
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (hf : ∀ j e,1/(2*(k+1:ℝ))≤f j e ∧ f j e≤2/(k+1:ℝ))
    (hwK : ∀ e,1/2≤wK e ∧ wK e≤3/2)
    (hd : ∀ j v,(9/10)*(p*D/(k+1:ℝ))≤d j v ∧ d j v≤(11/10)*(p*D/(k+1:ℝ)))
    (htotal : ∀ j,(∑ v,d j v)=∑ v,d 0 v)
    (hrow : ∀ i x,(∑ y,copiedMarkedCapacity tail head ktail khead (k+1) f wK i x y)=d i x)
    (hcommon : ∀ x y,x≠y → α*p^2*Fintype.card V ≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) :
    let a := copiedMarkedCapacity tail head ktail khead (k+1) f wK
    (∀ i,i≠Fin.last (k+1) → ∀ x y,cyclicCapacityTransition a d i x y≤
      (100/p₀)*(d (finRotate (k+2) i) y/(∑ z,d 0 z))) ∧
    (∀ i,i≠Fin.last (k+1) → finRotate (k+2) i≠Fin.last (k+1) →
      finRotate (k+2) (finRotate (k+2) i)≠Fin.last (k+1) → ∀ x z,
      (α/200)*(d (finRotate (k+2) (finRotate (k+2) (finRotate (k+2) i))) z/(∑ z,d 0 z))≤
      ∑ y,∑ w,cyclicCapacityTransition a d i x y*cyclicCapacityTransition a d (finRotate (k+2) i) y w*
        cyclicCapacityTransition a d (finRotate (k+2) (finRotate (k+2) i)) w z) := by
  classical
  let a := copiedMarkedCapacity tail head ktail khead (k+1) f wK
  let R := cyclicCapacityTransition a d
  let A (x y : V) : Prop := ∃ e,tail e=x ∧ head e=y
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hpp : 0<p := hp₀.trans_le hp
  have hDp : 0<D := by linarith
  have hq : 0<p*D/(k+1:ℝ) := by positivity
  have hdp (j : Fin (k+2)) (v : V) : 0<d j v :=
    (mul_pos (by norm_num : (0:ℝ)<9/10) hq).trans_le (hd j v).1
  have ha : ∀ i x y,0≤a i x y := (copiedMarkedCapacity_bounds tail head ktail khead hinj hkinj
    (k+1) (by omega) f wK (by simpa only [Nat.cast_add,Nat.cast_one] using hf) hwK).1
  have hR (i : Fin (k+2)) : IsTransition (R i) := by
    constructor
    · intro x y
      exact div_nonneg (ha i x y) (hdp i x).le
    · intro x
      change (∑ y,a i x y/d i x)=1
      rw [← Finset.sum_div,hrow,div_self (hdp i x).ne']
  have hentry (i : Fin (k+2)) (hi : i≠Fin.last (k+1)) (x y : V) :
      (A x y → 1/(6*p*Fintype.card V)≤R i x y) ∧ R i x y≤5/(p*Fintype.card V) := by
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact (hi rfl).elim
    · intro hi
      by_cases hxy : A x y
      · obtain ⟨e,rfl,rfl⟩ := hxy
        have he : R j.castSucc (tail e) (head e)=f j e/d j.castSucc (tail e) := by
          dsimp only [R,cyclicCapacityTransition,a]
          rw [copiedMarkedCapacity_ordinary,occurrenceCapacityMatrix_at_edge tail head hinj]
        rw [he]
        have hh := marked_transition_entry_bounds k p D (Fintype.card V) (f j e) (d j.castSucc (tail e))
          hpp hnr hDlo hDhi (hf j e) (hd _ _)
        exact ⟨fun _ => hh.1,hh.2⟩
      · have hz : R j.castSucc x y=0 := by
          dsimp only [R,cyclicCapacityTransition,a]
          rw [copiedMarkedCapacity_ordinary,occurrenceCapacityMatrix_zero tail head (f j) x y hxy,zero_div]
        exact ⟨fun h => (hxy h).elim,by rw [hz];positivity⟩
  have hμ (i : Fin (k+2)) (v : V) :
      1/(2*(Fintype.card V:ℝ))≤d i v/(∑ z,d 0 z) ∧ d i v/(∑ z,d 0 z)≤2/(Fintype.card V:ℝ) :=
    marked_stationary_bounds (d i) (p*D/(k+1:ℝ)) (∑ z,d 0 z) hn hq (hd i) (htotal i) v
  constructor
  · intro i hi x y
    exact marked_transition_domination p p₀ (Fintype.card V) (R i x y)
      (d (finRotate (k+2) i) y/(∑ z,d 0 z)) hp₀ hp hnr (hentry i hi x y).2 (hμ _ _).1
  · intro i hi hi1 hi2 x z
    have hh := ordinary_three_step_minorization (R i) (R (finRotate (k+2) i))
      (R (finRotate (k+2) (finRotate (k+2) i))) A
      (fun z => d (finRotate (k+2) (finRotate (k+2) (finRotate (k+2) i))) z/(∑ z,d 0 z))
      α p p₀ (Fintype.card V) hα hp₀ hp hnr hsize (hR i) (hR _).1 (hR _).1
      (fun x y => (hentry _ hi1 x y).1) (fun x y => (hentry _ hi2 x y).1)
      (fun x y => (hentry i hi x y).2) hcommon (fun y => (hμ _ y).2) x z
    simpa only [transitionCompose,Finset.mul_sum,mul_assoc] using hh

end Oberwolfach
