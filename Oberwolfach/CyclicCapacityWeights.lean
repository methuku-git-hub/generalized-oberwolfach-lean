module

public import Oberwolfach.CyclicCapacityProfiles
public import Oberwolfach.IntervalCycleWeightTransfer

@[expose] public section

/-! The long-capacity construction on cyclically ordered classes. The inputs
are the original cyclic capacities; periodic indices are confined to the proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1200000 in
theorem cyclic_capacity_three_interval_weights {X : Type*} [Fintype X] [Nonempty X]
    (L : Fin 3 → ℕ) [NeZero (∑ i,L i)] (t : ℕ) (hL : ∀ i,4*t+1 ≤ L i)
    (a : Fin (∑ i,L i) → X → X → ℝ) (d : Fin (∑ i,L i) → X → ℝ)
    (ha : ∀ i x y,0≤a i x y)
    (hrow : ∀ i x,∑ y,a i x y=d i x)
    (hcol : ∀ i y,∑ x,a i x y=d (finRotate (∑ i,L i) i) y)
    (n a₀ a₁ d₀ d₁ : ℝ) (hn : (Fintype.card X : ℝ)=n) (hnpos : 0<n)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hapos : ∀ i x y,0<a i x y → a₀ ≤ a i x y ∧ a i x y ≤ a₁)
    (hdscale : ∀ i x,d₀*n ≤ d i x ∧ d i x ≤ d₁*n)
    (J : Finset (Fin (∑ i,L i))) (hJ : J.card ≤ 1) (κ B : ℝ)
    (hκ : 0<κ) (hκ1 : κ<1) (hB : 1≤B)
    (ht : 1+3*⌈Real.log (10*(B+1))/(-Real.log (1-κ))⌉₊ ≤ t)
    (hupper : ∀ i,i∉J → ∀ x y,cyclicCapacityTransition a d i x y ≤ B*(d (finRotate (∑ i,L i) i) y/(∑ z,d 0 z)))
    (hminor : ∀ i,i∉J → finRotate (∑ i,L i) i∉J → finRotate (∑ i,L i) (finRotate (∑ i,L i) i)∉J →
      ∀ x z,κ*(d (finRotate (∑ i,L i) (finRotate (∑ i,L i) (finRotate (∑ i,L i) i))) z/(∑ z,d 0 z)) ≤
      ∑ y,∑ w,cyclicCapacityTransition a d i x y*cyclicCapacityTransition a d (finRotate (∑ i,L i) i) y w*
        cyclicCapacityTransition a d (finRotate (∑ i,L i) (finRotate (∑ i,L i) i)) w z) :
    ∃ w : (Fin (∑ i,L i) → X) → ℝ,
      (∀ v,0≤w v) ∧
      (∀ i x y,(∑ v,if v i=x ∧ v (finRotate (∑ i,L i) i)=y then w v else 0)=a i x y) ∧
      (∀ v,(∃ i,a i (v i) (v (finRotate (∑ i,L i) i))=0) → w v=0) ∧
      (∀ v,(∀ i,0<a i (v i) (v (finRotate (∑ i,L i) i))) →
        longCycleLower L a₀ d₀ d₁/n^((∑ i,L i)-2) ≤ w v ∧
          w v ≤ longCycleUpper L a₁ d₀ d₁/n^((∑ i,L i)-2)) := by
  let C := ∑ i,L i
  let s := threeBlockStart L
  let A := periodicCapacity a
  let D := periodicDegree d
  let M := ∑ x,d 0 x
  have hLp (i : Fin 3) : 0<L i := by have := hL i;omega
  have hd (i : Fin C) (x : X) : 0<d i x := (mul_pos hd₀ hnpos).trans_le (hdscale i x).1
  have hM : 0<M := Finset.sum_pos (fun x _ => hd 0 x) Finset.univ_nonempty
  obtain ⟨hAr,hAc⟩ := periodicCapacity_balance a d hrow hcol
  have hDm (j : ℕ) : (∑ x,D j x)=M := by
    simpa only [D,periodicDegree,cyclicIndex_zero] using
      balanced_capacity_mass_constant A D hAr hAc j
  have hAb (j : ℕ) (x y : X) : 0≤A j x y := ha _ _ _
  have hDp (j : ℕ) (x : X) : 0<D j x := hd _ _
  have hDs (j : ℕ) (x : X) : d₀*n ≤ D j x ∧ D j x ≤ d₁*n := hdscale _ _
  have hstart (i : Fin 3) : s i+L i ≤ C := by
    fin_cases i <;> simp [s,threeBlockStart,C,Fin.sum_univ_succ] <;> omega
  have hbd (i : Fin 3) (x : X) : D (s i+L i) x=D (s (finRotate 3 i)) x := by
    fin_cases i <;> norm_num [s,threeBlockStart,finRotate_apply] <;> try rfl
    change d (cyclicIndex C (L 0+L 1+L 2)) x=d (cyclicIndex C 0) x
    have he : L 0+L 1+L 2=C := by simp [C,Fin.sum_univ_succ,Nat.add_assoc]
    rw [he]
    simp [cyclicIndex]
  let JN := J.image Fin.val
  have hJN : JN.card ≤ 1 := Finset.card_image_le.trans hJ
  have hu (i : Fin 3) (j : ℕ) (_ : s i≤j) (hji : j<s i+L i) (hj : j∉JN) (x y : X) :
      capacityTransition A D j x y ≤ B*capacityProfile D M (j+1) y := by
    have hjc : j<C := lt_of_lt_of_le hji (hstart i)
    have hjJ : cyclicIndex C j∉J := fun hh => hj ((cyclicIndex_mem_image_iff J j hjc).mp hh)
    simpa only [capacityTransition,capacityProfile,A,D,M,periodicCapacity,periodicDegree,
      cyclicIndex_succ,cyclicCapacityTransition] using hupper (cyclicIndex C j) hjJ x y
  have hm (i : Fin 3) (j : ℕ) (_ : s i≤j) (hji : j+3≤s i+L i)
      (h0 : j∉JN) (h1 : j+1∉JN) (h2 : j+2∉JN) (x z : X) :
      κ*capacityProfile D M (j+3) z ≤ transitionWalk (capacityTransition A D) j 3 x z := by
    have h0c : j<C := by have := hstart i;omega
    have h1c : j+1<C := by have := hstart i;omega
    have h2c : j+2<C := by have := hstart i;omega
    have h0J : cyclicIndex C j∉J := fun hh => h0 ((cyclicIndex_mem_image_iff J j h0c).mp hh)
    have h1J : cyclicIndex C (j+1)∉J := fun hh => h1 ((cyclicIndex_mem_image_iff J (j+1) h1c).mp hh)
    have h2J : cyclicIndex C (j+2)∉J := fun hh => h2 ((cyclicIndex_mem_image_iff J (j+2) h2c).mp hh)
    rw [cyclicIndex_succ] at h1J
    rw [show j+2=j+1+1 from rfl,cyclicIndex_succ,cyclicIndex_succ] at h2J
    have hh := hminor (cyclicIndex C j) h0J h1J h2J x z
    simpa only [A,D,capacityProfile,periodicDegree,M,periodicCapacity_three,
      show j+3=j+1+1+1 from rfl,cyclicIndex_succ] using hh
  obtain ⟨ω,hω0,hωM,hωe,hωsupp,hωbounds⟩ := long_capacity_bounded_interval_weights
    A D hAb hDp hAr hAc M hM hDm s L t hbd JN hJN κ B hκ hκ1 hB ht hL hu hm
    n a₀ a₁ d₀ d₁ hn hnpos ha₀ ha₁ hd₀ hd₁ hDs
  let w := cycleWeightsOfIntervals L hLp ω
  have hwe (i : Fin C) (x y : X) :
      (∑ v,if v i=x ∧ v (finRotate C i)=y then w v else 0)=a i x y := by
    apply cycleWeightsOfIntervals_edge L hLp ω hω0 hωsupp a _ i x y
    intro q j u v
    have hval := threeBlockPosition_val L ⟨q,j⟩
    have he : cyclicIndex C (s q+j.val)=finSigmaFinEquiv ⟨q,j⟩ := by
      rw [← hval]
      exact cyclicIndex_fin _
    dsimp only [C] at he
    simpa only [A,periodicCapacity,he] using hωe q j u v
  have hw0 (v : Fin C → X) : 0≤w v := hω0 _
  refine ⟨w,hw0,hwe,?_,?_⟩
  · rintro v ⟨i,hi⟩
    exact cycleWeight_zero_at_zero_capacity a w hw0 hwe v i hi
  · intro v hv
    apply hωbounds (threePathsOfCycle L hLp v) (threePathsOfCycle_compatible L hLp v)
    intro i j
    have hb := threePathsOfCycle_edge L hLp v i j
    have hval := threeBlockPosition_val L ⟨i,j⟩
    have he : cyclicIndex C (s i+j.val)=finSigmaFinEquiv ⟨i,j⟩ := by
      rw [← hval]
      exact cyclicIndex_fin _
    dsimp only [C] at he
    simpa only [A,periodicCapacity,he,hb.1,hb.2] using hapos _ _ _ (hv (finSigmaFinEquiv ⟨i,j⟩))

end Oberwolfach
