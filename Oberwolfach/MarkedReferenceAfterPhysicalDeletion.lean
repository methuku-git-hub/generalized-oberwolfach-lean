module

public import Oberwolfach.MarkedProtectedActiveReferenceStatistics
public import Oberwolfach.MarkedReferenceFixedCuts

@[expose] public section

/-! Reference degree, two-step and cut estimates on a later rim-deleted
outcome. Interval coordinates, density targets and coefficient functions
are unchanged. The conclusions hold for every realized deletion graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_reference_statistics_after_physical_deletion
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color)
    (D ε δ γ γ' p k s t ζ : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (DR : SimpleGraph V)
    (hDR : ∀ x, (DR.degree x : ℝ) ≤ ζ*Fintype.card V)
    (hmargin : 2*ζ ≤ (3/2)*(γ-γ')*p^2)
    (hstats : MarkedReferenceStatistics P π d g j D ε δ γ p k s t σ) :
    MarkedReferenceStatistics P π d g j D (ε+ζ) δ γ' p k s t
      (rawMarkedDeleteRims σ DR.edgeFinset) := by
  refine ⟨⟨?_,?_⟩,hstats.2⟩
  · intro mark x
    have h := marked_rim_degree_physical_deletion P π d σ DR mark x
    have hc := hstats.1.1 mark x
    simp only [← Nat.cast_sum] at h
    have hout := (abs_sub_le
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y):ℕ):ℝ)
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y):ℕ):ℝ)
      ((if mark then k else p)*D)).trans (add_le_add (h.1.trans (hDR x)) hc.1)
    have hin := (abs_sub_le
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark y x):ℕ):ℝ)
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark y x):ℕ):ℝ)
      ((if mark then k else p)*D)).trans (add_le_add (h.2.trans (hDR _)) hc.2)
    constructor <;> nlinarith only [hout,hin]
  · intro x y hxy
    have h := marked_rim_two_step_physical_deletion P π d σ DR false
      (ζ*Fintype.card V) hDR x y
    have hlo := hstats.1.2 x y hxy
    simp only [markedPhysicalRim_pos_iff_one] at hlo ⊢
    have hloss := (abs_le.mp h).1
    have hm := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    nlinarith only [hlo,hloss,hm]

theorem marked_rim_cut_physical_deletion_bound
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (DR : SimpleGraph V)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hDR : ∀ x,(DR.degree x : ℝ) ≤ ζ*Fintype.card V)
    (mark : Bool) (S T : Finset V) :
    |(matrixCut (markedPhysicalRim P π (3*d)
        (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark) S T : ℝ)-
      (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) S T : ℝ)| ≤
      ζ*Fintype.card V*min (S.card : ℝ) T.card := by
  let R := fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
  let R' := fun x y=>markedPhysicalRim P π (3*d)
    (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1
  have hr (x : V) : (∑ y,if ¬(R x y ↔ R' x y) then (1:ℝ) else 0) ≤ ζ*Fintype.card V := by
    have h := (marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,false,x)).trans (hDR _)
    cases mark <;> simpa [R,R',markedRowRim,rawMarkedPairRims] using h
  have hc (y : V) : (∑ x,if ¬(R x y ↔ R' x y) then (1:ℝ) else 0) ≤ ζ*Fintype.card V := by
    have h := (marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,true,y)).trans (hDR _)
    cases mark <;> simpa [R,R',markedRowRim,rawMarkedPairRims] using h
  have h := bipartite_cut_change_degrees R R' ζ hζ
    (by intro x;convert hr x using 1 <;> congr!)
    (by intro y;convert hc y using 1 <;> congr!) S T
  have hi (τ : RawMarkedOutcome V U Γ Color) :
      (fun x y=>@ite ℕ (markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)
        (Classical.propDecidable _) 1 0)=
        markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark := by
    funext x y
    split_ifs with hh
    · exact hh.symm
    · have hh' := markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) mark x y
      simpa only [hh,ite_false] using hh'
  dsimp only [R,R'] at h
  rw [hi,hi] at h
  change |(matrixCut _ S T : ℝ)-(matrixCut _ S T : ℝ)| ≤ _ at h
  rw [← mul_min_of_nonneg _ _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))] at h
  simpa only [mul_assoc] using h

theorem marked_reference_cuts_after_physical_deletion
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color)
    (α α' p k t ζ : ℝ) (ha : α' ≤ α) (hζ : 0 ≤ ζ)
    (hmargin : ∀ mark : Bool, ζ ≤ (α-α')*(if mark then k else p)/4)
    (σ : RawMarkedOutcome V U Γ Color) (DR : SimpleGraph V)
    (hDR : ∀ x,(DR.degree x : ℝ) ≤ ζ*Fintype.card V)
    (hcuts : MarkedReferenceCutFamilies P π d g j α p k t σ) :
    MarkedReferenceCutFamilies P π d g j α' p k t (rawMarkedDeleteRims σ DR.edgeFinset) := by
  refine ⟨hcuts.1,?_⟩
  intro mark δ hdα hdp S T hST
  have hcut := hcuts.2 mark δ (hdα.trans (by linarith only [ha])) hdp S T hST
  have hloss := (abs_le.mp (marked_rim_cut_physical_deletion_bound P π d σ DR ζ hζ hDR mark S T)).1
  have hm := mul_le_mul_of_nonneg_right (hmargin mark)
    (show 0 ≤ (Fintype.card V : ℝ)*min (S.card : ℝ) T.card by positivity)
  nlinarith only [hcut,hloss,hm]

end Oberwolfach
