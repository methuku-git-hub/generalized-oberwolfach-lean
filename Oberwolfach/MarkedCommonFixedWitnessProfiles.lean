module

public import Oberwolfach.MarkedCommonRootLoadTransfer
public import Oberwolfach.MarkedCommonClassEquivalences
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.MarkedCommonPairCycleProfiles

@[expose] public section

/-! Construct the fixed pair profiles from a single common-witness event.
The selector for each pair of hubs is supplied and held fixed. The coefficients
are the supplied parent coefficients, with their original normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_fixed_witness_profiles
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (D p k s₀ ε βcycle βpath blo bhi:ℝ)
    (weight:(Fin (r+4+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hw:∀ C:Fin (r+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
      blo/(Fintype.card V:ℝ)^(r+4)≤weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤bhi/(Fintype.card V:ℝ)^(r+4))
    (κ:U→U→V→Bool)
    (hevent:∀ u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ ε ε ε
      βcycle βpath weight σ H (κ u u') u u'):
    Nonempty (MarkedCommonPairCycleProfiles
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (H false) (H true) π (3*d) r ((s₀/((r+4:ℕ):ℝ))^2) (min βcycle βpath) blo bhi ε):=by
  have hκ (u u':U) (hne:u≠u'):
      CommonWitnessEstimates P π d r D p k s₀ ε ε ε βcycle βpath weight σ H (κ u u') u u':=
    hevent u u' hne
  let A:=fun u u'=>commonSelectedClass H (κ u u') u u' true
  let B:=fun u u'=>commonSelectedClass H (κ u u') u u' false
  have hA (u u':U) (v:V):v∈A u u'↔H true v u∧H true v u':=by
    simp only [A,mem_commonSelectedClass,selectedSpokes,Bool.true_eq_false,false_implies,and_true]
  have hAs (u u':U) (v:V):v∈A u u'↔selectedSpokes H (κ u u') true v u∧selectedSpokes H (κ u u') true v u':=
    mem_commonSelectedClass H (κ u u') u u' true v
  have hBs (u u':U) (v:V):v∈B u u'↔selectedSpokes H (κ u u') false v u∧selectedSpokes H (κ u u') false v u':=
    mem_commonSelectedClass H (κ u u') u u' false v
  have hden:((r+4:ℕ):ℝ)≠0:=by positivity
  have hq:(((r:ℝ)+4)*(s₀/((r+4:ℕ):ℝ))^2)=s₀*s₀/((r+4:ℕ):ℝ):=by
    push_cast
    field_simp
    <;> ring
  refine ⟨{
    A := A
    B := B
    q := fun _ _ => (s₀/((r+4:ℕ):ℝ))^2
    w := fun _ _ C => weight C.val/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))
    q_lower := fun _ _ _ => le_rfl
    marked_class := fun u u' _ => hA u u'
    ordinary_class := ?_
    marked_size := ?_
    ordinary_size := ?_
    overlap := ?_
    cycles := ?_
    paths := ?_
    weight_bounds := ?_
    root_loads := ?_ }⟩
  · intro u u' _ v hv
    exact ⟨((hBs u u' v).mp hv).1.1,((hBs u u' v).mp hv).2.1⟩
  · intro u u' hne
    simpa only [A,pow_two,ite_true] using (hκ u u' hne).1 true
  · intro u u' hne
    rw [hq]
    simpa only [B,Bool.false_eq_true,ite_false] using (hκ u u' hne).1 false
  · intro u u' hne
    exact (hκ u u' hne).2.1
  · intro u u' hne
    have hc:=(hκ u u' hne).2.2.2.1
    have he:=common_marked_cycle_class_card (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
      (head:=fun e=>e.val.2) (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
      (khead:=fun e=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) u u' (A u u') (B u u') (hAs u u') (hBs u u')
    change βcycle*(Fintype.card V:ℝ)^(r+5)≤(Fintype.card (CommonMarkedCycle _ _ _ _ _ _ _ _ _ u u'):ℝ) at hc
    rw [he] at hc
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hc
  · intro u u' hne j v v' hv
    have hp:=(hκ u u' hne).2.2.2.2 v v' hv j
    have he:=root_first_common_marked_path_class_card (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
      (head:=fun e=>e.val.2) (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
      (khead:=fun e=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) u u' (A u u') (B u u') (hAs u u') (hBs u u') j v v'
    have hm:r+3+1=r+4:=by omega
    simp only [MarkedSampleCommonPathWithSpokes,hm,Matrix.cons_val_zero,Matrix.cons_val_one] at hp
    rw [he] at hp
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans hp
  · intro u u' _ C
    exact hw C.val (marked_sample_cycle_valid P π (3*d) (r+4) (fun e=>σ (Sum.inl e)) C) C.property.1
  · intro u u' hne j v
    rw [marked_common_root_load_transfer P π d (r+4) D p k (s₀*s₀/((r+4:ℕ):ℝ)) weight σ H (κ u u') u u']
    rw [abs_sub_comm]
    exact (hκ u u' hne).2.2.1 j v

end Oberwolfach
