module

public import Oberwolfach.MarkedIndexTupleCounts
public import Oberwolfach.PermutationConflictDegree

@[expose] public section

/-! Row degrees and codegrees of the actual marked endpoint assignment
graph, obtained from two and three specified spoke conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem count_error_after_comparing_target (a b target p err : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (herr : 0≤err)
    (ha : |a-p*target|≤err) (hb : |b-target|≤err) : |a-p*b|≤2*err := by
  obtain ⟨ha₁,ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁,hb₂⟩ := abs_le.mp hb
  have h₁ := mul_le_mul_of_nonneg_left hb₁ hp
  have h₂ := mul_le_mul_of_nonneg_left hb₂ hp
  have h₃ := mul_le_mul_of_nonneg_right hp1 herr
  apply abs_le.mpr
  constructor <;> nlinarith only [ha₁,ha₂,h₁,h₂,h₃]

theorem marked_endpoint_index_estimates
    (π : Equiv.Perm V) (d h : ℕ) (hh : 3≤h) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (err : ℝ) (herr : 0≤err)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hi : MarkedIndicesWithSpokes π d h B q s g j err σ H)
    (w : Bool→ℝ) (hq : ∀ u∈B,q u g=w true) (hs : ∀ u∈B,s u j=w false)
    (hw : ∀ t,0≤w t ∧ w t≤1) (r t : Bool) (x : V) :
    let Y := B.filter (H r x)
    (|((Y.card:ℝ)-w r*B.card)|≤err) ∧
    (∀ z,¬PermutationClose π (3*d) x z →
      |((Y.filter (H t z)).card:ℝ)-w t*Y.card|≤2*err) ∧
    (∀ z z',¬PermutationClose π (3*d) x z → ¬PermutationClose π (3*d) x z' →
      ¬PermutationClose π (3*d) z z' →
      ((Y.filter (fun u=>H t z u ∧ H t z' u)).card:ℝ)≤(w t)^2*Y.card+2*err) := by
  let Y := B.filter (H r x)
  have hsingle : |(Y.card:ℝ)-w r*B.card|≤err := by
    have he := marked_index_tuple_estimate π d h B q s g j err σ H hi w hq hs
      (fun _ : Fin 1=>x) (fun _=>r) (by intro a b _;exact Subsingleton.elim _ _)
      (by simpa using (show 1≤h by omega)) (by intro a b hne;exact (hne (Subsingleton.elim _ _)).elim)
    simpa [Y] using he.le
  refine ⟨hsingle,?_,?_⟩
  · intro z hxz
    have hne : x≠z := fun he=>hxz (Or.inl he)
    have he := marked_index_tuple_estimate π d h B q s g j err σ H hi w hq hs
      ![x,z] ![r,t] (by intro a b he;fin_cases a <;> fin_cases b <;> simp_all)
      (by simpa using (show 2≤h by omega)) (by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [permutationClose_symm])
    have he' : |((Y.filter (H t z)).card:ℝ)-w t*(w r*B.card)|≤err := by
      simpa [Y,Finset.filter_filter,Fin.forall_fin_two,mul_left_comm,mul_assoc] using he.le
    exact count_error_after_comparing_target _ _ _ _ err (hw t).1 (hw t).2 herr he' hsingle
  · intro z z' hxz hxz' hzz'
    have hne : x≠z := fun he=>hxz (Or.inl he)
    have hne' : x≠z' := fun he=>hxz' (Or.inl he)
    have hzz : z≠z' := fun he=>hzz' (Or.inl he)
    have he := marked_index_tuple_estimate π d h B q s g j err σ H hi w hq hs
      ![x,z,z'] ![r,t,t] (by intro a b he;fin_cases a <;> fin_cases b <;> simp_all)
      (by simpa using hh) (by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [permutationClose_symm])
    have he' : |((Y.filter (fun u=>H t z u ∧ H t z' u)).card:ℝ)-(w t)^2*(w r*B.card)|≤err := by
      have heq : (w r*(w t*w t))*B.card=(w t)^2*(w r*B.card) := by ring
      simpa [Y,Finset.filter_filter,Fin.forall_fin_succ,Fin.prod_univ_succ,pow_two,mul_assoc,mul_comm,mul_left_comm] using he.le
    have hp2 : (w t)^2≤1 := by nlinarith [(hw t).1,(hw t).2]
    have hc := count_error_after_comparing_target _ _ _ _ err (sq_nonneg _) hp2 herr he' hsingle
    exact (by linarith only [(abs_le.mp hc).2])

end Oberwolfach
