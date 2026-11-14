module

public import Oberwolfach.RetainedMarkedAbsorberOccurrence
public import Oberwolfach.RetainedRawIntervalCardinality

@[expose] public section
/-! A retained absorber row is covered by its raw marked-start intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_marked_absorber_row_le_starts
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):
    ((retainedFinalMarkedAt π d σ t J w).card:ℝ)≤d*rawIntervalHubStartCount π d false σ w:=by
  let A:=Finset.univ.filter (fun a=>rawIntervalColouredStart π d (fun e=>σ (w,e)) a false)
  let B:=A.biUnion (permutationWindow π 0 (d-1))
  have hsub:retainedFinalMarkedAt π d σ t J w⊆B:=by
    intro v hv
    have hstate:retainedRawFamilyState π d σ false t J (v,w)=some (Sum.inl false):=by
      simpa only [retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    have hR:∀a g,retainedRawStart π d σ false t J w a g→ rawIntervalColouredStart π d (fun e=>σ (w,e)) a g:=fun _ _ h=>h.1
    have hret:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ false t J w) v=some (Sum.inl false):=hstate
    obtain ⟨a,ha,hwin⟩:=(retainedIntervalState_interval_iff π d (fun e=>σ (w,e)) _ hR v false).mp hret
    apply Finset.mem_biUnion.mpr
    exact ⟨a,by simpa [A] using ha.1,hwin⟩
  have hB:B.card≤A.card*d:=by
    calc
      B.card≤∑a∈A,(permutationWindow π 0 (d-1) a).card:=Finset.card_biUnion_le
      _≤∑_a∈A,d:=by
        apply Finset.sum_le_sum
        intro a ha
        have hh:=permutationWindow_card_le π 0 (d-1) a
        simp only [zero_add] at hh
        omega
      _=A.card*d:=by simp
  have hc:(retainedFinalMarkedAt π d σ t J w).card≤A.card*d:=(Finset.card_le_card hsub).trans hB
  rw [raw_interval_hub_count_eq_card]
  have hA:A.card=Fintype.card {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a false}:=by
    simp [A,Fintype.card_subtype]
  rw [←hA]
  exact_mod_cast (by nlinarith : (retainedFinalMarkedAt π d σ t J w).card≤d*A.card)
end Oberwolfach
