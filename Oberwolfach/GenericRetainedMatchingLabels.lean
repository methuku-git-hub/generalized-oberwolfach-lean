module

public import Oberwolfach.ReservedPairAllowedHubs
public import Oberwolfach.RetainedMarkedAbsorberOccurrence

@[expose] public section
/-! Matching labels and retained-absorber bounds for an arbitrary finite vertex
type, with the equality instance shared throughout the retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem generic_retained_absorber_occurrence_le_extended
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t):
    ∀v,(Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card≤
      (rawIntervalExtendedAnyHubSet π d σ v).card:=by
  intro v
  apply Finset.card_le_card
  intro w hw
  have hstate:retainedRawFamilyState π d σ false t J (v,w)=some (Sum.inl false):=by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,retainedFinalMarkedAt] using hw
  have hR:∀a g,retainedRawStart π d σ false t J w a g→ rawIntervalColouredStart π d (fun e=>σ (w,e)) a g:=fun _ _ h=>h.1
  have hret:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ false t J w) v=some (Sum.inl false):=hstate
  obtain ⟨a,ha,hwin⟩:=(retainedIntervalState_interval_iff π d (fun e=>σ (w,e)) _ hR v false).mp hret
  have hwin':v∈permutationWindow π 0 d a:=permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) a hwin
  apply Finset.mem_union_left
  simp only [rawIntervalExtendedHubSet,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨a,ha.1,hwin'⟩

theorem generic_retained_absorber_budget
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (n:ℕ) (m b:ℝ) (hm:0<m) (hU:Fintype.card U≤n)
    (hM:4/m≤b/2) (hN:4*(n:ℝ)^(3/4:ℝ)≤b*n/2)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ)):
    ∀v,((Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ)≤b*n:=by
  intro v
  have hcard:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hU
  have hscale:4*(Fintype.card U:ℝ)/m≤b*n/2:=by
    have hh:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n)
    have hh':(4/m)*(Fintype.card U:ℝ)≤(4/m)*(n:ℝ):=mul_le_mul_of_nonneg_left hcard (by positivity)
    convert hh'.trans hh using 1 <;> ring
  have hsubset:=generic_retained_absorber_occurrence_le_extended π d σ t J v
  have hsub':(((Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ))≤
      (rawIntervalExtendedAnyHubSet π d σ v).card:=by exact_mod_cast hsubset
  linarith [hOcc v]

theorem generic_reserved_pair_matching_hypotheses
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (inner:Finset U) (Old:U→Finset V) (hOld:∀w,Disjoint (rawReservedSpokeList π d σ w) (Old w))
    (Kbad:SimpleGraph V) (Bad:V→Finset U) (n:ℕ) (ρ:ℝ) (hρ:0≤ρ)
    (hU:ρ*n≤Fintype.card U) (hinner:(inner.card:ℝ)≤ρ*n/80000)
    (herror:(n:ℝ)^(3/4:ℝ)≤ρ*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ)):
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner
    (∀e,Disjoint (Lbad e) inner) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,(ρ/40000)*n≤((Lbad e).card:ℝ)):=by
  intro Lbad
  have hmargin:(ρ/40000)*n+inner.card≤(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ):=by nlinarith
  obtain ⟨hout,hshield⟩:=protected_pair_edge_hubs_avoid_old_images (rawReservedSpokeList π d σ) Old inner hOld
  refine ⟨hout,?_,?_⟩
  · intro w e v he hv ho hw
    exact False.elim (hshield w e v hv ho hw)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:x≠y:=by
        intro h;subst y
        exact Kbad.loopless.irrefl x (by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he)
      have hh:=reserved_pair_allowed_hubs_lower π d σ inner x y _ (hpair x y hxy)
      change (ρ/40000)*n≤((protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner s(x,y)).card:ℝ)
      linarith
end Oberwolfach
