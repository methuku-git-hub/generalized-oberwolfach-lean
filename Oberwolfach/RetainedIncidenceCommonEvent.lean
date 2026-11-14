module

public import Oberwolfach.RetainedIncidenceTails
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! One physical Bernoulli event supplies all support sizes, intersections
and membership bounds. The event precedes every later deletion or choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_incidence_support_common_event (M ε:ℝ) (hM:1≤M) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→
    ∀ (V J E:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
      [Fintype E] [DecidableEq E], Fintype.card V≤n→Fintype.card J≤n→
    ∀ C:J→V→Finset E,
      (∀ i v,((C i v).card:ℝ)≤M)→
      (∀ i e,((Finset.univ.filter (fun v=>e∈C i v)).card:ℝ)≤M)→
      (∀ i j,i≠j→∀ v,Disjoint (C i v) (C j v))→
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
        (fun σ=>
          (∀ i,((retainedIncidenceSet C σ i).card:ℝ)<p*M*Fintype.card V+ε*n)∧
          (∀ i j,i≠j→((retainedIncidenceSet C σ i∩retainedIncidenceSet C σ j).card:ℝ)<p^2*M^2*Fintype.card V+ε*n)∧
          (∀ v,((Finset.univ.filter (fun i=>v∈retainedIncidenceSet C σ i)).card:ℝ)<p*M*Fintype.card J+ε*n)) := by
  have hM0:0<M:=by linarith
  obtain ⟨N,hN⟩:=linear_deviation_failure_eventually_small 3 ((2*M)^2) ε (by positivity) hε 2 q
  refine ⟨max 1 N,?_⟩
  intro n hn V J E _ _ _ _ _ _ hV hJ C hread haffect hdisj p hp hp1
  have hn0:0<n:=by omega
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr hn0
  have hVR:(Fintype.card V:ℝ)≤n:=Nat.cast_le.mpr hV
  have hJR:(Fintype.card J:ℝ)≤n:=Nat.cast_le.mpr hJ
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)
  let T:=J⊕(J×J)⊕V
  let Bad:T→(E→Bool)→Prop:=Sum.elim
    (fun i σ=>p*M*Fintype.card V+ε*n≤((retainedIncidenceSet C σ i).card:ℝ))
    (Sum.elim (fun ij σ=>ij.1≠ij.2∧
      p^2*M^2*Fintype.card V+ε*n≤((retainedIncidenceSet C σ ij.1∩retainedIncidenceSet C σ ij.2).card:ℝ))
      (fun v σ=>p*M*Fintype.card J+ε*n≤((Finset.univ.filter (fun i=>v∈retainedIncidenceSet C σ i)).card:ℝ)))
  let err:=2*Real.exp (-2*(ε*n)^2/((2*M)^2*n))
  have htail (t:T):μ.probability (Bad t)≤err := by
    rcases t with i|ij|v
    · exact retainedIncidenceSet_row_tail C i p hp hp1 M n hM0 hnR hVR (hread i) (haffect i) (ε*n) (by positivity)
    · by_cases hne:ij.1=ij.2
      · simp only [Bad,Sum.elim_inr,Sum.elim_inl,hne,ne_eq,not_true_eq_false,false_and]
        rw [finiteLaw_probability_false]
        dsimp [err];positivity
      · apply (finiteLaw_probability_mono μ _ _ (fun σ hσ=>hσ.2)).trans
        exact retainedIncidenceSet_pair_tail C ij.1 ij.2 (hdisj _ _ hne) p hp hp1 M n hM0 hnR hVR
          hread haffect (ε*n) (by positivity)
    · exact retainedIncidenceSet_membership_tail C v (fun i j hij=>hdisj i j hij v) p hp hp1
        M n hM hnR hJR (fun i=>hread i v) (ε*n) (by positivity)
  have hcount:(Fintype.card T:ℝ)≤3*(n:ℝ)^2 := by
    have hn1:(1:ℝ)≤n:=by exact_mod_cast hn0
    dsimp [T]
    simp only [Fintype.card_sum,Fintype.card_prod,Nat.cast_add,Nat.cast_mul]
    nlinarith [sq_nonneg ((n:ℝ)-Fintype.card J)]
  have hsmall:=hN n (by omega) (Fintype.card T) ((2*M)^2*n)
    (Nat.cast_nonneg _) hcount (by positivity) (le_refl _)
  have hh:=finiteLaw_common_event_lower μ Finset.univ Bad (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply ((sub_le_sub_left hsmall 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨fun i=>not_le.mp (hσ (Sum.inl i)),?_,fun v=>not_le.mp (hσ (Sum.inr (Sum.inr v)))⟩
  intro i j hij
  exact not_le.mp (fun hh=>hσ (Sum.inr (Sum.inl (i,j))) ⟨hij,hh⟩)

end Oberwolfach
