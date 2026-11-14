module

public import Oberwolfach.MarkedSeedNormalization
public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section

/-! Uniform seed bounds derived from the fixed successor weighting.
A zero coefficient remains zero; positive parent coefficients retain a lower bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

variable {V : Type} [Fintype V] {m b : ℕ} {P : SimpleGraph V} {π : Equiv.Perm V}
  {D τ A B : ℝ} {weight : (Fin (m+1)→V)→ℝ}

theorem successor_seed_nonneg_upper
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (hm : 1≤m) (hn : 0<Fintype.card V)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s≤1) (hB : 0≤B)
    (C : Fin (m+1)→V) :
    0≤weight C/(D*p^m*k*s^m) ∧
      weight C/(D*p^m*k*s^m)≤(2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m := by
  have hn' : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hh := marked_seed_coefficient_bounds m hm (Fintype.card V) D p k s 0 B (weight C) pstar
    hn' hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 (by norm_num) hB
    (by simpa using hw.nonneg C) (by simpa only [show m+1-2=m-1 by omega] using hw.upper C)
  simpa using hh

theorem successor_seed_positive_lower
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (hm : 1≤m) (hn : 0<Fintype.card V)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s≤1) (hA : 0≤A) (hB : 0≤B)
    (C : Fin (m+1)→V) (hvalid : SuccessorSequenceValid P π C) (hsep : PermutationSeparated π b C) :
    (A/2)/(Fintype.card V:ℝ)^m≤weight C/(D*p^m*k*s^m) := by
  have hn' : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  exact (marked_seed_coefficient_bounds m hm (Fintype.card V) D p k s A B (weight C) pstar
    hn' hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 hA hB
    (by simpa only [show m+1-2=m-1 by omega] using hw.lower C hvalid hsep)
    (by simpa only [show m+1-2=m-1 by omega] using hw.upper C)).1

end Oberwolfach
