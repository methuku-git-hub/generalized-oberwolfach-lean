module

public import Oberwolfach.MarkedExtensionCountRestriction

@[expose] public section

/-! The root-omitted canonical common-path count after a realized deletion.
The four root spokes are not needed for this count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem marked_canonical_path_count_restriction
    (hm : 1≤m) (PE : E → Prop) (PK : K → Prop)
    (β d : ℝ) (hbudget : 4*((m:ℝ)+1)*d≤β*Fintype.card V)
    (hEout : ∀ x,(∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hEin : ∀ x,(∑ e,if ¬PE e ∧ head e=x then (1:ℝ) else 0)≤d)
    (hKout : ∀ x,(∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d)
    (hKin : ∀ x,(∑ e,if ¬PK e ∧ khead e=x then (1:ℝ) else 0)≤d)
    (hH0 : ∀ u,(∑ x,if H₀ x u ∧ ¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHK : ∀ u,(∑ x,if Hₖ x u ∧ ¬Hₖ' x u then (1:ℝ) else 0)≤d)
    (i : Fin (m+1)) (v v' : V) (u u' : U)
    (hbase : 2*β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ)) :
    β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (CanonicalCommonMarkedPath (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' i v v' u u'):ℝ) := by
  have hloss := commonMarkedPath_deletion_count hm tail head ktail khead π b PE PK
    H₀ Hₖ H₀' Hₖ' i v v' u u' d hEout hEin hKout hKin hH0 hHK
  have hscale := mul_le_mul_of_nonneg_right hbudget (pow_nonneg (by positivity : 0≤(Fintype.card V:ℝ)) (m-1))
  have hscale' : 4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1)≤β*(Fintype.card V:ℝ)^m := by
    have he : (Fintype.card V:ℝ)^m=(Fintype.card V:ℝ)*(Fintype.card V:ℝ)^(m-1) := by
      rw [← pow_succ'];congr 1;omega
    rw [he]
    convert hscale using 1 <;> ring
  linarith

end Oberwolfach
