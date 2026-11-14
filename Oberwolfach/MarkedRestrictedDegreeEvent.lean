module

public import Oberwolfach.MarkedRestrictedDegreeCentres

@[expose] public section

/-! One physical sample controls all four restricted directed degrees
at every ambient root, including roots outside the invariant domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedRestrictedDegree_common_event (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (A : Finset V) (hInv : ∀ y,π y∈A ↔ y∈A) (t : ℝ) (ht : 0≤t) :
    1-8*Fintype.card V*Real.exp (-2*t^2/A.card)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>∀ (mark incoming : Bool) (x : V),
        |(markedRestrictedDegree P π b σ mark incoming x A:ℝ)-
          (if mark then k else p)*(P.neighborFinset (if mark && incoming then π x else x)∩A).card|≤t+(2*(b:ℝ)+1)) := by
  let I := Bool×Bool×V
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let Bad := fun (i : I) σ=>t≤|(markedRestrictedDegree P π b σ i.1 i.2.1 i.2.2 A:ℝ)-
    (if i.1 then k else p)*(markedDegreeDomain P π b i.1 i.2.1 i.2.2 A).card|
  have hh := finiteLaw_common_event_lower μ (Finset.univ : Finset I) Bad
    (fun _=>2*Real.exp (-2*t^2/A.card))
    (fun i _=>markedRestrictedDegree_tail P π b p k hp hk hsum i.1 i.2.1 i.2.2 A t ht)
  have he : (∑ _ : I,2*Real.exp (-2*t^2/A.card))=8*Fintype.card V*Real.exp (-2*t^2/A.card) := by
    simp only [Finset.sum_const,Finset.card_univ,I,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
    ring
  rw [he] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ mark incoming x
  have hi := (not_le.mp (hσ (mark,incoming,x) (Finset.mem_univ _))).le
  apply markedRestrictedDegree_parent_error P π b σ mark incoming x A hInv (if mark then k else p) t _ _ hi
  · cases mark <;> assumption
  · cases mark <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith

end Oberwolfach
