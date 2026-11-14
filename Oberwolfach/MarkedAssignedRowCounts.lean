module

public import Oberwolfach.MarkedAssignedRowWheel

@[expose] public section

/-! Complete the three permitted type combinations of assigned incoming
arc, outgoing arc and root spoke, under actual extension-count hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_assigned_row_wheel_from_counts
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c : ℝ}
    (hl : 2≤l) (v a z : V) (u : U) (jin jout : Bool)
    (htypes : ¬(jin=true ∧ jout=true))
    (W Z : Finset V) (hv : v∈Z)
    (haW : a∉W) (hzW : z∉W) (haZ : a∉Z) (hzZ : z∉Z)
    (haz : ¬PermutationClose π b a z)
    (haF : ∀ x∈Z, ¬PermutationClose π b a x) (hzF : ∀ x∈Z, ¬PermutationClose π b z x)
    (haH : if jout then HK a u else H₀ a u) (hzH : H₀ z u)
    (hroot : if jin then HK v u else H₀ v u)
    (hopen : markedArcPresent tail head ktail khead jout v a)
    (hclose : markedArcPresent tail head ktail khead jin z v)
    (hstep : ∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y)∧
      (if t then HK y u else H₀ y u))).card:ℝ))
    (hjoin : ∀ x y,x≠y→c≤((Finset.univ.filter (fun q=>(∃ e,tail e=x∧head e=q)∧
      (∃ e,tail e=q∧head e=y)∧H₀ q u)).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+l+4)*(2*b+1)<c) :
    ∃ p : Fin (l+3) ↪ V, ∃ C : MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      p 0=a ∧ p (Fin.last (l+2))=z ∧ C.2.val=u ∧
      (∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (l+3) jin jout i)) ∧
      (∀ i, p i∉W ∧ p i∉Z ∧ ∀ x∈Z, ¬PermutationClose π b (p i) x) ∧
      PermutationSeparated π b p := by
  cases jout
  · have ho : (∃ e, tail e=v ∧ head e=a) ∧ (∃ e, tail e=v ∧ head e=a) := by
      simpa [markedArcPresent] using hopen
    have hc : if jin then (∃ e, ktail e=z ∧ khead e=v) ∧ (∃ e, ktail e=z ∧ khead e=v)
        else (∃ e, tail e=z ∧ head e=v) ∧ (∃ e, tail e=z ∧ head e=v) := by
      cases jin <;> simpa [markedArcPresent] using hclose
    have hr : if jin then HK v u ∧ HK v u else H₀ v u ∧ H₀ v u := by
      cases jin <;> simpa using hroot
    obtain ⟨p,C,D,hp0,hplast,hCu,hDu,hC,hD,hav,hsep⟩ := marked_fixed_attachment_wheels
      tail head ktail khead H₀ HK π b l hl v v a z u jin W Z hv hv haW hzW haZ hzZ
      haz haF hzF ⟨haH,hzH⟩ hr ho hc c hstep hjoin hbudget
    exact ⟨p,C,hp0,hplast,hCu,hC,hav,hsep⟩
  · have hjin : jin=false := by cases jin <;> simp_all
    subst jin
    obtain ⟨p,C,hp0,hplast,hCu,hC,hav,hsep⟩ := marked_fixed_opening_wheel
      tail head ktail khead H₀ HK π b l (by omega) v a z u W Z hv haW hzW haZ hzZ
      haz haF hzF haH hzH hroot hopen hclose c (hstep false) hjoin hbudget
    exact ⟨p,C,hp0,hplast,hCu,hC,hav,hsep⟩

end Oberwolfach
