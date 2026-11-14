module

public import Oberwolfach.MarkedOpeningArcWheel
public import Oberwolfach.MarkedOpeningAttachmentPath
public import Oberwolfach.MarkedFixedAttachmentWheels

@[expose] public section

/-! Complete the assigned outgoing marked arc, incoming ordinary arc and
root spoke, choosing only the internal attachment-path vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [DecidableEq V]

theorem marked_fixed_opening_wheel
    (tail head : E → V) (ktail khead : K → V) (H₀ HK : V → U → Prop)
    (π : Equiv.Perm V) (b l : ℕ) (hl : 1≤l) (v a z : V) (u : U)
    (W Z : Finset V) (hv : v∈Z)
    (haW : a∉W) (hzW : z∉W) (haZ : a∉Z) (hzZ : z∉Z)
    (haz : ¬PermutationClose π b a z)
    (haF : ∀ x∈Z, ¬PermutationClose π b a x) (hzF : ∀ x∈Z, ¬PermutationClose π b z x)
    (haH : HK a u) (hzH : H₀ z u) (hroot : H₀ v u)
    (hopen : ∃ e, ktail e=v ∧ khead e=a) (hclose : ∃ e, tail e=z ∧ head e=v)
    (c : ℝ)
    (hstep : ∀ x, c≤((Finset.univ.filter (fun y => (∃ e, tail e=x ∧ head e=y) ∧ H₀ y u)).card:ℝ))
    (hjoin : ∀ x y, x≠y → c≤((Finset.univ.filter (fun q => (∃ e, tail e=x ∧ head e=q) ∧
      (∃ e, tail e=q ∧ head e=y) ∧ H₀ q u)).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+l+4)*(2*b+1)<c) :
    ∃ p : Fin (l+3) ↪ V, ∃ A : MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      p 0=a ∧ p (Fin.last (l+2))=z ∧ A.2.val=u ∧
      (∀ i, A.1.val i=Fin.cons (α:=fun _=>V) v p (canonicalMarkedRotation 0 i)) ∧
      (∀ i, p i∉W ∧ p i∉Z ∧ ∀ x∈Z, ¬PermutationClose π b (p i) x) ∧
      PermutationSeparated π b p := by
  let F := permutationConflictGraph π b
  have hF : ∀ x, (F.degree x:ℝ)≤2*b := by
    intro x; exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,hp0,hplast,hpa,hfirst,hfree,hav,hsep⟩ := marked_opening_attachment_path F
    (fun x y => ∃ e, tail e=x ∧ head e=y) H₀ HK u W Z l hl a z
    (fun he => haz (Or.inl he)) (fun he => haz he.2) haW hzW haZ hzZ
    (fun x hx he => haF x hx he.2) (fun x hx he => hzF x hx he.2)
    haH hzH (2*b) c (by positivity) hF hstep hjoin hbudget
  have hps : PermutationSeparated π b p := by
    intro i k hik hc
    exact hsep i k ⟨fun he => hik (p.injective he),hc⟩
  have hout (i : Fin (l+3)) (x : V) (hx : x∈Z) : ¬PermutationClose π b (p i) x := by
    intro hc
    exact (hav i).2.2 x hx ⟨fun he => (hav i).2.1 (he ▸ hx),hc⟩
  have hcons : PermutationSeparated π b (Fin.cons v p) :=
    permutationSeparated_cons π b v p hps
      (fun i he => hout i v hv ((permutationClose_symm π b v (p i)).mp he))
  obtain ⟨A,hAu,hA⟩ := marked_wheel_with_marked_opening tail head ktail khead (l+2) π b H₀ HK v u p
    hcons (by rw [hp0]; exact hopen) (by rw [hplast]; exact hclose) hpa hroot hfirst hfree
  exact ⟨p,A,hp0,hplast,hAu,hA,fun i => ⟨(hav i).1,(hav i).2.1,hout i⟩,hps⟩

end Oberwolfach
