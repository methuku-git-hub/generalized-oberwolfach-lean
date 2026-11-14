module

public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section
/-! Extension lower bounds persist when typed arcs and spokes are added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_host_extension_counts_mono
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V) (ktail' khead':K'→V)
    (H₀ HK H₀' HK':V→U→Prop) (π:Equiv.Perm V) (b l:ℕ) (c ch:ℝ)
    (hArc:∀ j x y,markedArcPresent tail head ktail khead j x y →
      markedArcPresent tail' head' ktail' khead' j x y)
    (h₀:∀x u,H₀ x u→H₀' x u) (hk:∀x u,HK x u→HK' x u)
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch):
    MarkedHostExtensionCounts tail' head' ktail' khead' H₀' HK' π b l c ch := by
  have hSp:∀ j P x,markedSpokesTo H₀ HK j P x→markedSpokesTo H₀' HK' j P x:=by
    intro j P x h u hu
    cases j <;> simp only [markedSpokesTo,Bool.false_eq_true,ite_false,ite_true] at h ⊢
    · exact h₀ x u (h u hu)
    · exact hk x u (h u hu)
  constructor
  · intro j k x P hP
    apply (Q.outgoing j k x P hP).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
    exact ⟨hArc j x y hy.1,hSp k P y hy.2⟩
  · intro j k x P hP
    apply (Q.incoming j k x P hP).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
    exact ⟨hArc j y x hy.1,hSp k P y hy.2⟩
  · intro k x y P hxy hP
    apply (Q.twoOutgoing k x y P hxy hP).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact ⟨hArc false x z hz.1,hArc false y z hz.2.1,hSp k P z hz.2.2⟩
  · intro j k x y P hxy hP
    apply (Q.twoIncoming j k x y P hxy hP).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact ⟨hArc j z x hz.1,hArc j z y hz.2.1,hSp k P z hz.2.2⟩
  · intro k x y P hxy hP
    apply (Q.twoStep k x y P hxy hP).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact ⟨hArc false x z hz.1,hArc false z y hz.2.1,hSp k P z hz.2.2⟩
  · intro A B hd hab hsep
    apply (Q.hubs A B hd hab hsep).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
    exact ⟨fun x hx=>h₀ x u (hu.1 x hx),fun x hx=>hk x u (hu.2 x hx)⟩
end Oberwolfach
