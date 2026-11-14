module

public import Oberwolfach.MarkedHubAbsorberCounts

@[expose] public section

/-! Uniform order threshold for the one-hub paired-absorber construction.
The positive count coefficient and order threshold precede the host graph,
permutation, separation distance, hub, and root choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem paired_absorber_order_threshold (m : ℕ) (β : ℝ) (hβ : 0<β) :
    ∃ N : ℕ,∀ n : ℕ,N≤n →
      2*(m+1:ℝ)^2≤β*n ∧ 2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤β*n := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (2*(m+1:ℝ)^2/β)
    (2*(m:ℝ)*(2*(m+1)+(m+1)*m)/β))
  refine ⟨N,?_⟩
  intro n hn
  have hNn : (N:ℝ)≤n := by exact_mod_cast hn
  have h₁ := (le_max_left (2*(m+1:ℝ)^2/β) _).trans (hN.le.trans hNn)
  have h₂ := (le_max_right _ (2*(m:ℝ)*(2*(m+1)+(m+1)*m)/β)).trans (hN.le.trans hNn)
  exact ⟨by nlinarith only [(div_le_iff₀ hβ).mp h₁],
    by nlinarith only [(div_le_iff₀ hβ).mp h₂]⟩

theorem marked_hub_paired_absorber_abundance (m : ℕ) (hm : 3<m+1)
    (β : ℝ) (hβ : 0<β) :
    ∃ a : ℝ,0<a ∧ ∃ N : ℕ,
      ∀ (V U E K : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (tail head : E → V) (ktail khead : K → V)
        (π : Equiv.Perm V) (b : ℕ) (H₀ Hₖ : V → U → Prop) (w : U),
      β*(Fintype.card V:ℝ)^(m+1)≤
        Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) →
      (∀ j : Bool,∀ v v' : V,v≠v' →
        (if j then Hₖ v w else H₀ v w) → (if j then Hₖ v' w else H₀ v' w) →
        β*(Fintype.card V:ℝ)^m≤
          Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' w w)) →
      ∀ x : Fin (m+1) → V,Function.Injective x → MarkedHubCompatible H₀ Hₖ x w →
      a*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
        Fintype.card (LabelledCycleRecord
          (hubMarkedCycleVertices (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
            (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) w)
          (pairedAbsorberTemplate (m+1)).val (Finset.univ.image x)) := by
  obtain ⟨N,hN⟩ := paired_absorber_order_threshold m β hβ
  refine ⟨(β/2)^(m+2),by positivity,N,?_⟩
  intro V U E K _ _ hn tail head ktail khead π b H₀ Hₖ w hbase hpath x hx hxhub
  exact marked_hub_paired_absorber_count hm w x hx hxhub β hβ hbase hpath
    (hN _ hn).1 (hN _ hn).2

end Oberwolfach
