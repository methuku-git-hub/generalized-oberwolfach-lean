module

public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.AlmostSpanningCyclePacking

@[expose] public section
/-! Choose the weight bounds and order threshold for all short lengths before
the actual set of retained lengths is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_lengths_positive_fractional_weights
    (K:ℕ) (n:Fin K→ℕ) (hn:∀ i,1≤n i) (α:ℝ) (hα:0<α):
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (S:Finset (Fin K)) (G:SimpleGraph V),
      (∀ i:{i:Fin K // i∈S},∀ v,(cycleThreshold (n i.val+2)+α)*Fintype.card V≤(G.degree v:ℝ))→
    ∃ w:∀ i:{i:Fin K // i∈S},OrdinaryCycle G (n i.val+2)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i.val/(Fintype.card V:ℝ)^(n i.val)) ∧
      (∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0):=by
  classical
  have hex:∀ i:Fin K,∃ c C:ℝ,0<c ∧ 0<C ∧ ∃ N:ℕ,0<N ∧
      ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→∀ G:SimpleGraph V,
        (∀ v,(cycleThreshold (n i+2)+α)*Fintype.card V≤(G.degree v:ℝ))→
      ∃ w:OrdinaryCycle G (n i+2)→ℝ,
        (∀ H,c/(Fintype.card V:ℝ)^((n i+2)-2)≤w H ∧ w H≤C/(Fintype.card V:ℝ)^((n i+2)-2)) ∧
        (∀ e:G.edgeSet,∑ H,w H*ordinaryCycleIncidence G (n i+2) H e=1):=by
    intro i
    exact positive_ordinary_fractional_cycle_weights (n i+2) (by have :=hn i;omega) α hα
  choose c B hc hB Ni hNi hweights using hex
  refine ⟨B,hB,max 1 (Finset.univ.sup Ni),le_max_left _ _,?_⟩
  intro V _ _ hN S G hdeg
  have hi (i:{i:Fin K // i∈S}):∃ w:OrdinaryCycle G (n i.val+2)→ℝ,
      (∀ C,0≤w C ∧ w C≤B i.val/(Fintype.card V:ℝ)^(n i.val)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then w C else 0)=if G.Adj x y then 1 else 0):=by
    obtain ⟨w,hw,he⟩:=hweights i.val V
      ((Finset.le_sup (Finset.mem_univ i.val)).trans ((le_max_right 1 _).trans hN)) G (hdeg i)
    refine ⟨w,?_,ordinary_cycle_incidence_load_adjacency G (n i.val+2) w he⟩
    intro C
    have hlo:= (hw C).1
    have htop:= (hw C).2
    have hnonneg:0≤c i.val/(Fintype.card V:ℝ)^((n i.val+2)-2):=
      div_nonneg (hc i.val).le (pow_nonneg (Nat.cast_nonneg _) _)
    constructor
    · exact hnonneg.trans hlo
    · simpa only [Nat.add_sub_cancel] using htop
  choose w hw he using hi
  exact ⟨w,hw,he⟩
end Oberwolfach
