module

public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.InducedFractionalCycles
public import Oberwolfach.LongPreparationBadGraphMargins

@[expose] public section
/-! The required inner edges are physically unassigned, unused approximate,
or ineligible. The three cases are determined by the original six-state
physical exposure, without changing its orientation or labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_inner_required_physical_containment
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hP₀:P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
    (hSelected:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y):
    spanningRestriction (P₀\Sel) I≤
      (spanningRestriction (longPhysicalStateGraph P σ {4}) I ⊔
       spanningRestriction (longPhysicalStateGraph P σ {2,3}\Used) I) ⊔
       longPreparationIneligibleGraph P π d:=by
  intro x y h
  have hinner:=(spanningRestriction_adj (P₀\Sel) I x y).mp h
  have hp₀:P₀.Adj x y:=hinner.1.1
  have hnotSel:¬Sel.Adj x y:=hinner.1.2
  have hclass:=hP₀ hp₀
  have hP:P.Adj x y:=hclass.1.1
  have hUnused:¬Used.Adj x y:=hclass.2
  have hcat:(σ (Sum.inl s(x,y))).1=0 ∨ (σ (Sum.inl s(x,y))).1=1 ∨
      (σ (Sum.inl s(x,y))).1=2 ∨ (σ (Sum.inl s(x,y))).1=3 ∨ (σ (Sum.inl s(x,y))).1=4:=by
    simpa [longPhysicalStateGraph] using hclass.1.2
  simp only [SimpleGraph.sup_adj]
  by_cases hbad:(longPreparationIneligibleGraph P π d).Adj x y
  · exact Or.inr hbad
  · have hnotSelected:¬(longSelectedPhysicalGraph P π d σ).Adj x y:=fun hs=>
      hnotSel (hSelected x hinner.2.1 y hinner.2.2 hs)
    rcases hcat with hc|hc|hc|hc|hc
    · exact (hnotSelected (selected_state_outside_ineligible_is_selected P π d σ x y hP hbad (Or.inl hc))).elim
    · exact (hnotSelected (selected_state_outside_ineligible_is_selected P π d σ x y hP hbad (Or.inr hc))).elim
    · left;right
      apply (spanningRestriction_adj _ _ _ _).mpr
      refine ⟨?_,hinner.2.1,hinner.2.2⟩
      exact ⟨⟨hP,by simp [longPhysicalStateGraph,hc]⟩,hUnused⟩
    · left;right
      apply (spanningRestriction_adj _ _ _ _).mpr
      refine ⟨?_,hinner.2.1,hinner.2.2⟩
      exact ⟨⟨hP,by simp [longPhysicalStateGraph,hc]⟩,hUnused⟩
    · left;left
      apply (spanningRestriction_adj _ _ _ _).mpr
      exact ⟨⟨hP,by simp [longPhysicalStateGraph,hc]⟩,hinner.2.1,hinner.2.2⟩

def longCloseRequiredGraph (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (D M:V→V→Prop):SimpleGraph V where
  Adj x y:=P.Adj x y ∧ PermutationClose π (3*d) x y ∧
    ((D x y ∧ ¬M x y) ∨ (D y x ∧ ¬M y x))
  symm:=⟨by
    intro x y h
    exact ⟨h.1.symm,(permutationClose_symm π (3*d) x y).mp h.2.1,Or.symm h.2.2⟩⟩
  loopless:=⟨by intro x h;exact P.loopless.irrefl x h.1⟩

def longRequiredPhysicalGraph (P P₀ Sel:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (I:Finset V) (D M:V→V→Prop):SimpleGraph V:=
  spanningRestriction (P₀\Sel) I ⊔ longCloseRequiredGraph P π d D M

theorem long_required_physical_containment
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hP₀:P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
    (hSelected:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y):
    longRequiredPhysicalGraph P P₀ Sel π d I D M≤
      (spanningRestriction (longPhysicalStateGraph P σ {4}) I ⊔
       spanningRestriction (longPhysicalStateGraph P σ {2,3}\Used) I) ⊔
       longPreparationIneligibleGraph P π d:=by
  apply sup_le
  · exact long_inner_required_physical_containment P P₀ Sel Used π d I σ hP₀ hSelected
  · intro x y h
    simp only [SimpleGraph.sup_adj]
    exact Or.inr ⟨h.1,Or.inl h.2.1⟩

theorem long_required_physical_graph_margins
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (I:Finset V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hP₀:P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
    (hSelected:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)
    (α θ ε lam t C₀:ℝ) (hα:0<α) (hθ:0≤θ) (hθhi:θ≤1/100)
    (he:0≤ε) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀))
    (hlam:0≤lam) (hlamhi:lam≤α/128) (ht:0≤t) (htbound:t≤lam*Fintype.card V)
    (hn:(1536*(d:ℝ))/α≤Fintype.card V)
    (hI:(I.card:ℝ)≤ε*Fintype.card V)
    (hA:∀v∈I,((longPhysicalStateGraph P σ {4}).degree v:ℝ)≤2*θ*I.card+t)
    (hB:∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V):
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V:=by
  apply long_preparation_bad_graph_margins P (longRequiredPhysicalGraph P P₀ Sel π d I D M)
    (longPhysicalStateGraph P σ {2,3}\Used) (longPhysicalStateGraph P σ {4}) π d hd I
    α θ ε lam t C₀ hα hθ hθhi he hC hehi hlam hlamhi ht htbound hn hI hA
  · intro v hv
    convert hB v hv using 1 <;> congr!
  · exact long_required_physical_containment P P₀ Sel Used π d I D M σ hP₀ hSelected
end Oberwolfach
