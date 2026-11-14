module

public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! The selected physical graph is contained in the sampled class, so exact
agreement on the first vortex set preserves every selected inner edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem long_selected_physical_subgraph_sampled_class
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    longSelectedPhysicalGraph P π d ω≤longPhysicalStateGraph P ω {0,1,2,3,4} := by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  let E:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true
  have hpair (a b x y:V) (hxy:x≠y) (h:({a,b}:Finset V)={x,y})
      (hab:(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj a b):
      (longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y := by
    have hx:x∈({a,b}:Finset V):=by rw [h];simp
    have hy:y∈({a,b}:Finset V):=by rw [h];simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with hxa|hxb <;> rcases hy with hya|hyb
    · exact (hxy (hxa.trans hya.symm)).elim
    · simpa only [hxa,hyb] using hab
    · simpa only [hxb,hya] using hab.symm
    · exact (hxy (hxb.trans hyb.symm)).elim
  have hArc (b:Bool) (a c:V) (h:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) b a c=1):
      (longPhysicalStateGraph P ω {0,1,2,3,4}).Adj a (if b then π c else c) := by
    obtain ⟨_,hP,hstate⟩:=(markedPhysicalRim_eq_one_iff P π (3*d) _ b a c).mp h
    have hcat:(ω (Sum.inl s(a,if b then π c else c))).1=0 ∨
        (ω (Sum.inl s(a,if b then π c else c))).1=1 := by
      by_cases h0:(ω (Sum.inl s(a,if b then π c else c))).1=0
      · exact Or.inl h0
      · by_cases h1:(ω (Sum.inl s(a,if b then π c else c))).1=1
        · exact Or.inr h1
        · simp only [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,if_neg h0,if_neg h1] at hstate
          cases hstate
    refine ⟨hP,?_⟩
    rcases hcat with h0|h1
    · simp [h0]
    · simp [h1]
  intro x y hxy
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hxy.2
  cases a with
  | inl e=>
    have ha':({e.val.1,e.val.2}:Finset V)={x,y}:=ha
    exact hpair e.val.1 e.val.2 x y hxy.1 ha' (by simpa using hArc false e.val.1 e.val.2 e.property)
  | inr e=>
    have ha':({e.val.1,π e.val.2}:Finset V)={x,y}:=ha
    exact hpair e.val.1 (π e.val.2) x y hxy.1 ha' (by simpa using hArc true e.val.1 e.val.2 e.property)

theorem long_selected_inner_preserved_in_regular_class
    (P S A:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (T:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hAgree:∀x y,((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y→
      (S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)):
    ∀x∈T,∀y∈T,(longSelectedPhysicalGraph P π d ω).Adj x y→S.Adj x y := by
  intro x hx y hy hxy
  have hz:(spanningRestriction (⊤:SimpleGraph V) T).Adj x y:=
    (spanningRestriction_adj ⊤ T x y).mpr ⟨hxy.1,hx,hy⟩
  exact (hAgree x y (show ((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y from Or.inl hz)).mpr
    ((long_selected_physical_subgraph_sampled_class P π d ω) hxy)
end Oberwolfach
