module

public import Oberwolfach.MarkedResourceRimGraph
public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.MarkedSupportedResourceFamilies

@[expose] public section

/-! Every rim resource of the selected absorber came from the corrected
sample, and hence lies in the original sampled class. Agreement on the
protected rim graph places it in the later regular class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem long_reserved_sample_rim_contained_in_class
    (P S Z:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (D:Finset (Sym2 V)):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let σ':=rawMarkedDeleteRims raw D
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
    (∀x y,(Z⊔markedResourceRimGraph C.edges).Adj x y→
      (S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y))→
    markedResourceRimGraph C.edges≤longPhysicalStateGraph P ω {0,1,2,3,4} ∧
      markedResourceRimGraph C.edges≤S := by
  intro raw σ' E' K' C hAgree
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
  have hArc (b:Bool) (a c:V) (h:markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) b a c=1):
      (longPhysicalStateGraph P ω {0,1,2,3,4}).Adj a (if b then π c else c) := by
    obtain ⟨_,hP,hstate⟩:=(markedPhysicalRim_eq_one_iff P π (3*d) _ b a c).mp h
    have hstate' : raw (Sum.inl s(a,if b then π c else c))=some (b,orientationBit a (if b then π c else c)) := by
      by_cases hd:s(a,if b then π c else c)∈D
      · simp only [σ',rawMarkedDeleteRims,if_pos hd] at hstate
        cases hstate
      · simpa only [σ',rawMarkedDeleteRims,if_neg hd] using hstate
    have hcat:(ω (Sum.inl s(a,if b then π c else c))).1=0 ∨
        (ω (Sum.inl s(a,if b then π c else c))).1=1 := by
      by_cases h0:(ω (Sum.inl s(a,if b then π c else c))).1=0
      · exact Or.inl h0
      · by_cases h1:(ω (Sum.inl s(a,if b then π c else c))).1=1
        · exact Or.inr h1
        · simp only [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,if_neg h0,if_neg h1] at hstate'
          cases hstate'
    refine ⟨hP,?_⟩
    rcases hcat with h0|h1
    · simp [h0]
    · simp [h1]
  have hsub:markedResourceRimGraph C.edges≤longPhysicalStateGraph P ω {0,1,2,3,4}:=by
    intro x y hxy
    have hmem:Sum.inl ({x,y}:Finset V)∈C.edges:=(Finset.mem_filter.mp hxy.2).2
    obtain ⟨a,ha,_,_⟩:=C.supported _ hmem
    cases a with
    | inl e=>
      have ha':({e.val.1,e.val.2}:Finset V)={x,y}:=ha
      exact hpair e.val.1 e.val.2 x y hxy.1 ha' (by simpa using hArc false e.val.1 e.val.2 e.property)
    | inr e=>
      have ha':({e.val.1,π e.val.2}:Finset V)={x,y}:=ha
      exact hpair e.val.1 (π e.val.2) x y hxy.1 ha' (by simpa using hArc true e.val.1 e.val.2 e.property)
  refine ⟨hsub,?_⟩
  intro x y hxy
  exact (hAgree x y (show (Z⊔markedResourceRimGraph C.edges).Adj x y from Or.inr hxy)).mpr (hsub hxy)
end Oberwolfach
