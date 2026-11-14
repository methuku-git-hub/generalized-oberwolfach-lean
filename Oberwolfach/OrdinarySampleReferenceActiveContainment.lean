module

public import Oberwolfach.OrdinaryApproximateActiveRimContainment

@[expose] public section
/-! Apart from the three exceptional colours and the conflict/deletion
graphs, the full sample outside its reference lies in the active rim graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_reference_active_rim_containment
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let Host:=ordinaryEligibleHost P π d
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims Host π d raw') (rawMarkedPairSpokes π d raw' true true)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let ι:PhysicalSampledActive φ state↪Sym2 (Fin n)⊕(Fin n×U):=Function.Embedding.subtype _
    let Except:=(((longPhysicalStateGraph P σ {1}⊔longPhysicalStateGraph P σ {3})⊔longPhysicalStateGraph P σ {4})⊔
      (permutationConflictGraph π (3*d+2)⊔Del));
    longPhysicalStateGraph P σ {0,1,2,3,4}\longPhysicalStateGraph P σ {0}≤physicalRimResidualGraph ι ∅⊔Except:=by
  intro raw raw' Host state φ ι Except x y hxy
  have hP:P.Adj x y:=hxy.1.1
  have hnot0:(σ (Sum.inl s(x,y))).1≠0:=by
    intro he
    apply hxy.2
    exact ⟨hP,by simpa using he⟩
  have hstate:(σ (Sum.inl s(x,y))).1=1 ∨ (σ (Sum.inl s(x,y))).1=2 ∨
      (σ (Sum.inl s(x,y))).1=3 ∨ (σ (Sum.inl s(x,y))).1=4:=by
    have hh:=hxy.1.2
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    tauto
  rcases hstate with h1|h2|h3|h4
  · right;left;left;left;exact ⟨hP,by simpa using h1⟩
  · have hh:=ordinary_approximate_colour_two_active_rim_containment P Del π d σ (show (longPhysicalStateGraph P σ {2}).Adj x y from ⟨hP,by simpa using h2⟩)
    rcases hh with hh|hh
    · rcases hh with hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inr (Or.inr hh))
  · right;left;left;right;exact ⟨hP,by simpa using h3⟩
  · right;left;right;exact ⟨hP,by simpa using h4⟩
end Oberwolfach
