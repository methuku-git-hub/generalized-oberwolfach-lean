module

public import Oberwolfach.MarkedFiniteDeletionGraphBounds
public import Oberwolfach.MarkedNeighbourhoodDeletionOnDomain

@[expose] public section

/-! The protected cover-down incidence output supplies both the full and
smaller-domain neighbourhood comparisons at the next step. Both graphs
are formed from the actual deleted finite arc and spoke sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_iteration_neighbourhoods_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (B : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ σ : ℝ) (hδ : 0≤δ) (hσ : 0≤σ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈B)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈B)).card : ℝ)≤δ)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈B.filter (markedStarResource X Z))).card : ℝ)≤σ)
    (P : SimpleGraph V) (d h : ℕ) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (errR errI errX errZ : ℝ) (ω : RawMarkedOutcome V U Γ Color)
    (hr : MarkedRowsWithSpokes P π d h Finset.univ p k q s g j errR ω H)
    (hi : MarkedIndicesWithSpokes π d h Finset.univ q s g j errI ω H)
    (hx : MarkedRowsWithSpokes P π d h X p k q s g j errX ω H)
    (hz : MarkedIndicesWithSpokes π d h Z q s g j errZ ω H) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S
    let ω' := rawMarkedDeleteRims ω DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS;
    MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (errR+2*h*δ) ω' H' ∧
    MarkedIndicesWithSpokes π d h Finset.univ q s g j (errI+h*δ) ω' H' ∧
    MarkedRowsWithSpokes P π d h X p k q s g j (errX+2*h*σ) ω' H' ∧
    MarkedIndicesWithSpokes π d h Z q s g j (errZ+h*σ) ω' H' := by
  intro DR DS ω' H'
  obtain ⟨hrim,hspoke,hinto,hrow,hcol⟩ := marked_finite_deletion_graph_bounds
    tail head ktail khead π (H false) (H true) A S B X Z hX δ σ hA hS hSB hB hStar
  have hg := marked_neighbourhoods_after_physical_deletion P π d h Finset.univ Finset.univ p k q s g j
    errR errI δ δ δ hδ hδ hδ ω H hr hi DR DS hrim (fun v=>hspoke (Sum.inl v)) (fun u=>hspoke (Sum.inr u))
  have hl := marked_neighbourhoods_after_deletion_on_domain P π d h X Z hX p k q s g j
    errX errZ σ σ σ hσ hσ hσ ω H hx hz DR DS hinto hrow hcol
  refine ⟨?_,hg.2,?_,hl.2⟩
  · convert hg.1 using 1 <;> ring
  · convert hl.1 using 1 <;> ring

end Oberwolfach
