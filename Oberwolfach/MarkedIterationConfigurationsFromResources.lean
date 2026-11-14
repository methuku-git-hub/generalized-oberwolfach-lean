module

public import Oberwolfach.MarkedFiniteDeletionGraphBounds
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletionOnDomain

@[expose] public section

/-! The actual protected-star resource loss controls local cycle and
root-omitted path counts at every ambient root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_iteration_configurations_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (B : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ σ : ℝ) (hn : 0<X.card)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈B)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈B)).card : ℝ)≤δ)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈B.filter (markedStarResource X Z))).card : ℝ)≤σ)
    (P : SimpleGraph V) (d r : ℕ) (βC βP : ℝ) (ω : RawMarkedOutcome V U Γ Color)
    (hc : MarkedLocalConfigurationsWithSpokes r P π d X βC βP ω H) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    MarkedLocalConfigurationsWithSpokes r P π d X
      (βC-2*(r+5:ℝ)*σ/X.card) (βP-(2*r+11:ℝ)*σ/X.card)
      (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) := by
  intro DR DS
  obtain ⟨_,_,hrim,_,hcol⟩ := marked_finite_deletion_graph_bounds tail head ktail khead π
    (H false) (H true) A S B X Z hX δ σ hA hS hSB hB hStar
  have hn0 : (X.card:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : σ/(X.card:ℝ)*X.card=σ := by field_simp
  have hh := marked_local_configurations_after_physical_deletion_on_domain r P π d X hX βC βP
    (σ/X.card) (σ/X.card) ω H hc DR DS
    (fun x=>by rw [he];exact hrim x) (fun u=>by rw [he];exact hcol u)
  convert hh using 1 <;> push_cast <;> ring

end Oberwolfach
