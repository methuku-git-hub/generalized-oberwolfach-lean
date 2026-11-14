module

public import Oberwolfach.MarkedFiniteCountsFromIncidence
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Concrete deletion graphs and their degrees, including neighbours of
external roots into a protected set. No restriction of the root set occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem finite_physical_arc_graph_degree
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (A : Finset (E⊕K)) (v : V) :
    (physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))).degree v ≤
      (A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card := by
  apply (physicalEdgeGraph_degree_le_incident _ v).trans
  rw [Finset.filter_image]
  exact Finset.card_image_le

theorem finite_spoke_graph_degree_counts (S : Finset (V×U)) :
    (∀ v,(markedFiniteSpokeGraph S).degree (Sum.inl v)≤(S.filter (fun s=>s.1=v)).card) ∧
    (∀ u,(markedFiniteSpokeGraph S).degree (Sum.inr u)≤(S.filter (fun s=>s.2=u)).card) := by
  constructor
  · intro v
    rw [markedFiniteSpokeGraph_degree_row]
    apply Finset.card_le_card_of_injOn (fun u=>(v,u))
    · intro u hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2,rfl⟩
    · intro a ha b hb h
      exact congrArg Prod.snd h
  · intro u
    rw [markedFiniteSpokeGraph_degree_col]
    apply Finset.card_le_card_of_injOn (fun v=>(v,u))
    · intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,rfl⟩
    · intro a ha b hb h
      exact congrArg Prod.fst h

theorem finite_physical_arc_graph_into_set
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (A : Finset (E⊕K)) (X : Finset V) (hX : ∀ v,π v∈X↔v∈X) (v : V) :
    ((physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))).neighborFinset v∩X).card ≤
      (physicalEdgeGraph ((A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)).image
        (markedPhysicalEdge tail head ktail khead π))).degree v := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hadj,hwX⟩ := Finset.mem_inter.mp hw
  have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hadj
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hadj.2
  apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
  refine ⟨hadj.1,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,he⟩⟩
  have hwA : w∈markedPhysicalEdge tail head ktail khead π a := by rw [he];simp
  cases a with
  | inl a=>
    simp only [Sum.elim_inl]
    have hw : w=tail a ∨ w=head a := by simpa only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] using hwA
    rcases hw with h|h
    · exact Or.inl (h ▸ hwX)
    · exact Or.inr (h ▸ hwX)
  | inr a=>
    simp only [Sum.elim_inr]
    have hw : w=ktail a ∨ w=π (khead a) := by simpa only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] using hwA
    rcases hw with h|h
    · exact Or.inl (h ▸ hwX)
    · exact Or.inr ((hX _).mp (h ▸ hwX))

theorem finite_spoke_graph_into_sets (S : Finset (V×U)) (X : Finset V) (Z : Finset U) :
    (∀ v,((Z.filter (fun u=>(markedFiniteSpokeGraph S).Adj (Sum.inl v) (Sum.inr u))).card)≤
      (markedFiniteSpokeGraph (S.filter (fun s=>s.1∈X ∨ s.2∈Z))).degree (Sum.inl v)) ∧
    (∀ u,((X.filter (fun v=>(markedFiniteSpokeGraph S).Adj (Sum.inl v) (Sum.inr u))).card)≤
      (markedFiniteSpokeGraph (S.filter (fun s=>s.1∈X ∨ s.2∈Z))).degree (Sum.inr u)) := by
  constructor
  · intro v
    rw [markedFiniteSpokeGraph_degree_row]
    apply Finset.card_le_card
    intro u hu
    obtain ⟨hu,hadj⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨(markedFiniteSpokeGraph_adj S v u).mp hadj,Or.inr hu⟩⟩
  · intro u
    rw [markedFiniteSpokeGraph_degree_col]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hv,hadj⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨(markedFiniteSpokeGraph_adj S v u).mp hadj,Or.inl hv⟩⟩

theorem marked_finite_deletion_graph_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H₀ HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (B : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ σ : ℝ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈S,H₀ s.1 s.2 ∨ HK s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈B)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B)).card : ℝ)≤δ)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B.filter (markedStarResource X Z))).card : ℝ)≤σ) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    (∀ v,(DR.degree v:ℝ)≤δ) ∧ (∀ z,(DS.degree z:ℝ)≤δ) ∧
    (∀ v,((DR.neighborFinset v∩X).card:ℝ)≤σ) ∧
    (∀ v,((Z.filter (fun u=>DS.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤σ) ∧
    (∀ u,((X.filter (fun v=>DS.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤σ) := by
  intro DR DS
  obtain ⟨_,hr,hc,ha⟩ := marked_finite_counts_from_incidence tail head ktail khead π H₀ HK A S B δ hA hS hSB hB
  obtain ⟨_,hsr,hsc,hsa⟩ := marked_finite_star_counts_from_incidence tail head ktail khead π H₀ HK A S B X Z hX σ hA hS hSB hStar
  let AS := A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)
  let SS := S.filter (fun s=>s.1∈X ∨ s.2∈Z)
  have hrd (v) : ((physicalEdgeGraph (AS.image (markedPhysicalEdge tail head ktail khead π))).degree v:ℝ)≤σ :=
    (Nat.cast_le.mpr (finite_physical_arc_graph_degree tail head ktail khead π AS v)).trans (hsa v)
  have hsd (z) : ((markedFiniteSpokeGraph SS).degree z:ℝ)≤σ := by
    cases z with
    | inl v=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts SS).1 v)).trans (hsr v)
    | inr u=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts SS).2 u)).trans (hsc u)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v;exact (Nat.cast_le.mpr (finite_physical_arc_graph_degree tail head ktail khead π A v)).trans (ha v)
  · intro z
    cases z with
    | inl v=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts S).1 v)).trans (hr v)
    | inr u=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts S).2 u)).trans (hc u)
  · intro v;exact (Nat.cast_le.mpr (finite_physical_arc_graph_into_set tail head ktail khead π A X hX v)).trans (hrd v)
  · intro v;exact (Nat.cast_le.mpr ((finite_spoke_graph_into_sets S X Z).1 v)).trans (hsd (Sum.inl v))
  · intro u;exact (Nat.cast_le.mpr ((finite_spoke_graph_into_sets S X Z).2 u)).trans (hsd (Sum.inr u))

end Oberwolfach
