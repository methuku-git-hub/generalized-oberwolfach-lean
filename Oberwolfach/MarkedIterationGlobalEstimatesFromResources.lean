module

public import Oberwolfach.MarkedFiniteDeletionGraphBounds
public import Oberwolfach.MarkedPackingPotentialPhysicalDeletion
public import Oberwolfach.MarkedCommonConfigurationsAfterPhysicalDeletion

@[expose] public section

/-! Global potential loads and common configurations after deletion of the
actual finite resources returned by cover-down. The original coefficient
function is retained, including at potential roots absent from the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_global_deletion_graph_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U))) (δ : ℝ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres)).card : ℝ)≤δ) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    (∀ v,(DR.degree v:ℝ)≤δ) ∧ (∀ z,(DS.degree z:ℝ)≤δ) := by
  intro DR DS
  obtain ⟨_,hr,hc,ha⟩ := marked_finite_counts_from_incidence tail head ktail khead π (H false) (H true)
    A S Bres δ hA hS hSB hB
  constructor
  · intro v
    exact (Nat.cast_le.mpr (finite_physical_arc_graph_degree tail head ktail khead π A v)).trans (ha v)
  · intro z
    cases z with
    | inl v=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts S).1 v)).trans (hr v)
    | inr u=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts S).2 u)).trans (hc u)

theorem marked_iteration_global_loads_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U))) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hBres : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres)).card : ℝ)≤δ)
    (P : SimpleGraph V) (d m : ℕ) (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (D τ aLo B : ℝ) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (m+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight)
    (eps : ℝ) (ω : RawMarkedOutcome V U Γ Color)
    (R : (((V×V)⊕(V×V))⊕(Bool×V×U))→Prop)
    (hload : let seed := fun (W : MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True))=>weight W.1.val/(D*p^m*k*s₀^m);
      ∀ root,R root→|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d ω) H root-1|≤eps) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S
    let seed := fun (W : MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True))=>weight W.1.val/(D*p^m*k*s₀^m);
    ∀ root,R root→|typedMarkedPotentialLoad seed
      (rawMarkedPairRims P π d (rawMarkedDeleteRims ω DR.edgeFinset))
      (markedDeletePhysicalSpokes H DS) root-1|≤
        eps+33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V := by
  intro DR DS seed root hroot
  obtain ⟨hr,hsdeg⟩ := marked_finite_global_deletion_graph_bounds tail head ktail khead π H A S Bres δ hA hS hSB hBres
  have hh := marked_packing_potential_after_physical_deletion P π d m hm hn hu D τ aLo B hDlo hDhi
    p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw δ δ hδ hδ ω H root DR DS hr
    (fun x=>hsdeg (Sum.inl x)) (fun u=>hsdeg (Sum.inr u))
  have h := (abs_sub_le
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedDeleteRims ω DR.edgeFinset))
      (markedDeletePhysicalSpokes H DS) root)
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d ω) H root) 1).trans
      (add_le_add hh (hload root hroot))
  convert h using 1 <;> ring

theorem marked_iteration_common_configurations_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U))) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres)).card : ℝ)≤δ)
    (P : SimpleGraph V) (d r : ℕ) (β ζ : ℝ) (hn : 0<Fintype.card V)
    (ω : RawMarkedOutcome V U Γ Color)
    (hc : MarkedCommonConfigurationsWithSpokes r P π d β ζ ω H) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    MarkedCommonConfigurationsWithSpokes r P π d β (ζ+4*δ/Fintype.card V)
      (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) := by
  intro DR DS
  obtain ⟨hr,hsdeg⟩ := marked_finite_global_deletion_graph_bounds tail head ktail khead π H A S Bres δ hA hS hSB hB
  exact marked_common_configurations_after_physical_deletion r P π d β ζ δ hδ hn ω H DR DS hr hsdeg hc

end Oberwolfach
