module

public import Oberwolfach.MarkedFiniteDeletionGraphBounds
public import Oberwolfach.MarkedDomainSpokeLoadsAfterDeletion
public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section

/-! Fixed local weights retain their potential-spoke estimates after the
actual protected-star deletion. The coefficient is charged at the original
local order, and the potential root need not survive the deletion. The hub
embedding is unrestricted: every deleted spoke with its row in X already
belongs to the protected star, even when its hub lies outside Y. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K W Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W]
    [DecidableEq U] [DecidableEq Z] [DecidableEq E] [DecidableEq K]

theorem finite_spoke_graph_comap_star
    (S : Finset (V×U)) (X : Finset V) (Y : Finset U) (f : W→V) (g : Z→U)
    (hf : ∀ x,f x∈X) :
    (markedFiniteSpokeGraph S).comap (Sum.map f g)=
      (markedFiniteSpokeGraph (S.filter (fun s=>s.1∈X ∨ s.2∈Y))).comap (Sum.map f g) := by
  ext a b
  cases a with
  | inl x=>
    cases b with
    | inl y=>simp only [SimpleGraph.comap_adj,Sum.map_inl,(markedFiniteSpokeGraph_same_part S).1,
        (markedFiniteSpokeGraph_same_part (S.filter (fun s=>s.1∈X ∨ s.2∈Y))).1]
    | inr u=>simp only [SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,markedFiniteSpokeGraph_adj,Finset.mem_filter,hf,or_true,true_or,and_true]
  | inr u=>
    cases b with
    | inl x=>simp only [SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,SimpleGraph.adj_comm,markedFiniteSpokeGraph_adj,Finset.mem_filter,hf,or_true,true_or,and_true]
    | inr v=>simp only [SimpleGraph.comap_adj,Sum.map_inr,(markedFiniteSpokeGraph_same_part S).2,
        (markedFiniteSpokeGraph_same_part (S.filter (fun s=>s.1∈X ∨ s.2∈Y))).2]

theorem marked_iteration_restricted_deletion_degrees
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Y : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ : ℝ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres.filter (markedStarResource X Y))).card : ℝ)≤δ)
    (f : W↪oV) (g : Z↪U) (hf : ∀ x,f x∈X)
 :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    (∀ x : W,((DR.comap f).degree x:ℝ)≤δ) ∧
    (∀ z : W⊕Z,((DS.comap (Sum.map f g)).degree z:ℝ)≤δ) := by
  intro DR DS
  obtain ⟨_,hr,hc,ha⟩ := marked_finite_star_counts_from_incidence tail head ktail khead π (H false) (H true)
    A S Bres X Y hX δ hA hS hSB hStar
  let AS := A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)
  let SS := S.filter (fun s=>s.1∈X ∨ s.2∈Y)
  have hrim (x : W) : ((DR.neighborFinset (f x)∩Finset.univ.image f).card:ℝ)≤δ := by
    have hsub : Finset.univ.image f⊆X := by
      intro v hv;obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hv;exact hf w
    have hle := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl (DR.neighborFinset (f x))) hsub)
    apply (Nat.cast_le.mpr hle).trans
    apply (Nat.cast_le.mpr (finite_physical_arc_graph_into_set tail head ktail khead π A X hX (f x))).trans
    exact (Nat.cast_le.mpr (finite_physical_arc_graph_degree tail head ktail khead π AS (f x))).trans (ha (f x))
  have hsp (z : W⊕Z) : (((DS.comap (Sum.map f g)).degree z):ℝ)≤δ := by
    have he : (DS.comap (Sum.map f g)).degree z=((markedFiniteSpokeGraph SS).comap (Sum.map f g)).degree z := by
      simp only [←SimpleGraph.ncard_neighborSet]
      rw [finite_spoke_graph_comap_star S X Y f g hf]
    rw [he]
    have hd := Nat.cast_le (α:=ℝ).mpr (graph_comap_injective_degree_le (markedFiniteSpokeGraph SS) (f.toEmbedding.sumMap g) z)
    apply hd.trans
    cases z with
    | inl x=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts SS).1 (f x))).trans (hr (f x))
    | inr u=>exact (Nat.cast_le.mpr ((finite_spoke_graph_degree_counts SS).2 (g u))).trans (hc (g u))
  refine ⟨?_,hsp⟩
  intro x
  exact (congrArg (fun n:ℕ=>(n:ℝ)) (graph_comap_degree_into_image DR f.toEmbedding x)).trans_le (hrim x)

theorem marked_iteration_local_loads_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Y : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres.filter (markedStarResource X Y))).card : ℝ)≤δ)
    (f : W↪oV) (g : Z↪U) (hf : ∀ x,f x∈X)
    (P : SimpleGraph V) (ρ : Equiv.Perm W) (d m : ℕ) (hm : 3≤m) (hn : 0<Fintype.card W)
    (D τ aLo B : ℝ) (hDlo : (Fintype.card W:ℝ)/2≤D) (hDhi : D≤2*Fintype.card W)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (m+1)→W)→ℝ)
    (hw : SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (eps : ℝ) (ω : RawMarkedOutcome V U Γ Color)
    (hload : MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight eps
      (rawMarkedRestrictPair f g ω) (fun b x z=>H b (f x) (g z))) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S;
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight
      (eps+15*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card W)
      (rawMarkedRestrictPair f g (rawMarkedDeleteRims ω DR.edgeFinset))
      (fun b x z=>markedDeletePhysicalSpokes H DS b (f x) (g z)) := by
  intro DR DS
  obtain ⟨hR,hS'⟩ := marked_iteration_restricted_deletion_degrees tail head ktail khead π H
    A S Bres X Y hX δ hA hS hSB hStar f g hf
  have hrim (x : W) : ((DR.neighborFinset (f x)∩Finset.univ.image f).card:ℝ)≤δ := by
    exact (congrArg (fun n:ℕ=>(n:ℝ)) (graph_comap_degree_into_image DR f.toEmbedding x).symm).trans_le (hR x)
  have hspoke (z : W⊕Z) : ((DS.neighborFinset (Sum.map f g z)∩Finset.univ.image (Sum.map f g)).card:ℝ)≤δ := by
    have he := graph_comap_degree_into_image DS (f.toEmbedding.sumMap g) z
    exact (congrArg (fun n:ℕ=>(n:ℝ)) he.symm).trans_le (hS' z)
  have hh := marked_domain_spoke_loads_after_global_physical_deletion f g P ρ d m hm hn D τ aLo B
    hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw eps δ δ hδ hδ ω H hload DR DS hrim hspoke
  convert hh using 1 <;> ring

end Oberwolfach
