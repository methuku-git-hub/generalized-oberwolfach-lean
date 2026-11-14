module

public import Oberwolfach.MarkedIterationLocalLoadsFromResources
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletion

@[expose] public section

/-! Local row and configuration estimates in a fixed inner vertex domain,
with arbitrary external hub domain, after the actual protected-star deletion.
The errors use the original local order and no new sampling event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K W Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W]
    [DecidableEq U] [DecidableEq Z] [DecidableEq E] [DecidableEq K]

theorem marked_iteration_restricted_profiles
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (Bres : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Y : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈Bres)
    (hS : ∀ s∈S,H false s.1 s.2 ∨ H true s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈Bres)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈Bres.filter (markedStarResource X Y))).card : ℝ)≤δ)
    (f : W↪oV) (g : Z↪U) (hf : ∀ x,f x∈X)
    (P : SimpleGraph V) (ρ : Equiv.Perm W) (d h r : ℕ) (hn : 0<Fintype.card W)
    (p k : ℝ) (q : Z→Γ→ℝ) (s : Z→Color→ℝ) (a : Γ) (c : Color)
    (err βC βP : ℝ) (σ : RawMarkedOutcome V U Γ Color)
    (hrow : MarkedRowsWithSpokes (P.comap f) ρ d h Finset.univ p k q s a c err
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)))
    (hconf : MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ βC βP
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u))) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S
    let σ' := rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let H' := fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d h Finset.univ p k q s a c (err+2*h*δ) σ' H' ∧
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ
      (βC-2*(r+5:ℝ)*δ/Fintype.card W) (βP-(2*r+11:ℝ)*δ/Fintype.card W) σ' H' := by
  intro DR DS σ' H'
  obtain ⟨hrim,hspoke⟩ := marked_iteration_restricted_deletion_degrees tail head ktail khead π H
    A S Bres X Y hX δ hA hS hSB hStar f g hf
  have hr := markedRows_after_physical_rim_deletion (P.comap f) ρ d h Finset.univ p k q s a c
    err δ hδ (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)) hrow (DR.comap f) hrim
  have hr' := markedRows_spoke_relation_changes (P.comap f) ρ d h Finset.univ p k q s a c
    (err+h*δ) δ hδ (rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset)
    (fun b x u=>H b (f x) (g u)) _ hr
    (fun b u=>(marked_spoke_physical_deletion_column_change (fun b x u=>H b (f x) (g u))
      (DS.comap (Sum.map f g)) Finset.univ b u).trans (hspoke (Sum.inr u)))
  have hn0 : (Fintype.card W:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : δ/(Fintype.card W:ℝ)*Fintype.card W=δ := by field_simp
  have hc := marked_local_configurations_after_physical_deletion r (P.comap f) ρ d βC βP
    (δ/Fintype.card W) (δ/Fintype.card W) (rawMarkedRestrictPair f g σ)
    (fun b x u=>H b (f x) (g u)) hconf (DR.comap f) (DS.comap (Sum.map f g))
    (fun x=>by rw [he];exact hrim x) (fun u=>by rw [he];exact hspoke (Sum.inr u))
  dsimp only [σ',H']
  rw [rawMarkedRestrictPair_deleteRims,markedDeletePhysicalSpokes_restrict]
  constructor
  · convert hr' using 1 <;> ring
  · convert hc using 1 <;> push_cast <;> ring

end Oberwolfach
