module

public import Oberwolfach.MarkedIterationGlobalEstimatesFromResources
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletion
public import Oberwolfach.MarkedLocalEstimateMonotonicity
public import Oberwolfach.MarkedIterationErrorScales

@[expose] public section

/-! A single global deletion allowance supplies the potential-load and
deep-stage configuration inputs at every cover-down level. The weights,
root predicates and normalizing order are fixed before deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_global_cover_input_margins
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (F : Finset (Finset V⊕(V×U)))
    (ζ : ℝ) (hζ : 0≤ζ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈F)
    (hS : ∀ s∈S,H false s.1 s.2∨H true s.1 s.2) (hSF : ∀ s∈S,Sum.inr s∈F)
    (hInc : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈F)).card:ℝ)≤ζ*Fintype.card V)
    (P : SimpleGraph V) (r d : ℕ) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (D τ aLo B : ℝ) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (r+4+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight)
    (ε κ θ b : ℝ) (hκ : 0≤κ) (hθ : 0≤θ) (hε : ε≤κ/4)
    (hLoad : 33*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4)
    (hLocal : 33*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤θ/4)
    (hCycle : 2*(r+5:ℝ)*ζ≤b) (hPath : (2*r+11:ℝ)*ζ≤b)
    (σ : RawMarkedOutcome V U Γ Color)
    (R : (((V×V)⊕(V×V))⊕(Bool×V×U))→Prop)
    (hload : let seed := fun (W : MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True))=>weight W.1.val/(D*p^(r+4)*k*s₀^(r+4));
      ∀ root,R root→|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤ε)
    (hlocal : MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/4) σ H)
    (hconfigs : MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (3*b) (3*b) σ H) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS
    let seed := fun (W : MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True))=>weight W.1.val/(D*p^(r+4)*k*s₀^(r+4));
    (∀ root,R root→|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤κ) ∧
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ' H' ∧
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*b) (2*b) σ' H' := by
  intro DR DS σ' H' seed
  have hn0 : (Fintype.card V:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnle : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have hδ := mul_nonneg hζ hnle
  obtain ⟨hDR,hDS⟩ := marked_finite_global_deletion_graph_bounds tail head ktail khead π H
    A S F (ζ*Fintype.card V) hA hS hSF hInc
  have hGlobal := marked_iteration_global_loads_from_resource_bounds tail head ktail khead π H
    A S F (ζ*Fintype.card V) hδ hA hS hSF hInc P d (r+4) (by omega) hn hu D τ aLo B
    hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw ε σ R hload
  have hSpoke := marked_iteration_global_loads_from_resource_bounds tail head ktail khead π H
    A S F (ζ*Fintype.card V) hδ hA hS hSF hInc P d (r+4) (by omega) hn hu D τ aLo B
    hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw (θ/4) σ
    (fun z=>∃ a:Bool×V×U,z=Sum.inr a) (by dsimp only;intro root h;obtain ⟨a,rfl⟩:=h;exact hlocal a)
  have he : 33*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*(ζ*Fintype.card V)/Fintype.card V=
      33*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ := by
    push_cast
    field_simp
    ring
  have hC := marked_local_configurations_after_physical_deletion r P π d (3*b) (3*b) ζ ζ
    σ H hconfigs DR DS hDR (fun u=>hDS (Sum.inr u))
  refine ⟨?_,?_,?_⟩
  · intro root hr
    have h := hGlobal root hr
    rw [he] at h
    exact h.trans (by linarith only [hε,hLoad,hκ])
  · intro a
    have h := hSpoke (Sum.inr a) ⟨a,rfl⟩
    rw [he] at h
    exact h.trans (by linarith only [hLocal])
  · apply markedLocalConfigurations_mono r P π d Finset.univ _ _ (2*b) (2*b) _ _ _ _ hC
    · push_cast
      nlinarith only [hCycle]
    · push_cast
      nlinarith only [hPath]

end Oberwolfach
