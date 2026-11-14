module

public import Oberwolfach.MarkedPackingLoadSpokeChanges
public import Oberwolfach.MarkedPackingPotentialPhysicalDeletion
public import Oberwolfach.MarkedPhysicalDeletionRestriction
public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section

/-! The full packing-load predicate, including external potential spokes
and all potential roots on the smaller hub domain, after physical deletion.
Both evaluations use the same original weight and normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U] [DecidableEq Z]

theorem rawMarkedRestrictHubs_deleteRims
    (f : Z→U) (σ : RawMarkedOutcome V U Γ Color) (D : SimpleGraph V) :
    rawMarkedRestrictHubs f (rawMarkedDeleteRims σ D.edgeFinset)=
      rawMarkedDeleteRims (rawMarkedRestrictHubs f σ) D.edgeFinset := by
  funext a
  cases a <;> rfl

theorem marked_packing_loads_after_physical_deletion
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (hm : 3≤m) (hn : 0<Fintype.card V)
    (D τ A B : ℝ) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (m+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (a : Γ) (j : Color) (f : Z↪U) (hz : Fintype.card Z≤Fintype.card V)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (ε δ : ℝ) (hδ : 0≤δ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hload : MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j f q s ε σ H)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U))
    (hDR : ∀ x,(DR.degree x:ℝ)≤δ) (hDS : ∀ z,(DS.degree z:ℝ)≤δ) :
    MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j f q s
      (ε+33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) := by
  constructor
  · have hh := marked_local_spoke_loads_after_physical_deletion P π d m hm hn D τ A B hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw ε δ δ hδ hδ σ H hload.1 DR DS
      hDR (fun x=>hDS (Sum.inl x)) (fun u=>hDS (Sum.inr u))
    intro root
    apply (hh root).trans
    have hcoef : 0≤((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V := by positivity
    convert add_le_add_left (mul_le_mul_of_nonneg_right (show (15:ℝ)≤33 by norm_num) hcoef) ε using 1 <;> ring
  · dsimp only
    intro root hroot
    let DS' := DS.comap (Sum.map (id : V→V) f)
    have hDS' (z : V⊕Z) : (DS'.degree z:ℝ)≤δ := by
      have hh := Nat.cast_le (α:=ℝ).mpr
        (graph_comap_injective_degree_le DS ((Function.Embedding.refl V).sumMap f) z)
      exact hh.trans (hDS _)
    have hh := marked_packing_potential_after_physical_deletion P π d m hm hn hz D τ A B hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw δ δ hδ hδ
      (rawMarkedRestrictHubs f σ) (fun b x z=>H b x (f z)) root DR DS'
      hDR (fun x=>hDS' (Sum.inl x)) (fun z=>hDS' (Sum.inr z))
    let seed := fun (W : MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:Z)=>True) (fun _ _=>True))=>weight W.1.val/(D*p^m*k*s₀^m)
    have h := (abs_sub_le
      (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d
        (rawMarkedDeleteRims (rawMarkedRestrictHubs f σ) DR.edgeFinset))
          (markedDeletePhysicalSpokes (fun b x z=>H b x (f z)) DS') root)
      (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
          (fun b x z=>H b x (f z)) root) 1).trans (add_le_add hh (hload.2 root hroot))
    have heH : (fun b x z=>markedDeletePhysicalSpokes H DS b x (f z))=
        markedDeletePhysicalSpokes (fun b x z=>H b x (f z)) DS' := by
      funext b x z
      rfl
    rw [rawMarkedRestrictHubs_deleteRims,heH]
    change |typedMarkedPotentialLoad seed _ _ root-1|≤_
    convert h using 1 <;> ring

end Oberwolfach
