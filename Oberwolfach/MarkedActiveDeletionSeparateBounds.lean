module

public import Oberwolfach.MarkedActiveDeletionDegrees
public import Oberwolfach.GraphComapUnionDegree

@[expose] public section

/-! Keep distinct row and hub allowances when summing deletions on the actual
active domains. Bounds on discarded roots are neither needed nor assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K V₀ U₀:Type} [Fintype V] [Fintype U] [Fintype V₀] [Fintype U₀]
  [LinearOrder V] [DecidableEq U] [DecidableEq V₀] [DecidableEq U₀]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_active_total_deletion_bounds_separate
    (MD:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (I T:Finset V) (J W:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅)
    (f:V₀↪V) (g:U₀↪U) (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U)) (eR eV eU cR cV cU:ℝ)
    (heR:∀ x,(ER.degree x:ℝ)≤eR) (heV:∀ x,(ES.degree (Sum.inl x):ℝ)≤eV) (heU:∀ u,(ES.degree (Sum.inr u):ℝ)≤eU)
    (hcR:0≤cR) (hcV:0≤cV)
    (hR:∀ x∉I,((markedPackingRimGraph MD).degree x:ℝ)≤cR)
    (hV:∀ x∉I,((Finset.univ.filter (markedPackingSpokes MD x)).card:ℝ)≤cV)
    (hU:∀ u∉W,((Finset.univ.filter (fun x=>markedPackingSpokes MD x u)).card:ℝ)≤cU):
    (∀ x,(((ER⊔markedPackingRimGraph MD).comap f).degree x:ℝ)≤eR+cR) ∧
    (∀ x,(((ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤eV+cV) ∧
    (∀ u,(((ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤eU+cU):=by
  have hb:=marked_packing_active_deletion_degrees MD I T J W hstar f g hf hg cR cV cU hcR hcV hR hV hU
  refine ⟨graph_comap_union_degree_bound ER _ f eR cR heR hb.1,?_,?_⟩
  · intro x
    have he:(ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)=
        ES.comap (Sum.map f g)⊔(markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g):=by ext a z;rfl
    have hES:((ES.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤eV:=
      (Nat.cast_le.mpr (graph_comap_injective_degree_le ES (f.sumMap g) (Sum.inl x))).trans (heV _) 
    have hsum:=graph_degree_sup_le (ES.comap (Sum.map f g))
      ((markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)) (Sum.inl x)
    have hr:=add_le_add hES (hb.2.1 x)
    have hh:= (Nat.cast_le (α:=ℝ)).mpr hsum
    push_cast at hh
    have hf':=hh.trans hr
    simpa only [←SimpleGraph.ncard_neighborSet,he] using hf'
  · intro u
    have he:(ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)=
        ES.comap (Sum.map f g)⊔(markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g):=by ext a z;rfl
    have hES:((ES.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤eU:=
      (Nat.cast_le.mpr (graph_comap_injective_degree_le ES (f.sumMap g) (Sum.inr u))).trans (heU _)
    have hsum:=graph_degree_sup_le (ES.comap (Sum.map f g))
      ((markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)) (Sum.inr u)
    have hr:=add_le_add hES (hb.2.2 u)
    have hh:= (Nat.cast_le (α:=ℝ)).mpr hsum
    push_cast at hh
    have hf':=hh.trans hr
    simpa only [←SimpleGraph.ncard_neighborSet,he] using hf'

end Oberwolfach
