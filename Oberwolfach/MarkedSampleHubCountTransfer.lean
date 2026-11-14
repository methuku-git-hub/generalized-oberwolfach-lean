module

public import Oberwolfach.SampledCommonMarkedPaths
public import Oberwolfach.HubCommonPathCycles
public import Oberwolfach.MarkedConfigurationSpokeChanges

@[expose] public section

/-! Surviving dense tuples give actual cycles and common paths at a hub.
The path roots remain outside the free-coordinate and spoke conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V]

def survivingBase_to_hub_cycle
    (P:SimpleGraph V) (π:Equiv.Perm V) (b m:ℕ)
    (τ:Sym2 V→Option (Bool×Bool)) (H₀ Hₖ:V→U→Prop) (u:U)
    (T₀ TK:Finset V) (h₀:∀ v∈T₀,H₀ v u) (hK:∀ v∈TK,Hₖ v u):
    {C:DenseMarkedBaseFamily P π b m T₀ TK // MarkedBaseRims P π b m τ C.val}↪
      HubMarkedCycle
        (fun e:MarkedSampleArc P π b τ false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π b τ true=>e.val.1) (fun e=>e.val.2) m π b H₀ Hₖ u where
  toFun C:=⟨C.val.val,⟨C.val.property.1,
    fun i=>⟨⟨(C.val.val i.castSucc,C.val.val i.succ),C.property.1 i⟩,rfl,rfl⟩,
    ⟨⟨(C.val.val (Fin.last m),C.val.val 0),C.property.2⟩,rfl,rfl⟩⟩,
    hK _ C.val.property.2.1,fun i=>h₀ _ (C.val.property.2.2.1 i)⟩
  inj' C D he:=by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C:HubMarkedCycle
      (fun e:MarkedSampleArc P π b τ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b τ true=>e.val.1) (fun e=>e.val.2) m π b H₀ Hₖ u=>C.val) he

def survivingPath_to_hub_path
    (P:SimpleGraph V) (π:Equiv.Perm V) (b m:ℕ) (hm:2≤m)
    (τ:Sym2 V→Option (Bool×Bool)) (H₀ Hₖ:V→U→Prop) (u:U)
    (T₀ TK:Finset V) (h₀:∀ v∈T₀,H₀ v u) (hK:∀ v∈TK,Hₖ v u)
    (j:Bool) (v v':V):
    {C:DenseRootMarkedPathFamily P π b m j T₀ TK v v' // MarkedPathRims P π b m j v v' τ C.val}↪
      RootFirstCommonMarkedPath
        (fun e:MarkedSampleArc P π b τ false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π b τ true=>e.val.1) (fun e=>e.val.2) (m+1) π b H₀ Hₖ j v v' u u where
  toFun C:=by
    refine ⟨C.val.val,?_,?_,?_⟩
    · exact markedPathRims_rootCycle P π b m j v v' τ hm C.val.val false C.val.property.1 C.property
    · exact markedPathRims_rootCycle P π b m j v v' τ hm C.val.val true C.val.property.2.1 C.property
    · intro i
      rw [rootFirstSpokeType_free m hm j i]
      have hmem:=C.val.property.2.2.1 i
      by_cases hc:j=false∧i.val=2
      · simp only [hc,ite_true,decide_true] at hmem ⊢
        exact ⟨hK _ hmem,hK _ hmem⟩
      · simp only [hc,ite_false,decide_false,Bool.false_eq_true] at hmem ⊢
        exact ⟨h₀ _ hmem,h₀ _ hmem⟩
  inj' C D he:=by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C:RootFirstCommonMarkedPath
      (fun e:MarkedSampleArc P π b τ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b τ true=>e.val.1) (fun e=>e.val.2) (m+1) π b H₀ Hₖ j v v' u u=>C.val) he

theorem marked_local_configurations_hub_counts
    [Fintype U] {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V)
    (βC βP:ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H):
    (∀ u,βC*(A.card:ℝ)^(r+5)≤Fintype.card (HubMarkedCycle
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (H false) (H true) u))∧
    (∀ u j v v',v≠v'→βP*(A.card:ℝ)^(r+4)≤Fintype.card (RootFirstCommonMarkedPath
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (H false) (H true) j v v' u u)):=by
  constructor
  · intro u
    apply (h.1 u).trans
    exact_mod_cast Fintype.card_le_of_injective _
      (survivingBase_to_hub_cycle P π (3*d) (r+4) (fun e=>σ (Sum.inl e)) (H false) (H true) u
        (A.filter (H false · u)) (A.filter (H true · u))
        (fun _ hx=>(Finset.mem_filter.mp hx).2) (fun _ hx=>(Finset.mem_filter.mp hx).2)).injective
  · intro u j v v' hv
    apply (h.2 u j v v' hv).trans
    exact_mod_cast Fintype.card_le_of_injective _
      (survivingPath_to_hub_path P π (3*d) (r+3) (by omega) (fun e=>σ (Sum.inl e)) (H false) (H true) u
        (A.filter (H false · u)) (A.filter (H true · u))
        (fun _ hx=>(Finset.mem_filter.mp hx).2) (fun _ hx=>(Finset.mem_filter.mp hx).2) j v v').injective

end Oberwolfach
