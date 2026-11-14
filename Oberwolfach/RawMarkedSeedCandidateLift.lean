module

public import Oberwolfach.MarkedRawSampledPhysicalEmbedding
public import Oberwolfach.TypedMarkedPotentialResources

@[expose] public section
/-! A marked seed whose typed resources all survive in the raw approximate
sample is an actual marked wheel with the same tuple and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_marked_seed_candidate_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    (∀z∈typedMarkedOccurrenceResources W,state z=true)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true
    let H:=rawMarkedPairSpokes π d raw g j
    ∃W':MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:K=>e.val.1) (fun e:K=>e.val.2) m π (3*d) (H false) (H true),
      W'.1.val=W.1.val ∧ W'.2.val=W.2.val:=by
  intro state hactive E K H
  have hOrd (i:Fin m):∃e:E,e.val.1=W.1.val i.castSucc ∧ e.val.2=W.1.val i.succ:=by
    let e:=Classical.choose (W.1.property.2.1 i)
    have he:=Classical.choose_spec (W.1.property.2.1 i)
    have hmem:Sum.inl (Sum.inl e)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_rim W (Sum.inl e)).mpr
      exact ⟨i.castSucc,by simp [markedCycleTypedEdge,e]⟩
    have hstate:=hactive _ hmem
    have he':markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false e.1 e.2=1:=by
      simpa [state,typedMarkedResourceState,rawMarkedPairRims] using hstate
    exact ⟨⟨e,he'⟩,he⟩
  have hMark:∃e:K,e.val.1=W.1.val (Fin.last m) ∧ e.val.2=W.1.val 0:=by
    let e:=Classical.choose W.1.property.2.2
    have he:=Classical.choose_spec W.1.property.2.2
    have hmem:Sum.inl (Sum.inr e)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_rim W (Sum.inr e)).mpr
      exact ⟨Fin.last m,by simp [markedCycleTypedEdge,e]⟩
    have hstate:=hactive _ hmem
    have he':markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) true e.1 e.2=1:=by
      simpa [state,typedMarkedResourceState,rawMarkedPairRims] using hstate
    exact ⟨⟨e,he'⟩,he⟩
  have hHub:MarkedHubCompatible (H false) (H true) W.1.val W.2.val:=by
    constructor
    · have hmem:Sum.inr (true,W.1.val 0,W.2.val)∈typedMarkedOccurrenceResources W:=by
        apply (typedMarkedOccurrenceResources_spoke W _).mpr
        exact ⟨0,by simp⟩
      simpa [state,H,typedMarkedResourceState] using hactive _ hmem
    · intro i
      have hmem:Sum.inr (false,W.1.val i.succ,W.2.val)∈typedMarkedOccurrenceResources W:=by
        apply (typedMarkedOccurrenceResources_spoke W _).mpr
        exact ⟨i.succ,by simp⟩
      simpa [state,H,typedMarkedResourceState] using hactive _ hmem
  let C':MarkedCycleTuple (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:K=>e.val.1) (fun e:K=>e.val.2) m π (3*d):=⟨W.1.val,W.1.property.1,hOrd,hMark⟩
  exact ⟨⟨C',⟨W.2.val,hHub⟩⟩,rfl,rfl⟩
end Oberwolfach
