module

public import Oberwolfach.OrdinaryProtectedPairLocalReference
public import Oberwolfach.OrdinaryReservoirSurvivesComplement
public import Oberwolfach.OrdinaryReservoirSpokeLabels

@[expose] public section
/-! Exact agreement on the protected pair only needs local reference-spoke
avoidance; the reservoir survives when its own labels are avoided. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_pair_exact_with_local_spoke_avoidance
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} [∀u,Fintype (X u)]
    (Target Sample Reference Protect Embedded:SimpleGraph V) (Inner:Finset V) (Hubs:Finset U)
    (Href:V→U→Prop) (f:∀u,X u↪V)
    (hRef:Reference≤Sample)
    (hRefTarget:∀v∈Inner,∀w∈Inner,Reference.Adj v w→Target.Adj v w) (hProtect:Protect≤Reference)
    (hInnerProtect:spanningRestriction Reference Inner≤Protect)
    (hEmbedded:Embedded≤Target\Protect)
    (hcover:ordinaryProtectedRequired Target Sample Reference Inner≤Embedded)
    (hAvoid:∀u,u∈Hubs→∀x,f u x∈Inner→¬Href (f u x) u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v):
    (∀v∈Inner,∀w∈Inner,((Target\Embedded).Adj v w ↔ Reference.Adj v w)) ∧
    (∀v∈Inner,∀u∈Hubs,(v∉Set.range (f u) ↔ Href v u)):=by
  constructor
  · intro v hv w hw
    constructor
    · exact ordinary_required_cover_forces_reference_inner Target Sample Reference Protect Embedded Inner hRef hProtect hcover v hv w hw
    · intro hr
      refine ⟨hRefTarget v hv w hw hr,?_⟩
      intro he
      have hp:Protect.Adj v w:=hInnerProtect ((spanningRestriction_adj Reference Inner v w).mpr ⟨hr,hv,hw⟩)
      exact (hEmbedded he).2 hp
  · intro v hv u hu
    constructor
    · intro hnot
      by_contra hn
      have hT:v∈ordinaryInnerSpokeTargets Inner Hubs Href u:=by
        simp [ordinaryInnerSpokeTargets,hu,hv,hn]
      obtain ⟨x,hx⟩:=hSpokeCover u v hT
      exact hnot ⟨x,hx⟩
    · intro h hx
      obtain ⟨x,hx⟩:=hx
      exact hAvoid u hu x (hx ▸ hv) (hx ▸ h)

theorem ordinary_protected_reservoir_survives_actual_label_avoidance {n q:ℕ}
    (Reference Target:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Href:Fin n→Fin q→Prop) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserve:ordinaryResourceRim Reference A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\ordinaryResourceRim Reference A).Adj (f u x) (f u y))
    (hAvoid:∀u x,f u x∉ordinaryReservoirSpokeLabels A u):
    A⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C f)
      (fun v u=>v∉Set.range (f u)):=by
  let HA:=fun v u=>Sum.inr (v,u)∈A
  have hA':A⊆ordinaryHostResources Target HA:=by
    intro e he
    cases e with
    | inl e=>
      induction e using Sym2.inductionOn with
      | _ v w=>
        apply (ordinaryHostResources_rim _ _ _).mpr
        exact hReserve ⟨(ordinaryHostResources_rim Reference Href _).mp (hA he),he⟩
    | inr z=>
      rcases z with ⟨v,u⟩
      exact (ordinaryHostResources_spoke Target HA v u).mpr he
  have heq:ordinaryResourceRim Target A=ordinaryResourceRim Reference A:=by
    apply SimpleGraph.ext
    funext v w
    apply propext
    constructor
    · rintro ⟨_,he⟩
      exact ⟨(ordinaryHostResources_rim Reference Href _).mp (hA he),he⟩
    · intro he
      exact ⟨hReserve he,he.2⟩
  apply ordinary_reservoir_survives_complement Target Fs C f HA A hA'
  · intro u x y hxy
    rw [heq]
    exact hRim u x y hxy
  · intro u x h
    apply hAvoid u x
    simpa only [ordinaryReservoirSpokeLabels,Finset.mem_filter,Finset.mem_univ,true_and] using h
end Oberwolfach
