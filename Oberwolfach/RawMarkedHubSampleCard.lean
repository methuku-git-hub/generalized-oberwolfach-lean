module

public import Oberwolfach.MarkedWheelHubSpokeCounts
public import Oberwolfach.RestrictedResourceSubsetCounts
public import Oberwolfach.MarkedRetainedResourceState

@[expose] public section
/-! The marked hub-spoke test set has one resource for each active raw
marked spoke at that hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def commonMarkedHubRoots (u:U):Finset (((V×V)⊕(V×V))⊕(Bool×V×U)):=
  Finset.univ.image (fun v:V=>Sum.inr (true,v,u))

theorem sampled_marked_hub_spoke_card
    (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop) (u:U):
    let state:=typedMarkedResourceState R H
    let e: {a // a∈bernoulliVertexSet state} ↪ (((V×V)⊕(V×V))⊕(Bool×V×U)):=
      Function.Embedding.subtype _
    ((restrictedResourceSubset e (commonMarkedHubRoots (V:=V) u)).card:ℕ)=
      (Finset.univ.filter (fun v=>H true v u)).card := by
  intro state e
  let A:=Finset.univ.filter (fun v=>H true v u)
  let f:V↪(((V×V)⊕(V×V))⊕(Bool×V×U)):=
    ⟨fun v=>Sum.inr (true,v,u),by intro x y h;exact congrArg Prod.fst (congrArg Prod.snd (Sum.inr.inj h))⟩
  have himage:(restrictedResourceSubset e (commonMarkedHubRoots (V:=V) u)).image e = A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
      have haS:a.val∈commonMarkedHubRoots (V:=V) u := (Finset.mem_filter.mp ha).2
      obtain ⟨v,_,hv⟩:=Finset.mem_image.mp haS
      have hz':a.val=Sum.inr (true,v,u):=hv.symm
      have hstate:state a.val=true:=(mem_bernoulliVertexSet state a.val).mp a.property
      have hvH:H true v u:=by simpa [state,hz',typedMarkedResourceState] using hstate
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvH⟩,by simpa [f,e] using hz'.symm⟩
    · intro hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      have hvH:H true v u:=(Finset.mem_filter.mp hv).2
      have ha:f v∈bernoulliVertexSet state:=by
        apply (mem_bernoulliVertexSet state (f v)).mpr
        simpa [state,f,typedMarkedResourceState] using hvH
      refine Finset.mem_image.mpr ⟨⟨f v,ha⟩,?_,rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hcard:=congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ e.injective,Finset.card_image_of_injective _ f.injective] at hcard
  exact hcard
theorem common_marked_wheel_hub_spoke_count
    {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b H₀ Hₖ) (u:U):
    (typedMarkedOccurrenceResources W∩commonMarkedHubRoots (V:=V) u).card=
      if W.2.val=u then 1 else 0 := by
  have hh:=marked_wheel_hub_marked_spoke_count W u
  have hroots:commonMarkedHubRoots (V:=V) u=markedHubSpokeRoots (V:=V) (E:=V×V) (K:=V×V) u := by
    ext z
    simp [commonMarkedHubRoots,markedHubSpokeRoots]
  rw [hroots]
  convert hh using 1 <;> congr! 4
end Oberwolfach
