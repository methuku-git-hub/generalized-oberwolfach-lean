module

public import Oberwolfach.ClassSharedRetentionProjection
public import Oberwolfach.ClassSimultaneousEvents200
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Intersect a partition event with all class-local raw-and-retained events
on the actual joint law, without assuming class independence. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_retained_simultaneous_events_200 (K:ℕ):
    ∃ χ:ℝ,0<χ ∧ ∃ N:ℕ,∀ k n:ℕ,k≤K+1→N≤n→
    ∀ (Ω C:Type) [Fintype Ω] [Fintype C]
      (A:Fin k→Type) [∀ i,Fintype (A i)]
      (F:∀ i,A i→Type) [∀ i x,Fintype (F i x)]
      (rawGlobal:FiniteLaw Ω) (colour:Ω→C) (colourLaw:FiniteLaw C)
      (view:∀ i,Ω→A i) (raw:∀ i,FiniteLaw (A i))
      (hcolour:rawGlobal.map colour=colourLaw) (hview:∀ i,rawGlobal.map (view i)=raw i)
      (ν:∀ i x,FiniteLaw (F i x))
      (Partition:C→Prop) (Good:∀ i,(Σ x:A i,F i x)→Prop),
      1-1/(n:ℝ)^10≤colourLaw.probability Partition→
      (∀ i,1-(100*χ+200/(n:ℝ))≤((raw i).sigma (ν i)).probability (Good i))→
      let joint:=rawGlobal.sigma (fun ω=>FiniteLaw.pi (fun i=>ν i (view i ω)));
      ∃ z,0<joint.mass z ∧ Partition (colour z.1) ∧ ∀ i,Good i ⟨view i z.1,z.2 i⟩:=by
  obtain ⟨χ,hχ,N,hN⟩:=class_simultaneous_events_200 K
  refine ⟨χ,hχ,N,?_⟩
  intro k n hk hn Ω C _ _ A _ F _ rawGlobal colour colourLaw view raw hcolour hview ν Partition Good hpart hgood joint
  have hc:joint.map (fun z=>colour z.1)=colourLaw:=by
    calc
      _ = (joint.map Sigma.fst).map colour:=by rw [finiteLaw_map_map]
      _ = _:=by
        dsimp [joint]
        rw [finiteLaw_sigma_map_first_dependent,hcolour]
  have hv:∀ i,joint.map (fun z=>(⟨view i z.1,z.2 i⟩:(Σ x:A i,F i x)))=(raw i).sigma (ν i):=by
    intro i
    rw [class_shared_retention_map,hview i]
  exact hN k n hk hn _ _ (fun i=>Σ x:A i,F i x) joint (fun z=>colour z.1) colourLaw
    (fun i z=>⟨view i z.1,z.2 i⟩) (fun i=>(raw i).sigma (ν i)) hc hv Partition Good hpart hgood
end Oberwolfach
