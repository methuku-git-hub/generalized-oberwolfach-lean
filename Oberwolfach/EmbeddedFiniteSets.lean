module

public import Oberwolfach.BernoulliVertexSampling

@[expose] public section

/-! Exact transport of sampled sets, alterations and cardinalities along
a fixed vertex embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def embeddedPreimage (e:V↪W) (A:Finset W):Finset V:=
  Finset.univ.filter (fun v=>e v∈A)

theorem embeddedPreimage_mem (e:V↪W) (A:Finset W) (v:V):
    v∈embeddedPreimage e A↔e v∈A:=by simp [embeddedPreimage]

theorem embeddedPreimage_image (e:V↪W) (A:Finset W)
    (hA:∀ v∈A,∃ x,e x=v):(embeddedPreimage e A).image e=A:=by
  ext v
  simp only [Finset.mem_image,embeddedPreimage_mem]
  constructor
  · rintro ⟨x,hx,rfl⟩;exact hx
  · intro hv;obtain ⟨x,rfl⟩:=hA v hv;exact ⟨x,hv,rfl⟩

theorem embeddedPreimage_card (e:V↪W) (A:Finset W)
    (hA:∀ v∈A,∃ x,e x=v):(embeddedPreimage e A).card=A.card:=by
  have hh:=congrArg Finset.card (embeddedPreimage_image e A hA)
  simpa only [Finset.card_image_of_injective _ e.injective] using hh

theorem embeddedPreimage_sdiff (e:V↪W) (A B:Finset W):
    embeddedPreimage e (A\B)=embeddedPreimage e A\embeddedPreimage e B:=by
  ext v;simp only [embeddedPreimage_mem,Finset.mem_sdiff]

theorem embedded_bernoulli_image (e:V↪W) (σ:W→Bool):
    (bernoulliVertexSet (fun v=>σ (e v))).image e=(Finset.univ.image e)∩bernoulliVertexSet σ:=by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_inter,bernoulliVertexSet,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x,hx,rfl⟩;exact ⟨⟨x,rfl⟩,hx⟩
  · rintro ⟨⟨x,rfl⟩,hx⟩;exact ⟨x,hx,rfl⟩

theorem embedded_bernoulli_alteration (e:V↪W) (σ:W→Bool) (Y:Finset W)
    (hY:∀ v∈Y,∃ x,e x=v):
    (bernoulliVertexSet (fun v=>σ (e v))\embeddedPreimage e Y).card+
      (embeddedPreimage e Y\bernoulliVertexSet (fun v=>σ (e v))).card=
    (((Finset.univ.image e)∩bernoulliVertexSet σ)\Y).card+
      (Y\((Finset.univ.image e)∩bernoulliVertexSet σ)).card:=by
  have hy:=embeddedPreimage_image e Y hY
  have hσ:=embedded_bernoulli_image e σ
  have h1:=Finset.image_sdiff (bernoulliVertexSet (fun v=>σ (e v))) (embeddedPreimage e Y) e.injective
  have h2:=Finset.image_sdiff (embeddedPreimage e Y) (bernoulliVertexSet (fun v=>σ (e v))) e.injective
  have hc1:=congrArg Finset.card h1
  have hc2:=congrArg Finset.card h2
  rw [Finset.card_image_of_injective _ e.injective,hσ,hy] at hc1
  rw [Finset.card_image_of_injective _ e.injective,hσ,hy] at hc2
  rw [hc1,hc2]

end Oberwolfach
