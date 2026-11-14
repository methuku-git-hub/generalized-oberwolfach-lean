module

public import Oberwolfach.ResourceRootOmittedLoads
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Embedding a candidate's resources preserves its root-omitted load;
no assumptions about random exposure are needed for this identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C:Type} [Fintype V] [Fintype W] [Fintype C] [DecidableEq V] [DecidableEq W]

theorem resource_root_omitted_load_map
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (keep:W→Prop) (root:V):
    resourceRootOmittedLoad (fun c=>(R c).map e) w keep (e root)=
      resourceRootOmittedLoad R w (fun x=>keep (e x)) root := by
  unfold resourceRootOmittedLoad
  apply Finset.sum_congr rfl
  intro c _
  have hm : e root∈(R c).map e ↔ root∈R c := by simp
  have hk : (∀y∈(R c).map e,y≠e root→keep y) ↔
      (∀x∈R c,x≠root→keep (e x)) := by
    constructor
    · intro h x hx hne
      apply h (e x) (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
      exact fun h=>hne (e.injective h)
    · intro h y hy hne
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
      apply h x hx
      exact fun h=>hne (congrArg e h)
  simp only [hm,hk]

theorem resource_root_omitted_load_map_outside
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (keep:W→Prop) (root:W)
    (hroot:∀x,e x≠root):
    resourceRootOmittedLoad (fun c=>(R c).map e) w keep root=0 := by
  unfold resourceRootOmittedLoad
  apply Finset.sum_eq_zero
  intro c _
  have hnot : root∉(R c).map e := by
    intro h
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp h
    exact hroot x hx
  simp [hnot]
/-- Root-omitted Boolean pattern loads are transported along the same
embedding, while the original outcome is pulled back to the source. -/
theorem resource_pattern_load_map
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (σ:W→Bool) (root:V):
    resourcePatternLoad (fun c=>(R c).map e) w (fun _ _=>true) (e root) σ =
      resourcePatternLoad R w (fun _ _=>true) root (fun x=>σ (e x)) := by
  rw [←bernoulli_root_load_pattern,resource_root_omitted_load_map,←bernoulli_root_load_pattern]
  congr 1
  funext x
  apply propext
  simp

theorem resource_pattern_load_map_outside
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (σ:W→Bool) (root:W)
    (hroot:∀x,e x≠root):
    resourcePatternLoad (fun c=>(R c).map e) w (fun _ _=>true) root σ=0 := by
  rw [←bernoulli_root_load_pattern]
  exact resource_root_omitted_load_map_outside R w e _ root hroot
theorem resource_omitted_pair_weight_map
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (u v:V):
    resourceOmittedPairWeight (fun c=>(R c).map e) w (e u) (e v) =
      resourceOmittedPairWeight R w u v := by
  unfold resourceOmittedPairWeight
  apply Finset.sum_congr rfl
  intro c _
  have hn : e v≠e u ↔ v≠u := by
    constructor
    · intro h hv;apply h;exact congrArg e hv
    · intro h he;apply h;exact e.injective he
  simp only [Finset.mem_map,e.injective.eq_iff,exists_eq_right,hn]

theorem resource_omitted_pair_weight_map_outside
    (R:C→Finset V) (w:C→ℝ) (e:V↪W) (u v:W) (hu:∀x,e x≠u):
    resourceOmittedPairWeight (fun c=>(R c).map e) w u v=0 := by
  unfold resourceOmittedPairWeight
  apply Finset.sum_eq_zero
  intro c _
  have hnot : u∉(R c).map e := by
    intro h
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp h
    exact hu x hx
  simp [hnot]
end Oberwolfach
