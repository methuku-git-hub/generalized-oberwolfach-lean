module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! Retain the original absorber on protected hubs and use no absorber on
other hubs. This permits target coverage at every hub without changing the
protected absorber. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem all_hub_effective_absorber_targets
    {V U:Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    (I:Finset V) (H:Finset U) (Raw Outer Y Absorber Old:U→Finset V)
    (hsub:∀u,Raw u⊆Outer u) (hAbs:∀u∈H,Disjoint (Absorber u) I):
    let AbsAll:=fun u=>if u∈H then Absorber u else ∅
    let Zold:=innerRequiredTargets H I Outer Y Absorber Old
    let Zall:=innerRequiredTargets Finset.univ I Outer Y AbsAll Old
    let Zraw:=innerRequiredTargets Finset.univ I Raw Y (fun _=>∅) Old;
    (∀u,Disjoint (AbsAll u) I) ∧
    (∀u,Zold u⊆Zall u) ∧ (∀u,Zall u⊆Zraw u) :=by
  intro AbsAll Zold Zall Zraw
  constructor
  · intro u
    by_cases hu:u∈H
    · simpa only [AbsAll,hu,if_true] using hAbs u hu
    · simp [AbsAll,hu]
  constructor
  · intro u v hv
    by_cases hu:u∈H
    · simpa only [Zold,Zall,AbsAll,innerRequiredTargets,hu,Finset.mem_univ,if_true] using hv
    · simp [Zold,innerRequiredTargets,hu] at hv
  · intro u v hv
    simp only [Zall,innerRequiredTargets,Finset.mem_univ,if_true,Finset.mem_sdiff,Finset.mem_union] at hv
    simp only [Zraw,innerRequiredTargets,Finset.mem_univ,if_true,Finset.mem_sdiff,Finset.mem_union]
    refine ⟨hv.1,?_⟩
    rintro (((hr|hy)|he)|ho)
    · exact hv.2 (Or.inl (Or.inl (Or.inl (hsub u hr))))
    · exact hv.2 (Or.inl (Or.inl (Or.inr hy)))
    · simpa using he
    · exact hv.2 (Or.inr ho)
end Oberwolfach
