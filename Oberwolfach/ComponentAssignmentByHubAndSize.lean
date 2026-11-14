module

public import Oberwolfach.SigmaKeyClassCount
public import Oberwolfach.ApproximateSelectedCapacity
public import Oberwolfach.CycleComponentFrequency

@[expose] public section
/-! Assignment to actual connected components, respecting hub and size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_wheels_assign_to_components {V U C:Type}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [DecidableEq C]
    (F:U→SimpleGraph V) (A:Finset C) (key:C→U×ℕ)
    (hcount:∀u r,(A.filter (fun c=>key c=(u,r))).card≤
      (Finset.univ.filter (fun D:(F u).ConnectedComponent=>Fintype.card D=r)).card):
    ∃h:{c // c∈A}↪(Σu,(F u).ConnectedComponent),
      ∀c,((h c).1,Fintype.card (h c).2)=key c.val :=by
  let D:=fun u=>(F u).ConnectedComponent
  let B:Finset (Σu,D u):=Finset.univ
  let g:=fun z:Σu,D u=>(z.1,Fintype.card z.2)
  have hcap:∀k:U×ℕ,(A.filter (fun c=>key c=k)).card≤(B.filter (fun z=>g z=k)).card:=by
    rintro ⟨u,r⟩
    have htarget:(B.filter (fun z=>g z=(u,r))).card=
        (Finset.univ.filter (fun C:D u=>Fintype.card C=r)).card:=by
      simpa only [B,g,Finset.filter_filter,Finset.mem_univ,true_and,Prod.mk.injEq] using
        sigma_key_class_count D (fun _ C=>Fintype.card C) u r
    rw [htarget]
    exact hcount u r
  obtain ⟨h,hhub⟩:=fiberwise_injective_assignment A B key g hcap
  refine ⟨h.trans (Function.Embedding.subtype (fun z=>z∈B)),?_⟩
  intro c
  exact hhub c
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_wheels_assign_from_approximate_counts {V U C:Type}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [DecidableEq C]
    (F:U→SimpleGraph V) (A:Finset C) (key:C→U×ℕ) (θ lam:ℝ) (hlamθ:lam≤θ)
    (t:U→ℕ→ℝ)
    (ht:∀u r,0≤t u r ∧ t u r≤
      (Finset.univ.filter (fun C:(F u).ConnectedComponent=>Fintype.card C=r)).card)
    (herr:∀u r,|(((A.filter (fun c=>key c=(u,r))).card:ℝ)-(1-θ)*t u r)|≤lam*t u r):
    ∃h:{c // c∈A}↪(Σu,(F u).ConnectedComponent),
      ∀c,((h c).1,Fintype.card (h c).2)=key c.val :=by
  apply selected_wheels_assign_to_components F A key
  intro u r
  exact approximate_selected_real_target_le_capacity _ _ (t u r) θ lam (ht u r).1 (ht u r).2 hlamθ (herr u r)
end Oberwolfach
