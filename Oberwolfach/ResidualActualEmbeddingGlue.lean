module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.PrescribedSubtypeCompleteGlue

@[expose] public section
/-! Glue a completed residual embedding to the actual previously embedded
selected paths and cycles. The full-source conclusion requires all deleted
cycle vertices to have been embedded; this condition is not inferred from the
residual graph alone. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V]
  [DecidableEq K] [DecidableEq J] {F:SimpleGraph X}

theorem actual_residual_embedding_glues_to_factor
    (a:ActualResidualData (K:=K) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (ψ:X→V) (hψ:Set.InjOn ψ (↑a.oldDomain:Set X))
    (B:Finset {x // x∈a.remaining})
    (g Φ:{x // x∈a.remaining}→V) (L C Z:Finset V)
    (hA₀B:residualSubtypeSet a.remaining a.prescribed⊆B)
    (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet a.remaining a.prescribed,g x=ψ x.1)
    (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.1)∪C∪Z)
    (hOldC:Disjoint (a.oldDomain.image ψ) C)
    (hOldZ:Disjoint (a.oldDomain.image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L (a.oldDomain.image ψ)):
    ∃h:X→V,Function.Injective h ∧ (∀x∈a.oldDomain,h x=ψ x) ∧
      (∀x:{x // x∈a.remaining},h x.1=Φ x):=by
  let embed:{x // x∈a.remaining}↪X:=⟨Subtype.val,Subtype.val_injective⟩
  have hA₀:∀x:{x // x∈a.remaining},
      x∈residualSubtypeSet a.remaining a.prescribed↔embed x∈a.oldDomain := by
    intro x
    exact (residual_subtype_glue_inputs a.remaining a.prescribed a.oldDomain
      (a.graph_facts hF).2.2.2.2.2 ψ hψ).1 x
  have hIm:(Finset.univ.image embed)=a.remaining := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    change (∃y:{y // y∈a.remaining},y.1=x) ↔ x∈a.remaining
    exact ⟨fun ⟨y,hy⟩=>hy ▸ y.2,fun hx=>⟨⟨x,hx⟩,rfl⟩⟩
  obtain ⟨h,hinj,hold,hres⟩:=prescribed_subtype_complete_factor_glue
    embed a.oldDomain (residualSubtypeSet a.remaining a.prescribed) B ψ (fun x=>ψ x.1) g Φ L C Z
    hA₀ hA₀B hψ hΦ (by intro x hx;rfl) hg hΦg himage hOldC hOldZ hfree hL
  refine ⟨h,?_,hold,hres⟩
  rw [hIm,a.old_domain_union_remaining hCycle] at hinj
  intro x y hxy
  exact hinj (by simp) (by simp) hxy
end Oberwolfach
