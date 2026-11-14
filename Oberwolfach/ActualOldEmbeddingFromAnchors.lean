module

public import Oberwolfach.ActualOldDomainSplit

@[expose] public section
/-! Glue the actual old-piece map to the prescribed anchor map on precisely
the old domain outside the final-path interiors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_embedding_from_pieces_and_anchors
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V) (g:{x // x∈data.prescribed}↪V),
    (∀x (hx:x∈A) (hy:x∈data.prescribed),f ⟨x,hx⟩=g ⟨x,hy⟩)→
    (∀x (hx:x∈data.prescribed) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y)→
    ∃ψ:X→V,Set.InjOn ψ (↑(data.oldDomain\data.additionalSelectedInteriors):Set X) ∧
      (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧
      (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩):=by
  classical
  intro A f g hagree hcross
  let ψ (x:X):V:=if hx:x∈A then f ⟨x,hx⟩ else if hy:x∈data.prescribed then g ⟨x,hy⟩ else Classical.choice inferInstance
  have hψA:∀x (hx:x∈A),ψ x=f ⟨x,hx⟩:=by intro x hx;simp [ψ,hx]
  have hψP:∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩:=by
    intro x hx
    by_cases ha:x∈A
    · exact (hψA x ha).trans (hagree x ha hx)
    · simp [ψ,ha,hx]
  refine ⟨ψ,?_,hψA,hψP⟩
  intro x hx y hy hxy
  have hs:=actual_old_domain_without_final_interiors data hG hCycle
  have hx':x∈data.prescribed ∪ A:=by
    change x∈data.oldDomain\data.additionalSelectedInteriors at hx
    rw [hs] at hx
    exact hx
  have hy':y∈data.prescribed ∪ A:=by
    change y∈data.oldDomain\data.additionalSelectedInteriors at hy
    rw [hs] at hy
    exact hy
  by_cases hxa:x∈A
  · by_cases hya:y∈A
    · have hh:f ⟨x,hxa⟩=f ⟨y,hya⟩:=by rw [←hψA x hxa,←hψA y hya];exact hxy
      exact congrArg Subtype.val (f.injective hh)
    · have hyp:y∈data.prescribed:=((Finset.mem_union.mp hy').resolve_right hya)
      have hh:g ⟨y,hyp⟩=f ⟨x,hxa⟩:=by rw [←hψP y hyp,←hψA x hxa];exact hxy.symm
      exact False.elim (hcross y hyp hya ⟨x,hxa⟩ hh)
  · have hxp:x∈data.prescribed:=((Finset.mem_union.mp hx').resolve_right hxa)
    by_cases hya:y∈A
    · have hh:g ⟨x,hxp⟩=f ⟨y,hya⟩:=by rw [←hψP x hxp,←hψA y hya];exact hxy
      exact False.elim (hcross x hxp hxa ⟨y,hya⟩ hh)
    · have hyp:y∈data.prescribed:=((Finset.mem_union.mp hy').resolve_right hya)
      have hh:g ⟨x,hxp⟩=g ⟨y,hyp⟩:=by rw [←hψP x hxp,←hψP y hyp];exact hxy
      exact congrArg Subtype.val (g.injective hh)
end Oberwolfach
