module

public import Oberwolfach.ActualOutsidePathAvoidance

@[expose] public section
/-! The residual completion preserves the marked roots outside the reserved
paths, including roots protected from assigned physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_anchor_root_avoidance
    {X V I K J:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [Fintype I]
    [DecidableEq K] [DecidableEq J] (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (hDR:Disjoint (bufferedPathStrictInterior n inner) data.remaining)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (ψ:X→V) (Φ g:{x // x∈data.remaining}→V)
    (B:Finset {x // x∈data.remaining}) (Lists Y E Z:Finset V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior n inner}),x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior n inner}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩)
    (hAnchor:∀x∈B,Φ x=g x) (hFree:∀x,x∉B→Φ x∈Lists)
    (hImage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.1)∪E∪Z)
    (hEAvoid:Disjoint E Y) (hZAvoid:Disjoint Z Y) (hListAvoid:Disjoint Lists Y)
    (hOldAvoid:∀x,x∈data.oldDomain→x∉bufferedPathFullDomain n inner→ψ x∉Y):
    Disjoint (outsideBufferedPathImage n inner fC) Y:=by
  apply actual_outside_buffered_path_image_avoids_reserved F data hCycle n inner fC ψ Φ g B Lists Y hold hnew hAnchor hFree hOldAvoid ?_ hListAvoid
  intro x hx hxOutside hY
  have hg:g x∈B.image g:=Finset.mem_image.mpr ⟨x,hx,rfl⟩
  rw [hImage] at hg
  rcases Finset.mem_union.mp hg with hleft|hZ
  · rcases Finset.mem_union.mp hleft with hpres|hE
    · obtain ⟨y,hy,heq⟩:=Finset.mem_image.mp hpres
      have hyPres:y.1∈data.prescribed:=(Finset.mem_filter.mp hy).2
      have hyOld:y.1∈data.oldDomain:=by
        have hh:data.oldDomain∩data.remaining=data.prescribed:=(data.graph_facts hF).2.2.2.2.2
        have hh':y.1∈data.oldDomain∩data.remaining:=by rw [hh];exact hyPres
        exact (Finset.mem_inter.mp hh').1
      have hxNot:x.1∉bufferedPathStrictInterior n inner:=by
        intro h;exact Finset.disjoint_left.mp hDR h x.property
      have hyNot:y.1∉bufferedPathStrictInterior n inner:=by
        intro h;exact Finset.disjoint_left.mp hDR h y.property
      have hf:fC ⟨x.1,hxNot⟩=fC ⟨y.1,hyNot⟩:=by
        calc
          fC ⟨x.1,hxNot⟩ = Φ x := hnew ⟨x.1,hxNot⟩ x.property
          _ = g x := hAnchor x hx
          _ = ψ y.1 := heq.symm
          _ = fC ⟨y.1,hyNot⟩ := (hold ⟨y.1,hyNot⟩ hyOld).symm
      have hxy:x.1=y.1:=congrArg (fun z:{x // x∉bufferedPathStrictInterior n inner}=>z.val) (fC.injective hf)
      have hyOutside:y.1∉bufferedPathFullDomain n inner:=by simpa [←hxy] using hxOutside
      apply hOldAvoid y.1 hyOld hyOutside
      simpa [heq] using hY
    · exact Finset.disjoint_left.mp hEAvoid hE hY
  · exact Finset.disjoint_left.mp hZAvoid hZ hY
end Oberwolfach
