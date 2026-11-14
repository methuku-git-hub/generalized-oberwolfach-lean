module

public import Oberwolfach.ComponentAssignmentByHubAndSize
public import Oberwolfach.LongKeptTargetComponentCapacity

@[expose] public section
/-! The manuscript's frequency estimate gives an injective assignment of
selected ordinary wheels to actual factor components of the right length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedWheelAssignmentFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem long_selected_wheels_assign_components {n K:ℕ} {U C:Type}
    [Fintype U] [DecidableEq U] [DecidableEq C] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (A:Finset C) (key:C→U×Fin K) (θ lam:ℝ) (hlamθ:lam≤θ)
    (herr:∀u i,
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
      |(((A.filter (fun c=>key c=(u,i))).card:ℝ)-(1-θ)*t)|≤lam*t):
    ∃h:{c // c∈A}↪(Σu,(F u).ConnectedComponent),
      ∀c,(h c).1=(key c.val).1 ∧ Fintype.card (h c).2=(key c.val).2.val+1 :=by
  let sizekey:=fun c=>((key c).1,(key c).2.val+1)
  have hcap:∀u r,(A.filter (fun c=>sizekey c=(u,r))).card≤
      (Finset.univ.filter (fun C:(F u).ConnectedComponent=>Fintype.card C=r)).card:=by
    intro u r
    by_cases hr:∃i:Fin K,i.val+1=r
    · obtain ⟨i,hi⟩:=hr
      have hf:A.filter (fun c=>sizekey c=(u,r))=A.filter (fun c=>key c=(u,i)):=by
        ext c
        simp only [Finset.mem_filter,sizekey,Prod.mk.injEq]
        constructor
        · rintro ⟨hc,hu,hlen⟩
          refine ⟨hc,Prod.ext hu ?_⟩
          apply Fin.ext
          change (key c).2.val=i.val
          have hlen' : (key c).2.val+1=i.val+1 := hlen.trans hi.symm
          omega
        · rintro ⟨hc,hkey⟩
          have hu:=congrArg Prod.fst hkey
          have hj:=congrArg Prod.snd hkey
          refine ⟨hc,hu,?_⟩
          simp only [hj,hi]
      rw [hf,←hi]
      have hc:=long_selected_ordinary_count_le_components hn F hF θ lam hlamθ i u _ (herr u i)
      convert hc using 1 <;> congr 1 <;> ext C <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    · have hf:A.filter (fun c=>sizekey c=(u,r))=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        have hh:=(Finset.mem_filter.mp hc).2
        exact hr ⟨(key c).2,congrArg Prod.snd hh⟩
      simp only [hf,Finset.card_empty,Nat.zero_le]
  obtain ⟨h,hh⟩:=selected_wheels_assign_to_components F A sizekey hcap
  refine ⟨h,?_⟩
  intro c
  exact Prod.mk.inj (hh c)
end Oberwolfach
