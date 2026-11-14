module

public import Oberwolfach.DirectedIncidenceSums
public import Oberwolfach.MarkedSpokeLoadGrouping

@[expose] public section

/-! The prescribed endpoints of each vertex-wheel path, defined directly
from the earlier rim and spoke paths and the two attachment bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A S:Type} [DecidableEq V] [Fintype A] [Fintype S] [DecidableEq A] [DecidableEq S]
    {src dst:A→V} {row:S→V}

 def markedAttachmentFirst (n:ℕ)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→Fin (n+1)→V) (ps:S→Fin (n+2)→V):
    (Σ v,DirectedIncidence src dst v)→V
  | ⟨_,.inl e⟩=>pr e.val 0
  | ⟨v,.inr e⟩=>ps (d v e).val 0

 def markedAttachmentLast (n:ℕ)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→Fin (n+1)→V) (ps:S→Fin (n+2)→V):
    (Σ v,DirectedIncidence src dst v)→V
  | ⟨v,.inl e⟩=>ps (a v e).val (Fin.last (n+1))
  | ⟨_,.inr e⟩=>pr e.val (Fin.last n)

 theorem fiber_equiv_total_injective {A S V:Type} (f:A→V) (g:S→V)
    (a:∀ v,{e:A // f e=v}≃{s:S // g s=v}):
    Function.Injective (fun z:Σ v,{e:A // f e=v}=>(a z.1 z.2).val):=by
  rintro ⟨v,e⟩ ⟨w,f⟩ he
  have hvw:v=w:=(a v e).property.symm.trans ((congrArg g he).trans (a w f).property)
  subst w
  have hef:e=f:=(a v).injective (Subtype.ext he)
  subst f
  rfl

 theorem marked_attachment_endpoints_injective (n:ℕ) (hn:0<n)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→(Fin (n+1)↪V)) (ps:S→(Fin (n+2)↪V))
    (hpr:∀ e f,e≠f→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr f)))
    (hps:∀ s t,s≠t→Disjoint (Finset.univ.image (ps s)) (Finset.univ.image (ps t)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s))):
    Function.Injective (markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s))∧
      Function.Injective (markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s))∧
      ∀ z z',markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s) z≠
        markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s) z':=by
  have hr:=disjoint_paths_joint_injective (n+1) pr hpr
  have hs:=disjoint_paths_joint_injective (n+2) ps hps
  have hcross:∀ e s i k,pr e i≠ps s k:=by
    intro e s i k he
    exact Finset.disjoint_left.mp (hrs e s)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩)
  have hin:Function.Injective (fun z:Σ v,{e:A // dst e=v}=>z.2.val):=by
    rintro ⟨v,e⟩ ⟨w,f⟩ he
    have hvw:v=w:=e.property.symm.trans ((congrArg dst he).trans f.property)
    subst w
    have hef:e=f:=Subtype.ext he
    subst f;rfl
  have hout:Function.Injective (fun z:Σ v,{e:A // src e=v}=>z.2.val):=by
    rintro ⟨v,e⟩ ⟨w,f⟩ he
    have hvw:v=w:=e.property.symm.trans ((congrArg src he).trans f.property)
    subst w
    have hef:e=f:=Subtype.ext he
    subst f;rfl
  refine ⟨?_,?_,?_⟩
  · rintro ⟨v,e⟩ ⟨w,f⟩ he
    cases e with
    | inl e=>
      cases f with
      | inl f=>
        have hh':(⟨v,e⟩:Σ v,{e:A // dst e=v})=⟨w,f⟩:=
          @hin ⟨v,e⟩ ⟨w,f⟩ (congrArg Prod.fst (@hr (e.val,0) (f.val,0) he))
        cases hh';rfl
      | inr f=>exact False.elim (hcross _ _ _ _ he)
    | inr e=>
      cases f with
      | inl f=>exact False.elim (hcross _ _ _ _ he.symm)
      | inr f=>
        have hh':(⟨v,e⟩:Σ v,{e:A // src e=v})=⟨w,f⟩:=
          fiber_equiv_total_injective src row d (congrArg Prod.fst (@hs ((d v e).val,0) ((d w f).val,0) he))
        cases hh';rfl
  · rintro ⟨v,e⟩ ⟨w,f⟩ he
    cases e with
    | inl e=>
      cases f with
      | inl f=>
        have hh':(⟨v,e⟩:Σ v,{e:A // dst e=v})=⟨w,f⟩:=
          fiber_equiv_total_injective dst row a (congrArg Prod.fst (@hs ((a v e).val,Fin.last (n+1)) ((a w f).val,Fin.last (n+1)) he))
        cases hh';rfl
      | inr f=>exact False.elim (hcross _ _ _ _ he.symm)
    | inr e=>
      cases f with
      | inl f=>exact False.elim (hcross _ _ _ _ he)
      | inr f=>
        have hh':(⟨v,e⟩:Σ v,{e:A // src e=v})=⟨w,f⟩:=
          @hout ⟨v,e⟩ ⟨w,f⟩ (congrArg Prod.fst (@hr (e.val,Fin.last n) (f.val,Fin.last n) he))
        cases hh';rfl
  · rintro ⟨v,e⟩ ⟨w,f⟩ he
    cases e with
    | inl e=>
      cases f with
      | inl f=>exact hcross _ _ _ _ he
      | inr f=>
        have hh:(0:Fin (n+1))=Fin.last n:=congrArg (fun z:A×Fin (n+1)=>z.2) (@hr (e.val,0) (f.val,Fin.last n) he)
        have hh':(0:ℕ)=n:=congrArg Fin.val hh
        omega
    | inr e=>
      cases f with
      | inl f=>
        have hh:(0:Fin (n+2))=Fin.last (n+1):=congrArg (fun z:S×Fin (n+2)=>z.2) (@hs ((d v e).val,0) ((a w f).val,Fin.last (n+1)) he)
        have hh':(0:ℕ)=n+1:=congrArg Fin.val hh
        omega
      | inr f=>exact hcross _ _ _ _ he.symm

 theorem two_endpoint_sets_disjoint {I:Type} (first last:I→V)
    (hf:Function.Injective first) (hl:Function.Injective last) (hfl:∀ i j,first i≠last j):
    ∀ i j,i≠j→Disjoint ({first i,last i}:Finset V) {first j,last j}:=by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
  rcases hv with rfl|rfl <;> rcases hw with hw|hw
  · exact hij (hf hw)
  · exact hfl i j hw
  · exact hfl j i hw.symm
  · exact hij (hl hw)

end Oberwolfach
