module

public import Oberwolfach.MarkedTransformerPaths
public import Oberwolfach.MarkedRootedPathCycles
public import Oberwolfach.PermutationConflictDegree
public import Oberwolfach.MarkedPathParent

@[expose] public section

/-! Construct the two actual marked wheels from host row counts. The
shared path is chosen here. The two old root spokes are supplied separately;
no spoke between either root and the other hub is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]

 theorem marked_transformer_path_wheels
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (v v':V) (u u':U) (j:Bool)
    (W Z:Finset V) (hv:v∈Z) (hv':v'∈Z) (c:ℝ)
    (hroot:if j then HK v u∧HK v' u' else H₀ v u∧H₀ v' u')
    (hopen:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=v∧head e=a)∧
      (∃ e,tail e=v'∧head e=a)∧H₀ a u∧H₀ a u')).card:ℝ))
    (hclose:c≤((Finset.univ.filter (fun a=>(if j then
      (∃ e,ktail e=a∧khead e=v)∧(∃ e,ktail e=a∧khead e=v') else
      (∃ e,tail e=a∧head e=v)∧(∃ e,tail e=a∧head e=v'))∧H₀ a u∧H₀ a u')).card:ℝ))
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)∧
      (if t then HK a u∧HK a u' else H₀ a u∧H₀ a u'))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y)∧H₀ a u∧H₀ a u')).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,
    ∃ A B:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      A.2.val=u∧B.2.val=u'∧
      (∀ i,A.1.val i=rootedCycleOrder (markedRootOrder (l+3) j) v p i)∧
      (∀ i,B.1.val i=rootedCycleOrder (markedRootOrder (l+3) j) v' p i)∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬PermutationClose π b (p i) z)∧
      PermutationSeparated π b p:=by
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by
    intro x
    exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,ho,hcl,hpa,hsp,havoid,hsep⟩:=marked_transformer_common_path F
    (fun x y=>∃ e,tail e=x∧head e=y) (fun x y=>∃ e,ktail e=x∧khead e=y)
    H₀ HK v v' u u' j W Z hv hv' l hl (2*b) c (by positivity) hF hopen hclose hstep hjoin hbudget
  have hfree:PermutationSeparated π b p:=by
    intro i k hik hclose
    exact hsep i k ⟨fun h=>hik (p.injective h),hclose⟩
  have hout (i:Fin (l+3)) (z:V) (hz:z∈Z):¬PermutationClose π b (p i) z:=by
    intro h
    exact (havoid i).2.2 z hz ⟨fun he=>(havoid i).2.1 (he ▸ hz),h⟩
  have hcons (z:V) (hz:z∈Z):PermutationSeparated π b (Fin.cons z p):=
    permutationSeparated_cons π b z p hfree (fun i h=>hout i z hz ((permutationClose_symm π b z (p i)).mp h))
  have hcl₁:if j then ∃ e,ktail e=p (Fin.last (l+2))∧khead e=v
      else ∃ e,tail e=p (Fin.last (l+2))∧head e=v:=by cases j <;> exact hcl.1
  have hcl₂:if j then ∃ e,ktail e=p (Fin.last (l+2))∧khead e=v'
      else ∃ e,tail e=p (Fin.last (l+2))∧head e=v':=by cases j <;> exact hcl.2
  have hroot₁:if j then HK v u else H₀ v u:=by cases j <;> exact hroot.1
  have hroot₂:if j then HK v' u' else H₀ v' u':=by cases j <;> exact hroot.2
  have hsp₁:∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u:=by
    intro i
    have hh:=hsp i
    split_ifs at hh ⊢ <;> exact hh.1
  have hsp₂:∀ i,if j=false∧i.val=2 then HK (p i) u' else H₀ (p i) u':=by
    intro i
    have hh:=hsp i
    split_ifs at hh ⊢ <;> exact hh.2
  obtain ⟨A,hAu,hA⟩:=marked_wheel_from_rooted_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v u p (hcons v hv) ho.1 hcl₁ hpa hroot₁ hsp₁
  obtain ⟨B,hBu,hB⟩:=marked_wheel_from_rooted_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v' u' p (hcons v' hv') ho.2 hcl₂ hpa hroot₂ hsp₂
  exact ⟨p,A,B,hAu,hBu,hA,hB,fun i=>⟨(havoid i).1,(havoid i).2.1,hout i⟩,hfree⟩

end Oberwolfach
