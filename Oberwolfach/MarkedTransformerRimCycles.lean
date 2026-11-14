module

public import Oberwolfach.MarkedTransformerBetweenRootsPaths
public import Oberwolfach.MarkedTwoRootPathCycles
public import Oberwolfach.PermutationConflictDegree
public import Oberwolfach.MarkedPathParent

@[expose] public section

/-! Construct the two directed cycles for a root rim arc and its image.
The common path is chosen from the actual oriented host before its new hub.
Its marked position is retained through the canonical coordinate change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [DecidableEq V]

 theorem marked_transformer_rim_cycles
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l)
    (v w v' w':V) (j:Bool) (W Z:Finset V)
    (hv:v∈Z) (hw:w∈Z) (hv':v'∈Z) (hw':w'∈Z)
    (hvw:¬PermutationClose π b v w) (hvw':¬PermutationClose π b v' w') (c:ℝ)
    (hroot:if j then (∃ e,ktail e=v∧khead e=w)∧(∃ e,ktail e=v'∧khead e=w')
      else (∃ e,tail e=v∧head e=w)∧(∃ e,tail e=v'∧head e=w'))
    (hopen:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=w∧head e=a)∧(∃ e,tail e=w'∧head e=a))).card:ℝ))
    (hclose:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=a∧head e=v)∧(∃ e,tail e=a∧head e=v'))).card:ℝ))
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧(∃ e,tail e=a∧head e=y))).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ C D:MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ i,C.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i))∧
      (∀ i,D.val i=Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) (canonicalMarkedRotation (if j then 0 else 3) i))∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬PermutationClose π b (p i) z)∧
      PermutationSeparated π b p:=by
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,ho,hcl,hpa,hsp,havoid,hsep⟩:=marked_transformer_between_roots_path F
    (fun x y=>∃ e,tail e=x∧head e=y) (fun x y=>∃ e,ktail e=x∧khead e=y)
    (fun (_:V) (_:Unit)=>True) (fun (_:V) (_:Unit)=>True) w w' v v' () () j false W Z l hl
    (2*b) c (by positivity) hF
    (by simpa only [and_true] using hopen) (by simpa only [Bool.false_eq_true,ite_false,and_true] using hclose)
    (by intro t x;simpa only [ite_self,and_true] using hstep t x)
    (by intro x y hxy;simpa only [and_true] using hjoin x y hxy) hbudget
  have hfree:PermutationSeparated π b p:=by
    intro i k hik hc
    exact hsep i k ⟨fun h=>hik (p.injective h),hc⟩
  have hout (i:Fin (l+3)) (z:V) (hz:z∈Z):¬PermutationClose π b (p i) z:=by
    intro hc
    exact (havoid i).2.2 z hz ⟨fun he=>(havoid i).2.1 (he ▸ hz),hc⟩
  have hcons (x y:V) (hx:x∈Z) (hy:y∈Z) (hxy:¬PermutationClose π b x y):
      PermutationSeparated π b (Fin.cons x (Fin.cons y p)):=by
    apply permutationSeparated_cons
    · apply permutationSeparated_cons π b y p hfree
      intro i hc
      exact hout i y hy ((permutationClose_symm π b y (p i)).mp hc)
    · intro i
      refine Fin.cases ?_ (fun k=>?_) i
      · exact hxy
      · intro hc
        exact hout k x hx ((permutationClose_symm π b x (p k)).mp hc)
  have hr₁:if j then ∃ e,ktail e=v∧khead e=w else ∃ e,tail e=v∧head e=w:=by cases j <;> exact hroot.1
  have hr₂:if j then ∃ e,ktail e=v'∧khead e=w' else ∃ e,tail e=v'∧head e=w':=by cases j <;> exact hroot.2
  obtain ⟨C,hC⟩:=marked_cycle_from_two_root_path tail head ktail khead (l+2) (by omega) π b j v w p
    (hcons v w hv hw hvw) hr₁ ho.1 hcl.1 hpa
  obtain ⟨D,hD⟩:=marked_cycle_from_two_root_path tail head ktail khead (l+2) (by omega) π b j v' w' p
    (hcons v' w' hv' hw' hvw') hr₂ ho.2 hcl.2 hpa
  exact ⟨p,C,D,hC,hD,fun i=>⟨(havoid i).1,(havoid i).2.1,hout i⟩,hfree⟩

end Oberwolfach
