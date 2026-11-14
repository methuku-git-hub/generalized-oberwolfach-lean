module

public import Oberwolfach.MarkedTransformerRimCycles
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Select all shared rim paths on a single oriented host, preserving
separation from old roots and between different paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

 theorem marked_rim_cycle_families
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l)
    (v w v' w':I→V) (j:I→Bool) (W Z:Finset V) (c:ℝ)
    (hroots:∀ i,v i∈Z∧w i∈Z∧v' i∈Z∧w' i∈Z)
    (hvw:∀ i,¬PermutationClose π b (v i) (w i))
    (hvw':∀ i,¬PermutationClose π b (v' i) (w' i))
    (hroot:∀ i,if j i then (∃ e,ktail e=v i∧khead e=w i)∧(∃ e,ktail e=v' i∧khead e=w' i)
      else (∃ e,tail e=v i∧head e=w i)∧(∃ e,tail e=v' i∧head e=w' i))
    (hopen:∀ i,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=w i∧head e=a)∧(∃ e,tail e=w' i∧head e=a))).card:ℝ))
    (hclose:∀ i,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=a∧head e=v i)∧(∃ e,tail e=a∧head e=v' i))).card:ℝ))
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧(∃ e,tail e=a∧head e=y))).card:ℝ))
    (hbudget:W.card+((Fintype.card I:ℝ)*(l+3)+Z.card+l+4)*(2*b+1)<c):
    ∃ p:I→(Fin (l+3)↪V),∃ C D:I→MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ i a,(C i).val a=Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i)) (canonicalMarkedRotation (if j i then 0 else 3) a))∧
      (∀ i a,(D i).val a=Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) (p i)) (canonicalMarkedRotation (if j i then 0 else 3) a))∧
      (∀ i a,p i a∉W∧p i a∉Z∧∀ z∈Z,¬PermutationClose π b (p i a) z)∧
      (∀ i,PermutationSeparated π b (p i))∧
      (∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))∧
      ∀ i k,∀ a z,p i a≠p k z→¬PermutationClose π b (p i a) (p k z):=by
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  let C₀:= (Fin (l+3)↪V)×
    (MarkedCycleTuple tail head ktail khead (l+4) π b×MarkedCycleTuple tail head ktail khead (l+4) π b)
  let S:C₀→Finset V:=fun q=>Finset.univ.image q.1
  let Good:I→C₀→Prop:=fun i q=>
    (∀ a,q.2.1.val a=Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) q.1) (canonicalMarkedRotation (if j i then 0 else 3) a))∧
    (∀ a,q.2.2.val a=Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) q.1) (canonicalMarkedRotation (if j i then 0 else 3) a))∧
    (∀ a,q.1 a∉Z∧∀ z∈Z,¬PermutationClose π b (q.1 a) z)∧PermutationSeparated π b q.1
  have hc:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*(l+3)*(2*b+1)→
      ∃ q,Good i q∧(S q).card≤l+3∧Disjoint (S q) B:=by
    intro i B hB
    have hbd:(B.card:ℝ)+(Z.card+l+4)*(2*b+1)<c:=by nlinarith only [hB,hbudget]
    obtain ⟨p,C,D,hC,hD,hav,hsp⟩:=marked_transformer_rim_cycles tail head ktail khead π b l hl
      (v i) (w i) (v' i) (w' i) (j i) B Z (hroots i).1 (hroots i).2.1
      (hroots i).2.2.1 (hroots i).2.2.2 (hvw i) (hvw' i) c (hroot i) (hopen i) (hclose i) hstep hjoin hbd
    refine ⟨⟨p,C,D⟩,⟨hC,hD,fun a=>(hav a).2,hsp⟩,?_,?_⟩
    · simpa only [S,Fintype.card_fin,Finset.card_univ] using Finset.card_image_le (f:=(p:Fin (l+3)→V)) (s:=Finset.univ)
    · apply Finset.disjoint_left.mpr
      intro x hx hxB
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
      exact (hav a).1 hxB
  obtain ⟨q,hq,hd⟩:=finite_conflict_separated_choices S Good W (l+3) F (2*b) (by positivity) hF (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hc)
  refine ⟨fun i=>(q i).1,fun i=>(q i).2.1,fun i=>(q i).2.2,
    fun i=>(hq i).1.1,fun i=>(hq i).1.2.1,?_,fun i=>(hq i).1.2.2.2,
    fun i k hik=>(hd i k hik).1,?_⟩
  · intro i a
    refine ⟨?_,(hq i).1.2.2.1 a⟩
    exact fun ha=>Finset.disjoint_left.mp (hq i).2.2 (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) ha
  · intro i k a z hne
    by_cases hik:i=k
    · subst k
      exact (hq i).1.2.2.2 a z (fun h=>hne (congrArg (q i).1 h))
    · intro hclose
      exact (hd i k hik).2 _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
        _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩) ⟨hne,hclose⟩

end Oberwolfach
