module

public import Oberwolfach.MarkedRimCycleFamilies
public import Oberwolfach.MarkedSpokeWheelFamilies

@[expose] public section

/-! Choose rim and spoke paths in the same host. The rim-path vertices
are included among the forbidden roots for the second choice, so the two
families are disjoint and separated, including across the two families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype A] [Fintype S]
  [DecidableEq V] [DecidableEq A] [DecidableEq S]

theorem marked_initial_paths
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l)
    (v w v' w':A→V) (jr:A→Bool) (s s':S→V) (u u':S→U) (js:S→Bool)
    (W Z:Finset V) (c:ℝ)
    (hroots:∀ i,v i∈Z∧w i∈Z∧v' i∈Z∧w' i∈Z)
    (hsroots:∀ i,s i∈Z∧s' i∈Z)
    (hvw:∀ i,¬PermutationClose π b (v i) (w i))
    (hvw':∀ i,¬PermutationClose π b (v' i) (w' i))
    (hroot:∀ i,if jr i then (∃ e,ktail e=v i∧khead e=w i)∧(∃ e,ktail e=v' i∧khead e=w' i)
      else (∃ e,tail e=v i∧head e=w i)∧(∃ e,tail e=v' i∧head e=w' i))
    (hropen:∀ i,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=w i∧head e=a)∧(∃ e,tail e=w' i∧head e=a))).card:ℝ))
    (hrclose:∀ i,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=a∧head e=v i)∧(∃ e,tail e=a∧head e=v' i))).card:ℝ))
    (hrstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hrjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧(∃ e,tail e=a∧head e=y))).card:ℝ))
    (hsroot:∀ i,if js i then HK (s i) (u i)∧HK (s' i) (u' i) else H₀ (s i) (u i)∧H₀ (s' i) (u' i))
    (hsopen:∀ i,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=s i∧head e=a)∧
      (∃ e,tail e=s' i∧head e=a)∧H₀ a (u i)∧H₀ a (u' i))).card:ℝ))
    (hsclose:∀ i,c≤((Finset.univ.filter (fun a=>(if js i then
      (∃ e,ktail e=a∧khead e=s i)∧(∃ e,ktail e=a∧khead e=s' i) else
      (∃ e,tail e=a∧head e=s i)∧(∃ e,tail e=a∧head e=s' i))∧H₀ a (u i)∧H₀ a (u' i))).card:ℝ))
    (hsstep:∀ i,∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)∧
      (if t then HK a (u i)∧HK a (u' i) else H₀ a (u i)∧H₀ a (u' i)))).card:ℝ))
    (hsjoin:∀ i,∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y)∧H₀ a (u i)∧H₀ a (u' i))).card:ℝ))
    (hbudget:W.card+((Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+Z.card+l+5)*(2*b+1)<c):
    ∃ pr:A→(Fin (l+3)↪V),∃ ps:S→(Fin (l+4)↪V),
    ∃ C D:A→MarkedCycleTuple tail head ktail khead (l+4) π b,
    ∃ SC SD:S→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i a,(C i).val a=Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (pr i)) (canonicalMarkedRotation (if jr i then 0 else 3) a))∧
      (∀ i a,(D i).val a=Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) (pr i)) (canonicalMarkedRotation (if jr i then 0 else 3) a))∧
      (∀ i,(SC i).2.val=u i∧(SD i).2.val=u' i)∧
      (∀ i a,(SC i).1.val a=rootedCycleOrder (markedRootOrder (l+4) (js i)) (s i) (ps i) a)∧
      (∀ i a,(SD i).1.val a=rootedCycleOrder (markedRootOrder (l+4) (js i)) (s' i) (ps i) a)∧
      (∀ i a,pr i a∉W∧pr i a∉Z∧∀ z∈Z,¬PermutationClose π b (pr i a) z)∧
      (∀ i a,ps i a∉W∧ps i a∉Z∧∀ z∈Z,¬PermutationClose π b (ps i a) z)∧
      (∀ i j,i≠j→Disjoint (Finset.univ.image (pr i)) (Finset.univ.image (pr j)))∧
      (∀ i j,i≠j→Disjoint (Finset.univ.image (ps i)) (Finset.univ.image (ps j)))∧
      (∀ i j,Disjoint (Finset.univ.image (pr i)) (Finset.univ.image (ps j)))∧
      (∀ i j a z,pr i a≠pr j z→¬PermutationClose π b (pr i a) (pr j z))∧
      (∀ i j a z,ps i a≠ps j z→¬PermutationClose π b (ps i a) (ps j z))∧
      ∀ i j a z,¬PermutationClose π b (pr i a) (ps j z):=by
  have hb:0≤(2*b+1:ℝ):=by positivity
  have hrb:W.card+((Fintype.card A:ℝ)*(l+3)+Z.card+l+4)*(2*b+1)<c:=by
    have hn:0≤(Fintype.card S:ℝ)*(l+4):=by positivity
    nlinarith only [hbudget,hb,hn]
  obtain ⟨pr,C,D,hC,hD,hrav,hrsep,hrdis,hrcross⟩:=marked_rim_cycle_families
    tail head ktail khead π b l hl v w v' w' jr W Z c hroots hvw hvw' hroot hropen hrclose hrstep hrjoin hrb
  let P:=Finset.univ.biUnion (fun i=>Finset.univ.image (pr i))
  have hPc:P.card≤Fintype.card A*(l+3):=by
    calc
      _≤∑ i:A,(Finset.univ.image (pr i)).card:=Finset.card_biUnion_le
      _≤∑ _:A,(l+3):=Finset.sum_le_sum (fun i _=>by simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_image_le (f:=(pr i:Fin (l+3)→V)) (s:=Finset.univ))
      _=Fintype.card A*(l+3):=by simp
  have hZc:((Z∪P).card:ℝ)≤Z.card+Fintype.card A*(l+3):=by
    have hu:=Finset.card_union_le Z P
    exact_mod_cast hu.trans (Nat.add_le_add_left hPc Z.card)
  have hsb:W.card+((Fintype.card S:ℝ)*((l+1)+3)+(Z∪P).card+(l+1)+4)*(2*b+1)<c:=by
    nlinarith only [hbudget,hZc,hb]
  obtain ⟨ps,SC,SD,hSh,hSC,hSD,hsav,hssep,hsdis,hscross⟩:=marked_spoke_wheel_families
    tail head ktail khead H₀ HK π b (l+1) (by omega) s s' u u' js W (Z∪P)
    (fun i=>⟨Finset.mem_union_left _ (hsroots i).1,Finset.mem_union_left _ (hsroots i).2⟩)
    c hsroot hsopen hsclose hsstep hsjoin (by simpa only [Nat.cast_add,Nat.cast_one] using hsb)
  refine ⟨pr,ps,C,D,SC,SD,hC,hD,hSh,hSC,hSD,hrav,?_,hrdis,hsdis,?_,hrcross,hscross,?_⟩
  · intro i a
    exact ⟨(hsav i a).1,fun h=>(hsav i a).2.1 (Finset.mem_union_left _ h),
      fun z hz=>(hsav i a).2.2 z (Finset.mem_union_left _ hz)⟩
  · intro i j
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hy
    exact (hsav j a).2.1 (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩))
  · intro i j a z hh
    exact (hsav j z).2.2 _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩))
      ((permutationClose_symm π b _ _).mp hh)

end Oberwolfach
