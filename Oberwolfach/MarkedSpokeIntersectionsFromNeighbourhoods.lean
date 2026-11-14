module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges
public import Oberwolfach.ConstantSpokeIntersections
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Actual column intersections and row codegrees from the stated marked
neighbourhood estimates. Close pairs form the explicit exceptional set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedRows_spoke_intersections
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err density:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (mark:Bool)
    (hden:∀ u,(if mark then q u g else s u j)=density)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j err σ H)
    (S:Finset U) (hS:S.card≤h):
    |((commonSpokeNeighbours (H mark) S).card:ℝ)-density^S.card*Fintype.card V|<err:=by
  let e:U↪(Bool×U):=⟨fun u=>(mark,u),fun _ _ he=>congrArg Prod.snd he⟩
  have hi:Set.InjOn (fun a:Bool×U=>a.2) (S.image e):=by
    intro a ha b hb he
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hb
    exact congrArg e he
  have hh:=hr ∅ ∅ (S.image e) (by simp) (by simp)
    (by simpa only [Finset.card_image_of_injective _ e.injective] using hS) hi
  have hdom:markedRowDomain P π (3*d) Finset.univ ∅ ∅=Finset.univ:=by
    simp [markedRowDomain,Set.InjOn]
  have hcount:markedRowCountWithSpokes P π d σ H Finset.univ ∅ (S.image e)=
      ((commonSpokeNeighbours (H mark) S).card:ℝ):=by
    simp only [markedRowCountWithSpokes,Finset.notMem_empty,false_implies,implies_true,forall_const,true_and,
      Finset.forall_mem_image,commonSpokeNeighbours,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rfl
  rw [hdom,hcount,Finset.prod_empty,one_mul,Finset.card_univ,
    Finset.prod_image (fun _ _ _ _ he=>e.injective he)] at hh
  have hprod:(∏ a∈S,if (e a).1 then q (e a).2 g else s (e a).2 j)=density^S.card:=by
    simp only [show ∀ a,(if (e a).1 then q (e a).2 g else s (e a).2 j)=density from hden,
      Finset.prod_const]
  rw [hprod] at hh
  exact hh

theorem markedIndices_spoke_codegree
    (π:Equiv.Perm V) (d h:ℕ) (hh:2≤h)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err density:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (mark:Bool)
    (hden:∀ u,(if mark then q u g else s u j)=density)
    (hi:MarkedIndicesWithSpokes π d h Finset.univ q s g j err σ H)
    (x y:V) (hxy:¬PermutationClose π (3*d) x y):
    |((Finset.univ.filter (fun u=>H mark x u∧H mark y u)).card:ℝ)-density^2*Fintype.card U|<err:=by
  have hne:x≠y:=fun he=>hxy (Or.inl he)
  have hpair:(mark,x)≠(mark,y):=fun he=>hne (congrArg Prod.snd he)
  have hsep:∀ a∈({(mark,x),(mark,y)}:Finset (Bool×V)),∀ b∈({(mark,x),(mark,y)}:Finset (Bool×V)),
      a≠b→¬PermutationClose π (3*d) a.2 b.2:=by
    intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact False.elim (hab rfl)
    · exact hxy
    · exact fun hc=>hxy ((permutationClose_symm π (3*d) y x).mp hc)
    · exact False.elim (hab rfl)
  have hc:=hi {(mark,x),(mark,y)} (by simpa [hpair] using hh) hsep
  have hcount:markedIndexCountWithSpokes H Finset.univ {(mark,x),(mark,y)}=
      ((Finset.univ.filter (fun u=>H mark x u∧H mark y u)).card:ℝ):=by
    simp only [markedIndexCountWithSpokes,Finset.mem_insert,Finset.mem_singleton,
      forall_eq_or_imp,forall_eq,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hp (u:U):(∏ a∈({(mark,x),(mark,y)}:Finset (Bool×V)),if a.1 then q u g else s u j)=density^2:=by
    rw [Finset.prod_insert (by simpa only [Finset.mem_singleton] using hpair),Finset.prod_singleton]
    rw [hden]
    ring
  rw [hcount] at hc
  simp only [hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hc
  simpa only [mul_comm] using hc

theorem marked_neighbourhoods_sparse_intersection_data
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:3≤h) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (errR errI density p₀ δ:ℝ)
    (hp₀:0<p₀) (hp:p₀≤density) (hp1:density≤1) (hδ:0≤δ)
    (hR:errR≤δ*Fintype.card V) (hI:errI≤δ*density^2*Fintype.card U)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (mark:Bool)
    (hden:∀ u,(if mark then q u g else s u j)=density)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h Finset.univ q s g j errI σ H):
    SparseIntersectionData (H mark) (fun _=>density) (fun _=>1/density)
      (max 1 (1/p₀)) δ (6*d+1):=by
  apply sparseIntersectionData_of_constant_density (H mark) density p₀ δ (6*d+1) hp₀ hp hp1 hδ (by positivity)
  · intro S hS₁ hS₃
    exact (markedRows_spoke_intersections P π d h p k q s g j errR density σ H mark hden hr S (hS₃.trans hh)).le.trans hR
  · intro x
    let E:=Finset.univ.filter (fun y=>PermutationClose π (3*d) x y)
    refine ⟨E,?_,?_⟩
    · have hc:=permutationClose_neighbour_card π (3*d) x
      have he:E.card=Fintype.card {y // PermutationClose π (3*d) x y}:=by
        simp only [E,Fintype.card_subtype]
      rw [←he] at hc
      exact_mod_cast (show E.card≤6*d+1 by omega)
    · intro y hy
      have hxy:¬PermutationClose π (3*d) x y:=by simpa only [E,Finset.mem_filter,Finset.mem_univ,true_and] using hy
      exact (markedIndices_spoke_codegree π d h (by omega) q s g j errI density σ H mark hden hi x y hxy).le.trans hI

end Oberwolfach
