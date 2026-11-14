module

public import Oberwolfach.OrderedOrdinaryWheelCountingEquiv
public import Oberwolfach.MarkedWheelEventScales

@[expose] public section
/-! Counting only: transfer the fixed-vertex and hub estimate through the
index equivalence, without identifying the two sampling models. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_normalized_event (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S:Finset V) (hS:1≤S.card) (hSm:S.card≤m+1) (T:Finset U)
    (P:OrderedOrdinaryWheel (U:=U) π b (m+1)→Prop)
    (hP:∀ W,P W→(∀ v∈S,v∈Set.range W.1.val) ∧ W.2∈T):
    (∑ W,if P W then w W else 0)≤
      (T.card:ℝ)*((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1):=by
  let e:=orderedOrdinaryMarkedWheelEquiv (V:=V) (U:=U) (π:=π) (m:=m) (b:=b)
  let wm:=fun W=>w (e.symm W)
  let Pm:=fun W=>P (e.symm W)
  have hh:=marked_wheel_normalized_event hn wm B hB (fun W=>hw (e.symm W)) S hS hSm T Pm (by
    intro W hW
    exact hP (e.symm W) hW)
  have he:(∑ W,if Pm W then wm W else 0)=∑ W,if P W then w W else 0:=by
    calc
      _ = ∑ W,if Pm (e W) then wm (e W) else 0 := (Equiv.sum_comp e _).symm
      _ = _ := by simp only [Pm,wm,Equiv.symm_apply_apply]
  rwa [he] at hh

theorem orderedOrdinary_fixed_hub_event (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S:Finset V) (hS:1≤S.card) (hSm:S.card≤m+1) (u:U)
    (P:OrderedOrdinaryWheel (U:=U) π b (m+1)→Prop)
    (hP:∀ W,P W→(∀ v∈S,v∈Set.range W.1.val) ∧ W.2=u):
    (∑ W,if P W then w W else 0)≤((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1):=by
  have hh:=orderedOrdinary_normalized_event hn w B hB hw S hS hSm {u} P
    (by intro W h;exact ⟨(hP W h).1,Finset.mem_singleton.mpr (hP W h).2⟩)
  simpa only [Finset.card_singleton,Nat.cast_one,one_mul] using hh

theorem orderedOrdinary_free_hub_event (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S:Finset V) (hS:2≤S.card) (hSm:S.card≤m+1)
    (P:OrderedOrdinaryWheel (U:=U) π b (m+1)→Prop)
    (hP:∀ W,P W→∀ v∈S,v∈Set.range W.1.val):
    (∑ W,if P W then w W else 0)≤((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-2):=by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hh:=orderedOrdinary_normalized_event hn w B hB hw S (by omega) hSm Finset.univ P
    (by intro W h;exact ⟨hP W h,Finset.mem_univ _⟩)
  simp only [Finset.card_univ] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (Fintype.card V:ℝ)*((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) :=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hu
    _ = _ :=by
      have hp:(Fintype.card V:ℝ)^(S.card-1)=(Fintype.card V:ℝ)^(S.card-2)*Fintype.card V:=by
        rw [←pow_succ];congr 1;omega
      rw [hp];field_simp

end Oberwolfach
