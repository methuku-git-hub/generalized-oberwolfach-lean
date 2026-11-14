module

public import Oberwolfach.OrdinaryAssignedRetainedHubTests
public import Oberwolfach.CycleComponentFrequency

@[expose] public section
/-! A retained frequency counts vertices in actual unreserved components of
its size. The reserved family may be nonempty only at its designated size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_retained_available_components
    {n K:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (s θ:ℝ) (hθ:0<θ)
    (u:U) (i:Fin K) (C:Finset (F u).ConnectedComponent)
    (hC:∀c∈C,Fintype.card c=i₀.val+1)
    (hreserve:((i₀.val+1:ℕ):ℝ)*(C.card:ℝ)=s*n)
    (hret:θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ s θ u i):
    let T:=Finset.univ.filter (fun c:(F u).ConnectedComponent=>Fintype.card c=i.val+1)
    ordinaryAssignedKeptFraction F hF K i₀ s θ u i*n =
      ((i.val+1:ℕ):ℝ)*((T\C).card:ℝ) :=by
  intro T
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hmin:0<θ/(100*(K:ℝ)):=by positivity
  have hkept:ordinaryAssignedKeptFraction F hF K i₀ s θ u i =
      ordinaryAssignedFraction F hF K u (some i)-(if i=i₀ then s else 0):=by
    by_cases hf:ordinaryAssignedFraction F hF K u (some i)-(if i=i₀ then s else 0)<θ/(100*(K:ℝ))
    · simp only [ordinaryAssignedKeptFraction, hf, if_true] at hret
      linarith
    · simp only [ordinaryAssignedKeptFraction, hf, if_false]
  have hcount:=long_preparation_fraction_component_count hn (F u) (hF u) i
  have hr:(((i.val+1:ℕ):ℝ))≠0:=by positivity
  have hraw:ordinaryAssignedFraction F hF K u (some i)*n=
      ((i.val+1:ℕ):ℝ)*(T.card:ℝ):=by
    have hh:=hcount
    dsimp only at hh
    have hh' : ordinaryAssignedFraction F hF K u (some i)*n / ((i.val+1:ℕ):ℝ)=(T.card:ℝ) := by
      convert hh using 1 <;> (try simp only [ordinaryAssignedFraction,T]) <;> congr! 5
    simpa only [mul_comm] using (div_eq_iff hr).mp hh'
  by_cases hi:i=i₀
  · subst i
    have hsub:C⊆T:=by
      intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hC c hc⟩
    have hcard:=Finset.card_sdiff_add_card_eq_card hsub
    have hcard' : (((T\C).card:ℕ):ℝ)+(C.card:ℝ)=(T.card:ℝ):=by exact_mod_cast hcard
    rw [hkept,if_pos rfl]
    nlinarith [hraw,hreserve]
  · have hdis:Disjoint T C:=by
      apply Finset.disjoint_left.mpr
      intro c hcT hcC
      have hc1: Fintype.card c=i.val+1 := (Finset.mem_filter.mp hcT).2
      have hc2:=hC c hcC
      have hv:i.val=i₀.val:=by omega
      exact hi (Fin.ext hv)
    have hcard:T\C=T:=Finset.sdiff_eq_self_of_disjoint hdis
    rw [hkept,if_neg hi,hcard]
    simpa using hraw
end Oberwolfach
