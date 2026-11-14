module

public import Oberwolfach.FiniteLabeledSetAssignment
public import Oberwolfach.OrdinaryRetainedCountCapacity

@[expose] public section
/-! Assign a hub's selected retained wheels injectively to unreserved
components of exactly the same size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_retained_component_assignment
    {n K:ℕ} (hn:0<n) {U A:Type} [Fintype U] [DecidableEq U] [DecidableEq A]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (s θ lam:ℝ) (hs0:0≤s) (hθ:0<θ) (hlam:lam<θ)
    (u:U) (C:Finset (F u).ConnectedComponent)
    (hC:∀c∈C,Fintype.card c=i₀.val+1)
    (hreserve:((i₀.val+1:ℕ):ℝ)*(C.card:ℝ)=s*n)
    (L:Finset A) (idx:A→Fin K)
    (hret:∀a∈L,θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ s θ u (idx a))
    (hcount:∀i:Fin K,∀hi:θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ s θ u i,
      |((longPaddedSeedExponent i+2:ℕ):ℝ)*((L.filter (fun a=>idx a=i)).card:ℝ)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ u i*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ s θ u i*n):
    ∃f:↥L↪↥(Finset.univ\C),∀a,Fintype.card (f a).val=(idx a.val).val+1 :=by
  classical
  apply finite_labeled_set_assignment L (Finset.univ\C) (fun a=>((idx a).val+1)) (fun c=>Fintype.card c)
  intro r
  by_cases hex:∃a∈L,(idx a).val+1=r
  · obtain ⟨a,ha,hr⟩:=hex
    let i:=idx a
    have hi:=hret a ha
    let z:OrdinaryAssignedRetainedHubTest F hF i₀ s θ:=⟨(i,u),hi⟩
    have hcap:=ordinary_retained_count_capacity hn F hF Allowed hAllowed hK i₀ s θ lam hs0 hθ hlam z C hC hreserve
      (L.filter (fun x=>idx x=i)).card (hcount i hi)
    dsimp only at hcap
    have hsrc:L.filter (fun x=>(idx x).val+1=r)=L.filter (fun x=>idx x=i):=by
      apply Finset.filter_congr
      intro x _
      constructor
      · intro hx
        apply Fin.ext
        dsimp [i] at *
        omega
      · intro hx
        rw [hx]
        exact hr
    have htgt:(Finset.univ\C).filter (fun c:(F u).ConnectedComponent=>Fintype.card c=r)=
        (Finset.univ.filter (fun c:(F u).ConnectedComponent=>Fintype.card c=i.val+1))\C:=by
      ext c
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
      rw [hr]
      tauto
    have hbound:(L.filter (fun x=>(idx x).val+1=r)).card ≤
        ((Finset.univ\C).filter (fun c:(F u).ConnectedComponent=>Fintype.card c=r)).card:=by
      rw [hsrc,htgt]
      exact hcap.le
    convert hbound using 1 <;> congr! 5
  · have hempty:L.filter (fun x=>(idx x).val+1=r)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hr
      exact hex ⟨a,ha,hr⟩
    have hh : (L.filter (fun x=>(idx x).val+1=r)).card ≤
        ((Finset.univ\C).filter (fun c:(F u).ConnectedComponent=>Fintype.card c=r)).card:=by
      rw [hempty,Finset.card_empty]
      exact Nat.zero_le _
    convert hh using 1 <;> congr! 5
end Oberwolfach
