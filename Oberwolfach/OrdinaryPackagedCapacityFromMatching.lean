module

public import Oberwolfach.OrdinaryPackagedCapacityFromMatchingShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packaged_capacity_from_matching
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (err:ℝ) (herr:0<err):
    OrdinaryPackagedCapacityFromMatchingShape m d hm hd θ hθ err herr :=by
  unfold OrdinaryPackagedCapacityFromMatchingShape
  obtain ⟨N,hN⟩:=ordinary_unreserved_family_size_and_capacity_with_targets_from_matching_eventually_candidate_direct_reserve m d hm hd θ hθ err herr
  refine ⟨N,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim
    H RM state RR φ L AM AU len wheels E S MW W Good Pack A B root Pos X G Arc Avail Reserve p Q Row
    hmatch hQ hζ he hrate hrow δ hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b z hα hb hbudgetCap Gbad Z hdegree hZ
  simp only [len,Nat.cast_sum,Nat.cast_add,Nat.cast_ofNat] at hmatch hmatchUpper
  have hFin:ordinaryForcedFamilySizeCapacityFin_candidate_direct_reserve n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hcall:=hN (n:=n) (K:=K) hnN (U:=U)
  rw [hFin] at hcall
  apply hcall hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim
    L (fun u=>(p u).marker) (fun u=>(p u).hGood) (fun u=>(p u).data)
    (fun u=>(p u).hc) (fun u=>(p u).hd) (fun u=>(p u).hs₁) (fun u=>(p u).hs₂)
    (fun u=>(p u).ht) (fun u=>(p u).hEmbed) (fun u=>(p u).hCycleLength) ?_
    hmatch hQ hζ he hrate hrow δ hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b z hα hb hbudgetCap Gbad Z hdegree hZ
  intro u i
  simpa only [Pos,root,retainedAndRawIntervalRoot] using (p u).hPos i
end Oberwolfach
