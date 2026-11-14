module

public import Oberwolfach.MarkedProtectedFiniteBalanceBounds
public import Oberwolfach.MarkedSamplePackingDomainBalanceBound
public import Oberwolfach.MarkedPackingFiniteStarAvoidance

@[expose] public section

/-! The protected balance estimates with the actual sampled wheel
packings. Divisibility of the removed sets and auxiliary incidence bounds
are deduced from the packings, their physical degrees and star avoidance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_protected_sample_balance_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hH:∀ v u,¬(H false v u∧H true v u)):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (C₀:Finset (E₀⊕E₁)) (CS₀:Finset (V×U))
      (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
    (∀ v,π v∈I↔v∈I)→(∀ v,π v∈T↔v∈T)→
    C₀⊆Finset.univ.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    CS₀⊆S.filter (fun s=>s.1∈I∧s.2∈J)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    ∀ (ME MD:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))),
    (∀ Y∈ME,∀ Z∈ME,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    (∀ Y∈MD,∀ Z∈MD,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    (MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅→
    ∀ εI εT δ₀ δR δS:ℝ,0≤εT→0≤δ₀→0≤δR→0≤δS→
    (∀ z i,|markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S m I J z i|≤εI)→
    (∀ z i,|markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S m T W z i|≤εT)→
    (∀ v,((C₀.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ₀)→
    (∀ v,((CS₀.filter (fun s=>s.1=v)).card:ℝ)≤δ₀)→
    (∀ u,((CS₀.filter (fun s=>s.2=u)).card:ℝ)≤δ₀)→
    (∀ v,((markedPackingRimGraph ME).degree v:ℝ)≤δR)→
    (∀ v,((Finset.univ.filter (markedPackingSpokes ME v)).card:ℝ)≤δS)→
    (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes ME v u)).card:ℝ)≤δS)→
    let C:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\C₀
    let CS:=(S.filter (fun s=>s.1∈I∧s.2∈J))\CS₀
    let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun s=>s.1∈T∨s.2∈W)
    let EA:=ME.biUnion markedWheelArcs
    let ES:=ME.biUnion markedWheelSpokePairs
    let DA:=MD.biUnion markedWheelArcs
    let DS:=MD.biUnion markedWheelSpokePairs;
    EA⊆Finset.univ\KA→ES⊆S\KS→DA⊆(Finset.univ\KA)\EA→DS⊆(S\KS)\ES→
    ∀ (z:V⊕U),Sum.elim (fun v=>v∉T) (fun u=>u∉W) z→∀ i:Fin 4,
    |markedFiniteBalance tail head ktail khead (H true) (((Finset.univ\KA)\EA)\DA) (((S\KS)\ES)\DS) m z i|
      ≤εT+(m+2)*δ₀∧
    |markedFiniteDomainBalance tail head ktail khead (H true) (((Finset.univ\KA)\EA)\DA) (((S\KS)\ES)\DS) m (I\T) (J\W) z i|
      ≤εI+εT+(m+2)*(4*δR+δS):=by
  intro E₀ E₁ tail head ktail khead S C₀ CS₀ I T J W hTI hWJ hI hT hC₀ hCS₀ hdiv ME MD hME hMD hstar
    εI εT δ₀ δR δS hεT hδ₀ hδR hδS hAI hAT hC₀A hC₀R hC₀C hMER hMES hMEC
    C CS KA KS EA ES DA DS hEA hES hDA hDS z hz i
  have hactive:∀ v,π v∈I\T↔v∈I\T:=by
    intro v;simp only [Finset.mem_sdiff,hI,hT]
  obtain ⟨hDAvoid,hDSvoid⟩:=marked_packing_finite_star_avoidance MD (I\T) (J\W) hactive hstar
  have hphysical:=marked_finite_physical_incidence_bound P π d σ EA δR (by
    rw [markedSampleArcSetGraph_packing];exact hMER)
  obtain ⟨hrow,hcol⟩:=markedPacking_finite_spoke_incidence_counts ME
  have hEinc:∀ v,((EA.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤4*δR+δS:=by
    intro v;exact (hphysical v).trans (by linarith)
  have hER:∀ v,((ES.filter (fun s=>s.1=v)).card:ℝ)≤4*δR+δS:=by
    intro v
    change (((ME.biUnion markedWheelSpokePairs).filter (fun s=>s.1=v)).card:ℝ)≤_
    rw [hrow]
    exact (hMES v).trans (by linarith)
  have hEC:∀ u,((ES.filter (fun s=>s.2=u)).card:ℝ)≤4*δR+δS:=by
    intro u
    change (((ME.biUnion markedWheelSpokePairs).filter (fun s=>s.2=u)).card:ℝ)≤_
    rw [hcol]
    exact (hMEC u).trans (by linarith)
  exact marked_protected_finite_balance_bounds tail head ktail khead (H true) Finset.univ C₀ EA DA S CS₀ ES DS m
    I T J W hTI hWJ hC₀ hCS₀ hdiv (marked_packing_finite_divisible hH ME hME)
    (marked_packing_finite_divisible hH MD hMD) hDAvoid hDSvoid εI εT δ₀ (4*δR+δS) hεT hδ₀
    (by positivity) hAI hAT hC₀A hC₀R hC₀C hEinc hER hEC hEA hES hDA hDS z hz i

end Oberwolfach
