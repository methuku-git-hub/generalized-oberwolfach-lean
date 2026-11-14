module

public import Oberwolfach.LongMarkedDeletedPairBounds
public import Oberwolfach.LongRawAdaptivePhysicalDeletion

@[expose] public section
/-! A bounded physical-rim deletion has a quantitative, root-uniform effect
on every fixed ordinary-wheel seed load in the mixed resource universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {m b:ℕ}

theorem long_marked_fixed_load_after_physical_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (hm:3≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m)
    (root:LongRawHubResource n U) (target δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ):
    let R:=typedMarkedOccurrenceResources
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let survived:=fun z=>decide (z∈S)
    let A:=longMarkedRootVertices root
    let M:=((m:ℝ)+1)^4*B/(n:ℝ)
    let N:=((m:ℝ)+1)^4*B/(n:ℝ)^2
    |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        2*δ*((A.card+A.card:ℝ)*M+(n:ℝ)*N) :=by
  intro R state S survived A M N
  have hM:0≤M:=by dsimp [M];positivity
  have hN:0≤N:=by dsimp [N];positivity
  let Deleted:Finset (LongRawHubResource n U):=(bernoulliVertexSet state).filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈D.edgeFinset)
  have hpair:∀a∈Deleted,resourceOmittedPairWeight R w root a≤
      (if longRawResourceTail a∈A ∨ longRawResourceHead a∈A then M else N):=by
    intro a ha
    obtain ⟨e,rfl,_⟩:=(long_raw_deleted_resource_iff_rim_changed P D π d raw g j a).mp ha
    convert long_marked_deleted_rim_pair_near_far hm hn hu w B hB hw root e using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have hp:=long_raw_adaptive_pattern_load_physical_deletion P D π d raw g j R w
    (fun W=>(hw W).1) root target δ M N hM hN hD A A hpair
  exact hp
theorem long_marked_root_vertices_card_le_two (root:LongRawHubResource n U):
    (longMarkedRootVertices root).card≤2 :=by
  classical
  cases root with
  | inl r =>
    simp only [longMarkedRootVertices]
    exact (Finset.card_insert_le _ _).trans (by simp)
  | inr r =>
    rcases r with ⟨mark,v,u⟩
    simp [longMarkedRootVertices]

theorem long_marked_fixed_load_after_physical_deletion_uniform
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (hm:3≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m)
    (root:LongRawHubResource n U) (target δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ):
    let R:=typedMarkedOccurrenceResources
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let survived:=fun z=>decide (z∈S)
    |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        10*δ*((m:ℝ)+1)^4*B/(n:ℝ) :=by
  intro R state S survived
  have h:=long_marked_fixed_load_after_physical_deletion P D π d raw g j hm hn hu w B hB hw root target δ hD
  let A:=longMarkedRootVertices root
  let C:ℝ:=((m:ℝ)+1)^4*B
  let M:=C/(n:ℝ)
  let N:=C/(n:ℝ)^2
  change |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        2*δ*((A.card+A.card:ℝ)*M+(n:ℝ)*N) at h
  have hA:(A.card:ℝ)≤2:=by exact_mod_cast long_marked_root_vertices_card_le_two root
  have hδ:0≤δ:=(Nat.cast_nonneg (D.degree ⟨0,hn⟩)).trans (hD ⟨0,hn⟩)
  have hM:0≤M:=by dsimp [M,C];positivity
  have hnR:(n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum:(A.card:ℝ)+(A.card:ℝ)≤4:=by linarith
  have hscale:2*δ*((A.card+A.card:ℝ)*M+(n:ℝ)*N)≤2*δ*(4*M+(n:ℝ)*N):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_right hsum hM) (le_refl _)
  have hid:2*δ*(4*M+(n:ℝ)*N)=10*δ*C/(n:ℝ):=by
    dsimp [M,N]
    field_simp
    ring
  have hb:=hscale.trans_eq hid
  apply h.trans
  convert add_le_add (le_refl _) hb using 1 <;> congr 1 <;> simp only [C] <;> ring

end Oberwolfach
