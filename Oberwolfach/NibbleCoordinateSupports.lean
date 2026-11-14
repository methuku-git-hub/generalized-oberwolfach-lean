module

public import Oberwolfach.CoinConflictCertificates
public import Oberwolfach.NibbleAvailableColours
public import Oberwolfach.JointColourRetention

@[expose] public section

/-! Exact coordinate supports of the counts in a tentative-colouring
round. These supports are fixed before the random assignments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def closedSetNeighbours {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset V := S∪setNeighbours G S

theorem coinColourSurvives_congr
    {V C : Type*} (G : SimpleGraph V) (σ τ : V → C×Bool) (v : V)
    (hv : σ v=τ v) (hN : ∀ u,G.Adj v u → σ u=τ u) :
    coinColourSurvives G σ v ↔ coinColourSurvives G τ v := by
  unfold coinColourSurvives tentativeColourSurvives
  rw [hv]
  apply and_congr_right'
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  change (σ u).1≠(σ v).1 ↔ (τ u).1≠(τ v).1
  rw [hN u hu,hv]

theorem coinConflictSet_congr
    {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (σ τ : V → C×Bool)
    (he : ∀ u∈closedSetNeighbours G T,σ u=τ u) :
    coinConflictSet G T σ=coinConflictSet G T τ := by
  ext v
  simp only [coinConflictSet,Finset.mem_filter]
  apply and_congr_right
  intro hv
  apply not_congr
  apply coinColourSurvives_congr G σ τ v
  · exact he v (Finset.mem_union_left _ hv)
  · intro u hu
    exact he u (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,hu⟩))

theorem colourAssignedIn_congr
    {V C : Type*} (T : Finset V) (σ τ : V → C×Bool)
    (he : ∀ v∈T,σ v=τ v) (c : C) :
    colourAssignedIn T σ c ↔ colourAssignedIn T τ c := by
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  rw [he v hv]

theorem colourRejectedIn_congr
    {V C : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (T : Finset V) (σ τ : V → C×Bool)
    (he : ∀ v∈closedSetNeighbours G T,σ v=τ v) (c : C) :
    colourRejectedIn G T σ c ↔ colourRejectedIn G T τ c := by
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  have hroot := he v (Finset.mem_union_left _ hv)
  have hsurv := coinColourSurvives_congr G σ τ v hroot (fun u hu=>
    he u (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,hu⟩)))
  change (σ v).1=c ∧ ¬coinColourSurvives G σ v ↔
    (τ v).1=c ∧ ¬coinColourSurvives G τ v
  rw [hroot,hsurv]

theorem closedSetNeighbours_mono
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {S T : Finset V} (hST : S⊆T) : closedSetNeighbours G S⊆closedSetNeighbours G T := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Finset.mem_union_left _ (hST hv)
  · obtain ⟨u,hu,huv⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hST hu,huv⟩)

theorem nibbleColourCount_support
    {V C J : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (L : Finset C) (a b : ℕ) (σ τ : V → C×Bool)
    (he : ∀ v∈closedSetNeighbours G (Q.biUnion T),σ v=τ v) :
    nibbleColourCount G Q T L a b σ=nibbleColourCount G Q T L a b τ := by
  have hclose (j : J) (hj : j∈Q) :
      ∀ v∈closedSetNeighbours G (T j),σ v=τ v :=
    fun v hv=>he v (closedSetNeighbours_mono G
      (fun v hv=>Finset.mem_biUnion.mpr ⟨j,hj,hv⟩) hv)
  have ha (c : C) : assignedSetIndices Q T σ c=assignedSetIndices Q T τ c := by
    ext j
    simp only [assignedSetIndices,Finset.mem_filter]
    apply and_congr_right
    intro hj
    exact colourAssignedIn_congr (T j) σ τ
      (fun v hv=>hclose j hj v (Finset.mem_union_left _ hv)) c
  have hb (c : C) : rejectedSetIndices G Q T σ c=rejectedSetIndices G Q T τ c := by
    ext j
    simp only [rejectedSetIndices,Finset.mem_filter]
    apply and_congr_right
    intro hj
    exact colourRejectedIn_congr G (T j) σ τ (hclose j hj) c
  unfold nibbleColourCount
  simp_rw [ha,hb]

theorem closedSetNeighbours_card_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {d : ℕ} (hd : ∀ v,(Finset.univ.filter (fun u=>G.Adj v u)).card≤d)
    (S : Finset V) : (closedSetNeighbours G S).card≤S.card*(d+1) := by
  have he : setNeighbours G S=S.biUnion (fun v=>Finset.univ.filter (fun u=>G.Adj v u)) := by
    ext u
    simp [setNeighbours]
  have hN : (setNeighbours G S).card≤S.card*d := by
    rw [he]
    exact Finset.card_biUnion_le_card_mul _ _ _ (fun v _=>hd v)
  have hcard := Finset.card_union_le S (setNeighbours G S)
  change (S∪setNeighbours G S).card≤_
  nlinarith

end Oberwolfach
