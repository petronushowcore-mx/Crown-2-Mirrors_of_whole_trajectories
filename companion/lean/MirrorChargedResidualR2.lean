import Mathlib

set_option autoImplicit false

namespace MirrorResidualWear

variable {α : Type*}

def wear (cost : α → Nat) (path : List α) : Nat :=
  (path.map cost).sum

def charge (cost : α → Nat) (b : Nat) (past : List α) : Nat :=
  b + wear cost past

def WholeViable (cost : α → Nat) (b C : Nat) (path : List α) : Prop :=
  ∀ k : Nat, k ≤ path.length → b + wear cost (path.take k) ≤ C

theorem wear_take_le (cost : α → Nat) (path : List α) (k : Nat) :
    wear cost (path.take k) ≤ wear cost path := by
  induction path generalizing k with
  | nil => simp [wear]
  | cons c path ih =>
      cases k with
      | zero => simp [wear]
      | succ k =>
          simpa [wear] using Nat.add_le_add_left (ih k) (cost c)

theorem whole_viable_iff_final (cost : α → Nat)
    (b C : Nat) (path : List α) :
    WholeViable cost b C path ↔ b + wear cost path ≤ C := by
  constructor
  · intro h
    simpa using h path.length (Nat.le_refl path.length)
  · intro h k _hk
    exact le_trans (Nat.add_le_add_left (wear_take_le cost path k) b) h

theorem wear_append (cost : α → Nat) (past suffix : List α) :
    wear cost (past ++ suffix) = wear cost past + wear cost suffix := by
  simp [wear, List.map_append, List.sum_append]

theorem charge_append (cost : α → Nat)
    (b : Nat) (past suffix : List α) :
    charge cost (charge cost b past) suffix =
      charge cost b (past ++ suffix) := by
  simp [charge, wear_append, Nat.add_assoc]

theorem whole_viable_append_iff (cost : α → Nat)
    (b C : Nat) (past suffix : List α) :
    WholeViable cost b C (past ++ suffix) ↔
      WholeViable cost (charge cost b past) C suffix := by
  simp only [whole_viable_iff_final]
  simp [charge, wear_append, Nat.add_assoc]

def ReservoirMember (cost : α → Nat)
    (reach identity admissible : List α → Prop)
    (b C : Nat) (path : List α) : Prop :=
  reach path ∧ identity path ∧ admissible path ∧ WholeViable cost b C path

theorem reservoir_residual_iff (cost : α → Nat)
    (b C : Nat) (past suffix : List α)
    (reachWhole identityWhole admissibleWhole : List α → Prop)
    (reachSuffix identitySuffix admissibleSuffix : List α → Prop)
    (hReach : reachWhole (past ++ suffix) ↔ reachSuffix suffix)
    (hIdentity : identityWhole (past ++ suffix) ↔ identitySuffix suffix)
    (hAdmissible : admissibleWhole (past ++ suffix) ↔ admissibleSuffix suffix) :
    ReservoirMember cost reachWhole identityWhole admissibleWhole
        b C (past ++ suffix) ↔
      ReservoirMember cost reachSuffix identitySuffix admissibleSuffix
        (charge cost b past) C suffix := by
  unfold ReservoirMember
  rw [hReach, hIdentity, hAdmissible, whole_viable_append_iff]

theorem reservoir_set_residual (cost : α → Nat)
    (b C : Nat) (past : List α)
    (reachWhole identityWhole admissibleWhole : List α → Prop)
    (reachSuffix identitySuffix admissibleSuffix : List α → Prop)
    (hReach : ∀ suffix, reachWhole (past ++ suffix) ↔ reachSuffix suffix)
    (hIdentity : ∀ suffix, identityWhole (past ++ suffix) ↔ identitySuffix suffix)
    (hAdmissible : ∀ suffix, admissibleWhole (past ++ suffix) ↔ admissibleSuffix suffix) :
    {suffix | ReservoirMember cost reachWhole identityWhole admissibleWhole b C (past ++ suffix)} =
      {suffix | ReservoirMember cost reachSuffix identitySuffix admissibleSuffix
        (charge cost b past) C suffix} := by
  ext suffix
  exact reservoir_residual_iff cost b C past suffix
    reachWhole identityWhole admissibleWhole reachSuffix identitySuffix admissibleSuffix
    (hReach suffix) (hIdentity suffix) (hAdmissible suffix)

theorem reset_false_acceptance :
    WholeViable id 0 1 [1] ∧
    ¬ WholeViable id 0 1 ([1] ++ [1]) ∧
    ¬ WholeViable id (charge id 0 [1]) 1 [1] := by
  simp only [whole_viable_iff_final]
  norm_num [charge, wear]

theorem charged_positive_example :
    charge id 0 [1] = 1 ∧
    WholeViable id 0 2 ([1] ++ [1]) ∧
    WholeViable id (charge id 0 [1]) 2 [1] := by
  simp only [whole_viable_iff_final]
  norm_num [charge, wear]

theorem history_append_one_grows (history : List α) (event : α) :
    (history ++ [event]).length = history.length + 1 ∧
    history.length < (history ++ [event]).length := by
  have hLength : (history ++ [event]).length = history.length + 1 := by simp
  exact ⟨hLength, by omega⟩

end MirrorResidualWear
