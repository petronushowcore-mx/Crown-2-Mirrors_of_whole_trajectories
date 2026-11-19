import Mathlib

/-!
# Mirrors of Whole Trajectories: what a gate leaves, what a budget allows, what a mechanism supplies

Statements that connect results kept apart in the line. Everything here is a statement about the
declared discrete models below. Nothing says that a physical system satisfies these premises, and no
result identifies the toy edge of Section 5 with the corpus's endogenous operator.

Map to the text: M9 is `key_sufficient_iff` with `reservoir_eq_iff` and
`residual_depends_on_last_bit`; M10 is Section 5 here; M11 is `spendsAll_has_mixed_fibres`;
M12 is `residue_is_a_missing_event` with `floor_is_needed`; M13 is `silent_after_depth` and
`determined_at_depth`; M14 is `driven_spends_all`; M15 is Section 4 here; M16 is `frontier_iff` and
`payable_finite`. Section 7 here belongs to Section 11.4 of the text.

* Section 1: with a uniform positive cost for every event and a finite budget, an inadmissible legal
  trajectory that has no excluded prefix is silent from some step on, and the admitted trajectories
  near it differ from it only by an event after that silence.
* Section 2: a uniform cost and a bound on silence decide every predicate at one explicit depth.
* Section 3: a non-closed predicate survives a cost floor, so the separation of finite mirrors does
  not need infinitely many events.
* Section 4: the ledger without a floor is the core toy sampled at returns; the same series is the
  maintenance of a halving witness. A witness floor, an infinite horizon and a finite budget do not
  go together.
* Section 5: capability and realised continuation are independent, and in this model capability is
  exactly a bound on silence under a silent environment.
* Section 6: a key is sufficient for continuation exactly when residuals factor through it. A ledger
  needs only as much resolution as the tail costs require, and finite state is not finite depth.
* Section 7: on the doubling tower exact witnesses and unexplained logs are two different groups.
-/

namespace MirrorsComposition

open Finset

/-! ## 1. Trajectories with silence -/

section Silence

variable {Ev : Type*}

/-- A trajectory: at each step an event, or silence (`none`). -/
abbrev Traj (Ev : Type*) := ℕ → Option Ev

/-- Agreement on the first `n` steps. -/
def Agree (x y : Traj Ev) (n : ℕ) : Prop := ∀ k < n, x k = y k

/-- Membership in the prefix closure of `A`. -/
def InClosure (A : Set (Traj Ev)) (x : Traj Ev) : Prop := ∀ n, ∃ y ∈ A, Agree x y n

/-- The number of events among the first `n` steps. -/
noncomputable def count (x : Traj Ev) : ℕ → ℕ
  | 0 => 0
  | n + 1 => count x n + (if (x n).isSome then 1 else 0)

theorem count_mono (x : Traj Ev) {n m : ℕ} (h : n ≤ m) : count x n ≤ count x m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    simp only [count]
    omega

/-- The increments `d` pay for `x` with floor `ε` inside budget `R`. -/
structure Paid (x : Traj Ev) (d : ℕ → ℝ) (ε R : ℝ) : Prop where
  floor_pos : 0 < ε
  nonneg : ∀ k, 0 ≤ d k
  floor : ∀ k, (x k).isSome → ε ≤ d k
  legal : ∀ n, ∑ k ∈ range n, d k ≤ R

theorem count_mul_floor_le {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R) (n : ℕ) :
    (count x n : ℝ) * ε ≤ ∑ k ∈ range n, d k := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases h : (x n).isSome
    · have hc : count x (n + 1) = count x n + 1 := by simp [count, h]
      rw [hc]
      push_cast
      have hf := p.floor n h
      have e : ((count x n : ℝ) + 1) * ε = (count x n : ℝ) * ε + ε := by ring
      rw [e]
      linarith
    · have hc : count x (n + 1) = count x n := by simp [count, h]
      rw [hc]
      have := p.nonneg n
      linarith

/-- With a floor and a finite budget the count of events is bounded. -/
theorem count_bounded {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R) (N : ℕ)
    (hN : R < ((N : ℝ) + 1) * ε) (n : ℕ) : count x n ≤ N := by
  have h1 := count_mul_floor_le p n
  have h2 := p.legal n
  have h3 : (count x n : ℝ) * ε < ((N : ℝ) + 1) * ε := by linarith
  have h4 : (count x n : ℝ) < (N : ℝ) + 1 := lt_of_mul_lt_mul_right h3 p.floor_pos.le
  have h5 : count x n < N + 1 := by exact_mod_cast h4
  omega

theorem exists_bound (ε R : ℝ) (hε : 0 < ε) : ∃ N : ℕ, R < ((N : ℝ) + 1) * ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R / ε)
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ hε] at hN
  nlinarith

/-- With a floor and a finite budget every legal trajectory is silent from some step on. -/
theorem eventually_silent {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R) :
    ∃ L, ∀ k ≥ L, x k = none := by
  by_contra hne
  push_neg at hne
  obtain ⟨N, hN⟩ := exists_bound ε R p.floor_pos
  have grow : ∀ m : ℕ, ∃ n, m ≤ count x n := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hk, hkn⟩ := hne n
      refine ⟨k + 1, ?_⟩
      have hs : (x k).isSome := Option.isSome_iff_ne_none.mpr hkn
      have h1 : count x n ≤ count x k := count_mono x hk
      simp only [count, hs, if_true]
      omega
  obtain ⟨n, hn⟩ := grow (N + 1)
  have := count_bounded p N hN n
  omega

/-- **What a gate leaves.** Let `x` be legal under a cost floor, out of `A`, and in the prefix closure
of `A`, so that it has no excluded finite prefix. Then `x` is silent from some step `L` on, and for
every `m ≥ L` a member of `A` agrees with `x` on `m` steps and has an event at or after `m`. The fault
of `x` is a next event that never comes. -/
theorem residue_is_a_missing_event {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R)
    {A : Set (Traj Ev)} (hxA : x ∉ A) (hcl : InClosure A x) :
    ∃ L, (∀ k ≥ L, x k = none) ∧ ∀ m ≥ L, ∃ y ∈ A, Agree x y m ∧ ∃ k ≥ m, y k ≠ none := by
  obtain ⟨L, hL⟩ := eventually_silent p
  refine ⟨L, hL, fun m hm => ?_⟩
  obtain ⟨y, hyA, hag⟩ := hcl m
  refine ⟨y, hyA, hag, ?_⟩
  have hne : x ≠ y := fun e => hxA (e ▸ hyA)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hkm : m ≤ k := by
    by_contra hlt
    exact hk (hag k (by omega))
  refine ⟨k, hkm, fun hy => hk ?_⟩
  rw [hy, hL k (by omega)]

/-- Under a floor and a finite budget a predicate asking for infinitely many events is empty. -/
theorem no_infinite_events {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R) :
    ¬ ∀ t, ∃ s ≥ t, (x s).isSome = true := by
  intro h
  obtain ⟨L, hL⟩ := eventually_silent p
  obtain ⟨s, hs, hv⟩ := h L
  rw [hL s hs] at hv
  simp at hv

end Silence

/-! ## 2. A bound on silence decides at one explicit depth -/

section Depth

variable {Ev : Type*}

/-- Every event comes within `D + 1` steps of the start or of the previous event. -/
def SilenceBound (D : ℕ) (x : Traj Ev) : Prop :=
  ∀ k, (x k).isSome → k ≤ D ∨ ∃ j < k, k ≤ j + D + 1 ∧ (x j).isSome

theorem position_lt {D : ℕ} {x : Traj Ev} (hg : SilenceBound D x) :
    ∀ k, (x k).isSome → k < count x (k + 1) * (D + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hs
    have hstep : count x (k + 1) = count x k + 1 := by simp [count, hs]
    rcases hg k hs with hk | ⟨j, hj, hkj, hjs⟩
    · rw [hstep]
      nlinarith [Nat.zero_le (count x k)]
    · have h1 := ih j hj hjs
      have h2 : count x (j + 1) ≤ count x k := count_mono x hj
      rw [hstep]
      have h3 : count x (j + 1) * (D + 1) ≤ count x k * (D + 1) := Nat.mul_le_mul_right _ h2
      have h4 : (count x k + 1) * (D + 1) = count x k * (D + 1) + (D + 1) := by ring
      omega

/-- With a floor and a bound on silence, nothing happens after an explicit depth. -/
theorem silent_after_depth {D N : ℕ} {x : Traj Ev} {d : ℕ → ℝ} {ε R : ℝ} (p : Paid x d ε R)
    (hN : R < ((N : ℝ) + 1) * ε) (hg : SilenceBound D x) :
    ∀ k ≥ N * (D + 1), x k = none := by
  intro k hk
  by_contra hne
  have hs : (x k).isSome := Option.isSome_iff_ne_none.mpr hne
  have h1 := position_lt hg k hs
  have h2 := count_bounded p N hN (k + 1)
  have h3 : count x (k + 1) * (D + 1) ≤ N * (D + 1) := Nat.mul_le_mul_right _ h2
  omega

/-- Two such trajectories that agree up to depth `N * (D + 1)` are equal. -/
theorem determined_at_depth {D N : ℕ} {x y : Traj Ev} {dx dy : ℕ → ℝ} {ε R : ℝ}
    (px : Paid x dx ε R) (py : Paid y dy ε R) (hN : R < ((N : ℝ) + 1) * ε)
    (gx : SilenceBound D x) (gy : SilenceBound D y) (hag : Agree x y (N * (D + 1))) : x = y := by
  funext k
  by_cases hk : k < N * (D + 1)
  · exact hag k hk
  · rw [silent_after_depth px hN gx k (by omega), silent_after_depth py hN gy k (by omega)]

/-- **Every predicate is decided at that depth.** Among trajectories with a floor and a bound on
silence, a trajectory out of `A` is separated from every member of `A` by its first `N * (D + 1)`
steps, whatever `A` is. -/
theorem decided_at_depth {D N : ℕ} {x y : Traj Ev} {dx dy : ℕ → ℝ} {ε R : ℝ}
    (px : Paid x dx ε R) (py : Paid y dy ε R) (hN : R < ((N : ℝ) + 1) * ε)
    (gx : SilenceBound D x) (gy : SilenceBound D y) {A : Set (Traj Ev)}
    (hxA : x ∉ A) (hyA : y ∈ A) : ¬ Agree x y (N * (D + 1)) := fun hag =>
  hxA (determined_at_depth px py hN gx gy hag ▸ hyA)

end Depth

/-! ## 3. A non-closed predicate under a cost floor -/

section SpendsAll

/-- Silence for `n` steps, then `N` events, then silence. -/
def late (N n : ℕ) : Traj Unit := fun k => if n ≤ k ∧ k < n + N then some () else none

/-- Eternal silence. -/
def quiet : Traj Unit := fun _ => none

/-- Unit cost on events. -/
noncomputable def unitCost (x : Traj Unit) : ℕ → ℝ := fun k => if (x k).isSome then 1 else 0

theorem sum_unitCost (x : Traj Unit) (n : ℕ) :
    ∑ k ∈ range n, unitCost x k = (count x n : ℝ) := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [count, unitCost]
    by_cases h : (x n).isSome <;> simp [h]

theorem count_late (N n m : ℕ) : count (late N n) m = min (m - n) N := by
  induction m with
  | zero => simp [count]
  | succ m ih =>
    simp only [count, ih, late]
    by_cases h : n ≤ m ∧ m < n + N
    · simp only [h, and_self, if_true, Option.isSome_some]
      omega
    · simp only [h, if_false, Option.isSome_none]
      simp only [Bool.false_eq_true, if_false]
      omega

theorem count_quiet (m : ℕ) : count quiet m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [count, ih, quiet]

/-- A trajectory that spends the whole budget of `N` events. -/
def SpendsAll (N : ℕ) (x : Traj Unit) : Prop := ∃ m, count x m = N

/-- Each member of this family is legal under unit cost and budget `N`. -/
theorem late_paid (N n : ℕ) : Paid (late N n) (unitCost (late N n)) 1 N where
  floor_pos := one_pos
  nonneg := fun k => by simp only [unitCost]; split_ifs <;> norm_num
  floor := fun k h => by simp [unitCost, h]
  legal := fun m => by
    rw [sum_unitCost, count_late]
    exact_mod_cast min_le_right _ _

theorem quiet_paid (N : ℕ) : Paid quiet (unitCost quiet) 1 N where
  floor_pos := one_pos
  nonneg := fun k => by simp [unitCost, quiet]
  floor := fun k h => by simp [quiet] at h
  legal := fun m => by
    rw [sum_unitCost, count_quiet]
    simp

/-- **The separation of finite mirrors survives the floor.** With a budget of `N ≥ 1` events, "spends
the whole budget" is met by a legal trajectory after any finite silence and missed by eternal
silence, and the two agree on the first `n` steps. Nothing here needs infinitely many events. -/
theorem spendsAll_has_mixed_fibres (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    SpendsAll N (late N n) ∧ ¬ SpendsAll N quiet ∧ Agree quiet (late N n) n := by
  refine ⟨⟨n + N, ?_⟩, ?_, ?_⟩
  · rw [count_late]
    omega
  · rintro ⟨m, hm⟩
    rw [count_quiet] at hm
    omega
  · intro k hk
    simp only [quiet, late]
    rw [if_neg]
    omega

/-- A bound on silence removes these fibres: `late N n` has no bound `D` below `n`. -/
theorem late_breaks_silence_bound (N n D : ℕ) (hN : 1 ≤ N) (hD : D < n) :
    ¬ SilenceBound D (late N n) := by
  intro hg
  have hs : (late N n n).isSome := by
    simp only [late]
    rw [if_pos]
    · rfl
    · omega
  rcases hg n hs with h | ⟨j, hj, _, hjs⟩
  · omega
  · simp only [late] at hjs
    rw [if_neg (by omega)] at hjs
    simp at hjs

/-- Eternal silence is in the closure of "spends the whole budget", and out of it. So the residue
statement of Section 1 has an instance, under a floor and with finitely many events everywhere. -/
theorem quiet_is_a_residue (N : ℕ) (hN : 1 ≤ N) :
    quiet ∉ {x | SpendsAll N x} ∧ InClosure {x | SpendsAll N x} quiet := by
  refine ⟨(spendsAll_has_mixed_fibres N hN 0).2.1, fun n => ?_⟩
  exact ⟨late N n, (spendsAll_has_mixed_fibres N hN n).1, (spendsAll_has_mixed_fibres N hN n).2.2⟩

/-- Driven with a bound on silence: while the budget of `N` events is not spent, an event comes within
`D + 1` steps. -/
def Driven {Ev : Type*} (N D : ℕ) (x : Traj Ev) : Prop :=
  ∀ t, count x t < N → ∃ s, t ≤ s ∧ s ≤ t + D ∧ (x s).isSome = true

theorem driven_count {Ev : Type*} {N D : ℕ} {x : Traj Ev} (h : Driven N D x) :
    ∀ m, m ≤ N → m ≤ count x (m * (D + 1)) := by
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
    intro hm
    have hm' := ih (by omega)
    have ht' : (m + 1) * (D + 1) = m * (D + 1) + D + 1 := by ring
    rw [ht']
    by_cases hc : count x (m * (D + 1)) < N
    · obtain ⟨s, hs1, hs2, hs⟩ := h _ hc
      have h1 : count x (m * (D + 1)) ≤ count x s := count_mono x hs1
      have h2 : count x (s + 1) = count x s + 1 := by simp [count, hs]
      have h3 : count x (s + 1) ≤ count x (m * (D + 1) + D + 1) := count_mono x (by omega)
      omega
    · have h3 : count x (m * (D + 1)) ≤ count x (m * (D + 1) + D + 1) := count_mono x (by omega)
      omega

/-- **What a mechanism supplies.** No prefix-determined check can demand the next event
(`spendsAll_has_mixed_fibres`). A mechanism with a bound on silence delivers it: on a budget of `N`
events the whole budget is spent by depth `N * (D + 1)`. -/
theorem driven_spends_all {Ev : Type*} {N D : ℕ} {x : Traj Ev} (h : Driven N D x)
    (hle : ∀ n, count x n ≤ N) : count x (N * (D + 1)) = N :=
  le_antisymm (hle _) (driven_count h N le_rfl)

/-- These premises are met: immediate events on a budget of `N` satisfy both bounds. -/
theorem late_zero_driven (N : ℕ) : Driven N 0 (late N 0) := by
  intro t ht
  rw [count_late] at ht
  have htN : t < N := by omega
  refine ⟨t, le_rfl, by omega, ?_⟩
  simp only [late]
  rw [if_pos (by omega)]
  rfl

theorem late_zero_silence_bound (N : ℕ) : SilenceBound 0 (late N 0) := by
  intro k hk
  by_cases h0 : k = 0
  · exact Or.inl (by omega)
  · refine Or.inr ⟨k - 1, by omega, by omega, ?_⟩
    have hkN : k < 0 + N := by
      by_contra hn
      simp only [late] at hk
      rw [if_neg (by omega)] at hk
      simp at hk
    simp only [late]
    rw [if_pos (by omega)]
    rfl

/-- **The floor is needed.** Without it, a legal trajectory out of `A` with no excluded prefix can be
active at every step, so the residue need not be silence. Here the costs are `(1/2)^k`. -/
theorem floor_is_needed :
    ∃ (x : Traj Bool) (d : ℕ → ℝ) (A : Set (Traj Bool)),
      (∀ k, 0 ≤ d k) ∧ (∀ n, ∑ k ∈ range n, d k ≤ 2) ∧ (∀ k, (x k).isSome = true) ∧
      x ∉ A ∧ InClosure A x := by
  refine ⟨fun _ => some false, fun k => (1 / 2 : ℝ) ^ k, {y | ∃ k, y k = some true},
    fun k => by positivity, fun n => ?_, fun _ => rfl, ?_, fun n => ?_⟩
  · have h : ∑ k ∈ range n, (1 / 2 : ℝ) ^ k = 2 * (1 - (1 / 2 : ℝ) ^ n) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
    rw [h]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    linarith
  · rintro ⟨k, hk⟩
    simp at hk
  · refine ⟨fun k => if k < n then some false else some true, ⟨n, by simp⟩, fun k hk => ?_⟩
    simp [hk]

end SpendsAll

/-! ## 4. Floor, horizon and budget -/

section Budget

/-- The core toy sampled at returns: remaining fuel is `C q^n`, and the sum of the debits is the
burden `C - C q^n`. Every debit is positive and the sum stays below `C`. -/
theorem toy_ledger (C q : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (C * q ^ k - C * q ^ (k + 1)) = C - C * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem toy_ledger_below_capacity (C q : ℝ) (hC : 0 < C) (hq : 0 < q) (n : ℕ) :
    C - C * q ^ n < C := by
  have : 0 < C * q ^ n := by positivity
  linarith

/-- At `q = 1/2` this is the ledger `C (1 - 2^{-n})`. -/
theorem toy_ledger_half (C : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (C * (1 / 2 : ℝ) ^ k - C * (1 / 2 : ℝ) ^ (k + 1)) = C * (1 - (1 / 2 : ℝ) ^ n) := by
  rw [toy_ledger]
  ring

/-- The toy has no floor: its debits fall below every positive bound. -/
theorem toy_has_no_floor (C q ε : ℝ) (hC : 0 < C) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 < ε) :
    ∃ n, C * q ^ n - C * q ^ (n + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / C by positivity) hq1
  refine ⟨n, ?_⟩
  have h1 : C * q ^ n < ε := by
    rw [lt_div_iff₀ hC] at hn
    linarith
  have h2 : 0 < C * q ^ (n + 1) := by positivity
  linarith

/-- Under the maintenance law, a witness floor bounds the number of maintained events. -/
theorem floor_bounds_horizon (c s R : ℝ) (σ : ℕ → ℝ) (N : ℕ) (hc : 0 < c)
    (hf : ∀ n < N, s ≤ |σ n|) (hb : ∑ n ∈ range N, c * |σ n| ≤ R) :
    (N : ℝ) * (c * s) ≤ R := by
  have h : ∑ _n ∈ range N, c * s ≤ ∑ n ∈ range N, c * |σ n| := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (hf n (Finset.mem_range.mp hn)) hc.le
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith

/-- An integral witness that stays non-zero has floor one, so at most `R / c` events are paid. -/
theorem integral_witness_bounds_horizon (c R : ℝ) (σ : ℕ → ℤ) (N : ℕ) (hc : 0 < c)
    (hne : ∀ n < N, σ n ≠ 0) (hb : ∑ n ∈ range N, c * |(σ n : ℝ)| ≤ R) :
    (N : ℝ) * c ≤ R := by
  have := floor_bounds_horizon c 1 R (fun n => (σ n : ℝ)) N hc (fun n hn => by
    have h : (1 : ℤ) ≤ |σ n| := Int.one_le_abs (hne n hn)
    have h' : ((1 : ℤ) : ℝ) ≤ ((|σ n| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h') hb
  simpa using this

/-- **Witness floor, infinite horizon, finite budget: not all three.** If every prefix of an infinite
sequence of maintained events is paid from a finite budget, the witness has no floor. -/
theorem infinite_horizon_has_no_floor (c s R : ℝ) (σ : ℕ → ℝ) (hc : 0 < c) (hs : 0 < s)
    (hb : ∀ N, ∑ n ∈ range N, c * |σ n| ≤ R) : ¬ ∀ n, s ≤ |σ n| := by
  intro hf
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (c * s))
  have h := floor_bounds_horizon c s R σ N hc (fun n _ => hf n) (hb N)
  rw [div_lt_iff₀ (by positivity)] at hN
  linarith

/-- Moreover the periods tend to zero. -/
theorem infinite_horizon_period_tends_to_zero (c R : ℝ) (σ : ℕ → ℝ) (hc : 0 < c)
    (hb : ∀ N, ∑ n ∈ range N, c * |σ n| ≤ R) :
    Filter.Tendsto (fun n => |σ n|) Filter.atTop (nhds 0) := by
  have hs : Summable (fun n => c * |σ n|) :=
    summable_of_sum_range_le (fun n => by positivity) hb
  have ht := hs.tendsto_atTop_zero
  have := ht.const_mul (1 / c)
  simp only [mul_zero] at this
  refine this.congr fun n => ?_
  field_simp

/-- An integral witness that never vanishes cannot be maintained forever on a finite budget. -/
theorem integral_witness_has_finite_life (c R : ℝ) (σ : ℕ → ℤ) (hc : 0 < c)
    (hne : ∀ n, σ n ≠ 0) : ¬ ∀ N, ∑ n ∈ range N, c * |(σ n : ℝ)| ≤ R := by
  intro hb
  refine infinite_horizon_has_no_floor c 1 R (fun n => (σ n : ℝ)) hc one_pos hb fun n => ?_
  have h : (1 : ℤ) ≤ |σ n| := Int.one_le_abs (hne n)
  have h' : ((1 : ℤ) : ℝ) ≤ ((|σ n| : ℤ) : ℝ) := by exact_mod_cast h
  simpa using h'

/-- The maintenance of a halving witness, in closed form. -/
theorem halving_sum (c p : ℝ) (N : ℕ) :
    ∑ n ∈ range N, c * |p / 2 ^ n| = 2 * c * |p| * (1 - (1 / 2 : ℝ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ N by positivity),
      pow_succ (1 / 2 : ℝ) N, one_div_pow]
    field_simp
    ring

/-- A witness halving at each step is paid forever by a finite budget. -/
theorem halving_witness_is_affordable (c p : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    ∑ n ∈ range N, c * |p / 2 ^ n| ≤ 2 * c * |p| := by
  rw [halving_sum]
  have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
  have h2 : 0 ≤ 2 * c * |p| := by positivity
  nlinarith

/-- **The two series are one.** Under the maintenance law the running cost of a halving witness is the
toy ledger at `q = 1/2`, with capacity `2 c |p|`. This compares the two series; it does not say that
witness and budget are one register. -/
theorem halving_maintenance_is_the_toy_ledger (c p : ℝ) (N : ℕ) :
    ∑ n ∈ range N, c * |p / 2 ^ n| =
      ∑ k ∈ range N, ((2 * c * |p|) * (1 / 2 : ℝ) ^ k - (2 * c * |p|) * (1 / 2 : ℝ) ^ (k + 1)) := by
  rw [halving_sum, toy_ledger_half]

/-- A constant witness is not: the budget bounds the number of events. -/
theorem constant_witness_is_not_affordable (c p R : ℝ) (hc : 0 < c) (hp : p ≠ 0) :
    ¬ ∀ N : ℕ, ∑ _n ∈ range N, c * |p| ≤ R := by
  intro hb
  exact infinite_horizon_has_no_floor c |p| R (fun _ => p) hc (abs_pos.mpr hp) hb fun _ => le_rfl

/-- **The frontier is not free.** If a live period must draw at least `c` and the debit of a period
at fuel `F` is `F (1 - q)`, then the floor holds on the whole region `F ≥ τ` exactly when
`τ (1 - q) ≥ c`. -/
theorem frontier_iff (q τ c : ℝ) (hq : q < 1) :
    (∀ F, τ ≤ F → c ≤ F * (1 - q)) ↔ c ≤ τ * (1 - q) := by
  constructor
  · intro h
    exact h τ le_rfl
  · intro h F hF
    have : τ * (1 - q) ≤ F * (1 - q) :=
      mul_le_mul_of_nonneg_right hF (by linarith)
    linarith

/-- A witness of magnitude `s` can be paid at return `n` only while `F₀ q^n (1 - q) ≥ c s`. The set of
such `n` is finite, with no declared frontier, and it shrinks as `s` grows. -/
def Payable (F0 q c s : ℝ) (n : ℕ) : Prop := c * s ≤ F0 * q ^ n * (1 - q)

theorem payable_antitone_magnitude (F0 q c s s' : ℝ) (n : ℕ) (hc : 0 ≤ c) (h : s ≤ s')
    (hp : Payable F0 q c s' n) : Payable F0 q c s n :=
  le_trans (mul_le_mul_of_nonneg_left h hc) hp

theorem payable_finite (F0 q c s : ℝ) (hF : 0 < F0) (hq0 : 0 < q) (hq1 : q < 1) (hcs : 0 < c * s) :
    ∃ N, ∀ n ≥ N, ¬ Payable F0 q c s n := by
  have hk : 0 < F0 * (1 - q) := mul_pos hF (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hcs hk) hq1
  refine ⟨N, fun n hn hp => ?_⟩
  have h1 : q ^ n ≤ q ^ N := pow_le_pow_of_le_one hq0.le hq1.le hn
  have h2 : q ^ N * (F0 * (1 - q)) < c * s := by
    rwa [lt_div_iff₀ hk] at hN
  have h3 : q ^ n * (F0 * (1 - q)) ≤ q ^ N * (F0 * (1 - q)) :=
    mul_le_mul_of_nonneg_right h1 hk.le
  simp only [Payable] at hp
  nlinarith

end Budget

/-! ## 5. Capability and continuation -/

section Capability

/-- The phases of the three-state device of the identification note. -/
inductive Phase
  | i | j | c
  deriving DecidableEq

/-- Inputs at a step: silence, an external request, an external block. -/
inductive Input
  | silent | request | inhibit
  deriving DecidableEq

/-- The transition law with mode `b`, the internal edge. -/
def step (b : Bool) : Phase → Input → Phase
  | .i, _ => .j
  | .j, _ => .c
  | .c, .request => .i
  | .c, .silent => if b then .i else .c
  | .c, .inhibit => .c

/-- The run under an input stream. -/
def run (b : Bool) (e : ℕ → Input) : ℕ → Phase
  | 0 => .i
  | n + 1 => step b (run b e n) (e n)

/-- Capability: the restart edge exists with the environment silent. Fixed by the law, before any run. -/
def Capable (b : Bool) : Prop := step b .c .silent = .i

/-- Realised continuation: the run keeps coming back to `i`. -/
def Continues (b : Bool) (e : ℕ → Input) : Prop := ∀ t, ∃ s ≥ t, run b e s = .i

theorem capable_iff (b : Bool) : Capable b ↔ b = true := by
  cases b <;> simp [Capable, step]

/-- Under a stream that restarts at `c`, the run is the period-three cycle. -/
theorem run_cycle (b : Bool) (e : ℕ → Input)
    (he : ∀ n, n % 3 = 2 → step b .c (e n) = .i) (m : ℕ) :
    run b e (3 * m) = .i ∧ run b e (3 * m + 1) = .j ∧ run b e (3 * m + 2) = .c := by
  induction m with
  | zero => simp [run, step]
  | succ m ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 : 3 * (m + 1) = (3 * m + 2) + 1 := by ring
    have hc := he (3 * m + 2) (by omega)
    have r0 : run b e (3 * (m + 1)) = .i := by
      rw [e0]
      show step b (run b e (3 * m + 2)) (e (3 * m + 2)) = .i
      rw [h2]
      exact hc
    have r1 : run b e (3 * (m + 1) + 1) = .j := by
      show step b (run b e (3 * (m + 1))) (e (3 * (m + 1))) = .j
      rw [r0]
      rfl
    have r2 : run b e (3 * (m + 1) + 2) = .c := by
      show step b (run b e (3 * (m + 1) + 1)) (e (3 * (m + 1) + 1)) = .c
      rw [r1]
      rfl
    exact ⟨r0, r1, r2⟩

theorem continues_of_cycle (b : Bool) (e : ℕ → Input)
    (he : ∀ n, n % 3 = 2 → step b .c (e n) = .i) : Continues b e := fun t =>
  ⟨3 * t, by omega, (run_cycle b e he t).1⟩

/-- If the stream never restarts at `c`, the run stays at `c` from step two. -/
theorem stuck_of_no_restart (b : Bool) (e : ℕ → Input)
    (he : ∀ n, step b .c (e n) = .c) : ∀ n, run b e (n + 2) = .c := by
  intro n
  induction n with
  | zero => simp [run, step]
  | succ n ih =>
    show step b (run b e (n + 2)) (e (n + 2)) = .c
    rw [ih]
    exact he _

theorem not_continues_of_stuck (b : Bool) (e : ℕ → Input)
    (he : ∀ n, step b .c (e n) = .c) : ¬ Continues b e := by
  intro h
  obtain ⟨s, hs, hi⟩ := h 2
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  rw [stuck_of_no_restart b e he n] at hi
  cases hi

/-- **Capability and continuation are independent.** All four combinations occur on one law. -/
theorem four_cells :
    (Capable true ∧ Continues true (fun _ => .silent)) ∧
    (¬ Capable false ∧ Continues false (fun _ => .request)) ∧
    (Capable true ∧ ¬ Continues true (fun _ => .inhibit)) ∧
    (¬ Capable false ∧ ¬ Continues false (fun _ => .silent)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp [Capable, step]
  · exact continues_of_cycle _ _ fun _ _ => by simp [step]
  · simp [Capable, step]
  · exact continues_of_cycle _ _ fun _ _ => by simp [step]
  · simp [Capable, step]
  · exact not_continues_of_stuck _ _ fun _ => by simp [step]
  · simp [Capable, step]
  · exact not_continues_of_stuck _ _ fun _ => by simp [step]

/-- The two modes differ only at the pair (`c`, silent). -/
theorem step_agree (p : Phase) (e : Input) (h : ¬ (p = .c ∧ e = .silent)) :
    step true p e = step false p e := by
  cases p <;> cases e <;> simp_all [step]

/-- **Observation under any stream that is not silent at completion is blind to the mode.** -/
theorem runs_agree (e : ℕ → Input) (he : ∀ n, run false e n = .c → e n ≠ .silent) :
    ∀ n, run true e n = run false e n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    exact step_agree _ _ fun ⟨h1, h2⟩ => he n h1 h2

/-- Silence at completion reveals the mode. -/
theorem silence_reveals :
    run true (fun _ => .silent) 3 = .i ∧ run false (fun _ => .silent) 3 = .c := by
  simp [run, step]

/-- **In this model capability is a bound on silence under a silent environment.** -/
theorem capable_iff_bounded_silence (b : Bool) :
    Capable b ↔ ∃ D, ∀ t, ∃ s, t ≤ s ∧ s ≤ t + D ∧ run b (fun _ => .silent) s = .i := by
  constructor
  · intro hb
    obtain rfl := (capable_iff b).mp hb
    refine ⟨2, fun t => ?_⟩
    have he : ∀ n, n % 3 = 2 → step true .c ((fun _ => Input.silent) n) = .i := fun _ _ => by
      simp [step]
    have key : ∀ m, run true (fun _ => .silent) (3 * m) = .i ∧
        run true (fun _ => .silent) (3 * m + 1) = .j ∧
        run true (fun _ => .silent) (3 * m + 2) = .c := run_cycle true _ he
    obtain ⟨m, hm⟩ : ∃ m, t ≤ 3 * m ∧ 3 * m ≤ t + 2 := ⟨(t + 2) / 3, by omega, by omega⟩
    exact ⟨3 * m, hm.1, hm.2, (key m).1⟩
  · rintro ⟨D, hD⟩
    cases b
    · exfalso
      obtain ⟨s, hs, _, hi⟩ := hD 2
      obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
      rw [stuck_of_no_restart false _ (fun _ => by simp [step]) n] at hi
      cases hi
    · simp [Capable, step]

end Capability

/-! ## 6. What a state must retain -/

section Canonical

/-- **A key is sufficient for continuation exactly when residuals factor through it.** This is the
fibre criterion with the residual language as its target. -/
theorem key_sufficient_iff {Pre Key Suf : Type*} (K : Pre → Key) (L : Pre → Set Suf) :
    (∃ B : Key → Set Suf, ∀ ρ, L ρ = B (K ρ)) ↔ ∀ ρ σ, K ρ = K σ → L ρ = L σ := by
  classical
  constructor
  · rintro ⟨B, hB⟩ ρ σ h
    rw [hB ρ, hB σ, h]
  · intro h
    refine ⟨fun k => if hk : ∃ ρ, K ρ = k then L hk.choose else ∅, fun ρ => ?_⟩
    have hk : ∃ σ, K σ = K ρ := ⟨ρ, rfl⟩
    simp only [dif_pos hk]
    exact h _ _ hk.choose_spec.symm

/-- The tails still affordable at load `φ`. -/
def Reservoir {Ω : Type*} (c : Ω → ℝ) (C φ : ℝ) : Set Ω := {η | φ + c η ≤ C}

/-- **A ledger needs only the resolution of the tail costs.** Two loads have one reservoir exactly when
no tail cost lies between them. -/
theorem reservoir_eq_iff {Ω : Type*} (c : Ω → ℝ) (C φ φ' : ℝ) (h : φ ≤ φ') :
    Reservoir c C φ = Reservoir c C φ' ↔ ¬ ∃ η, C - φ' < c η ∧ c η ≤ C - φ := by
  constructor
  · rintro he ⟨η, h1, h2⟩
    have hm : η ∈ Reservoir c C φ := by simp only [Reservoir, Set.mem_setOf_eq]; linarith
    rw [he] at hm
    simp only [Reservoir, Set.mem_setOf_eq] at hm
    linarith
  · intro hn
    ext η
    simp only [Reservoir, Set.mem_setOf_eq]
    constructor
    · intro h1
      by_contra h2
      exact hn ⟨η, by linarith, by linarith⟩
    · intro h1
      linarith

/-- One visible configuration, two loads, two continuation sets: the load is a coordinate that a
sufficient state must keep. -/
theorem load_is_a_coordinate :
    Reservoir (fun b : Bool => if b then (2 : ℝ) else 0) 2 0 ≠
    Reservoir (fun b : Bool => if b then (2 : ℝ) else 0) 2 1 := by
  intro h
  have hm : true ∈ Reservoir (fun b : Bool => if b then (2 : ℝ) else 0) 2 0 := by
    simp [Reservoir]
  rw [h] at hm
  simp only [Reservoir, Set.mem_setOf_eq, if_true] at hm
  norm_num at hm

/-- The predicate of Section 7.3 of the work on boolean words. -/
def PS (b : ℕ → Bool) : Prop :=
  b 0 = true ∧ (∀ j, ¬ (b j = true ∧ b (j + 1) = true)) ∧ ∀ t, ∃ s ≥ t, b s = true

/-- A prefix of length `n` followed by `y`. -/
def prep (n : ℕ) (w y : ℕ → Bool) : ℕ → Bool := fun k => if k < n then w k else y (k - n)

/-- A legal prefix of length `n ≥ 1`. -/
def LegalPrefix (n : ℕ) (w : ℕ → Bool) : Prop :=
  1 ≤ n ∧ w 0 = true ∧ ∀ j, j + 1 < n → ¬ (w j = true ∧ w (j + 1) = true)

theorem PS_prep_iff (n : ℕ) (w y : ℕ → Bool) (hw : LegalPrefix n w) :
    PS (prep n w y) ↔ (¬ (w (n - 1) = true ∧ y 0 = true)) ∧
      (∀ j, ¬ (y j = true ∧ y (j + 1) = true)) ∧ ∀ t, ∃ s ≥ t, y s = true := by
  obtain ⟨hn, h0, hl⟩ := hw
  have val_lt : ∀ k, k < n → prep n w y k = w k := fun k hk => by simp [prep, hk]
  have val_ge : ∀ k, prep n w y (n + k) = y k := fun k => by simp [prep]
  constructor
  · rintro ⟨_, hadj, hinf⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2⟩
      apply hadj (n - 1)
      have e : n - 1 + 1 = n + 0 := by omega
      rw [e, val_ge, val_lt (n - 1) (by omega)]
      exact ⟨h1, h2⟩
    · rintro j ⟨h1, h2⟩
      apply hadj (n + j)
      rw [val_ge, show n + j + 1 = n + (j + 1) by ring, val_ge]
      exact ⟨h1, h2⟩
    · intro t
      obtain ⟨s, hs, hv⟩ := hinf (n + t)
      obtain ⟨k, rfl⟩ : ∃ k, s = n + k := ⟨s - n, by omega⟩
      rw [val_ge] at hv
      exact ⟨k, by omega, hv⟩
  · rintro ⟨hseam, hadj, hinf⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [val_lt 0 (by omega)]
      exact h0
    · rintro j ⟨h1, h2⟩
      by_cases hj : j + 1 < n
      · rw [val_lt j (by omega)] at h1
        rw [val_lt (j + 1) hj] at h2
        exact hl j hj ⟨h1, h2⟩
      · by_cases hj' : j + 1 = n
        · rw [val_lt j (by omega)] at h1
          have e : j + 1 = n + 0 := by omega
          rw [e, val_ge] at h2
          have e' : j = n - 1 := by omega
          rw [e'] at h1
          exact hseam ⟨h1, h2⟩
        · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
          rw [val_ge] at h1
          rw [show n + k + 1 = n + (k + 1) by ring, val_ge] at h2
          exact hadj k ⟨h1, h2⟩
    · intro t
      obtain ⟨s, hs, hv⟩ := hinf t
      exact ⟨n + s, by omega, by rw [val_ge]; exact hv⟩

/-- **Finite state is not finite depth.** The residual of a legal prefix depends only on its last bit,
so the predicate has a finite sufficient state, while no fixed prefix decides it (M5). -/
theorem residual_depends_on_last_bit (n m : ℕ) (w w' y : ℕ → Bool) (hw : LegalPrefix n w)
    (hw' : LegalPrefix m w') (hlast : w (n - 1) = w' (m - 1)) :
    PS (prep n w y) ↔ PS (prep m w' y) := by
  rw [PS_prep_iff n w y hw, PS_prep_iff m w' y hw', hlast]

end Canonical

/-! ## 7. Exact witnesses and unexplained logs on the doubling tower -/

section Doubling

/-- A seam log is explained by a global family when it is that family's defect word. -/
def Explained (y : ℕ → ℤ) : Prop := ∃ a : ℕ → ℤ, ∀ n, a n - 2 * a (n + 1) = y n

/-- **The defect word of a family is explained by that family, on any horizon.** The class of a
family's own word is zero: only a log not derived from a global family can carry a class. -/
theorem defect_word_is_explained (a : ℕ → ℤ) : Explained (fun n => a n - 2 * a (n + 1)) :=
  ⟨a, fun _ => rfl⟩

/-- Every finite window of any log is explained. -/
theorem every_window_is_explained (y : ℕ → ℤ) (N : ℕ) :
    ∃ a : ℕ → ℤ, ∀ n < N, a n - 2 * a (n + 1) = y n := by
  induction N generalizing y with
  | zero => exact ⟨fun _ => 0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨a, ha⟩ := ih (fun n => y (n + 1))
    refine ⟨fun n => match n with
      | 0 => y 0 + 2 * a 0
      | k + 1 => a k, fun n hn => ?_⟩
    cases n with
    | zero => simp
    | succ k => exact ha k (by omega)

/-- If every power of four divides `v`, then `v = 0`. -/
theorem eq_zero_of_all_pow_four_dvd (v : ℤ) (h : ∀ m : ℕ, (4 : ℤ) ^ m ∣ v) : v = 0 := by
  by_contra hv
  have hlt : v.natAbs < 4 ^ v.natAbs := Nat.lt_pow_self (by norm_num)
  have hd : ((4 : ℤ) ^ v.natAbs) ∣ v := h _
  have h1 : ((4 : ℤ) ^ v.natAbs).natAbs ∣ v.natAbs := Int.natAbs_dvd_natAbs.mpr hd
  have h2 : ((4 : ℤ) ^ v.natAbs).natAbs = 4 ^ v.natAbs := by simp [Int.natAbs_pow]
  rw [h2] at h1
  have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hv) h1
  omega

/-- The log `1, 0, 1, 0, ...`. -/
def altLog : ℕ → ℤ := fun n => if n % 2 = 0 then 1 else 0

/-- **Finite windows do not glue.** Each window of this log is explained by some integer family, and no
integer family explains the whole log. -/
theorem altLog_not_explained : ¬ Explained altLog := by
  rintro ⟨a, ha⟩
  have key : ∀ m : ℕ, 3 * a 0 + 1 = 4 ^ m * (3 * a (2 * m) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := ha (2 * m)
      have h2 := ha (2 * m + 1)
      have e1 : altLog (2 * m) = 1 := by simp [altLog]
      have e2 : altLog (2 * m + 1) = 0 := by
        simp only [altLog]
        rw [if_neg (by omega)]
      rw [e1] at h1
      rw [e2] at h2
      have e3 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [e3, ih, pow_succ]
      have h3 : a (2 * m) = 1 + 4 * a (2 * m + 1 + 1) := by
        have : a (2 * m + 1) = 2 * a (2 * m + 1 + 1) := by linarith
        rw [show 2 * m + 1 = 2 * m + 1 from rfl] at h1
        linarith
      rw [h3]
      ring
  have hz : 3 * a 0 + 1 = 0 :=
    eq_zero_of_all_pow_four_dvd _ fun m => ⟨_, key m⟩
  omega

/-- **An exact integral family on the whole tower is zero.** The group of exact witnesses is trivial
over the integers. -/
theorem exact_integral_family_is_zero (a : ℕ → ℤ) (h : ∀ n, a n = 2 * a (n + 1)) (n : ℕ) :
    a n = 0 := by
  have key : ∀ m : ℕ, a n = 2 ^ m * a (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, h (n + m), pow_succ, show n + (m + 1) = n + m + 1 by ring]
      ring
  by_contra hne
  have hlt : (a n).natAbs < 2 ^ (a n).natAbs := Nat.lt_pow_self (by norm_num)
  have hd : ((2 : ℤ) ^ (a n).natAbs) ∣ a n := ⟨_, key _⟩
  have h1 : ((2 : ℤ) ^ (a n).natAbs).natAbs ∣ (a n).natAbs := Int.natAbs_dvd_natAbs.mpr hd
  have h2 : ((2 : ℤ) ^ (a n).natAbs).natAbs = 2 ^ (a n).natAbs := by simp [Int.natAbs_pow]
  rw [h2] at h1
  have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h1
  omega

/-- Over the reals the exact family exists and has no floor. -/
theorem exact_real_family (p : ℝ) (n : ℕ) : p / 2 ^ n = 2 * (p / 2 ^ (n + 1)) := by
  rw [pow_succ]
  field_simp

end Doubling

end MirrorsComposition
