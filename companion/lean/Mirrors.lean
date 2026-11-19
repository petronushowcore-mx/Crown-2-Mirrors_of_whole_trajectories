import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mirrors of Whole Trajectories: formal companion

What is formalised: M1 and its corollaries, M2 with its weaker premise and the counterexample of
Section 4.1, the shared-control obstruction of Section 5.1 on the closed form of its solutions, M3
with the identification of the prefix closure and the cylinder closure, M5 with the extension rule,
M6, the toy of Section 9.1, the XOR example of Section 9.2 at the level of fibres, the fibre form of
Section 9.3, the matrices of Section 11.3, the scale law with the exact condition for a lower bound,
and the statements of Section 11.4 on finite chains, the lattice and the doubling tower.

Not in this file: M4 and the de Rham calculations of Section 7 (only their rational inequalities are
here; `MirrorNativeClassInverseLimit-r3p.lean` and `MirrorNumericalInterfaces-p.lean` carry M4 on the
declared native quotient), the mutual informations of Section 9.2 (only the fibres), the vanishing of `lim^1` on general
towers (only the doubling tower here), its packaging as `Z_2 / Z` (its content, congruence to one
integer modulo every power of two, is here), and the Milnor sequence. These rest on the text and on
the cited sources. A proof here is about these statements:
that they say what the text says is for the reader to check.
-/

namespace Mirrors

/-! ## Section 3: the property contract -/

section Property

variable {Γ Y : Type*}

/-- M1: a property factors through the mirror on its image exactly when it is constant on fibres. -/
theorem M1_fibre_sufficiency (q : Γ → Y) (P : Γ → Bool) :
    (∃ Pbar : Set.range q → Bool, ∀ γ, P γ = Pbar ⟨q γ, γ, rfl⟩) ↔
      ∀ γ γ', q γ = q γ' → P γ = P γ' := by
  constructor
  · rintro ⟨Pbar, h⟩ γ γ' e
    rw [h γ, h γ']
    congr 1
    exact Subtype.ext e
  · intro h
    refine ⟨fun y => P (Classical.choose (show ∃ g, q g = y.1 from y.2)), fun γ => ?_⟩
    have hs := Classical.choose_spec (show ∃ g, q g = q γ from ⟨γ, rfl⟩)
    exact h _ _ hs.symm

/-- M1: the factor is unique on the image. -/
theorem M1_unique (q : Γ → Y) (P : Γ → Bool) (A B : Set.range q → Bool)
    (hA : ∀ γ, P γ = A ⟨q γ, γ, rfl⟩) (hB : ∀ γ, P γ = B ⟨q γ, γ, rfl⟩) : A = B := by
  funext y
  obtain ⟨y, γ, rfl⟩ := y
  rw [← hA γ, ← hB γ]

/-- A decoder of a datum makes every property of that datum constant on the mirror's fibres. -/
theorem decoder_gives_datum_properties {Z : Type*} (q : Γ → Y) (w : Γ → Z) (d : Y → Z)
    (hd : ∀ γ, d (q γ) = w γ) (Phat : Z → Bool) (γ γ' : Γ) (e : q γ = q γ') :
    Phat (w γ) = Phat (w γ') := by
  rw [← hd γ, ← hd γ', e]

/-- Exact determination of every binary property forces the mirror to be injective. -/
theorem all_properties_force_injective (q : Γ → Y)
    (h : ∀ P : Γ → Bool, ∀ γ γ', q γ = q γ' → P γ = P γ') : Function.Injective q := by
  classical
  intro a b e
  have h2 : decide (a = a) = decide (b = a) := h (fun g => decide (g = a)) a b e
  have h3 : b = a := by simpa using h2.symm
  exact h3.symm

/-- Section 3.2: recovery of the whole datum does not determine a property of the enlarged object. -/
theorem complete_datum_misses_enlarged_object {Z : Type*} (z : Z) :
    ¬ ∀ γ γ' : Z × Bool, Prod.fst γ = Prod.fst γ' → Prod.snd γ = Prod.snd γ' := by
  intro h
  have := h (z, true) (z, false) rfl
  simp at this

/-- Section 5.2: a conjunction of properties constant on the fibres of `q` is constant on them. -/
theorem conjunction_constant_on_fibres {ι : Type*} (q : Γ → Y) (P : ι → Γ → Prop)
    (h : ∀ i γ γ', q γ = q γ' → (P i γ ↔ P i γ')) (γ γ' : Γ) (e : q γ = q γ') :
    (∀ i, P i γ) ↔ ∀ i, P i γ' :=
  forall_congr' fun i => h i γ γ' e

end Property

/-! ## Section 4: the continuation contract -/

section Continuation

variable {ΓX ΓY SX SY : Type*} (eX : ΓX → SX) (eY : ΓY → SY) (AX : Set ΓX) (AY : Set ΓY)
  (Q : ΓX → ΓY) (q0 : SX → SY)

/-- M2, the forward inclusion. -/
theorem M2_forward (hroot : ∀ γ, eY (Q γ) = q0 (eX γ)) (hadm : ∀ γ ∈ AX, Q γ ∈ AY) :
    eX '' AX ⊆ q0 ⁻¹' (eY '' AY) := by
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨Q γ, hadm γ hγ, hroot γ⟩

/-- M2, equality under the weaker premise: one admitted source witness at every viable image. -/
theorem M2_equality_of_root_witness (hroot : ∀ γ, eY (Q γ) = q0 (eX γ))
    (hadm : ∀ γ ∈ AX, Q γ ∈ AY) (h : ∀ x, q0 x ∈ eY '' AY → ∃ γ ∈ AX, eX γ = x) :
    eX '' AX = q0 ⁻¹' (eY '' AY) := by
  apply Set.Subset.antisymm (M2_forward eX eY AX AY Q q0 hroot hadm)
  intro x hx
  obtain ⟨γ, hγ, e⟩ := h x hx
  exact ⟨γ, hγ, e⟩

/-- M2, equality under rooted lifting of every admitted target history. -/
theorem M2_equality (hroot : ∀ γ, eY (Q γ) = q0 (eX γ)) (hadm : ∀ γ ∈ AX, Q γ ∈ AY)
    (hlift : ∀ x η, η ∈ AY → eY η = q0 x → ∃ γ ∈ AX, eX γ = x ∧ Q γ = η) :
    eX '' AX = q0 ⁻¹' (eY '' AY) := by
  refine M2_equality_of_root_witness eX eY AX AY Q q0 hroot hadm fun x hx => ?_
  obtain ⟨η, hη, e⟩ := hx
  obtain ⟨γ, hγ, hr, _⟩ := hlift x η hη e
  exact ⟨γ, hγ, hr⟩

/-- Section 4.1: a surjective, admission-preserving, root-compatible path map misses a root. -/
theorem global_coverage_misses_root :
    ∃ (ΓX ΓY SX SY : Type) (eX : ΓX → SX) (eY : ΓY → SY) (AX : Set ΓX) (AY : Set ΓY)
      (Q : ΓX → ΓY) (q0 : SX → SY),
      Function.Surjective Q ∧ (∀ γ, eY (Q γ) = q0 (eX γ)) ∧ (∀ γ ∈ AX, Q γ ∈ AY) ∧
        eX '' AX ≠ q0 ⁻¹' (eY '' AY) := by
  refine ⟨Unit, Unit, Bool, Unit, fun _ => true, fun _ => (), Set.univ, Set.univ, id, fun _ => (),
    Function.surjective_id, fun _ => rfl, fun _ _ => trivial, ?_⟩
  intro h
  have hb : (false : Bool) ∈ (fun _ : Unit => (true : Bool)) '' (Set.univ : Set Unit) := by
    rw [h]
    exact ⟨(), trivial, rfl⟩
  obtain ⟨_, _, e⟩ := hb
  simp at e

/-- M6: a data equation preserves the joint verdict, and rooted lifting adds the viable sets. -/
theorem M6_joint_contract {Z ι : Type*} (wX : ΓX → Z) (wY : ΓY → Z) (Phat : ι → Z → Prop)
    (hw : ∀ γ, wY (Q γ) = wX γ) (hroot : ∀ γ, eY (Q γ) = q0 (eX γ)) :
    (∀ γ, (∀ i, Phat i (wX γ)) ↔ ∀ i, Phat i (wY (Q γ))) ∧
      ((∀ x η, (∀ i, Phat i (wY η)) → eY η = q0 x →
          ∃ γ, (∀ i, Phat i (wX γ)) ∧ eX γ = x ∧ Q γ = η) →
        eX '' {γ | ∀ i, Phat i (wX γ)} = q0 ⁻¹' (eY '' {η | ∀ i, Phat i (wY η)})) := by
  refine ⟨fun γ => by rw [hw γ], fun hlift => ?_⟩
  apply M2_equality eX eY _ _ Q q0 hroot
  · intro γ hγ i
    show Phat i (wY (Q γ))
    rw [hw γ]
    exact hγ i
  · intro x η hη e
    obtain ⟨γ, hγ, hr, hq⟩ := hlift x η hη e
    exact ⟨γ, hγ, hr, hq⟩

end Continuation

/-! ## Section 5.1: the shared-control obstruction, on the closed form of the solutions -/

section SharedControl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- With `x₁ t = t + A t` and `x₂ t = t - A t`, no common control keeps both at or below zero. -/
theorem shared_control_no_common_witness (A : K → K) (t : K) (ht : 0 < t) :
    ¬ (t + A t ≤ 0 ∧ t - A t ≤ 0) := by
  rintro ⟨h1, h2⟩
  linarith

/-- Separately, `u = -1` holds the first obligation and `u = 1` the second. -/
theorem shared_control_individual_witnesses (t : K) : t + (-t) ≤ 0 ∧ t - t ≤ 0 := by
  constructor <;> simp

end SharedControl

/-! ## Section 6: finite exclusion -/

section FiniteExclusion

variable {S : Type*}

/-- The trajectories all of whose finite prefixes admit a continuation in `A`. -/
def prefixClosure (A : Set (ℕ → S)) : Set (ℕ → S) :=
  {γ | ∀ n, ∃ η ∈ A, ∀ i, i < n → η i = γ i}

/-- M3, first part: the prefix closure is the closure in the cylinder topology. -/
theorem prefixClosure_eq_closure [TopologicalSpace S] [DiscreteTopology S] (A : Set (ℕ → S)) :
    prefixClosure A = closure A := by
  ext γ
  rw [(PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => S)).mem_closure_iff]
  constructor
  · rintro h o ⟨z, m, rfl⟩ hγ
    obtain ⟨η, hη, e⟩ := h m
    refine ⟨η, ?_, hη⟩
    rw [PiNat.mem_cylinder_iff] at hγ ⊢
    intro i hi
    rw [e i hi]
    exact hγ i hi
  · intro h n
    obtain ⟨η, hη, hA⟩ := h (PiNat.cylinder γ n) ⟨γ, n, rfl⟩ (PiNat.self_mem_cylinder γ n)
    exact ⟨η, hA, PiNat.mem_cylinder_iff.1 hη⟩

/-- M3, second part: every inadmissible trajectory of `Γ` has an excluded finite prefix exactly when
`A` contains its prefix closure within `Γ`. -/
theorem M3_excluded_prefix_iff (Γ A : Set (ℕ → S)) :
    (∀ γ ∈ Γ, γ ∉ A → ∃ n, ∀ η ∈ A, ∃ i, i < n ∧ η i ≠ γ i) ↔ Γ ∩ prefixClosure A ⊆ A := by
  constructor
  · rintro h γ ⟨hΓ, hc⟩
    by_contra hn
    obtain ⟨n, hn'⟩ := h γ hΓ hn
    obtain ⟨η, hη, e⟩ := hc n
    obtain ⟨i, hi, ne⟩ := hn' η hη
    exact ne (e i hi)
  · intro h γ hΓ hn
    by_contra hx
    apply hn
    apply h
    refine ⟨hΓ, fun n => ?_⟩
    by_contra hne
    apply hx
    refine ⟨n, fun η hη => ?_⟩
    by_contra hall
    apply hne
    refine ⟨η, hη, fun i hi => ?_⟩
    by_contra hi2
    exact hall ⟨i, hi, hi2⟩

end FiniteExclusion

/-! ## Section 7.3: the predicate -/

section Words

/-- The local conditions: first digit one, no two adjacent ones. -/
def Legal (b : ℕ → ℤ) : Prop := b 0 = 1 ∧ ∀ j, b j * b (j + 1) = 0

/-- Infinitely many ones. -/
def InfOnes (b : ℕ → ℤ) : Prop := ∀ N, ∃ j, N ≤ j ∧ b j = 1

/-- The predicate `P_*` of Section 7.3. -/
def Pstar (b : ℕ → ℤ) : Prop := Legal b ∧ InfOnes b

/-- Binary words. -/
def Bin (b : ℕ → ℤ) : Prop := ∀ j, b j = 0 ∨ b j = 1

/-- The word `1 0 0 0 ...`. -/
def oneZeros : ℕ → ℤ := fun j => if j = 0 then 1 else 0

/-- `1 0^n` followed by a separated alternating tail. -/
def altTail (n : ℕ) : ℕ → ℤ := fun j =>
  if j = 0 then 1 else if j ≤ n then 0 else if (j - n) % 2 = 0 then 1 else 0

theorem not_Pstar_oneZeros : ¬ Pstar oneZeros := by
  rintro ⟨_, h⟩
  obtain ⟨j, hj, e⟩ := h 1
  have hne : j ≠ 0 := by omega
  simp [oneZeros, hne] at e

theorem Pstar_altTail (n : ℕ) : Pstar (altTail n) := by
  refine ⟨⟨by simp [altTail], fun j => ?_⟩, fun N => ⟨n + 2 + 2 * N, by omega, ?_⟩⟩
  · unfold altTail
    split_ifs <;> first | contradiction | omega | simp
  · unfold altTail
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- M5: for every `n` the mirror of the first `n` digits has a mixed fibre. -/
theorem M5_mixed_fibre (n : ℕ) :
    (∀ i, i < n → altTail n i = oneZeros i) ∧ Pstar (altTail n) ∧ ¬ Pstar oneZeros := by
  refine ⟨fun i hi => ?_, Pstar_altTail n, not_Pstar_oneZeros⟩
  unfold altTail oneZeros
  by_cases h0 : i = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0, if_pos (by omega)]

/-- Append a separating zero and an alternating tail after a prefix of length `n`. -/
def extendAlt (c : ℕ → ℤ) (n : ℕ) : ℕ → ℤ := fun j =>
  if j < n then c j else if (j - n) % 2 = 0 then 0 else 1

/-- M5: every locally legal prefix has an admitted infinite extension. -/
theorem legal_prefix_has_admitted_extension (c : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) (h0 : c 0 = 1)
    (hc : ∀ j, j + 1 < n → c j * c (j + 1) = 0) :
    Pstar (extendAlt c n) ∧ ∀ i, i < n → extendAlt c n i = c i := by
  refine ⟨⟨⟨?_, fun j => ?_⟩, fun N => ⟨n + 1 + 2 * N, by omega, ?_⟩⟩, fun i hi => ?_⟩
  · unfold extendAlt
    rw [if_pos (by omega)]
    exact h0
  · unfold extendAlt
    by_cases h1 : j + 1 < n
    · rw [if_pos (by omega), if_pos h1]
      exact hc j h1
    · by_cases h2 : j < n
      · rw [if_pos h2, if_neg h1, if_pos (by omega), mul_zero]
      · rw [if_neg h2, if_neg h1]
        split_ifs <;> omega
  · unfold extendAlt
    rw [if_neg (by omega), if_neg (by omega)]
  · unfold extendAlt
    rw [if_pos hi]

/-- M3 on the example: `1 0 0 0 ...` is inadmissible, lies in the closure, and has no excluded prefix. -/
theorem oneZeros_in_prefix_closure : oneZeros ∈ prefixClosure {b | Pstar b} := fun n =>
  ⟨altTail n, Pstar_altTail n, (M5_mixed_fibre n).1⟩

end Words

/-! ## Section 11.4: what re-declaration can remove -/

section Tower

/-- A tower of groups: `f j` carries level `j + 1` to level `j`. On a finite stretch every word on the
steps is a coboundary. This is the removal of defects on a finite chain, for any coefficients. -/
theorem finite_word_is_coboundary {A : ℕ → Type*} [∀ j, AddCommGroup (A j)]
    (f : ∀ j, A (j + 1) →+ A j) (y : ∀ j, A j) (n : ℕ) :
    ∀ s, ∃ x : ∀ j, A j, ∀ j, s ≤ j → j < s + n → x j - f j (x (j + 1)) = y j := by
  induction n with
  | zero =>
    intro s
    exact ⟨fun _ => 0, fun j _ h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro s
    obtain ⟨x, hx⟩ := ih (s + 1)
    refine ⟨Function.update x s (y s + f s (x (s + 1))), fun j h1 h2 => ?_⟩
    by_cases hj : j = s
    · subst hj
      rw [Function.update_self, Function.update_of_ne (by omega : j + 1 ≠ j)]
      exact add_sub_cancel_right _ _
    · rw [Function.update_of_ne hj, Function.update_of_ne (by omega : j + 1 ≠ s)]
      exact hx j (by omega) (by omega)

/-- Re-choosing a family removes its defects on a finite chain: the new family obeys the exact law. -/
theorem rechosen_family_obeys_exact_law {A : ℕ → Type*} [∀ j, AddCommGroup (A j)]
    (f : ∀ j, A (j + 1) →+ A j) (a : ∀ j, A j) (n : ℕ) :
    ∃ x : ∀ j, A j, ∀ j, j < n → a j - x j = f j (a (j + 1) - x (j + 1)) := by
  obtain ⟨x, hx⟩ := finite_word_is_coboundary f (fun j => a j - f j (a (j + 1))) n 0
  refine ⟨x, fun j hj => ?_⟩
  have e : x j - f j (x (j + 1)) = a j - f j (a (j + 1)) := hx j (Nat.zero_le j) (by omega)
  rw [map_sub]
  have h2 : x j = f j (x (j + 1)) + (a j - f j (a (j + 1))) := by
    rw [← e]
    abel
  rw [h2]
  abel

variable {K : Type*} [Field K] {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module K (M j)]
  (T : ∀ j, M j →ₗ[K] M (j + 1))

/-- The realised class along the chain. -/
def transport (c0 : M 0) : ∀ j, M j
  | 0 => c0
  | j + 1 => T j (transport c0 j)

/-- Under the exact law the pairing is constant along the chain. -/
theorem pairing_constant (a : ∀ j, Module.Dual K (M j)) (c0 : M 0) (n : ℕ)
    (h : ∀ j, j < n → a j = LinearMap.comp (a (j + 1)) (T j)) :
    ∀ j, j ≤ n → a j (transport T c0 j) = a 0 c0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have e := ih (by omega)
    rw [← e, h j (by omega)]
    rfl

/-- Pulling back from the end gives a family obeying the exact law with any final covector. -/
theorem exists_family_pulled_back : ∀ (n : ℕ) (e : Module.Dual K (M n)),
    ∃ a : ∀ j, Module.Dual K (M j), a n = e ∧ ∀ j, j < n → a j = LinearMap.comp (a (j + 1)) (T j) := by
  intro n
  induction n with
  | zero =>
    intro e
    exact ⟨Function.update (fun _ => 0) 0 e, Function.update_self _ _ _,
      fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    intro e
    obtain ⟨a, ha, hc⟩ := ih (LinearMap.comp e (T n))
    refine ⟨Function.update a (n + 1) e, Function.update_self _ _ _, fun j hj => ?_⟩
    rw [Function.update_of_ne (by omega : j ≠ n + 1)]
    by_cases hjn : j = n
    · subst hjn
      rw [Function.update_self, ha]
    · rw [Function.update_of_ne (by omega : j + 1 ≠ n + 1)]
      exact hc j (by omega)

/-- Statement A: a family obeying the exact law with a non-zero pairing, chosen after the execution,
exists exactly when the final class is non-zero. -/
theorem posthoc_witness_iff (c0 : M 0) (n : ℕ) :
    (∃ a : ∀ j, Module.Dual K (M j),
        (∀ j, j < n → a j = LinearMap.comp (a (j + 1)) (T j)) ∧ a 0 c0 ≠ 0) ↔
      transport T c0 n ≠ 0 := by
  constructor
  · rintro ⟨a, h, hne⟩ hz
    have e := pairing_constant T a c0 n h n le_rfl
    rw [hz, map_zero] at e
    exact hne e.symm
  · intro hne
    obtain ⟨e, he⟩ : ∃ e : Module.Dual K (M n), e (transport T c0 n) ≠ 0 := by
      by_contra hno
      apply hne
      refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun f => ?_
      by_contra hf
      exact hno ⟨f, hf⟩
    obtain ⟨a, ha, hc⟩ := exists_family_pulled_back T n e
    refine ⟨a, hc, ?_⟩
    have e2 := pairing_constant T a c0 n hc n le_rfl
    rw [← e2, ha]
    exact he

end Tower

/-! ## Section 11.3: the matrices -/

section Matrices

/-- Pairing of a row covector with a column class. -/
def pair (a c : ℤ × ℤ) : ℤ := a.1 * c.1 + a.2 * c.2

/-- The class map of `U`. -/
def U (c : ℤ × ℤ) : ℤ × ℤ := (c.1 - c.2, c.2)

/-- The class map of the inverse of `U`. -/
def Uinv (c : ℤ × ℤ) : ℤ × ℤ := (c.1 + c.2, c.2)

/-- The pullback of a covector by `U`. -/
def pullU (a : ℤ × ℤ) : ℤ × ℤ := (a.1, -a.1 + a.2)

/-- Section 11.3: the realised class keeps its pairing, the covector is not fixed, another class
loses its period and regains it under the inverse. -/
theorem U_separates_realised_from_uniform :
    U (1, 0) = (1, 0) ∧ pair (1, 0) (1, 0) = 1 ∧ pullU (1, 0) ≠ (1, 0) ∧
      pair (1, 0) (1, 1) = 1 ∧ U (1, 1) = (0, 1) ∧ pair (1, 0) (0, 1) = 0 ∧
      Uinv (0, 1) = (1, 1) := by
  decide

/-- Statement A on that example: `(0, 1)`, chosen afterwards, is fixed by `U` and keeps the period of
`(1, 1)` at one. -/
theorem late_witness_keeps_the_period :
    pullU (0, 1) = (0, 1) ∧ pair (0, 1) (1, 1) = 1 ∧ pair (0, 1) (U (1, 1)) = 1 := by
  decide

/-- Non-vanishing is weaker than exact preservation: doubling keeps a non-zero value non-zero. -/
theorem doubling_keeps_non_zero (p : ℤ) (h : p ≠ 0) : 2 * p ≠ 0 ∧ (p ≠ 0 → 2 * p ≠ p) := by
  constructor <;> [omega; (intro _; omega)]

end Matrices

/-! ## Section 11.3: the scale law -/

section Scale

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The partial products of the scales. -/
def partialProd (lam : ℕ → K) (n : ℕ) : K := ∏ j ∈ Finset.range n, lam j

theorem partial_pos (lam : ℕ → K) (hpos : ∀ j, 0 < lam j) (n : ℕ) : 0 < partialProd lam n :=
  Finset.prod_pos fun j _ => hpos j

/-- The formula: the pairing is the initial pairing over the partial product. -/
theorem scale_law_formula (lam p : ℕ → K) (hpos : ∀ j, 0 < lam j)
    (h : ∀ j, p j = lam j * p (j + 1)) (n : ℕ) : p n = p 0 / partialProd lam n := by
  induction n with
  | zero => simp [partialProd]
  | succ n ih =>
    have hne : lam n ≠ 0 := (hpos n).ne'
    have e : p (n + 1) = p n / lam n := by
      rw [eq_div_iff hne, mul_comm]
      exact (h n).symm
    rw [e, ih]
    simp only [partialProd, Finset.prod_range_succ]
    rw [div_div]

/-- The modulus has a positive lower bound over the levels exactly when the partial products are
bounded above. -/
theorem lower_bound_iff_bounded (lam p : ℕ → K) (hpos : ∀ j, 0 < lam j)
    (h : ∀ j, p j = lam j * p (j + 1)) (h0 : p 0 ≠ 0) :
    (∃ ε, 0 < ε ∧ ∀ n, ε ≤ |p n|) ↔ ∃ B, ∀ n, partialProd lam n ≤ B := by
  have hP := partial_pos lam hpos
  have hf : ∀ n, |p n| = |p 0| / partialProd lam n := by
    intro n
    rw [scale_law_formula lam p hpos h n, abs_div, abs_of_pos (hP n)]
  have h0' : 0 < |p 0| := abs_pos.2 h0
  constructor
  · rintro ⟨ε, hε, hb⟩
    refine ⟨|p 0| / ε, fun n => ?_⟩
    have e := hb n
    rw [hf n, le_div_iff₀ (hP n)] at e
    rw [le_div_iff₀ hε]
    linarith [mul_comm (partialProd lam n) ε]
  · rintro ⟨B, hB⟩
    have hB1 : 0 < B := lt_of_lt_of_le (hP 0) (hB 0)
    refine ⟨|p 0| / B, div_pos h0' hB1, fun n => ?_⟩
    rw [hf n, div_le_div_iff₀ hB1 (hP n)]
    exact mul_le_mul_of_nonneg_left (hB n) h0'.le

/-- Repeated scale two has unbounded partial products: no positive lower bound. -/
theorem repeated_scale_two_unbounded [Archimedean K] (p : ℕ → K) (h : ∀ j, p j = 2 * p (j + 1)) (h0 : p 0 ≠ 0) :
    ¬ ∃ ε, 0 < ε ∧ ∀ n, ε ≤ |p n| := by
  rw [lower_bound_iff_bounded (fun _ => (2 : K)) p (fun _ => by norm_num) h h0]
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : K) < 2)
  have e := hB n
  simp only [partialProd, Finset.prod_const, Finset.card_range] at e
  linarith

/-- Scale one half keeps a positive lower bound although it is not unit scale. -/
theorem scale_one_half_bounded (p : ℕ → K) (h : ∀ j, p j = (1 / 2) * p (j + 1)) (h0 : p 0 ≠ 0) :
    ∃ ε, 0 < ε ∧ ∀ n, ε ≤ |p n| := by
  rw [lower_bound_iff_bounded (fun _ => (1 / 2 : K)) p (fun _ => by norm_num) h h0]
  refine ⟨1, fun n => ?_⟩
  simp only [partialProd, Finset.prod_const, Finset.card_range]
  exact pow_le_one₀ (by norm_num) (by norm_num)

end Scale

/-! ## Statement B: integral data under repeated scale two -/

section Lattice

/-- Halving along a chain of integers: the initial value is the last one times a power of two. -/
theorem halving_factor (p : ℕ → ℤ) (n : ℕ) (h : ∀ j, j < n → p j = 2 * p (j + 1)) :
    p 0 = 2 ^ n * p n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih fun j hj => h j (by omega), h n (by omega)]
    ring

/-- Statement B: integral data stop repeated scale two at the 2-adic valuation of the initial value. -/
theorem halving_depth_le_valuation (p : ℕ → ℤ) (n : ℕ) (h : ∀ j, j < n → p j = 2 * p (j + 1))
    (h0 : p 0 ≠ 0) : n ≤ padicValInt 2 (p 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have d : (2 : ℤ) ^ n ∣ p 0 := ⟨p n, halving_factor p n h⟩
  have d2 : ((2 : ℕ) : ℤ) ^ n ∣ p 0 := by simpa using d
  rcases (padicValInt_dvd_iff (p := 2) n (p 0)).1 d2 with e | e
  · exact absurd e h0
  · exact e

/-- The bound is reached: a value `2 ^ k * m` halves for `k` steps. -/
theorem halving_reaches_depth (k : ℕ) (m : ℤ) :
    ∃ p : ℕ → ℤ, p 0 = 2 ^ k * m ∧ ∀ j, j < k → p j = 2 * p (j + 1) := by
  refine ⟨fun j => 2 ^ (k - j) * m, by simp, fun j hj => ?_⟩
  have e : k - j = (k - (j + 1)) + 1 := by omega
  show 2 ^ (k - j) * m = 2 * (2 ^ (k - (j + 1)) * m)
  rw [e]
  ring

/-- No non-zero integer value survives an infinite chain of halvings. -/
theorem no_infinite_halving (p : ℕ → ℤ) (h : ∀ j, p j = 2 * p (j + 1)) : p 0 = 0 := by
  by_contra h0
  have e := halving_depth_le_valuation p (padicValInt 2 (p 0) + 1) (fun j _ => h j) h0
  omega

/-- On the lattice `(1/q)ℤ` the same holds for the numerators, so the bound is `v₂(q p₀)`. -/
theorem lattice_numerators_halve (q : ℤ) (hq : q ≠ 0) (r : ℕ → ℤ)
    (h : ∀ j, ((r j : ℚ) / q) = 2 * ((r (j + 1) : ℚ) / q)) (j : ℕ) : r j = 2 * r (j + 1) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have e := h j
  have e2 : (r j : ℚ) = 2 * (r (j + 1) : ℚ) := by
    field_simp at e
    linarith
  exact_mod_cast e2

/-- Real data continue: the premise of integrality carries the bound. -/
theorem real_halving_continues {K : Type*} [Field K] [CharZero K] (p0 : K) (h0 : p0 ≠ 0) :
    ∃ p : ℕ → K, p 0 = p0 ∧ (∀ j, p j = 2 * p (j + 1)) ∧ ∀ j, p j ≠ 0 := by
  refine ⟨fun j => p0 / 2 ^ j, by simp, fun j => ?_, fun j => ?_⟩
  · show p0 / 2 ^ j = 2 * (p0 / 2 ^ (j + 1))
    have h2 : (2 : K) ^ j ≠ 0 := pow_ne_zero j two_ne_zero
    field_simp
    ring
  · exact div_ne_zero h0 (pow_ne_zero j two_ne_zero)

/-- Growth is not stopped by the lattice: a degree-two self-map doubles periods indefinitely. -/
theorem doubling_stays_on_the_lattice (p0 : ℤ) :
    ∃ p : ℕ → ℤ, p 0 = p0 ∧ ∀ j, p (j + 1) = 2 * p j :=
  ⟨fun j => 2 ^ j * p0, by simp, fun j => by
    show 2 ^ (j + 1) * p0 = 2 * (2 ^ j * p0)
    ring⟩

end Lattice

/-! ## Statement C: the doubling tower -/

section Doubling

/-- A word on the steps is removed when it is the coboundary of an integer family on the levels. -/
def Solvable (y : ℕ → ℤ) : Prop := ∃ x : ℕ → ℤ, ∀ n, x n - 2 * x (n + 1) = y n

/-- The partial sums of `z(y)`. -/
def zPart (y : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, y i * 2 ^ i

/-- Telescoping along the tower. -/
theorem telescoping (x y : ℕ → ℤ) (h : ∀ n, x n - 2 * x (n + 1) = y n) (n : ℕ) :
    x 0 = zPart y n + 2 ^ n * x n := by
  induction n with
  | zero => simp [zPart]
  | succ n ih =>
    rw [ih]
    simp only [zPart, Finset.sum_range_succ]
    rw [← h n]
    ring

/-- A word is removed exactly when `z(y)` is an integer: congruent to one integer modulo every power
of two. This is the content of `lim^1 = Z_2 / Z`, without the packaging of the 2-adic integers. -/
theorem solvable_iff_integer_limit (y : ℕ → ℤ) :
    Solvable y ↔ ∃ m : ℤ, ∀ n, (2 : ℤ) ^ n ∣ m - zPart y n := by
  constructor
  · rintro ⟨x, h⟩
    refine ⟨x 0, fun n => ⟨x n, ?_⟩⟩
    rw [telescoping x y h n]
    ring
  · rintro ⟨m, h⟩
    have h' : ∀ n, ∃ c, m - zPart y n = 2 ^ n * c := fun n => h n
    choose x hx using h'
    refine ⟨x, fun n => ?_⟩
    have h1 := hx n
    have h2 := hx (n + 1)
    have hs : zPart y (n + 1) = zPart y n + y n * 2 ^ n := by
      simp [zPart, Finset.sum_range_succ]
    rw [hs] at h2
    have hpos : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    apply mul_left_cancel₀ hpos
    linear_combination (-1 : ℤ) * h1 + h2

/-- Every finite prefix of a word on the doubling tower is removed. -/
theorem finite_prefix_removed (y : ℕ → ℤ) (n : ℕ) :
    ∃ x : ℕ → ℤ, ∀ j, j < n → x j - 2 * x (j + 1) = y j := by
  obtain ⟨x, hx⟩ := finite_word_is_coboundary (A := fun _ => ℤ)
    (fun _ => AddMonoidHom.mulLeft (2 : ℤ)) y n 0
  exact ⟨x, fun j hj => hx j (Nat.zero_le j) (by omega)⟩

theorem solvable_tail (y : ℕ → ℤ) : Solvable y ↔ Solvable (fun n => y (n + 1)) := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨fun n => x (n + 1), fun n => h (n + 1)⟩
  · rintro ⟨x, h⟩
    refine ⟨fun n => match n with
      | 0 => y 0 + 2 * x 0
      | k + 1 => x k, fun n => ?_⟩
    cases n with
    | zero =>
      show y 0 + 2 * x 0 - 2 * x 0 = y 0
      ring
    | succ k => exact h k

/-- The class does not see a finite prefix. -/
theorem solvable_congr_tail (N : ℕ) : ∀ y y' : ℕ → ℤ,
    (∀ j, N ≤ j → y j = y' j) → (Solvable y ↔ Solvable y') := by
  induction N with
  | zero =>
    intro y y' h
    have e : y = y' := funext fun j => h j (Nat.zero_le j)
    rw [e]
  | succ N ih =>
    intro y y' h
    rw [solvable_tail y, solvable_tail y']
    exact ih _ _ fun j hj => h (j + 1) (by omega)

theorem solvable_zero : Solvable (fun _ => (0 : ℤ)) := ⟨fun _ => 0, fun _ => by simp⟩

/-- The class is additive. -/
theorem solvable_add (y y' : ℕ → ℤ) (h : Solvable y) (h' : Solvable y') :
    Solvable (fun n => y n + y' n) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨x', hx'⟩ := h'
  refine ⟨fun n => x n + x' n, fun n => ?_⟩
  have e := hx n
  have e' := hx' n
  show x n + x' n - 2 * (x (n + 1) + x' (n + 1)) = y n + y' n
  rw [← e, ← e']
  ring

/-- A solvable binary word is eventually constant. -/
theorem binary_solvable_eventually_constant (b : ℕ → ℤ) (hb : Bin b) (hs : Solvable b) :
    ∃ N, (∀ j, N ≤ j → b j = 0) ∨ (∀ j, N ≤ j → b j = 1) := by
  obtain ⟨x, h⟩ := hs
  have descend : ∀ k : ℕ, ∀ s, -(k : ℤ) ≤ x s → x s ≤ k → ∃ N, x N = 0 ∨ x N = -1 := by
    intro k
    induction k with
    | zero =>
      intro s h1 h2
      exact ⟨s, Or.inl (by omega)⟩
    | succ k ih =>
      intro s h1 h2
      by_cases h0 : x s = 0 ∨ x s = -1
      · exact ⟨s, h0⟩
      · have e := h s
        have e1 := hb s
        apply ih (s + 1) <;> omega
  obtain ⟨N, hN⟩ := descend (x 0).natAbs 0 (by omega) (by omega)
  refine ⟨N, ?_⟩
  rcases hN with h0 | h1
  · left
    have stuck : ∀ d, x (N + d) = 0 := by
      intro d
      induction d with
      | zero => exact h0
      | succ d ih =>
        have e := h (N + d)
        have e1 := hb (N + d)
        show x (N + d + 1) = 0
        omega
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    have e := h (N + d)
    have s1 := stuck d
    have s2 : x (N + d + 1) = 0 := stuck (d + 1)
    omega
  · right
    have stuck : ∀ d, x (N + d) = -1 := by
      intro d
      induction d with
      | zero => exact h1
      | succ d ih =>
        have e := h (N + d)
        have e1 := hb (N + d)
        show x (N + d + 1) = -1
        omega
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    have e := h (N + d)
    have s1 := stuck d
    have s2 : x (N + d + 1) = -1 := stuck (d + 1)
    omega

/-- Statement C on the words of Section 7.3: `P_*` is the non-vanishing of the class. -/
theorem Pstar_iff_not_solvable (b : ℕ → ℤ) (hb : Bin b) (hl : Legal b) :
    Pstar b ↔ ¬ Solvable b := by
  constructor
  · rintro ⟨_, hi⟩ hs
    obtain ⟨N, h0 | h1⟩ := binary_solvable_eventually_constant b hb hs
    · obtain ⟨j, hj, e⟩ := hi N
      have e0 := h0 j hj
      omega
    · have a := h1 N le_rfl
      have c := h1 (N + 1) (by omega)
      have e := hl.2 N
      rw [a, c] at e
      norm_num at e
  · intro hn
    refine ⟨hl, fun N => ?_⟩
    by_contra hno
    apply hn
    refine (solvable_congr_tail N b (fun _ => 0) fun j hj => ?_).2 solvable_zero
    rcases hb j with h | h
    · exact h
    · exact (hno ⟨j, hj, h⟩).elim

/-- The legal premise carries the statement: all ones has infinitely many ones and a zero class. -/
theorem all_ones_infinite_with_zero_class :
    InfOnes (fun _ => 1) ∧ Solvable (fun _ => 1) ∧ ¬ Legal (fun _ => 1) := by
  refine ⟨fun N => ⟨N, le_rfl, rfl⟩, ⟨fun _ => -1, fun _ => by norm_num⟩, ?_⟩
  rintro ⟨_, h⟩
  have e := h 0
  norm_num at e

/-- For a word not eventually constant, two binary words have the same class exactly when they agree
from some index on: the class is the tail of the word. -/
theorem same_class_iff_same_tail (b c : ℕ → ℤ) (hb : Bin b) (hc : Bin c)
    (hbn : ¬ ∃ N, (∀ j, N ≤ j → b j = 0) ∨ (∀ j, N ≤ j → b j = 1)) :
    Solvable (fun n => b n - c n) ↔ ∃ N, ∀ j, N ≤ j → b j = c j := by
  constructor
  · rintro ⟨x, h⟩
    have h' : ∀ n, x n - 2 * x (n + 1) = b n - c n := h
    have descend : ∀ k : ℕ, ∀ s, -(k : ℤ) ≤ x s → x s ≤ k →
        ∃ N, x N = 0 ∨ x N = 1 ∨ x N = -1 := by
      intro k
      induction k with
      | zero =>
        intro s h1 h2
        exact ⟨s, Or.inl (by omega)⟩
      | succ k ih =>
        intro s h1 h2
        by_cases h0 : x s = 0 ∨ x s = 1 ∨ x s = -1
        · exact ⟨s, h0⟩
        · have e := h' s
          have e1 := hb s
          have e2 := hc s
          apply ih (s + 1) <;> omega
    obtain ⟨N, hN⟩ := descend (x 0).natAbs 0 (by omega) (by omega)
    by_cases hz : ∃ M, N ≤ M ∧ x M = 0
    · obtain ⟨M, _, hM⟩ := hz
      refine ⟨M, ?_⟩
      have stuck : ∀ d, x (M + d) = 0 := by
        intro d
        induction d with
        | zero => exact hM
        | succ d ih =>
          have e := h' (M + d)
          have e1 := hb (M + d)
          have e2 := hc (M + d)
          show x (M + d + 1) = 0
          omega
      intro j hj
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      have e := h' (M + d)
      have s1 := stuck d
      have s2 : x (M + d + 1) = 0 := stuck (d + 1)
      omega
    · exfalso
      have hz' : ∀ M, N ≤ M → x M ≠ 0 := fun M hM e => hz ⟨M, hM, e⟩
      rcases hN with h0 | h1 | h2
      · exact hz' N le_rfl h0
      · have stuck : ∀ d, x (N + d) = 1 := by
          intro d
          induction d with
          | zero => exact h1
          | succ d ih =>
            have e := h' (N + d)
            have e1 := hb (N + d)
            have e2 := hc (N + d)
            have ne := hz' (N + d + 1) (by omega)
            show x (N + d + 1) = 1
            omega
        apply hbn
        refine ⟨N, Or.inl fun j hj => ?_⟩
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
        have e := h' (N + d)
        have e1 := hb (N + d)
        have e2 := hc (N + d)
        have s1 := stuck d
        have s2 : x (N + d + 1) = 1 := stuck (d + 1)
        omega
      · have stuck : ∀ d, x (N + d) = -1 := by
          intro d
          induction d with
          | zero => exact h2
          | succ d ih =>
            have e := h' (N + d)
            have e1 := hb (N + d)
            have e2 := hc (N + d)
            have ne := hz' (N + d + 1) (by omega)
            show x (N + d + 1) = -1
            omega
        apply hbn
        refine ⟨N, Or.inr fun j hj => ?_⟩
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
        have e := h' (N + d)
        have e1 := hb (N + d)
        have e2 := hc (N + d)
        have s1 := stuck d
        have s2 : x (N + d + 1) = -1 := stuck (d + 1)
        omega
  · rintro ⟨N, h⟩
    refine (solvable_congr_tail N _ (fun _ => 0) fun j hj => ?_).2 solvable_zero
    show b j - c j = 0
    rw [h j hj]
    ring

/-- Over a field of characteristic zero every word on the doubling tower is removed. -/
theorem real_word_always_removed {K : Type*} [Field K] [CharZero K] (y : ℕ → K) (x0 : K) :
    ∃ x : ℕ → K, x 0 = x0 ∧ ∀ n, x n - 2 * x (n + 1) = y n := by
  refine ⟨fun n => Nat.rec x0 (fun n v => (v - y n) / 2) n, rfl, fun n => ?_⟩
  show (Nat.rec x0 (fun n v => (v - y n) / 2) n : K)
      - 2 * (((Nat.rec x0 (fun n v => (v - y n) / 2) n : K) - y n) / 2) = y n
  ring

end Doubling

/-! ## Sections 7, 9.1, 9.2, 9.3: small facts -/

section Small

/-- The rational inequalities of Section 7. -/
theorem section7_inequalities :
    (3 : ℚ) / 16 < 1 / 2 ∧ (9 : ℚ) / 32 < 1 / 2 ∧ (9 : ℚ) / 16 < 3 / 4 ∧ (3 : ℚ) / 4 < 13 / 16 ∧
      (11 : ℚ) / 16 < 3 / 4 := by
  norm_num

/-- Section 9.1: the external channel determines the property, the constant transcript does not. -/
theorem external_channel_toy :
    (∀ γ γ' : Bool, id γ = id γ' → γ = γ') ∧ ¬ ∃ h : Unit → Bool, ∀ γ : Bool, γ = h () := by
  refine ⟨fun _ _ e => e, ?_⟩
  rintro ⟨h, e⟩
  have e1 := e true
  have e2 := e false
  rw [← e2] at e1
  exact absurd e1 (by decide)

/-- Section 9.2: each component has a mixed fibre for the bit, the pair determines it. -/
theorem xor_fibres :
    (∀ u : Bool, ∃ θ θ' : Bool, θ ≠ θ' ∧ u = u) ∧
      (∀ v : Bool, ∃ θ θ' u u' : Bool, θ ≠ θ' ∧ xor θ u = v ∧ xor θ' u' = v) ∧
      (∀ θ θ' u u' : Bool, u = u' → xor θ u = xor θ' u' → θ = θ') := by
  decide

/-- Section 9.3: a mixed fibre of the recorded map refutes completeness of the list. -/
theorem mixed_fibre_refutes_completeness {St R : Type*} (mK : St → R) (E : St → Bool) (s s' : St)
    (e : mK s = mK s') (ne : E s ≠ E s') :
    ¬ ∃ Ebar : Set.range mK → Bool, ∀ t, E t = Ebar ⟨mK t, t, rfl⟩ := by
  rw [M1_fibre_sufficiency]
  exact fun h => ne (h s s' e)

/-- Section 3.1: equal totals, different first crossing of one half. -/
theorem ordered_traces_separate :
    (1 : ℚ) / 3 + 2 / 3 = 2 / 3 + 1 / 3 ∧ (1 : ℚ) / 3 ≤ 1 / 2 ∧ (1 : ℚ) / 2 < 1 / 3 + 2 / 3 ∧
      (1 : ℚ) / 2 < 2 / 3 := by
  norm_num

/-- Section 10: with capacity one and burden `1 - 2^(-n)` the margin stays positive at every level. -/
theorem margin_positive_at_every_level (n : ℕ) : (0 : ℚ) < 1 - (1 - 1 / 2 ^ n) := by
  have h : (0 : ℚ) < 1 / 2 ^ n := by positivity
  linarith

end Small

end Mirrors
