import Std.Tactic

namespace MirrorCausalLifting

universe u v w z

def SamePrefix {X : Type u} {A : Type v} (obs : X → Nat → A)
    (n : Nat) (x x' : X) : Prop := ∀ t, t ≤ n → obs x t = obs x' t

def PrefixCausal {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
    (ox : X → Nat → A) (oy : Y → Nat → B) (f : X → Y) : Prop :=
  ∀ n x x', SamePrefix ox n x x' → SamePrefix oy n (f x) (f x')

theorem inverse_causal_iff_prefix_reflection
    {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
    (ox : X → Nat → A) (oy : Y → Nat → B) (q : X → Y) (g : Y → X)
    (hleft : ∀ x, g (q x) = x) (hright : ∀ y, q (g y) = y) :
    PrefixCausal oy ox g ↔
      ∀ n x x', SamePrefix oy n (q x) (q x') → SamePrefix ox n x x' := by
  constructor
  · intro hc n x x' hp
    simpa only [hleft] using hc n (q x) (q x') hp
  · intro hr n y y' hp
    apply hr n (g y) (g y')
    simpa only [hright] using hp

def mapHistory {A : Type u} {B : Type v} (f : A → B) (h : Nat → A) : Nat → B :=
  fun t => f (h t)

theorem map_history_causal {A : Type u} {B : Type v} (f : A → B) :
    PrefixCausal (fun h t => h t) (fun h t => h t) (mapHistory f) := by
  intro n x x' hp t ht
  exact congrArg f (hp t ht)

theorem pointwise_prefix_iff
    {A : Type u} {B : Type v} (f : A → B) (g : B → A)
    (hleft : ∀ a, g (f a) = a) (n : Nat) (x x' : Nat → A) :
    SamePrefix (fun h t => h t) n (mapHistory f x) (mapHistory f x') ↔
      SamePrefix (fun h t => h t) n x x' := by
  constructor
  · intro hp t ht
    have hh := congrArg g (hp t ht)
    simpa only [mapHistory, hleft] using hh
  · exact map_history_causal f n x x'

theorem causal_conjugate
    {A : Type u} {B : Type v} (f : A → B) (g : B → A)
    (p : (Nat → A) → (Nat → A))
    (hc : PrefixCausal (fun h t => h t) (fun h t => h t) p) :
    PrefixCausal (fun h t => h t) (fun h t => h t)
      (fun y => mapHistory f (p (mapHistory g y))) := by
  intro n y y' hp
  exact map_history_causal f n _ _
    (hc n _ _ (map_history_causal g n y y' hp))

-- A finite family of complete streams, with a common root and a delayed target readout.
def sourceObs (ab : Bool × Bool) : Nat → Option Bool
  | 0 => none
  | 1 => some ab.1
  | _ + 2 => some ab.2

def targetObs (b : Bool) : Nat → Option Bool
  | 0 => none
  | 1 => none
  | _ + 2 => some b

def admitted (ab : Bool × Bool) : Prop := ab.1 = ab.2

def q (ab : Bool × Bool) : Bool := ab.2

def diagonal (b : Bool) : Bool × Bool := (b, b)

theorem common_root_source (ab : Bool × Bool) : sourceObs ab 0 = none := rfl

theorem common_root_target (b : Bool) : targetObs b 0 = none := rfl

theorem diagonal_admitted (b : Bool) : admitted (diagonal b) := rfl

theorem diagonal_right_inverse (b : Bool) : q (diagonal b) = b := rfl

theorem diagonal_left_inverse (ab : Bool × Bool) (ha : admitted ab) :
    diagonal (q ab) = ab := by
  rcases ab with ⟨a, b⟩
  change a = b at ha
  cases ha
  rfl

theorem forward_is_causal : PrefixCausal sourceObs targetObs q := by
  intro n x x' hp t ht
  cases t with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ j => exact hp (Nat.succ (Nat.succ j)) ht

theorem no_causal_admitted_section :
    ¬ ∃ g : Bool → Bool × Bool,
      (∀ b, admitted (g b) ∧ q (g b) = b) ∧
      PrefixCausal targetObs sourceObs g := by
  rintro ⟨g, hlift, hcausal⟩
  have hp : SamePrefix targetObs 1 false true := by
    intro t ht
    cases t with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ j =>
        have bad : Nat.succ j ≤ 0 := Nat.le_of_succ_le_succ ht
        exact False.elim (Nat.not_succ_le_zero j bad)
  have hx := hcausal 1 false true hp 1 (Nat.le_refl 1)
  have ha0 : (g false).1 = false := (hlift false).1.trans (hlift false).2
  have ha1 : (g true).1 = true := (hlift true).1.trans (hlift true).2
  change some (g false).1 = some (g true).1 at hx
  rw [ha0, ha1] at hx
  cases Option.some.inj hx

end MirrorCausalLifting
