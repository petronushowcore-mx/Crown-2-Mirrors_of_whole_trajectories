import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Path
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Geometry of manuscript Section 7 in the genuine Euclidean plane C,
   viewed over R. The metric is not transported to the max-norm product.
   Positive manuscript hole indices are j >= 1. Level 0 is a harmless
   auxiliary stage; XInfinity unions only positive levels. -/
noncomputable section
namespace MirrorGeometry
open Set

def c (j : Nat) : ℝ := (1 / 2 : ℝ) ^ j
def rho (j : Nat) : ℝ := c j / 8
def a (n : Nat) : ℝ := 3 * c n / 4
def loopRadius (j : Nat) : ℝ := 3 * c j / 16
def center (j : Nat) : ℂ := (c j : ℂ)
def disk (j : Nat) : Set ℂ := Metric.closedBall (center j) (rho j)

def rectangle (n : Nat) : Set ℂ :=
  {p | a n < p.re ∧ p.re < 2 ∧ -1 < p.im ∧ p.im < 1}

def X (n : Nat) : Set ℂ :=
  rectangle n ∩ ⋂ j : Fin n, {p | rho (j.val + 1) < dist p (center (j.val + 1))}

def XInfinity : Set ℂ := ⋃ n : Nat, X (n + 1)
def markedCircle (j : Nat) : Set ℂ := Metric.sphere (center j) (loopRadius j)

theorem euclidean_distance (p q : ℂ) :
    dist p q = Real.sqrt ((p.re - q.re)^2 + (p.im - q.im)^2) :=
  Complex.dist_eq_re_im p q

theorem c_pos (j : Nat) : 0 < c j := by
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j

theorem c_le_one (j : Nat) : c j ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)

theorem c_succ (j : Nat) : c (j + 1) = c j / 2 := by
  simp only [c, pow_succ]
  ring

theorem c_antitone {i j : Nat} (hij : i ≤ j) : c j ≤ c i := by
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hij

theorem c_later_le_half {i j : Nat} (hij : i < j) : c j ≤ c i / 2 := by
  have h := c_antitone (show i + 1 ≤ j by omega)
  simpa [c_succ] using h

theorem center_distance (i j : Nat) :
    dist (center i) (center j) = |c i - c j| := by
  rw [Complex.dist_of_im_eq (by simp [center]), Real.dist_eq]
  simp [center]

theorem adjacent_center_distance (j : Nat) :
    dist (center j) (center (j + 1)) = c j / 2 := by
  rw [center_distance, c_succ]
  have hp := c_pos j
  rw [abs_of_nonneg (by linarith)]
  ring

theorem adjacent_radius_sum (j : Nat) :
    rho j + rho (j + 1) = 3 * c j / 16 := by
  simp only [rho, c_succ]
  ring

theorem disk_gap {i j : Nat} (hij : i < j) :
    rho i + rho j < dist (center i) (center j) := by
  have hhalf := c_later_le_half hij
  have hp := c_pos i
  rw [center_distance, abs_of_nonneg (by linarith)]
  dsimp [rho]
  linarith

theorem disks_disjoint {i j : Nat} (hij : i < j) :
    Disjoint (disk i) (disk j) := by
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  have hi : dist p (center i) ≤ rho i := hpi
  have hj : dist p (center j) ≤ rho j := hpj
  have ht := dist_triangle (center i) p (center j)
  rw [dist_comm (center i) p] at ht
  have hg := disk_gap hij
  linarith

theorem real_coordinate_bound (p : ℂ) (j : Nat) :
    |p.re - c j| ≤ dist p (center j) := by
  simpa [center, dist_eq_norm] using Complex.abs_re_le_norm (p - center j)

theorem imag_coordinate_bound (p : ℂ) (j : Nat) :
    |p.im| ≤ dist p (center j) := by
  simpa [center, dist_eq_norm] using Complex.abs_im_le_norm (p - center j)

theorem next_disk_right_edge (n : Nat) :
    c (n + 1) + rho (n + 1) = 9 * c n / 16 := by
  simp only [rho, c_succ]
  ring

theorem next_disk_left_of_boundary (n : Nat) :
    c (n + 1) + rho (n + 1) < a n := by
  rw [next_disk_right_edge]
  dsimp [a]
  linarith [c_pos n]

theorem next_disk_points_left (n : Nat) (p : ℂ)
    (hp : p ∈ disk (n + 1)) : p.re < a n := by
  have hd : dist p (center (n + 1)) ≤ rho (n + 1) := hp
  have hb := (le_abs_self (p.re - c (n + 1))).trans
    (real_coordinate_bound p (n + 1))
  have he := next_disk_left_of_boundary n
  linarith

theorem next_disk_avoided (n : Nat) (p : ℂ) (hp : a n < p.re) :
    rho (n + 1) < dist p (center (n + 1)) := by
  have hb := (le_abs_self (p.re - c (n + 1))).trans
    (real_coordinate_bound p (n + 1))
  have he := next_disk_left_of_boundary n
  linarith

theorem a_succ_lt (n : Nat) : a (n + 1) < a n := by
  dsimp [a]
  rw [c_succ]
  linarith [c_pos n]

theorem mem_X (n : Nat) (p : ℂ) :
    p ∈ X n ↔
      (a n < p.re ∧ p.re < 2 ∧ -1 < p.im ∧ p.im < 1) ∧
      (∀ j : Fin n, rho (j.val + 1) < dist p (center (j.val + 1))) := by
  simp [X, rectangle]

theorem X_eq_punctured_rectangle (n : Nat) :
    X n = rectangle n \ ⋃ j : Fin n, disk (j.val + 1) := by
  ext p
  simp [X, disk, Metric.mem_closedBall]

theorem stage_nesting (n : Nat) : X n ⊆ X (n + 1) := by
  intro p hp
  rcases (mem_X n p).mp hp with ⟨⟨ha, hright, hlow, hhigh⟩, hdisks⟩
  apply (mem_X (n + 1) p).mpr
  refine ⟨⟨lt_trans (a_succ_lt n) ha, hright, hlow, hhigh⟩, ?_⟩
  intro j
  by_cases hj : j.val < n
  · exact hdisks ⟨j.val, hj⟩
  · have he : j.val = n := by omega
    simpa [he] using next_disk_avoided n p ha

theorem stages_monotone : Monotone X :=
  monotone_nat_of_le_succ stage_nesting

theorem rectangle_open (n : Nat) : IsOpen (rectangle n) := by
  have hleft : IsOpen {p : ℂ | a n < p.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hright : IsOpen {p : ℂ | p.re < 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hlow : IsOpen {p : ℂ | -1 < p.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hhigh : IsOpen {p : ℂ | p.im < 1} :=
    isOpen_lt Complex.continuous_im continuous_const
  exact hleft.inter (hright.inter (hlow.inter hhigh))

theorem stage_open (n : Nat) : IsOpen (X n) := by
  apply (rectangle_open n).inter
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const (continuous_id.dist continuous_const)

theorem union_open : IsOpen XInfinity :=
  isOpen_iUnion (fun n => stage_open (n + 1))

/- A small Euclidean neighbourhood around each marked centre lies strictly
   inside every later rectangle. Bounds use actual coordinate-distance laws. -/
theorem small_neighbourhood_in_rectangle (n j : Nat) (hjn : j ≤ n)
    (p : ℂ) (hd : dist p (center j) ≤ loopRadius j) :
    p ∈ rectangle n := by
  have hscale := c_antitone hjn
  have hp := c_pos j
  have hunit := c_le_one j
  rcases abs_le.mp ((real_coordinate_bound p j).trans hd) with ⟨hl, hu⟩
  rcases abs_le.mp ((imag_coordinate_bound p j).trans hd) with ⟨hyl, hyu⟩
  change a n < p.re ∧ p.re < 2 ∧ -1 < p.im ∧ p.im < 1
  dsimp [a, loopRadius] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem old_disk_inside_rectangle (n j : Nat) (hjn : j ≤ n) :
    disk j ⊆ rectangle n := by
  intro p hp
  have hd : dist p (center j) ≤ rho j := hp
  apply small_neighbourhood_in_rectangle n j hjn p
  have hr : rho j ≤ loopRadius j := by
    dsimp [rho, loopRadius]
    linarith [c_pos j]
  exact hd.trans hr

theorem marked_circle_avoids_disk (j i : Nat) (p : ℂ)
    (hp : p ∈ markedCircle j) : rho i < dist p (center i) := by
  have hd : dist p (center j) = loopRadius j := hp
  rcases lt_trichotomy i j with hij | heq | hji
  · have hh := c_later_le_half hij
    have hpos := c_pos i
    have hcent : dist (center i) (center j) = c i - c j := by
      rw [center_distance, abs_of_nonneg (by linarith)]
    have ht := dist_triangle (center i) p (center j)
    rw [hcent, dist_comm (center i) p, hd] at ht
    dsimp [rho, loopRadius] at *
    linarith
  · subst i
    rw [hd]
    dsimp [rho, loopRadius]
    linarith [c_pos j]
  · have hh := c_later_le_half hji
    have hpos := c_pos j
    have hcent : dist (center j) (center i) = c j - c i := by
      rw [center_distance, abs_of_nonneg (by linarith)]
    have ht := dist_triangle (center j) p (center i)
    rw [hcent, dist_comm (center j) p, hd] at ht
    dsimp [rho, loopRadius] at *
    linarith

/- This is containment of the actual circle set. A smooth loop
   parametrisation, orientation, and curve-integral periods are separate. -/
theorem marked_circle_inside_stage (n j : Nat) (_hj : 1 ≤ j) (hjn : j ≤ n) :
    markedCircle j ⊆ X n := by
  intro p hp
  have hd : dist p (center j) = loopRadius j := hp
  apply (mem_X n p).mpr
  refine ⟨small_neighbourhood_in_rectangle n j hjn p hd.le, ?_⟩
  intro i
  exact marked_circle_avoids_disk j (i.val + 1) p hp

theorem marked_circle_nonempty (j : Nat) : (markedCircle j).Nonempty := by
  let p : ℂ := ((c j + loopRadius j : ℝ) : ℂ)
  have hr : 0 < loopRadius j := by
    dsimp [loopRadius]
    linarith [c_pos j]
  refine ⟨p, ?_⟩
  change dist p (center j) = loopRadius j
  have him : p.im = (center j).im := by simp [p, center]
  rw [Complex.dist_of_im_eq him, Real.dist_eq]
  change |(c j + loopRadius j) - c j| = loopRadius j
  have hsub : (c j + loopRadius j) - c j = loopRadius j := by ring
  rw [hsub, abs_of_pos hr]

theorem positive_stage_nonempty (n : Nat) (hn : 1 ≤ n) : (X n).Nonempty := by
  obtain ⟨p, hp⟩ := marked_circle_nonempty 1
  exact ⟨p, marked_circle_inside_stage n 1 (by omega) hn hp⟩


end MirrorGeometry

/- Smooth cutoff with the exact manuscript Section 7.2 thresholds.
   This namespace is a scalar cutoff only; F_j, eta_j and omega_j are not formalised here. -/
open scoped ContDiff

namespace MirrorSmoothCutoff

def left (j : Nat) : ℝ := 5 * MirrorGeometry.c j / 4
def right (j : Nat) : ℝ := 11 * MirrorGeometry.c j / 8

def chi (j : Nat) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - left j) / (right j - left j))

theorem transition_span_eq (j : Nat) :
    right j - left j = MirrorGeometry.c j / 8 := by
  dsimp [left, right]
  ring

theorem transition_span_pos (j : Nat) : 0 < right j - left j := by
  rw [transition_span_eq]
  exact div_pos (MirrorGeometry.c_pos j) (by norm_num)

theorem chi_zero_left (j : Nat) {x : ℝ} (hx : x ≤ left j) :
    chi j x = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (transition_span_pos j).le

theorem chi_one_right (j : Nat) {x : ℝ} (hx : right j ≤ x) :
    chi j x = 1 := by
  unfold chi
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (transition_span_pos j)).2
  linarith

theorem chi_smooth (j : Nat) : ContDiff ℝ ∞ (chi j) := by
  unfold chi
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (right j - left j))

theorem chi_nonnegative (j : Nat) (x : ℝ) : 0 ≤ chi j x :=
  Real.smoothTransition.nonneg _

theorem chi_le_one (j : Nat) (x : ℝ) : chi j x ≤ 1 :=
  Real.smoothTransition.le_one _


end MirrorSmoothCutoff

/- Smooth zero-extension of the scalar arctangent potential from manuscript
   Section 7.2. Lean division is total; the cutoff kills a whole neighbourhood
   of the singular line. The differential-form identity and periods are separate. -/
namespace MirrorSmoothPotential
open scoped ContDiff Topology
open Filter

def potential (j : Nat) (p : ℂ) : ℝ :=
  Real.arctan (p.im / (p.re - MirrorGeometry.c j)) / (2 * Real.pi)

def F (j : Nat) (p : ℂ) : ℝ :=
  MirrorSmoothCutoff.chi j p.re * potential j p

theorem center_left_gap (j : Nat) :
    MirrorSmoothCutoff.left j - MirrorGeometry.c j = MirrorGeometry.c j / 4 := by
  dsimp [MirrorSmoothCutoff.left]
  ring

theorem center_lt_left (j : Nat) :
    MirrorGeometry.c j < MirrorSmoothCutoff.left j := by
  have hpos := MirrorGeometry.c_pos j
  dsimp [MirrorSmoothCutoff.left]
  linarith

theorem normalisation_pos : 0 < 2 * Real.pi :=
  mul_pos (by norm_num) Real.pi_pos

theorem F_zero_left (j : Nat) {p : ℂ}
    (hp : p.re ≤ MirrorSmoothCutoff.left j) : F j p = 0 := by
  unfold F
  rw [MirrorSmoothCutoff.chi_zero_left j hp, zero_mul]

theorem F_agrees_right (j : Nat) {p : ℂ}
    (hp : MirrorSmoothCutoff.right j ≤ p.re) : F j p = potential j p := by
  unfold F
  rw [MirrorSmoothCutoff.chi_one_right j hp, one_mul]

theorem potential_smoothAt (j : Nat) {p : ℂ}
    (hp : p.re ≠ MirrorGeometry.c j) : ContDiffAt ℝ ∞ (potential j) p := by
  unfold potential
  have hre : ContDiffAt ℝ ∞ (fun q : ℂ => q.re) p :=
    Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun q : ℂ => q.im) p :=
    Complex.imCLM.contDiff.contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun q : ℂ => q.re - MirrorGeometry.c j) p :=
    hre.sub contDiffAt_const
  have hratio : ContDiffAt ℝ ∞
      (fun q : ℂ => q.im / (q.re - MirrorGeometry.c j)) p :=
    him.div hden (sub_ne_zero.mpr hp)
  exact hratio.arctan.div_const (2 * Real.pi)

theorem F_eventually_zero (j : Nat) {p : ℂ}
    (hp : p.re < MirrorSmoothCutoff.left j) :
    F j =ᶠ[𝓝 p] (fun _ : ℂ => (0 : ℝ)) := by
  exact (Complex.continuous_re.continuousAt.eventually_lt continuousAt_const hp).mono
    (fun q hq => F_zero_left j hq.le)

theorem F_smooth (j : Nat) : ContDiff ℝ ∞ (F j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.re < MirrorSmoothCutoff.left j
  · exact contDiffAt_const.congr_of_eventuallyEq (F_eventually_zero j hp)
  · have hc : MirrorGeometry.c j < p.re :=
      (center_lt_left j).trans_le (le_of_not_gt hp)
    have hchi : ContDiff ℝ ∞ (fun q : ℂ => MirrorSmoothCutoff.chi j q.re) :=
      (MirrorSmoothCutoff.chi_smooth j).comp Complex.reCLM.contDiff
    exact hchi.contDiffAt.mul (potential_smoothAt j (ne_of_gt hc))

theorem F_zero_on_closed_left (j : Nat) {p : ℂ}
    (hp : p.re ≤ MirrorGeometry.c j) : F j p = 0 :=
  F_zero_left j (hp.trans (center_lt_left j).le)


end MirrorSmoothPotential

/- Prepared derivative component. No compilation or kernel admission is
   claimed by this source being saved. Scope: the real Frechet derivative
   of the uncut potential on the right half-plane, not of F everywhere. -/
namespace MirrorPotentialDifferential

def eta (j : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * Real.pi * ((p.re - MirrorGeometry.c j)^2 + p.im^2))⁻¹ •
    ((-p.im) • Complex.reCLM + (p.re - MirrorGeometry.c j) • Complex.imCLM)

def chainDerivative (j : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ •
    ((1 / (1 + (p.im / (p.re - MirrorGeometry.c j))^2)) •
      (p.im • ((-(((p.re - MirrorGeometry.c j)^2)⁻¹)) • Complex.reCLM) +
        (p.re - MirrorGeometry.c j)⁻¹ • Complex.imCLM))

theorem chain_eq_eta (j : Nat) {p : ℂ}
    (hp : MirrorGeometry.c j < p.re) :
    chainDerivative j p = eta j p := by
  have hdpos : 0 < p.re - MirrorGeometry.c j := sub_pos.mpr hp
  have hd : p.re - MirrorGeometry.c j ≠ 0 := ne_of_gt hdpos
  have hquadratic : (p.re - MirrorGeometry.c j)^2 + p.im^2 ≠ 0 := by
    apply ne_of_gt
    have hd2 := pow_pos hdpos 2
    have hy2 := sq_nonneg p.im
    linarith
  have hnorm : 2 * Real.pi ≠ 0 :=
    ne_of_gt MirrorSmoothPotential.normalisation_pos
  have hunit : 1 + (p.im / (p.re - MirrorGeometry.c j))^2 ≠ 0 := by
    apply ne_of_gt
    have hsq := sq_nonneg (p.im / (p.re - MirrorGeometry.c j))
    linarith
  unfold chainDerivative eta
  ext v
  simp only [smul_apply, add_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  field_simp [hd, hquadratic, hnorm, hunit]

theorem potential_hasFDerivAt (j : Nat) {p : ℂ}
    (hp : MirrorGeometry.c j < p.re) :
    HasFDerivAt (MirrorSmoothPotential.potential j) (eta j p) p := by
  have hd : p.re - MirrorGeometry.c j ≠ 0 :=
    ne_of_gt (sub_pos.mpr hp)
  have hre : HasFDerivAt (fun q : ℂ => q.re) Complex.reCLM p :=
    Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun q : ℂ => q.im) Complex.imCLM p :=
    Complex.imCLM.hasFDerivAt
  have hden : HasFDerivAt (fun q : ℂ => q.re - MirrorGeometry.c j)
      Complex.reCLM p :=
    hre.sub_const (MirrorGeometry.c j)
  have hinv : HasFDerivAt (fun q : ℂ => (q.re - MirrorGeometry.c j)⁻¹)
      ((-(((p.re - MirrorGeometry.c j)^2)⁻¹)) • Complex.reCLM) p := by
    convert! (hasDerivAt_inv hd).comp_hasFDerivAt p hden using 1 <;>
      simp [Function.comp_def]
  have hprod : HasFDerivAt
      (fun q : ℂ => q.im * (q.re - MirrorGeometry.c j)⁻¹)
      (p.im • ((-(((p.re - MirrorGeometry.c j)^2)⁻¹)) • Complex.reCLM) +
        (p.re - MirrorGeometry.c j)⁻¹ • Complex.imCLM) p :=
    him.mul hinv
  have hchain : HasFDerivAt (MirrorSmoothPotential.potential j)
      (chainDerivative j p) p := by
    convert! hprod.arctan.mul_const ((2 * Real.pi)⁻¹) using 1 <;>
      simp [MirrorSmoothPotential.potential, chainDerivative, div_eq_mul_inv]
  rw [chain_eq_eta j hp] at hchain
  exact hchain

theorem potential_fderiv (j : Nat) {p : ℂ}
    (hp : MirrorGeometry.c j < p.re) :
    fderiv ℝ (MirrorSmoothPotential.potential j) p = eta j p :=
  (potential_hasFDerivAt j hp).fderiv


end MirrorPotentialDifferential

/- Pointwise derivative of the cut-off scalar potential. Strict inequalities
   supply a whole neighbourhood; equality at the right threshold is not claimed.
   omega here is a real continuous-linear covector field only. Smooth one-form
   typing on the punctured union, closedness and periods remain separate. -/
namespace MirrorCutoffDifferential
open scoped Topology
open Filter

def omega (j : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  MirrorPotentialDifferential.eta j p - fderiv ℝ (MirrorSmoothPotential.F j) p

theorem F_eventually_agrees_right (j : Nat) {p : ℂ}
    (hp : MirrorSmoothCutoff.right j < p.re) :
    MirrorSmoothPotential.F j =ᶠ[𝓝 p] MirrorSmoothPotential.potential j := by
  exact (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hp).mono
    (fun q hq => MirrorSmoothPotential.F_agrees_right j hq.le)

theorem F_hasFDerivAt_right (j : Nat) {p : ℂ}
    (hp : MirrorSmoothCutoff.right j < p.re) :
    HasFDerivAt (MirrorSmoothPotential.F j)
      (MirrorPotentialDifferential.eta j p) p := by
  have hc : MirrorGeometry.c j < MirrorSmoothCutoff.right j := by
    dsimp [MirrorSmoothCutoff.right]
    linarith [MirrorGeometry.c_pos j]
  exact (MirrorPotentialDifferential.potential_hasFDerivAt j (hc.trans hp)).congr_of_eventuallyEq (F_eventually_agrees_right j hp)

theorem F_fderiv_right (j : Nat) {p : ℂ}
    (hp : MirrorSmoothCutoff.right j < p.re) :
    fderiv ℝ (MirrorSmoothPotential.F j) p = MirrorPotentialDifferential.eta j p :=
  (F_hasFDerivAt_right j hp).fderiv

theorem F_hasFDerivAt_zero_left (j : Nat) {p : ℂ}
    (hp : p.re < MirrorSmoothCutoff.left j) :
    HasFDerivAt (MirrorSmoothPotential.F j) (0 : ℂ →L[ℝ] ℝ) p :=
  (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).congr_of_eventuallyEq (MirrorSmoothPotential.F_eventually_zero j hp)

theorem F_fderiv_zero_on_closed_left (j : Nat) {p : ℂ}
    (hp : p.re ≤ MirrorGeometry.c j) :
    fderiv ℝ (MirrorSmoothPotential.F j) p = (0 : ℂ →L[ℝ] ℝ) :=
  (F_hasFDerivAt_zero_left j
    (lt_of_le_of_lt hp (MirrorSmoothPotential.center_lt_left j))).fderiv

theorem omega_zero_right (j : Nat) {p : ℂ}
    (hp : MirrorSmoothCutoff.right j < p.re) : omega j p = 0 := by
  simp only [omega, F_fderiv_right j hp, sub_self]

theorem omega_eq_eta_on_closed_left (j : Nat) {p : ℂ}
    (hp : p.re ≤ MirrorGeometry.c j) :
    omega j p = MirrorPotentialDifferential.eta j p := by
  simp only [omega, F_fderiv_zero_on_closed_left j hp, sub_zero]


end MirrorCutoffDifferential
/- Smooth real covector fields off the centre and on the positive-index union.
   Exterior closedness, periods and the de Rham quotient are separate. -/
namespace MirrorCovectorSmoothness
open scoped ContDiff
open Set

theorem quadratic_pos_off_center (j : Nat) {p : ℂ}
    (hp : p ≠ MirrorGeometry.center j) :
    0 < (p.re - MirrorGeometry.c j)^2 + p.im^2 := by
  by_cases hx : p.re = MirrorGeometry.c j
  · have hy : p.im ≠ 0 := by
      intro hy
      apply hp
      apply Complex.ext
      · simpa [MirrorGeometry.center] using hx
      · simpa [MirrorGeometry.center] using hy
    simpa [hx] using sq_pos_of_ne_zero hy
  · have hdx := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    linarith [sq_nonneg p.im]

theorem eta_smoothAt (j : Nat) {p : ℂ}
    (hp : p ≠ MirrorGeometry.center j) :
    ContDiffAt ℝ ∞ (MirrorPotentialDifferential.eta j) p := by
  have hre : ContDiffAt ℝ ∞ (fun q : ℂ => q.re) p :=
    Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun q : ℂ => q.im) p :=
    Complex.imCLM.contDiff.contDiffAt
  have hdelta : ContDiffAt ℝ ∞
      (fun q : ℂ => q.re - MirrorGeometry.c j) p :=
    hre.sub contDiffAt_const
  have hquadratic : ContDiffAt ℝ ∞
      (fun q : ℂ => (q.re - MirrorGeometry.c j)^2 + q.im^2) p :=
    (hdelta.pow 2).add (him.pow 2)
  have hden : 2 * Real.pi * ((p.re - MirrorGeometry.c j)^2 + p.im^2) ≠ 0 :=
    mul_ne_zero (ne_of_gt MirrorSmoothPotential.normalisation_pos)
      (ne_of_gt (quadratic_pos_off_center j hp))
  have hweight : ContDiffAt ℝ ∞
      (fun q : ℂ => (2 * Real.pi *
        ((q.re - MirrorGeometry.c j)^2 + q.im^2))⁻¹) p :=
    (contDiffAt_const.mul hquadratic).inv hden
  have hnumerator : ContDiffAt ℝ ∞
      (fun q : ℂ => (-q.im) • Complex.reCLM +
        (q.re - MirrorGeometry.c j) • Complex.imCLM) p :=
    (him.neg.smul_const Complex.reCLM).add (hdelta.smul_const Complex.imCLM)
  exact hweight.smul hnumerator

theorem eta_smoothOn_punctured_plane (j : Nat) :
    ContDiffOn ℝ ∞ (MirrorPotentialDifferential.eta j)
      {p : ℂ | p ≠ MirrorGeometry.center j} := by
  intro p hp
  exact (eta_smoothAt j hp).contDiffWithinAt

theorem F_fderiv_smooth (j : Nat) :
    ContDiff ℝ ∞ (fun p : ℂ => fderiv ℝ (MirrorSmoothPotential.F j) p) := by
  exact (MirrorSmoothPotential.F_smooth j).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)

theorem omega_smoothAt (j : Nat) {p : ℂ}
    (hp : p ≠ MirrorGeometry.center j) :
    ContDiffAt ℝ ∞ (MirrorCutoffDifferential.omega j) p :=
  (eta_smoothAt j hp).sub (F_fderiv_smooth j).contDiffAt

theorem omega_smoothOn_punctured_plane (j : Nat) :
    ContDiffOn ℝ ∞ (MirrorCutoffDifferential.omega j)
      {p : ℂ | p ≠ MirrorGeometry.center j} := by
  intro p hp
  exact (omega_smoothAt j hp).contDiffWithinAt

theorem positive_center_not_mem_stage (j n : Nat) (hj : 1 ≤ j) :
    MirrorGeometry.center j ∉ MirrorGeometry.X n := by
  intro hp
  rcases (MirrorGeometry.mem_X n (MirrorGeometry.center j)).mp hp with ⟨hr, hd⟩
  by_cases hjn : j ≤ n
  · let i : Fin n := ⟨j - 1, by omega⟩
    have h := hd i
    have hi : i.val + 1 = j := by dsimp [i]; omega
    rw [hi, dist_self] at h
    have hpos : 0 < MirrorGeometry.rho j :=
      div_pos (MirrorGeometry.c_pos j) (by norm_num)
    linarith
  · have hbound : MirrorGeometry.c j ≤ MirrorGeometry.c (n + 1) :=
      MirrorGeometry.c_antitone (by omega)
    have hedge : MirrorGeometry.c (n + 1) < MirrorGeometry.a n := by
      have hgap := MirrorGeometry.next_disk_left_of_boundary n
      have hpos : 0 < MirrorGeometry.rho (n + 1) :=
        div_pos (MirrorGeometry.c_pos (n + 1)) (by norm_num)
      linarith
    have hleft : MirrorGeometry.a n < MirrorGeometry.c j := by
      simpa [MirrorGeometry.center] using hr.1
    linarith

theorem positive_center_not_mem_union (j : Nat) (hj : 1 ≤ j) :
    MirrorGeometry.center j ∉ MirrorGeometry.XInfinity := by
  intro hp
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
  exact (positive_center_not_mem_stage j (n + 1) hj) hn

theorem eta_smoothOn_union (j : Nat) (hj : 1 ≤ j) :
    ContDiffOn ℝ ∞ (MirrorPotentialDifferential.eta j) MirrorGeometry.XInfinity := by
  intro p hp
  have hne : p ≠ MirrorGeometry.center j := by
    intro he
    subst p
    exact (positive_center_not_mem_union j hj) hp
  exact (eta_smoothAt j hne).contDiffWithinAt

theorem omega_smoothOn_union (j : Nat) (hj : 1 ≤ j) :
    ContDiffOn ℝ ∞ (MirrorCutoffDifferential.omega j) MirrorGeometry.XInfinity := by
  intro p hp
  have hne : p ≠ MirrorGeometry.center j := by
    intro he
    subst p
    exact (positive_center_not_mem_union j hj) hp
  exact (omega_smoothAt j hne).contDiffWithinAt


end MirrorCovectorSmoothness

/- Arbitrary real coefficient sequences, with a uniform finite local cutoff.
   The total tsum outside XInfinity is not claimed convergent or geometric.
   On XInfinity it is an actual finite local sum of smooth real covectors.
   Closedness, marked periods and the de Rham quotient remain separate. -/
namespace MirrorLocalSynthesis
open scoped ContDiff Topology
open Set Filter

def weightedTerm (b : Nat → ℝ) (k : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  b (k + 1) • MirrorCutoffDifferential.omega (k + 1) p

def combined (b : Nat → ℝ) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  ∑' k : Nat, weightedTerm b k p

def patch (b : Nat → ℝ) (n : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  ∑ k ∈ Finset.range n, weightedTerm b k p

theorem omega_tail_zero_on_stage (j n : Nat) (hjn : n < j)
    {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    MirrorCutoffDifferential.omega j p = 0 := by
  have hhalf := MirrorGeometry.c_later_le_half hjn
  have hright : MirrorSmoothCutoff.right j < MirrorGeometry.a n := by
    dsimp [MirrorSmoothCutoff.right, MirrorGeometry.a]
    linarith [MirrorGeometry.c_pos n]
  have hleft := ((MirrorGeometry.mem_X n p).mp hp).1.1
  exact MirrorCutoffDifferential.omega_zero_right j (hright.trans hleft)

theorem weighted_tail_zero_on_stage (b : Nat → ℝ) (n k : Nat)
    (hk : n ≤ k) {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    weightedTerm b k p = 0 := by
  unfold weightedTerm
  rw [omega_tail_zero_on_stage (k + 1) n (by omega) hp, smul_zero]

theorem weighted_hasSum_on_stage (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    HasSum (fun k : Nat => weightedTerm b k p) (patch b n p) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  exact weighted_tail_zero_on_stage b n k
    (by simpa only [Finset.mem_range, not_lt] using hk) hp

theorem combined_eq_patch_on_stage (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    combined b p = patch b n p :=
  (weighted_hasSum_on_stage b n hp).tsum_eq

theorem patch_smoothAt_union (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    ContDiffAt ℝ ∞ (patch b n) p := by
  unfold patch
  apply ContDiffAt.sum
  intro k hk
  have hne : p ≠ MirrorGeometry.center (k + 1) := by
    intro he
    subst p
    exact (MirrorCovectorSmoothness.positive_center_not_mem_union (k + 1) (by omega)) hp
  exact ContDiffAt.const_smul (b (k + 1))
    (MirrorCovectorSmoothness.omega_smoothAt (k + 1) hne)

theorem combined_eventually_eq_patch (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    combined b =ᶠ[𝓝 p] patch b n :=
  Filter.mem_of_superset ((MirrorGeometry.stage_open n).mem_nhds hp)
    (fun q hq => combined_eq_patch_on_stage b n hq)

theorem combined_smoothAt_union (b : Nat → ℝ)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    ContDiffAt ℝ ∞ (combined b) p := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
  exact (patch_smoothAt_union b (n + 1) hp).congr_of_eventuallyEq
    (combined_eventually_eq_patch b (n + 1) hn)

theorem combined_smoothOn_union (b : Nat → ℝ) :
    ContDiffOn ℝ ∞ (combined b) MirrorGeometry.XInfinity := by
  intro p hp
  exact (combined_smoothAt_union b hp).contDiffWithinAt

theorem local_uniform_tail_zero {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    ∃ (n : Nat) (u : Set ℂ), IsOpen u ∧ p ∈ u ∧
      ∀ j : Nat, n < j → ∀ q ∈ u, MirrorCutoffDifferential.omega j q = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
  exact ⟨n + 1, MirrorGeometry.X (n + 1), MirrorGeometry.stage_open (n + 1), hn,
    fun j hj q hq => omega_tail_zero_on_stage j (n + 1) hj hq⟩


end MirrorLocalSynthesis

/- Native alternating one-forms and their exterior derivative.
   Local angular primitives cover both coordinate charts of the punctured plane.
   This does not compute marked periods or the de Rham quotient. -/
namespace MirrorExteriorClosedness
open Set Filter
open scoped Topology ContDiff

def liftCovector : (ℂ →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (ℂ [⋀^Fin 1]→L[ℝ] ℝ) :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)

def oneForm (a : ℂ → ℂ →L[ℝ] ℝ) (p : ℂ) : ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  liftCovector (a p)

def zeroForm (f : ℂ → ℝ) (p : ℂ) : ℂ [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ ℂ (Fin 0) (f p)

theorem exact_form_bridge (f : ℂ → ℝ) :
    extDeriv (zeroForm f) = oneForm (fderiv ℝ f) := by
  funext p
  exact extDeriv_constOfIsEmpty f p

theorem zeroForm_smoothAt {f : ℂ → ℝ} {p : ℂ}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (zeroForm f) p := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).contDiff.contDiffAt.comp p hf

theorem exact_form_closed {f : ℂ → ℝ} {p : ℂ}
    (hf : ContDiffAt ℝ ∞ f p) :
    extDeriv (oneForm (fderiv ℝ f)) p = 0 := by
  rw [← exact_form_bridge]
  exact extDeriv_extDeriv_apply (zeroForm_smoothAt hf) (by simp [minSmoothness])

theorem oneForm_smoothAt {a : ℂ → ℂ →L[ℝ] ℝ} {p : ℂ}
    (ha : ContDiffAt ℝ ∞ a p) : ContDiffAt ℝ ∞ (oneForm a) p := by
  exact liftCovector.contDiff.contDiffAt.comp p ha

theorem chain_eq_eta_off_vertical (j : Nat) {p : ℂ}
    (hp : p.re ≠ MirrorGeometry.c j) :
    MirrorPotentialDifferential.chainDerivative j p = MirrorPotentialDifferential.eta j p := by
  have hd : p.re - MirrorGeometry.c j ≠ 0 := sub_ne_zero.mpr hp
  have hquadratic : (p.re - MirrorGeometry.c j)^2 + p.im^2 ≠ 0 := by
    apply ne_of_gt
    linarith [sq_pos_of_ne_zero hd, sq_nonneg p.im]
  have hnorm : 2 * Real.pi ≠ 0 := ne_of_gt MirrorSmoothPotential.normalisation_pos
  have hunit : 1 + (p.im / (p.re - MirrorGeometry.c j))^2 ≠ 0 := by
    apply ne_of_gt
    linarith [sq_nonneg (p.im / (p.re - MirrorGeometry.c j))]
  unfold MirrorPotentialDifferential.chainDerivative MirrorPotentialDifferential.eta
  ext v
  simp only [smul_apply, add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  field_simp [hd, hquadratic, hnorm, hunit]

theorem horizontal_hasFDerivAt (j : Nat) {p : ℂ}
    (hp : p.re ≠ MirrorGeometry.c j) :
    HasFDerivAt (MirrorSmoothPotential.potential j) (MirrorPotentialDifferential.eta j p) p := by
  have hd : p.re - MirrorGeometry.c j ≠ 0 := sub_ne_zero.mpr hp
  have hre : HasFDerivAt (fun q : ℂ => q.re) Complex.reCLM p := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun q : ℂ => q.im) Complex.imCLM p := Complex.imCLM.hasFDerivAt
  have hden := hre.sub_const (MirrorGeometry.c j)
  have hinv : HasFDerivAt (fun q : ℂ => (q.re - MirrorGeometry.c j)⁻¹)
      ((-(((p.re - MirrorGeometry.c j)^2)⁻¹)) • Complex.reCLM) p := by
    convert! (hasDerivAt_inv hd).comp_hasFDerivAt p hden using 1 <;> simp [Function.comp_def]
  have hprod := him.mul hinv
  have hchain : HasFDerivAt (MirrorSmoothPotential.potential j)
      (MirrorPotentialDifferential.chainDerivative j p) p := by
    convert! hprod.arctan.mul_const ((2 * Real.pi)⁻¹) using 1 <;>
      simp [MirrorSmoothPotential.potential, MirrorPotentialDifferential.chainDerivative, div_eq_mul_inv]
  rw [chain_eq_eta_off_vertical j hp] at hchain
  exact hchain

def verticalPotential (j : Nat) (p : ℂ) : ℝ :=
  -(Real.arctan ((p.re - MirrorGeometry.c j) / p.im) / (2 * Real.pi))

def verticalChain (j : Nat) (p : ℂ) : ℂ →L[ℝ] ℝ :=
  -((2 * Real.pi)⁻¹ •
    ((1 / (1 + ((p.re - MirrorGeometry.c j) / p.im)^2)) •
      ((p.re - MirrorGeometry.c j) • ((-(p.im^2)⁻¹) • Complex.imCLM) +
        p.im⁻¹ • Complex.reCLM)))

theorem verticalChain_eq_eta (j : Nat) {p : ℂ} (hp : p.im ≠ 0) :
    verticalChain j p = MirrorPotentialDifferential.eta j p := by
  have hquadratic : (p.re - MirrorGeometry.c j)^2 + p.im^2 ≠ 0 := by
    apply ne_of_gt
    linarith [sq_nonneg (p.re - MirrorGeometry.c j), sq_pos_of_ne_zero hp]
  have hnorm : 2 * Real.pi ≠ 0 := ne_of_gt MirrorSmoothPotential.normalisation_pos
  have hunit : 1 + ((p.re - MirrorGeometry.c j) / p.im)^2 ≠ 0 := by
    apply ne_of_gt
    linarith [sq_nonneg ((p.re - MirrorGeometry.c j) / p.im)]
  unfold verticalChain MirrorPotentialDifferential.eta
  ext v
  simp only [neg_apply, smul_apply, add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  field_simp [hp, hquadratic, hnorm, hunit]
  <;> ring

theorem vertical_hasFDerivAt (j : Nat) {p : ℂ} (hp : p.im ≠ 0) :
    HasFDerivAt (verticalPotential j) (MirrorPotentialDifferential.eta j p) p := by
  have hre : HasFDerivAt (fun q : ℂ => q.re) Complex.reCLM p := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun q : ℂ => q.im) Complex.imCLM p := Complex.imCLM.hasFDerivAt
  have hdelta := hre.sub_const (MirrorGeometry.c j)
  have hinv : HasFDerivAt (fun q : ℂ => q.im⁻¹)
      ((-(p.im^2)⁻¹) • Complex.imCLM) p := by
    convert! (hasDerivAt_inv hp).comp_hasFDerivAt p him using 1 <;> simp [Function.comp_def]
  have hprod := hdelta.mul hinv
  have hchain : HasFDerivAt (verticalPotential j) (verticalChain j p) p := by
    convert! (hprod.arctan.mul_const ((2 * Real.pi)⁻¹)).neg using 1 <;>
      simp [verticalPotential, verticalChain, div_eq_mul_inv]
  rw [verticalChain_eq_eta j hp] at hchain
  exact hchain

theorem vertical_smoothAt (j : Nat) {p : ℂ} (hp : p.im ≠ 0) :
    ContDiffAt ℝ ∞ (verticalPotential j) p := by
  have hre : ContDiffAt ℝ ∞ (fun q : ℂ => q.re) p := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun q : ℂ => q.im) p := Complex.imCLM.contDiff.contDiffAt
  exact ((hre.sub contDiffAt_const).div him hp).arctan.div_const (2 * Real.pi) |>.neg

theorem eta_locally_exact (j : Nat) {p : ℂ} (hp : p ≠ MirrorGeometry.center j) :
    ∃ f : ℂ → ℝ, ContDiffAt ℝ ∞ f p ∧
      oneForm (MirrorPotentialDifferential.eta j) =ᶠ[𝓝 p] oneForm (fderiv ℝ f) := by
  by_cases hx : p.re ≠ MirrorGeometry.c j
  · refine ⟨MirrorSmoothPotential.potential j, MirrorSmoothPotential.potential_smoothAt j hx, ?_⟩
    have he := Complex.continuous_re.continuousAt.eventually_ne hx
    filter_upwards [he] with q hq
    unfold oneForm
    rw [(horizontal_hasFDerivAt j hq).fderiv]
  · have hy : p.im ≠ 0 := by
      intro hy
      apply hp
      apply Complex.ext
      · simpa [MirrorGeometry.center] using not_ne_iff.mp hx
      · simpa [MirrorGeometry.center] using hy
    refine ⟨verticalPotential j, vertical_smoothAt j hy, ?_⟩
    have he := Complex.continuous_im.continuousAt.eventually_ne hy
    filter_upwards [he] with q hq
    unfold oneForm
    rw [(vertical_hasFDerivAt j hq).fderiv]

theorem eta_closed (j : Nat) {p : ℂ} (hp : p ≠ MirrorGeometry.center j) :
    extDeriv (oneForm (MirrorPotentialDifferential.eta j)) p = 0 := by
  obtain ⟨f, hf, he⟩ := eta_locally_exact j hp
  rw [he.extDeriv_eq]
  exact exact_form_closed hf

theorem cutoff_exact_form_closed (j : Nat) (p : ℂ) :
    extDeriv (oneForm (fderiv ℝ (MirrorSmoothPotential.F j))) p = 0 :=
  exact_form_closed (MirrorSmoothPotential.F_smooth j).contDiffAt

theorem omega_closed (j : Nat) {p : ℂ} (hp : p ≠ MirrorGeometry.center j) :
    extDeriv (oneForm (MirrorCutoffDifferential.omega j)) p = 0 := by
  have heq : oneForm (MirrorCutoffDifferential.omega j) =
      (fun q => oneForm (MirrorPotentialDifferential.eta j) q +
        (-1 : ℝ) • oneForm (fderiv ℝ (MirrorSmoothPotential.F j)) q) := by
    funext q
    change liftCovector (MirrorPotentialDifferential.eta j q - fderiv ℝ (MirrorSmoothPotential.F j) q) =
      liftCovector (MirrorPotentialDifferential.eta j q) +
        (-1 : ℝ) • liftCovector (fderiv ℝ (MirrorSmoothPotential.F j) q)
    calc
      liftCovector (MirrorPotentialDifferential.eta j q - fderiv ℝ (MirrorSmoothPotential.F j) q) =
        liftCovector (MirrorPotentialDifferential.eta j q) -
          liftCovector (fderiv ℝ (MirrorSmoothPotential.F j) q) := liftCovector.map_sub _ _
      _ = liftCovector (MirrorPotentialDifferential.eta j q) +
          (-1 : ℝ) • liftCovector (fderiv ℝ (MirrorSmoothPotential.F j) q) := by
        rw [sub_eq_add_neg]
        exact congrArg (fun z => liftCovector (MirrorPotentialDifferential.eta j q) + z)
          (neg_one_smul ℝ (liftCovector (fderiv ℝ (MirrorSmoothPotential.F j) q))).symm
  rw [heq, extDeriv_fun_add
    ((oneForm_smoothAt (MirrorCovectorSmoothness.eta_smoothAt j hp)).differentiableAt (by simp))
    (((oneForm_smoothAt (MirrorCovectorSmoothness.F_fderiv_smooth j).contDiffAt).const_smul (-1 : ℝ)).differentiableAt (by simp))]
  have hs : extDeriv (fun q => (-1 : ℝ) • oneForm (fderiv ℝ (MirrorSmoothPotential.F j)) q) p =
      (-1 : ℝ) • extDeriv (oneForm (fderiv ℝ (MirrorSmoothPotential.F j))) p :=
    extDeriv_fun_smul (-1 : ℝ) _
  rw [hs, eta_closed j hp, cutoff_exact_form_closed j p]
  simp

theorem omega_closed_on_union (j : Nat) (hj : 1 ≤ j) :
    ∀ p ∈ MirrorGeometry.XInfinity, extDeriv (oneForm (MirrorCutoffDifferential.omega j)) p = 0 := by
  intro p hp
  apply omega_closed j
  intro he
  subst p
  exact (MirrorCovectorSmoothness.positive_center_not_mem_union j hj) hp


end MirrorExteriorClosedness


/- Native closedness of the actual finite patches and locally finite combined form.
   No differentiation of an arbitrary convergent infinite series is assumed.
   Marked periods, global exactness and the quotient remain separate. -/
namespace MirrorCombinedClosedness
open Set Filter MirrorExteriorClosedness
open scoped Topology ContDiff

theorem weighted_oneForm (b : Nat → ℝ) (k : Nat) :
    oneForm (MirrorLocalSynthesis.weightedTerm b k) =
      b (k + 1) • oneForm (MirrorCutoffDifferential.omega (k + 1)) := by
  funext q
  exact liftCovector.map_smul (b (k + 1)) (MirrorCutoffDifferential.omega (k + 1) q)

theorem weighted_form_smoothAt_union (b : Nat → ℝ) (k : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    ContDiffAt ℝ ∞ (oneForm (MirrorLocalSynthesis.weightedTerm b k)) p := by
  have hne : p ≠ MirrorGeometry.center (k + 1) := by
    intro he
    subst p
    exact (MirrorCovectorSmoothness.positive_center_not_mem_union (k + 1) (by omega)) hp
  apply oneForm_smoothAt
  exact ContDiffAt.const_smul (b (k + 1))
    (MirrorCovectorSmoothness.omega_smoothAt (k + 1) hne)

theorem weighted_form_closed_union (b : Nat → ℝ) (k : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    extDeriv (oneForm (MirrorLocalSynthesis.weightedTerm b k)) p = 0 := by
  rw [weighted_oneForm, extDeriv_smul,
    omega_closed_on_union (k + 1) (by omega) p hp, smul_zero]

theorem patch_form_succ (b : Nat → ℝ) (n : Nat) :
    oneForm (MirrorLocalSynthesis.patch b (n + 1)) =
      (fun q => oneForm (MirrorLocalSynthesis.patch b n) q +
        oneForm (MirrorLocalSynthesis.weightedTerm b n) q) := by
  funext q
  simp only [oneForm, MirrorLocalSynthesis.patch, Finset.sum_range_succ]
  exact liftCovector.map_add _ _

theorem patch_closed_union (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    extDeriv (oneForm (MirrorLocalSynthesis.patch b n)) p = 0 := by
  induction n with
  | zero =>
      have heq : oneForm (MirrorLocalSynthesis.patch b 0) =
          (fun _ : ℂ => (0 : ℂ [⋀^Fin 1]→L[ℝ] ℝ)) := by
        funext q
        simp [oneForm, MirrorLocalSynthesis.patch]
      rw [heq]
      simp [extDeriv]
      exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ ℂ ℝ).map_zero
  | succ n ih =>
      rw [patch_form_succ, extDeriv_fun_add
        ((oneForm_smoothAt (MirrorLocalSynthesis.patch_smoothAt_union b n hp)).differentiableAt (by simp))
        ((weighted_form_smoothAt_union b n hp).differentiableAt (by simp))]
      rw [ih, weighted_form_closed_union b n hp]
      simp

theorem combined_form_eventually_eq_patch (b : Nat → ℝ) (n : Nat)
    {p : ℂ} (hp : p ∈ MirrorGeometry.X n) :
    oneForm (MirrorLocalSynthesis.combined b) =ᶠ[𝓝 p]
      oneForm (MirrorLocalSynthesis.patch b n) :=
  (MirrorLocalSynthesis.combined_eventually_eq_patch b n hp).mono
    (fun q hq => congrArg liftCovector hq)

theorem combined_closed_union (b : Nat → ℝ)
    {p : ℂ} (hp : p ∈ MirrorGeometry.XInfinity) :
    extDeriv (oneForm (MirrorLocalSynthesis.combined b)) p = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
  rw [(combined_form_eventually_eq_patch b (n + 1) hn).extDeriv_eq]
  exact patch_closed_union b (n + 1) hp


end MirrorCombinedClosedness

/- Actual positively parametrised marked loop and diagonal native real curve integral.
   Off-diagonal periods, arbitrary combined periods and the de Rham quotient remain separate. -/
namespace MirrorMarkedLoopDiagonal
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorPotentialDifferential MirrorCovectorSmoothness

def param (j : Nat) (t : ℝ) : ℂ :=
  circleMap (center j) (loopRadius j) (2 * Real.pi * t)

def velocity (j : Nat) (t : ℝ) : ℂ :=
  (2 * Real.pi) • (circleMap 0 (loopRadius j) (2 * Real.pi * t) * Complex.I)

theorem loopRadius_pos (j : Nat) : 0 < loopRadius j := by
  dsimp [loopRadius]
  linarith [c_pos j]

theorem param_mem_circle (j : Nat) (t : ℝ) : param j t ∈ markedCircle j := by
  exact circleMap_mem_sphere (center j) (loopRadius_pos j).le (2 * Real.pi * t)

theorem param_mem_stage (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) (t : ℝ) :
    param j t ∈ X n :=
  marked_circle_inside_stage n j hj hjn (param_mem_circle j t)

theorem param_mem_union (j : Nat) (hj : 1 ≤ j) (t : ℝ) : param j t ∈ XInfinity := by
  cases j with
  | zero => omega
  | succ k =>
      exact Set.mem_iUnion.mpr ⟨k, param_mem_stage (k + 1) (k + 1) hj (by omega) t⟩

theorem param_smooth (j : Nat) : ContDiff ℝ ∞ (param j) :=
  (contDiff_circleMap (center j) (loopRadius j)).comp (contDiff_const.mul contDiff_id)

theorem param_endpoints (j : Nat) : param j 1 = param j 0 := by
  simpa [param] using periodic_circleMap (center j) (loopRadius j) 0

theorem param_hasDerivAt (j : Nat) (t : ℝ) : HasDerivAt (param j) (velocity j t) t := by
  have hscale : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  unfold param velocity
  exact (hasDerivAt_circleMap (center j) (loopRadius j) (2 * Real.pi * t)).scomp t hscale

theorem eta_rotated_radius (j : Nat) {p : ℂ} (hp : p ≠ center j) :
    eta j p ((p - center j) * Complex.I) = (2 * Real.pi)⁻¹ := by
  have hq := quadratic_pos_off_center j hp
  simp only [eta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    MirrorGeometry.center, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [ne_of_gt hq, Real.pi_ne_zero]
  <;> ring

theorem eta_velocity_one (j : Nat) (t : ℝ) : eta j (param j t) (velocity j t) = 1 := by
  have hp : param j t ≠ center j :=
    circleMap_ne_center (ne_of_gt (loopRadius_pos j))
  have heq : circleMap 0 (loopRadius j) (2 * Real.pi * t) = param j t - center j :=
    (circleMap_sub_center (center j) (loopRadius j) (2 * Real.pi * t)).symm
  rw [velocity, heq, map_smul, eta_rotated_radius j hp]
  change (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1
  exact mul_inv_cancel₀ (ne_of_gt MirrorSmoothPotential.normalisation_pos)

theorem param_re_lt_left (j : Nat) (t : ℝ) :
    (param j t).re < MirrorSmoothCutoff.left j := by
  have hd : dist (param j t) (center j) = loopRadius j := param_mem_circle j t
  have hbound := real_coordinate_bound (param j t) j
  rw [hd] at hbound
  have habs := le_abs_self ((param j t).re - c j)
  dsimp [MirrorSmoothCutoff.left, loopRadius] at *
  linarith [c_pos j]

theorem omega_eq_eta_on_param (j : Nat) (t : ℝ) :
    MirrorCutoffDifferential.omega j (param j t) = eta j (param j t) := by
  have hd := (MirrorCutoffDifferential.F_hasFDerivAt_zero_left j (param_re_lt_left j t)).fderiv
  simp only [MirrorCutoffDifferential.omega, hd, sub_zero]

theorem omega_velocity_one (j : Nat) (t : ℝ) :
    MirrorCutoffDifferential.omega j (param j t) (velocity j t) = 1 := by
  rw [omega_eq_eta_on_param]
  exact eta_velocity_one j t

def markedPath (j : Nat) : Path (param j 0) (param j 0) :=
  Path.ofLine (param_smooth j).continuous.continuousOn rfl (param_endpoints j)

theorem path_extend_eq (j : Nat) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (markedPath j).extend t = param j t := by
  rw [Path.extend_apply _ ht]
  rfl

theorem path_range_inside_union (j : Nat) (hj : 1 ≤ j) :
    Set.range (fun t : unitInterval => markedPath j t) ⊆ XInfinity := by
  rintro p ⟨t, rfl⟩
  exact param_mem_union j hj (t : ℝ)

theorem path_derivWithin (j : Nat) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (markedPath j).extend (Icc (0 : ℝ) 1) t = velocity j t := by
  have hd : HasDerivWithinAt (markedPath j).extend (velocity j t) (Icc (0 : ℝ) 1) t :=
    (param_hasDerivAt j t).hasDerivWithinAt.congr_of_mem
      (fun u hu => path_extend_eq j hu) ht
  exact hd.derivWithin ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) t ht)

theorem eta_curveIntegralFun_one (j : Nat) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (eta j) (markedPath j) t = 1 := by
  rw [curveIntegralFun_def, path_extend_eq j ht, path_derivWithin j ht]
  exact eta_velocity_one j t

theorem omega_curveIntegralFun_one (j : Nat) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (MirrorCutoffDifferential.omega j) (markedPath j) t = 1 := by
  rw [curveIntegralFun_def, path_extend_eq j ht, path_derivWithin j ht]
  exact omega_velocity_one j t

theorem eta_curveIntegrable (j : Nat) : CurveIntegrable (eta j) (markedPath j) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo (g := fun _ : ℝ => (1 : ℝ)) ?_).mpr
  · exact intervalIntegrable_const
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact eta_curveIntegralFun_one j ⟨ht.1.le, ht.2.le⟩

theorem omega_curveIntegrable (j : Nat) :
    CurveIntegrable (MirrorCutoffDifferential.omega j) (markedPath j) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo (g := fun _ : ℝ => (1 : ℝ)) ?_).mpr
  · exact intervalIntegrable_const
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact omega_curveIntegralFun_one j ⟨ht.1.le, ht.2.le⟩

theorem eta_period_one (j : Nat) : curveIntegral (eta j) (markedPath j) = 1 := by
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun (eta j) (markedPath j) t) =
        ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact eta_curveIntegralFun_one j ht
    _ = 1 := by simp

theorem omega_period_one (j : Nat) :
    curveIntegral (MirrorCutoffDifferential.omega j) (markedPath j) = 1 := by
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun (MirrorCutoffDifferential.omega j) (markedPath j) t) =
        ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact omega_curveIntegralFun_one j ht
    _ = 1 := by simp


end MirrorMarkedLoopDiagonal

/- Actual separated-circle real periods. Local charts only, explicit integrability.
   Positive indices supply the open-union interpretation; index0 is auxiliary. -/
namespace MirrorOffDiagonalPeriods
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorMarkedLoopDiagonal MirrorPotentialDifferential

 theorem param_re_upper (i : Nat) (t : ℝ) :
    (param i t).re ≤ c i + loopRadius i := by
  have hd : dist (param i t) (center i) = loopRadius i := param_mem_circle i t
  have hb := real_coordinate_bound (param i t) i
  rw [hd] at hb
  linarith [le_abs_self ((param i t).re - c i)]

 theorem param_re_lower (i : Nat) (t : ℝ) :
    c i - loopRadius i ≤ (param i t).re := by
  have hd : dist (param i t) (center i) = loopRadius i := param_mem_circle i t
  have hb := real_coordinate_bound (param i t) i
  rw [hd] at hb
  linarith [neg_le_abs ((param i t).re - c i)]

 theorem later_circle_left (i j : Nat) (hji : j < i) (t : ℝ) :
    (param i t).re < c j := by
  have hu := param_re_upper i t
  have hh := c_later_le_half hji
  dsimp [loopRadius] at hu
  linarith [c_pos j]

 theorem earlier_circle_right (i j : Nat) (hij : i < j) (t : ℝ) :
    MirrorSmoothCutoff.right j < (param i t).re := by
  have hl := param_re_lower i t
  have hh := c_later_le_half hij
  dsimp [loopRadius] at hl
  dsimp [MirrorSmoothCutoff.right]
  linarith [c_pos i]

 theorem omega_zero_earlier (i j : Nat) (hij : i < j) (t : ℝ) :
    MirrorCutoffDifferential.omega j (param i t) = 0 :=
  MirrorCutoffDifferential.omega_zero_right j (earlier_circle_right i j hij t)

 theorem omega_curveFun_zero_earlier (i j : Nat) (hij : i < j)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (MirrorCutoffDifferential.omega j) (markedPath i) t = 0 := by
  rw [curveIntegralFun_def, path_extend_eq i ht, path_derivWithin i ht,
    omega_zero_earlier i j hij]
  simp

 theorem omega_integrable_earlier (i j : Nat) (hij : i < j) :
    CurveIntegrable (MirrorCutoffDifferential.omega j) (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo (g := fun _ : ℝ => (0 : ℝ)) ?_).mpr
  · exact intervalIntegrable_const
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact omega_curveFun_zero_earlier i j hij ⟨ht.1.le, ht.2.le⟩

 theorem omega_period_zero_earlier (i j : Nat) (hij : i < j) :
    curveIntegral (MirrorCutoffDifferential.omega j) (markedPath i) = 0 := by
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun
        (MirrorCutoffDifferential.omega j) (markedPath i) t) =
        ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact omega_curveFun_zero_earlier i j hij ht
    _ = 0 := by simp

 theorem omega_eq_eta_later (i j : Nat) (hji : j < i) (t : ℝ) :
    MirrorCutoffDifferential.omega j (param i t) = eta j (param i t) :=
  MirrorCutoffDifferential.omega_eq_eta_on_closed_left j (later_circle_left i j hji t).le

 theorem potential_path_hasDerivAt (i j : Nat) (hji : j < i) (t : ℝ) :
    HasDerivAt (fun u : ℝ => MirrorSmoothPotential.potential j (param i u))
      (eta j (param i t) (velocity i t)) t := by
  exact (MirrorExteriorClosedness.horizontal_hasFDerivAt j
    (ne_of_lt (later_circle_left i j hji t))).comp_hasDerivAt t (param_hasDerivAt i t)

 theorem velocity_continuous (i : Nat) : Continuous (velocity i) := by
  unfold velocity
  have hbase : ContDiff ℝ ∞ (circleMap (0 : ℂ) (loopRadius i)) :=
    contDiff_circleMap (0 : ℂ) (loopRadius i)
  have hc : Continuous (fun t : ℝ =>
      circleMap (0 : ℂ) (loopRadius i) (2 * Real.pi * t)) :=
    hbase.continuous.comp (continuous_const.mul continuous_id)
  exact (continuous_const : Continuous (fun _ : ℝ => (2 * Real.pi : ℝ))).smul
    (hc.mul continuous_const)

 theorem eta_pullback_continuous_later (i j : Nat) (hji : j < i) :
    Continuous (fun t : ℝ => eta j (param i t) (velocity i t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne : param i t ≠ center j := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [MirrorGeometry.center, Complex.ofReal_re] at hre
    linarith [later_circle_left i j hji t]
  have hf : ContinuousAt (fun u : ℝ => eta j (param i u)) t :=
    (MirrorCovectorSmoothness.eta_smoothAt j hne).continuousAt.comp
      (param_smooth i).continuous.continuousAt
  exact hf.clm_apply (velocity_continuous i).continuousAt

 theorem eta_pullback_integrable_later (i j : Nat) (hji : j < i) :
    IntervalIntegrable (fun t : ℝ => eta j (param i t) (velocity i t)) volume 0 1 :=
  (eta_pullback_continuous_later i j hji).intervalIntegrable 0 1

 theorem omega_curveFun_pullback_later (i j : Nat) (hji : j < i)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (MirrorCutoffDifferential.omega j) (markedPath i) t =
      eta j (param i t) (velocity i t) := by
  rw [curveIntegralFun_def, path_extend_eq i ht, path_derivWithin i ht,
    omega_eq_eta_later i j hji]

 theorem omega_integrable_later (i j : Nat) (hji : j < i) :
    CurveIntegrable (MirrorCutoffDifferential.omega j) (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => eta j (param i t) (velocity i t)) ?_).mpr
  · exact eta_pullback_integrable_later i j hji
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact omega_curveFun_pullback_later i j hji ⟨ht.1.le, ht.2.le⟩

 theorem omega_period_zero_later (i j : Nat) (hji : j < i) :
    curveIntegral (MirrorCutoffDifferential.omega j) (markedPath i) = 0 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => MirrorSmoothPotential.potential j (param i t))
    (f' := fun t : ℝ => eta j (param i t) (velocity i t))
    (fun t _ => potential_path_hasDerivAt i j hji t)
    (eta_pullback_integrable_later i j hji)
  rw [param_endpoints i, sub_self] at hFTC
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun
        (MirrorCutoffDifferential.omega j) (markedPath i) t) =
        ∫ t in (0 : ℝ)..1, eta j (param i t) (velocity i t) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact omega_curveFun_pullback_later i j hji ht
    _ = 0 := hFTC

 theorem omega_integrable_all (i j : Nat) :
    CurveIntegrable (MirrorCutoffDifferential.omega j) (markedPath i) := by
  rcases lt_trichotomy i j with hij | heq | hji
  · exact omega_integrable_earlier i j hij
  · subst j
    exact omega_curveIntegrable i
  · exact omega_integrable_later i j hji

 theorem omega_period_matrix (i j : Nat) :
    curveIntegral (MirrorCutoffDifferential.omega j) (markedPath i) =
      if i = j then 1 else 0 := by
  rcases lt_trichotomy i j with hij | heq | hji
  · rw [if_neg (ne_of_lt hij)]
    exact omega_period_zero_earlier i j hij
  · subst j
    simp only [ite_true]
    exact omega_period_one i
  · rw [if_neg (ne_of_gt hji)]
    exact omega_period_zero_later i j hji

end MirrorOffDiagonalPeriods

/- Prescribed periods of the actual locally finite combined field.
   Transfer is on an entire marked path inside one finite stage.
   No infinite integral interchange or global zero-period exactness is assumed. -/
namespace MirrorCombinedPeriods
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorLocalSynthesis MirrorMarkedLoopDiagonal MirrorOffDiagonalPeriods

theorem weighted_function_eq_smul (b : Nat → ℝ) (k : Nat) :
    weightedTerm b k =
      b (k + 1) • MirrorCutoffDifferential.omega (k + 1) := rfl

theorem weighted_integrable (b : Nat → ℝ) (k i : Nat) :
    CurveIntegrable (weightedTerm b k) (markedPath i) := by
  rw [weighted_function_eq_smul]
  exact (omega_integrable_all i (k + 1)).smul

theorem weighted_period (b : Nat → ℝ) (k i : Nat) :
    curveIntegral (weightedTerm b k) (markedPath i) =
      b (k + 1) * (if i = k + 1 then 1 else 0) := by
  rw [weighted_function_eq_smul, curveIntegral_smul, omega_period_matrix]
  rfl

theorem patch_function_zero (b : Nat → ℝ) : patch b 0 = 0 := by
  funext p
  simp [patch]

theorem patch_function_succ (b : Nat → ℝ) (n : Nat) :
    patch b (n + 1) = patch b n + weightedTerm b n := by
  funext p
  simp only [patch, Finset.sum_range_succ, Pi.add_apply]

theorem patch_integrable (b : Nat → ℝ) (n i : Nat) :
    CurveIntegrable (patch b n) (markedPath i) := by
  induction n with
  | zero =>
      rw [patch_function_zero]
      exact CurveIntegrable.zero
  | succ n ih =>
      rw [patch_function_succ]
      exact ih.add (weighted_integrable b n i)

theorem patch_period_sum (b : Nat → ℝ) (n i : Nat) :
    curveIntegral (patch b n) (markedPath i) =
      ∑ k ∈ Finset.range n, b (k + 1) * (if i = k + 1 then 1 else 0) := by
  induction n with
  | zero =>
      simp [patch_function_zero]
  | succ n ih =>
      rw [patch_function_succ,
        curveIntegral_add (patch_integrable b n i) (weighted_integrable b n i),
        ih, Finset.sum_range_succ, weighted_period]

theorem patch_period_own (b : Nat → ℝ) (n i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    curveIntegral (patch b n) (markedPath i) = b i := by
  rw [patch_period_sum]
  have hm : i - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hs : i - 1 + 1 = i := by omega
  rw [Finset.sum_eq_single (i - 1)]
  · simp [hs]
  · intro k hk hki
    have hne : i ≠ k + 1 := by omega
    simp [hne]
  · intro hnot
    exact False.elim (hnot hm)

theorem combined_curveFun_eq_patch (b : Nat → ℝ) (i : Nat) (hi : 1 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (combined b) (markedPath i) t =
      curveIntegralFun (patch b i) (markedPath i) t := by
  simp only [curveIntegralFun_def, path_extend_eq i ht]
  rw [combined_eq_patch_on_stage b i (param_mem_stage i i hi le_rfl t)]

theorem combined_integrable (b : Nat → ℝ) (i : Nat) (hi : 1 ≤ i) :
    CurveIntegrable (combined b) (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := curveIntegralFun (patch b i) (markedPath i)) ?_).mpr
  · exact patch_integrable b i i
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact combined_curveFun_eq_patch b i hi ⟨ht.1.le, ht.2.le⟩

theorem combined_period (b : Nat → ℝ) (i : Nat) (hi : 1 ≤ i) :
    curveIntegral (combined b) (markedPath i) = b i := by
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun (combined b) (markedPath i) t) =
        ∫ t in (0 : ℝ)..1, curveIntegralFun (patch b i) (markedPath i) t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact combined_curveFun_eq_patch b i hi ht
    _ = b i := by
      simpa only [curveIntegral_def] using patch_period_own b i i hi le_rfl

theorem arbitrary_marked_periods_realised (b : Nat → ℝ) :
    ∃ w : ℂ → ℂ →L[ℝ] ℝ,
      ContDiffOn ℝ ∞ w XInfinity ∧
      (∀ p ∈ XInfinity, extDeriv (MirrorExteriorClosedness.oneForm w) p = 0) ∧
      (∀ i : Nat, 1 ≤ i →
        CurveIntegrable w (markedPath i) ∧ curveIntegral w (markedPath i) = b i) := by
  refine ⟨combined b, combined_smoothOn_union b, ?_, ?_⟩
  · intro p hp
    exact MirrorCombinedClosedness.combined_closed_union b hp
  · intro i hi
    exact ⟨combined_integrable b i hi, combined_period b i hi⟩

end MirrorCombinedPeriods

namespace MirrorExactPeriods
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorMarkedLoopDiagonal MirrorOffDiagonalPeriods

/-- Smooth scalar potential only on the actual open union. -/
theorem scalar_smoothAt_union (g : ℂ → ℝ) (hg : ContDiffOn ℝ ∞ g XInfinity)
    {p : ℂ} (hp : p ∈ XInfinity) : ContDiffAt ℝ ∞ g p :=
  hg.contDiffAt (union_open.mem_nhds hp)

/-- The chain derivative is real, along the actual positive marked circle. -/
theorem scalar_path_hasDerivAt (g : ℂ → ℝ) (hg : ContDiffOn ℝ ∞ g XInfinity)
    (i : Nat) (hi : 1 ≤ i) (t : ℝ) :
    HasDerivAt (fun u => g (param i u))
      ((fderiv ℝ g (param i t)) (velocity i t)) t := by
  have hd : DifferentiableAt ℝ g (param i t) :=
    (scalar_smoothAt_union g hg (param_mem_union i hi t)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (param_hasDerivAt i t)

/-- No regularity of g outside the union is used. -/
theorem gradient_pullback_continuous (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g XInfinity) (i : Nat) (hi : 1 ≤ i) :
    Continuous (fun t : ℝ => (fderiv ℝ g (param i t)) (velocity i t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ g) (param i t) :=
    (scalar_smoothAt_union g hg (param_mem_union i hi t)).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have hc : ContinuousAt (fun u : ℝ => fderiv ℝ g (param i u)) t :=
    hdf.continuousAt.comp (param_smooth i).continuous.continuousAt
  exact hc.clm_apply (velocity_continuous i).continuousAt

/-- Actual curve integrand equality includes both endpoints. -/
theorem gradient_curveFun_eq (g : ℂ → ℝ) (i : Nat)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (fderiv ℝ g) (markedPath i) t =
      (fderiv ℝ g (param i t)) (velocity i t) := by
  rw [curveIntegralFun_def, path_extend_eq i ht, path_derivWithin i ht]

theorem gradient_integrable (g : ℂ → ℝ) (hg : ContDiffOn ℝ ∞ g XInfinity)
    (i : Nat) (hi : 1 ≤ i) : CurveIntegrable (fderiv ℝ g) (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => (fderiv ℝ g (param i t)) (velocity i t)) ?_).mpr
  · exact (gradient_pullback_continuous g hg i hi).intervalIntegrable 0 1
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact gradient_curveFun_eq g i ⟨ht.1.le, ht.2.le⟩

/-- Exact smooth differentials have zero actual marked-loop period. -/
theorem gradient_period_zero (g : ℂ → ℝ) (hg : ContDiffOn ℝ ∞ g XInfinity)
    (i : Nat) (hi : 1 ≤ i) : curveIntegral (fderiv ℝ g) (markedPath i) = 0 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := fun t => g (param i t))
    (f' := fun t => (fderiv ℝ g (param i t)) (velocity i t))
    (fun t _ => scalar_path_hasDerivAt g hg i hi t)
    ((gradient_pullback_continuous g hg i hi).intervalIntegrable 0 1)
  rw [param_endpoints i, sub_self] at hFTC
  rw [curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1, curveIntegralFun (fderiv ℝ g) (markedPath i) t) =
        ∫ t in (0 : ℝ)..1, (fderiv ℝ g (param i t)) (velocity i t) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact gradient_curveFun_eq g i ht
    _ = 0 := hFTC

theorem period_add_gradient_eq (w : ℂ → ℂ →L[ℝ] ℝ) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g XInfinity) (i : Nat) (hi : 1 ≤ i)
    (hw : CurveIntegrable w (markedPath i)) :
    curveIntegral (fun p => w p + fderiv ℝ g p) (markedPath i) =
      curveIntegral w (markedPath i) := by
  rw [curveIntegral_fun_add hw (gradient_integrable g hg i hi),
    gradient_period_zero g hg i hi, add_zero]

/-- Exact difference is required only on the union, along the entire marked path. -/
theorem period_of_exact_difference_on_union
    (w v : ℂ → ℂ →L[ℝ] ℝ) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g XInfinity) (i : Nat) (hi : 1 ≤ i)
    (hw : CurveIntegrable w (markedPath i))
    (he : ∀ p ∈ XInfinity, v p = w p + fderiv ℝ g p) :
    CurveIntegrable v (markedPath i) ∧
      curveIntegral v (markedPath i) = curveIntegral w (markedPath i) := by
  have hEq : ∀ t ∈ Icc (0 : ℝ) 1,
      curveIntegralFun v (markedPath i) t =
        curveIntegralFun (fun p => w p + fderiv ℝ g p) (markedPath i) t := by
    intro t ht
    simp only [curveIntegralFun_def, path_extend_eq i ht]
    rw [he (param i t) (param_mem_union i hi t)]
  constructor
  · unfold CurveIntegrable
    apply (intervalIntegrable_congr_uIoo
      (g := curveIntegralFun (fun p => w p + fderiv ℝ g p) (markedPath i)) ?_).mpr
    · exact hw.add (gradient_integrable g hg i hi)
    · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact hEq t ⟨ht.1.le, ht.2.le⟩
  · calc
      curveIntegral v (markedPath i) =
          curveIntegral (fun p => w p + fderiv ℝ g p) (markedPath i) := by
        simp only [curveIntegral_def]
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hEq
      _ = curveIntegral w (markedPath i) := period_add_gradient_eq w g hg i hi hw

end MirrorExactPeriods

namespace MirrorPeriodQuotient
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorMarkedLoopDiagonal MirrorOffDiagonalPeriods MirrorExactPeriods

/-- Actual smooth native-closed covectors on the union; outside values are not constrained. -/
structure ClosedField where
  value : ℂ → ℂ →L[ℝ] ℝ
  smooth : ContDiffOn ℝ ∞ value XInfinity
  closed : ∀ p ∈ XInfinity, extDeriv (MirrorExteriorClosedness.oneForm value) p = 0

abbrev PositiveIndex := {i : Nat // 1 ≤ i}

theorem field_curveFun_eq (w : ℂ → ℂ →L[ℝ] ℝ) (i : Nat)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun w (markedPath i) t = w (param i t) (velocity i t) := by
  rw [curveIntegralFun_def, path_extend_eq i ht, path_derivWithin i ht]

theorem field_pullback_continuous (w : ℂ → ℂ →L[ℝ] ℝ)
    (hw : ContDiffOn ℝ ∞ w XInfinity) (i : Nat) (hi : 1 ≤ i) :
    Continuous (fun t : ℝ => w (param i t) (velocity i t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : ContinuousAt (fun u : ℝ => w (param i u)) t :=
    (hw.contDiffAt (union_open.mem_nhds (param_mem_union i hi t))).continuousAt.comp
      (param_smooth i).continuous.continuousAt
  exact hc.clm_apply (velocity_continuous i).continuousAt

theorem smooth_field_integrable (w : ℂ → ℂ →L[ℝ] ℝ)
    (hw : ContDiffOn ℝ ∞ w XInfinity) (i : Nat) (hi : 1 ≤ i) :
    CurveIntegrable w (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => w (param i t) (velocity i t)) ?_).mpr
  · exact (field_pullback_continuous w hw i hi).intervalIntegrable 0 1
  · rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact field_curveFun_eq w i ⟨ht.1.le, ht.2.le⟩

/-- Equality modulo a smooth exact difference, only on the open union. -/
def ExactRel (u v : ClosedField) : Prop :=
  ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g XInfinity ∧
    ∀ p ∈ XInfinity, v.value p = u.value p + fderiv ℝ g p

theorem exactRel_refl (u : ClosedField) : ExactRel u u := by
  refine ⟨fun _ : ℂ => (0 : ℝ), contDiff_const.contDiffOn, ?_⟩
  intro p hp
  simp

theorem exactRel_symm {u v : ClosedField} (h : ExactRel u v) : ExactRel v u := by
  rcases h with ⟨g, hg, he⟩
  refine ⟨fun p => -g p, hg.neg, ?_⟩
  intro p hp
  rw [fderiv_fun_neg, he p hp]
  simp

theorem exactRel_trans {u v w : ClosedField} (huv : ExactRel u v)
    (hvw : ExactRel v w) : ExactRel u w := by
  rcases huv with ⟨g, hg, he⟩
  rcases hvw with ⟨h, hh, hf⟩
  refine ⟨fun p => g p + h p, hg.add hh, ?_⟩
  intro p hp
  have hdg : DifferentiableAt ℝ g p :=
    (scalar_smoothAt_union g hg hp).differentiableAt (by simp)
  have hdh : DifferentiableAt ℝ h p :=
    (scalar_smoothAt_union h hh hp).differentiableAt (by simp)
  rw [fderiv_fun_add hdg hdh, hf p hp, he p hp]
  exact add_assoc _ _ _

theorem exactRel_equivalence : Equivalence ExactRel :=
  ⟨exactRel_refl, fun h => exactRel_symm h, fun h₁ h₂ => exactRel_trans h₁ h₂⟩

def exactSetoid : Setoid ClosedField where
  r := ExactRel
  iseqv := exactRel_equivalence

abbrev FieldQuotient := Quotient exactSetoid

def periods (u : ClosedField) : PositiveIndex → ℝ :=
  fun i => curveIntegral u.value (markedPath i.val)

theorem exactRel_periods {u v : ClosedField} (h : ExactRel u v) :
    periods u = periods v := by
  rcases h with ⟨g, hg, he⟩
  funext i
  exact (period_of_exact_difference_on_union u.value v.value g hg i.val i.property
    (smooth_field_integrable u.value u.smooth i.val i.property) he).2.symm

/-- The native lift is justified by the proved exact-difference invariance. -/
def quotientPeriods : FieldQuotient → (PositiveIndex → ℝ) :=
  Quotient.lift (s := exactSetoid) periods (fun _ _ h => exactRel_periods h)

theorem quotientPeriods_mk (u : ClosedField) :
    quotientPeriods (Quotient.mk exactSetoid u) = periods u := rfl

/-- Nat0 is an unused auxiliary coefficient, not a period coordinate. -/
def positiveExtend (b : PositiveIndex → ℝ) (i : Nat) : ℝ :=
  if hi : 1 ≤ i then b ⟨i, hi⟩ else 0

theorem positiveExtend_apply (b : PositiveIndex → ℝ) (i : PositiveIndex) :
    positiveExtend b i.val = b i := by
  simp [positiveExtend, i.property]

def realise (b : PositiveIndex → ℝ) : ClosedField where
  value := MirrorLocalSynthesis.combined (positiveExtend b)
  smooth := MirrorLocalSynthesis.combined_smoothOn_union (positiveExtend b)
  closed := fun p hp => MirrorCombinedClosedness.combined_closed_union (positiveExtend b) hp

theorem realise_periods (b : PositiveIndex → ℝ) : periods (realise b) = b := by
  funext i
  change curveIntegral (MirrorLocalSynthesis.combined (positiveExtend b)) (markedPath i.val) = b i
  rw [MirrorCombinedPeriods.combined_period (positiveExtend b) i.val i.property]
  exact positiveExtend_apply b i

def realiseClass (b : PositiveIndex → ℝ) : FieldQuotient :=
  Quotient.mk exactSetoid (realise b)

theorem quotientPeriods_realiseClass (b : PositiveIndex → ℝ) :
    quotientPeriods (realiseClass b) = b :=
  realise_periods b

/-- Surjectivity only; the zero-period global-exactness converse is not assumed. -/
theorem quotientPeriods_surjective : Function.Surjective quotientPeriods := by
  intro b
  exact ⟨realiseClass b, quotientPeriods_realiseClass b⟩

end MirrorPeriodQuotient

namespace MirrorLocalExactness
open Set
open scoped Topology ContDiff
open MirrorGeometry MirrorExteriorClosedness MirrorPeriodQuotient

/- The exterior derivative uses the existing real Fin1 embedding.
   This bridge requires actual differentiability at the point. -/
theorem oneForm_fderiv {w : ℂ → ℂ →L[ℝ] ℝ} {p : ℂ}
    (hw : DifferentiableAt ℝ w p) :
    fderiv ℝ (oneForm w) p =
      liftCovector.toContinuousLinearMap ∘L fderiv ℝ w p := by
  exact (liftCovector.toContinuousLinearMap.hasFDerivAt.comp p hw.hasFDerivAt).fderiv

theorem extDeriv_covector_apply {w : ℂ → ℂ →L[ℝ] ℝ} {p : ℂ}
    (hw : DifferentiableAt ℝ w p) (v : Fin 2 → ℂ) :
    extDeriv (oneForm w) p v =
      fderiv ℝ w p (v 0) (v 1) - fderiv ℝ w p (v 1) (v 0) := by
  unfold extDeriv
  rw [oneForm_fderiv hw, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two]
  simp [liftCovector, ContinuousAlternatingMap.ofSubsingletonLIE,
    Fin.removeNth, Fin.succAbove, Fin.tail, sub_eq_add_neg]

theorem closed_iff_symmetric {w : ℂ → ℂ →L[ℝ] ℝ} {p : ℂ}
    (hw : DifferentiableAt ℝ w p) :
    extDeriv (oneForm w) p = 0 ↔
      ∀ u v : ℂ, fderiv ℝ w p u v = fderiv ℝ w p v u := by
  constructor
  · intro h u v
    have he := congrArg (fun a : ℂ [⋀^Fin 2]→L[ℝ] ℝ => a ![u, v]) h
    rw [extDeriv_covector_apply hw] at he
    have hz : fderiv ℝ w p u v - fderiv ℝ w p v u = 0 := by
      simpa using he
    exact sub_eq_zero.mp hz
  · intro h
    ext v
    rw [extDeriv_covector_apply hw]
    change fderiv ℝ w p (v 0) (v 1) - fderiv ℝ w p (v 1) (v 0) = 0
    exact sub_eq_zero.mpr (h (v 0) (v 1))

/- Native convex Poincare supplies the potential. Its smoothness follows
   from the existing field and the open-domain derivative criterion.
   Neither equality nor regularity outside the domain is asserted. -/
theorem smooth_closed_convex_primitive {s : Set ℂ} {w : ℂ → ℂ →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hso : IsOpen s) (hw : ContDiffOn ℝ ∞ w s)
    (hclosed : ∀ p ∈ s, extDeriv (oneForm w) p = 0) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g s ∧
      ∀ p ∈ s, HasFDerivAt g (w p) p := by
  have hdw : DifferentiableOn ℝ w s := hw.differentiableOn (by simp)
  have hsym : ∀ p ∈ s, ∀ u v : ℂ, fderiv ℝ w p u v = fderiv ℝ w p v u := by
    intro p hp
    exact (closed_iff_symmetric (hdw.differentiableAt (hso.mem_nhds hp))).mp
      (hclosed p hp)
  obtain ⟨g, hg⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso hdw hsym
  have hdg : DifferentiableOn ℝ g s := fun p hp =>
    (hg p hp).differentiableAt.differentiableWithinAt
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ g) s :=
    hw.congr (fun p hp => (hg p hp).fderiv)
  exact ⟨g, (contDiffOn_infty_iff_fderiv_of_isOpen hso).mpr ⟨hdg, hdf⟩, hg⟩

theorem closedField_primitive_on_convex (w : ClosedField) {s : Set ℂ}
    (hs : Convex ℝ s) (hso : IsOpen s) (hsub : s ⊆ XInfinity) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g s ∧
      ∀ p ∈ s, fderiv ℝ g p = w.value p := by
  obtain ⟨g, hgs, hg⟩ := smooth_closed_convex_primitive hs hso (w.smooth.mono hsub)
    (fun p hp => w.closed p (hsub hp))
  exact ⟨g, hgs, fun p hp => (hg p hp).fderiv⟩

/- Every actual union point has a contained positive-radius convex ball.
   This is local exactness, not a global primitive on the punctured union. -/
theorem closedField_local_primitive (w : ClosedField) {p : ℂ} (hp : p ∈ XInfinity) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ XInfinity ∧
      ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (Metric.ball p r) ∧
        ∀ q ∈ Metric.ball p r, fderiv ℝ g q = w.value q := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp union_open p hp
  obtain ⟨g, hgs, hg⟩ := closedField_primitive_on_convex w (convex_ball p r)
    Metric.isOpen_ball hsub
  exact ⟨r, hr, hsub, g, hgs, hg⟩

end MirrorLocalExactness

namespace MirrorZeroLoopPrimitive
open Set Filter MeasureTheory AffineMap
open scoped Topology ContDiff unitInterval Interval

inductive SmoothPieces (s : Set ℂ) : {p q : ℂ} → Path p q → Prop
  | smooth {p q : ℂ} (γ : Path p q)
      (hc : ContDiffOn ℝ 1 γ.extend I) (hs : Set.range γ ⊆ s) : SmoothPieces s γ
  | trans {p q r : ℂ} {α : Path p q} {β : Path q r}
      (hα : SmoothPieces s α) (hβ : SmoothPieces s β) : SmoothPieces s (α.trans β)
  | symm {p q : ℂ} {γ : Path p q} (hγ : SmoothPieces s γ) : SmoothPieces s γ.symm

variable {s : Set ℂ} {a : ℂ} {w : ℂ → ℂ →L[ℝ] ℝ}

theorem pieces_contained {p q : ℂ} {γ : Path p q} (hγ : SmoothPieces s γ) :
    Set.range γ ⊆ s := by
  induction hγ with
  | smooth γ hc hs => exact hs
  | trans hα hβ ihα ihβ =>
      rw [Path.trans_range]
      exact union_subset ihα ihβ
  | symm hγ ih =>
      rw [Path.symm_range]
      exact ih

theorem pieces_integrable (hw : ContinuousOn w s)
    {p q : ℂ} {γ : Path p q} (hγ : SmoothPieces s γ) : CurveIntegrable w γ := by
  induction hγ with
  | smooth γ hc hs =>
      exact hw.curveIntegrable_of_contDiffOn hc (fun t => hs (mem_range_self t))
  | trans hα hβ ihα ihβ => exact ihα.trans ihβ
  | symm hγ ih => exact ih.symm

def PiecewiseReach (s : Set ℂ) (a : ℂ) : Prop :=
  ∀ q ∈ s, ∃ γ : Path a q, SmoothPieces s γ

def ZeroPieceLoops (s : Set ℂ) (w : ℂ → ℂ →L[ℝ] ℝ) : Prop :=
  ∀ p ∈ s, ∀ γ : Path p p, SmoothPieces s γ → curveIntegral w γ = 0

theorem path_integrals_equal (hw : ContinuousOn w s)
    (hz : ZeroPieceLoops s w) (ha : a ∈ s)
    {q : ℂ} (α β : Path a q) (hα : SmoothPieces s α) (hβ : SmoothPieces s β) :
    curveIntegral w α = curveIntegral w β := by
  have he := hz a ha (α.trans β.symm) (hα.trans hβ.symm)
  rw [curveIntegral_trans (pieces_integrable hw hα) (pieces_integrable hw hβ.symm),
    curveIntegral_symm] at he
  linarith

theorem local_segment_piece {p q : ℂ} {r : ℝ}
    (hp : p ∈ Metric.ball p r) (hq : q ∈ Metric.ball p r)
    (hb : Metric.ball p r ⊆ s) : SmoothPieces s (Path.segment p q) := by
  apply SmoothPieces.smooth
  · have hc : ContDiff ℝ 1 (fun t : ℝ => lineMap p q t) := by fun_prop
    exact hc.contDiffOn.congr (Path.eqOn_extend_segment p q)
  · rw [Path.range_segment]
    exact ((convex_ball p r).segment_subset hp hq).trans hb

noncomputable def potential (w : ℂ → ℂ →L[ℝ] ℝ)
    (hreach : PiecewiseReach s a) (q : ℂ) : ℝ := by
  classical
  exact if hq : q ∈ s then curveIntegral w (Classical.choose (hreach q hq)) else 0

theorem potential_eq_path_integral (hw : ContinuousOn w s)
    (hreach : PiecewiseReach s a) (hz : ZeroPieceLoops s w)
    (ha : a ∈ s) {q : ℂ} (hq : q ∈ s) (γ : Path a q) (hγ : SmoothPieces s γ) :
    potential w hreach q = curveIntegral w γ := by
  classical
  simp only [potential, dif_pos hq]
  exact path_integrals_equal hw hz ha _ γ (Classical.choose_spec (hreach q hq)) hγ

theorem potential_increment_neighbourhood (hs : IsOpen s)
    (hw : ContDiffOn ℝ ∞ w s) (hreach : PiecewiseReach s a)
    (hz : ZeroPieceLoops s w) (ha : a ∈ s) {p : ℂ} (hp : p ∈ s) :
    potential w hreach =ᶠ[𝓝 p]
      (fun q => potential w hreach p + curveIntegral w (Path.segment p q)) := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hs p hp
  obtain ⟨γ, hγ⟩ := hreach p hp
  apply Filter.mem_of_superset (Metric.ball_mem_nhds p hr)
  intro q hq
  have hseg := local_segment_piece (Metric.mem_ball_self hr) hq hb
  change potential w hreach q =
    potential w hreach p + curveIntegral w (Path.segment p q)
  rw [potential_eq_path_integral hw.continuousOn hreach hz ha (hb hq)
    (γ.trans (Path.segment p q)) (hγ.trans hseg),
    curveIntegral_trans (pieces_integrable hw.continuousOn hγ)
      (pieces_integrable hw.continuousOn hseg),
    potential_eq_path_integral hw.continuousOn hreach hz ha hp γ hγ]

theorem potential_hasFDerivAt (hs : IsOpen s) (hw : ContDiffOn ℝ ∞ w s)
    (hreach : PiecewiseReach s a) (hz : ZeroPieceLoops s w) (ha : a ∈ s)
    {p : ℂ} (hp : p ∈ s) :
    HasFDerivAt (potential w hreach) (w p) p := by
  have he : ∀ᶠ q in 𝓝 p, ContinuousAt w q :=
    Filter.mem_of_superset (hs.mem_nhds hp)
      (fun q hq => (hw.contDiffAt (hs.mem_nhds hq)).continuousAt)
  exact ((HasFDerivAt.curveIntegral_segment_source' he).const_add
    (potential w hreach p)).congr_of_eventuallyEq
      (potential_increment_neighbourhood hs hw hreach hz ha hp)

theorem global_smooth_primitive (hs : IsOpen s) (hw : ContDiffOn ℝ ∞ w s)
    (hreach : PiecewiseReach s a) (hz : ZeroPieceLoops s w) (ha : a ∈ s) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g s ∧
      ∀ p ∈ s, HasFDerivAt g (w p) p := by
  have hd : ∀ p ∈ s, HasFDerivAt (potential w hreach) (w p) p :=
    fun p hp => potential_hasFDerivAt hs hw hreach hz ha hp
  have hdg : DifferentiableOn ℝ (potential w hreach) s :=
    fun p hp => (hd p hp).differentiableAt.differentiableWithinAt
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ (potential w hreach)) s :=
    hw.congr (fun p hp => (hd p hp).fderiv)
  exact ⟨potential w hreach,
    (contDiffOn_infty_iff_fderiv_of_isOpen hs).mpr ⟨hdg, hdf⟩, hd⟩

end MirrorZeroLoopPrimitive

namespace MirrorPuncturedCorridor
open Set Filter MeasureTheory AffineMap
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorZeroLoopPrimitive

def point (x y : ℝ) : ℂ := ⟨x, y⟩
def anchor : ℂ := point 1 (1 / 2)

theorem interp_bounds {L R x y t : ℝ}
    (hx : L < x ∧ x < R) (hy : L < y ∧ y < R)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    L < (1-t)*x+t*y ∧ (1-t)*x+t*y < R := by
  by_cases he : t = 1
  · simpa [he] using hy
  have hpos : 0 < 1-t := by rcases ht with ⟨h0,h1⟩; rcases lt_or_eq_of_le h1 with h|h; linarith; exact False.elim (he h)
  have hL := mul_pos hpos (sub_pos.mpr hx.1)
  have hR := mul_pos hpos (sub_pos.mpr hx.2)
  have hyL := mul_nonneg ht.1 (sub_nonneg.mpr hy.1.le)
  have hyR := mul_nonneg ht.1 (sub_nonneg.mpr hy.2.le)
  constructor <;> nlinarith

theorem line_re (p q : ℂ) (t : ℝ) :
    (lineMap p q t).re = (1-t)*p.re+t*q.re := by
  simp [lineMap_apply_module]
theorem line_im (p q : ℂ) (t : ℝ) :
    (lineMap p q t).im = (1-t)*p.im+t*q.im := by
  simp [lineMap_apply_module]

theorem point_rectangle (n : Nat) {x y : ℝ}
    (hx : a n < x ∧ x < 2) (hy : -1 < y ∧ y < 1) :
    point x y ∈ rectangle n := by exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem rectangle_line (n : Nat) {p q : ℂ}
    (hp : p ∈ rectangle n) (hq : q ∈ rectangle n)
    {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    lineMap p q t ∈ rectangle n := by
  rcases hp with ⟨hpl,hpr,hpb,hpt⟩
  rcases hq with ⟨hql,hqr,hqb,hqt⟩
  have hx := interp_bounds ⟨hpl,hpr⟩ ⟨hql,hqr⟩ ht
  have hy := interp_bounds ⟨hpb,hpt⟩ ⟨hqb,hqt⟩ ht
  change a n < (lineMap p q t).re ∧ (lineMap p q t).re < 2 ∧
    -1 < (lineMap p q t).im ∧ (lineMap p q t).im < 1
  rw [line_re,line_im]
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem high_im_clear (n : Nat) {p : ℂ}
    (hp : p ∈ rectangle n) (hy : 1/2 ≤ |p.im|) : p ∈ X n := by
  apply (mem_X n p).mpr
  refine ⟨hp,?_⟩
  intro j
  have hc := c_le_one (j.val+1)
  have hd := imag_coordinate_bound p (j.val+1)
  dsimp [rho]
  linarith

theorem high_re_clear (n : Nat) {p : ℂ}
    (hp : p ∈ rectangle n) (hx : 1 ≤ p.re) : p ∈ X n := by
  apply (mem_X n p).mpr
  refine ⟨hp,?_⟩
  intro j
  have hc : c (j.val+1) ≤ 1/2 := by
    calc
      c (j.val+1) ≤ c 0 / 2 := c_later_le_half (show 0 < j.val+1 by omega)
      _ = 1/2 := by norm_num [c]
  have hd := (le_abs_self (p.re-c (j.val+1))).trans (real_coordinate_bound p (j.val+1))
  dsimp [rho]
  linarith

theorem anchor_mem (n : Nat) : anchor ∈ X n := by
  apply high_im_clear n
  · apply point_rectangle n
    · dsimp [a]
      constructor <;> nlinarith [c_le_one n]
    · norm_num
  · norm_num [anchor,point]

theorem signed_abs_le {s x : ℝ} (hs : s=1 ∨ s= -1) : s*x ≤ |x| := by
  rcases hs with hs|hs
  · simpa [hs] using le_abs_self x
  · simpa [hs] using neg_le_abs x

theorem vertical_to_corridor (n : Nat) (p : ℂ) (hp : p ∈ X n)
    (s : ℝ) (hs : s=1 ∨ s= -1) (hpy : 0 ≤ s*p.im)
    {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    lineMap p (point p.re (s/2)) t ∈ X n := by
  let z := lineMap p (point p.re (s/2)) t
  have hpRect : p ∈ rectangle n := hp.1
  have hqRect : point p.re (s/2) ∈ rectangle n := by
    apply point_rectangle n ⟨hpRect.1,hpRect.2.1⟩
    rcases hs with hs|hs <;> rw [hs] <;> norm_num
  have hzRect : z ∈ rectangle n := rectangle_line n hpRect hqRect ht
  have hzr : z.re=p.re := by dsimp [z]; rw [line_re]; simp [point]; ring
  have hzi : z.im=(1-t)*p.im+t*(s/2) := by dsimp [z]; rw [line_im]; rfl
  have hzy : s*z.im=(1-t)*(s*p.im)+t/2 := by
    rw [hzi]; rcases hs with hs|hs <;> rw [hs] <;> ring
  by_cases hsmall : s*p.im ≤ 1/2
  · have hdiff := mul_nonneg ht.1 (sub_nonneg.mpr hsmall)
    have hzpy : s*p.im ≤ s*z.im := by rw [hzy]; nlinarith
    have hzp : 0 ≤ s*z.im := hpy.trans hzpy
    have hprod := mul_nonneg (sub_nonneg.mpr hzpy) (show 0 ≤ s*z.im+s*p.im by linarith)
    have hsq : p.im^2 ≤ z.im^2 := by
      rcases hs with hs|hs <;> rw [hs] at hprod <;> nlinarith
    apply (mem_X n z).mpr
    refine ⟨hzRect,?_⟩
    intro j
    have hd : dist p (center (j.val+1)) ≤ dist z (center (j.val+1)) := by
      rw [euclidean_distance,euclidean_distance]
      apply Real.sqrt_le_sqrt
      simp only [MirrorGeometry.center,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
      rw [hzr]
      nlinarith
    exact ((mem_X n p).mp hp).2 j |>.trans_le hd
  · have hlarge : 1/2 ≤ s*p.im := (lt_of_not_ge hsmall).le
    have hprod := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hlarge)
    have hzhalf : 1/2 ≤ s*z.im := by rw [hzy]; nlinarith
    exact high_im_clear n hzRect (hzhalf.trans (signed_abs_le hs))

theorem segment_piece {n : Nat} {p q : ℂ}
    (h : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → lineMap p q t ∈ X n) :
    SmoothPieces (X n) (Path.segment p q) := by
  apply SmoothPieces.smooth
  · have hc : ContDiff ℝ 1 (fun t : ℝ => lineMap p q t) := by fun_prop
    exact hc.contDiffOn.congr (Path.eqOn_extend_segment p q)
  · rintro z ⟨t,rfl⟩
    exact h t t.property

theorem horizontal_corridor (n : Nat) (p : ℂ) (y : ℝ)
    (hp : p ∈ rectangle n) (hpy : p.im=y)
    (hy : -1<y ∧ y<1) (hyabs : 1/2 ≤ |y|) :
    SmoothPieces (X n) (Path.segment p (point 1 y)) := by
  apply segment_piece
  intro t ht
  have hq : point 1 y ∈ rectangle n := by
    apply point_rectangle n
    · dsimp [a]
      constructor <;> nlinarith [c_le_one n]
    · exact hy
  apply high_im_clear n (rectangle_line n hp hq ht)
  have he : (lineMap p (point 1 y) t).im = y := by
    rw [line_im,hpy]; simp [point]; ring
  simpa [he] using hyabs

theorem right_connector (n : Nat) :
    SmoothPieces (X n) (Path.segment (point 1 (-1/2)) anchor) := by
  apply segment_piece
  intro t ht
  have hlo : point 1 (-1/2) ∈ rectangle n := by
    apply point_rectangle n
    · dsimp [a]
      constructor <;> nlinarith [c_le_one n]
    · norm_num
  have hhi : anchor ∈ rectangle n := (anchor_mem n).1
  apply high_re_clear n (rectangle_line n hlo hhi ht)
  rw [line_re]
  norm_num [point,anchor]

theorem stage_piecewise_reach (n : Nat) : PiecewiseReach (X n) anchor := by
  intro p hp
  have hpRect : p ∈ rectangle n := hp.1
  by_cases hpy : 0 ≤ p.im
  · let u := point p.re (1/2)
    have hα : SmoothPieces (X n) (Path.segment p u) := by
      apply segment_piece
      intro t ht
      simpa [u] using vertical_to_corridor n p hp 1 (Or.inl rfl) (by simpa) ht
    have hu : u ∈ rectangle n := point_rectangle n ⟨hpRect.1,hpRect.2.1⟩ (by norm_num)
    have hβ : SmoothPieces (X n) (Path.segment u anchor) := by
      exact horizontal_corridor n u (1/2) hu rfl (by norm_num) (by norm_num)
    exact ⟨((Path.segment p u).trans (Path.segment u anchor)).symm,(hα.trans hβ).symm⟩
  · let l := point p.re (-1/2)
    have hα : SmoothPieces (X n) (Path.segment p l) := by
      apply segment_piece
      intro t ht
      simpa [l] using vertical_to_corridor n p hp (-1) (Or.inr rfl) (by nlinarith) ht
    have hl : l ∈ rectangle n := point_rectangle n ⟨hpRect.1,hpRect.2.1⟩ (by norm_num)
    have hβ : SmoothPieces (X n) (Path.segment l (point 1 (-1/2))) :=
      horizontal_corridor n l (-1/2) hl rfl (by norm_num) (by norm_num)
    exact ⟨(((Path.segment p l).trans (Path.segment l (point 1 (-1/2)))).trans
      (Path.segment (point 1 (-1/2)) anchor)).symm,
      ((hα.trans hβ).trans (right_connector n)).symm⟩

theorem pieces_mono {s v : Set ℂ} (hv : s ⊆ v)
    {p q : ℂ} {γ : Path p q} (hγ : SmoothPieces s γ) : SmoothPieces v γ := by
  induction hγ with
  | smooth γ hc hs => exact .smooth γ hc (hs.trans hv)
  | trans hα hβ ihα ihβ => exact ihα.trans ihβ
  | symm hγ ih => exact ih.symm

theorem union_piecewise_reach : PiecewiseReach XInfinity anchor := by
  intro p hp
  rcases mem_iUnion.mp hp with ⟨n,hn⟩
  obtain ⟨γ,hγ⟩ := stage_piecewise_reach (n+1) p hn
  refine ⟨γ,pieces_mono ?_ hγ⟩
  intro q hq
  exact mem_iUnion.mpr ⟨n,hq⟩

/- Actual geometric reach is supplied; zero ALL admitted-piece-loop periods
   is still a separate premise, not zero only the marked circles. -/
theorem union_primitive_of_zero_piece_loops
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContDiffOn ℝ ∞ w XInfinity)
    (hz : ZeroPieceLoops XInfinity w) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g XInfinity ∧
      ∀ p ∈ XInfinity, HasFDerivAt g (w p) p :=
  global_smooth_primitive union_open hw union_piecewise_reach hz
    (mem_iUnion.mpr ⟨0,anchor_mem 1⟩)

end MirrorPuncturedCorridor



namespace MirrorSlitSquare
open Set Filter MeasureTheory AffineMap
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorZeroLoopPrimitive MirrorPuncturedCorridor

def verticalClear (n : Nat) : Set ℂ :=
  ⋂ j : Fin n, {p | rho (j.val+1) < |p.re-c (j.val+1)|}
def slit (n : Nat) (s : ℝ) : Set ℂ :=
  X n ∩ ({p | 0 < s*p.im} ∪ verticalClear n)

theorem mem_verticalClear (n : Nat) (p : ℂ) :
    p ∈ verticalClear n ↔ ∀ j : Fin n, rho (j.val+1) < |p.re-c (j.val+1)| := by
  simp [verticalClear]

theorem verticalClear_open (n : Nat) : IsOpen (verticalClear n) := by
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const ((Complex.continuous_re.sub continuous_const).abs)

theorem verticalClear_same_re {n : Nat} {p q : ℂ}
    (hp : p ∈ verticalClear n) (hr : q.re=p.re) : q ∈ verticalClear n := by
  apply (mem_verticalClear n q).mpr
  intro j
  rw [hr]
  exact (mem_verticalClear n p).mp hp j

theorem verticalClear_in_stage {n : Nat} {p : ℂ}
    (hr : p ∈ rectangle n) (hc : p ∈ verticalClear n) : p ∈ X n := by
  apply (mem_X n p).mpr
  refine ⟨hr,?_⟩
  intro j
  exact ((mem_verticalClear n p).mp hc j).trans_le (real_coordinate_bound p (j.val+1))

theorem verticalClear_of_real {n : Nat} {p : ℂ}
    (hp : p ∈ X n) (hy : p.im=0) : p ∈ verticalClear n := by
  apply (mem_verticalClear n p).mpr
  intro j
  have he : dist p (MirrorGeometry.center (j.val+1))=|p.re-c (j.val+1)| := by
    rw [Complex.dist_of_im_eq (by simpa [MirrorGeometry.center] using hy),Real.dist_eq]
    simp [MirrorGeometry.center]
  rw [← he]
  exact ((mem_X n p).mp hp).2 j

theorem slit_open (n : Nat) (s : ℝ) : IsOpen (slit n s) :=
  (stage_open n).inter
    ((isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).union
      (verticalClear_open n))

theorem corridor_point_slit (n : Nat) {x : ℝ} (hx : a n<x ∧ x<2)
    (s : ℝ) (hs : s=1 ∨ s= -1) : point x (s/2) ∈ slit n s := by
  have hr : point x (s/2) ∈ rectangle n := by
    apply point_rectangle n hx
    rcases hs with hs|hs <;> rw [hs] <;> norm_num
  refine ⟨high_im_clear n hr ?_,Or.inl ?_⟩
  · rcases hs with hs|hs <;> norm_num [point,hs]
  · rcases hs with hs|hs <;> norm_num [point,hs]

theorem slit_cover (n : Nat) : X n=slit n 1 ∪ slit n (-1) := by
  ext p
  constructor
  · intro hp
    rcases lt_trichotomy p.im 0 with hlo|hz|hhi
    · exact Or.inr ⟨hp,Or.inl (by change 0 < (-1:ℝ)*p.im; nlinarith)⟩
    · exact Or.inl ⟨hp,Or.inr (verticalClear_of_real hp hz)⟩
    · exact Or.inl ⟨hp,Or.inl (by change 0 < (1:ℝ)*p.im; simpa using hhi)⟩
  · rintro (hp|hp) <;> exact hp.1

theorem slit_overlap (n : Nat) :
    slit n 1 ∩ slit n (-1)=rectangle n ∩ verticalClear n := by
  ext p
  constructor
  · rintro ⟨hu,hl⟩
    refine ⟨hu.1.1,?_⟩
    rcases hu.2 with hyu|hc
    · rcases hl.2 with hyl|hc
      · change 0 < (1:ℝ)*p.im at hyu; change 0 < (-1:ℝ)*p.im at hyl; exfalso; nlinarith
      · exact hc
    · exact hc
  · rintro ⟨hr,hc⟩
    have hp := verticalClear_in_stage hr hc
    exact ⟨⟨hp,Or.inr hc⟩,⟨hp,Or.inr hc⟩⟩

theorem slit_vertical (n : Nat) (p : ℂ) (s : ℝ)
    (hs : s=1 ∨ s= -1) (hp : p ∈ slit n s)
    {t : ℝ} (ht : 0≤t ∧ t≤1) :
    lineMap p (point p.re (s/2)) t ∈ slit n s := by
  let z := lineMap p (point p.re (s/2)) t
  have hpRect : p ∈ rectangle n := hp.1.1
  have hq := corridor_point_slit n ⟨hpRect.1,hpRect.2.1⟩ s hs
  have hzRect : z ∈ rectangle n := rectangle_line n hpRect hq.1.1 ht
  have hzr : z.re=p.re := by dsimp [z]; rw [line_re]; simp [point]; ring
  rcases hp.2 with hpos|hclear
  · have hX : z ∈ X n := vertical_to_corridor n p hp.1 s hs hpos.le ht
    have hhigh : s*p.im<1 := by
      rcases hs with hs|hs
      · rw [hs]; simpa using hpRect.2.2.2
      · rw [hs]; nlinarith [hpRect.2.2.1]
    have hzy : s*z.im=(1-t)*(s*p.im)+t/2 := by
      dsimp [z]; rw [line_im]; simp [point]
      rcases hs with hs|hs <;> rw [hs] <;> ring
    refine ⟨hX,Or.inl ?_⟩
    change 0 < s*z.im
    rw [hzy]
    simpa only [div_eq_mul_inv, one_mul] using
      (interp_bounds ⟨hpos,hhigh⟩ (by norm_num : (0:ℝ)<1/2 ∧ (1/2:ℝ)<1) ht).1
  · have hzClear := verticalClear_same_re hclear hzr
    exact ⟨verticalClear_in_stage hzRect hzClear,Or.inr hzClear⟩

theorem slit_segment_piece {n : Nat} {s : ℝ} {p q : ℂ}
    (h : ∀ t : ℝ, 0≤t ∧ t≤1 → lineMap p q t ∈ slit n s) :
    SmoothPieces (slit n s) (Path.segment p q) := by
  apply SmoothPieces.smooth
  · have hc : ContDiff ℝ 1 (fun t : ℝ => lineMap p q t) := by fun_prop
    exact hc.contDiffOn.congr (Path.eqOn_extend_segment p q)
  · rintro z ⟨t,rfl⟩
    exact h t t.property

theorem slit_horizontal (n : Nat) {x : ℝ} (hx : a n<x ∧ x<2)
    (s : ℝ) (hs : s=1 ∨ s= -1) :
    SmoothPieces (slit n s) (Path.segment (point x (s/2)) (point 1 (s/2))) := by
  apply slit_segment_piece
  intro t ht
  have h1 : a n<1 ∧ (1:ℝ)<2 := by dsimp [a]; constructor <;> nlinarith [c_le_one n]
  have hzX := interp_bounds hx h1 ht
  have he : lineMap (point x (s/2)) (point 1 (s/2)) t =
      point ((1-t)*x+t) (s/2) := by
    apply Complex.ext
    · rw [line_re]; simp [point]
    · rw [line_im]; simp [point]; ring
  rw [he]
  exact corridor_point_slit n (by simpa using hzX) s hs

theorem slit_piecewise_reach (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1) :
    PiecewiseReach (slit n s) (point 1 (s/2)) := by
  intro p hp
  let u := point p.re (s/2)
  have hα : SmoothPieces (slit n s) (Path.segment p u) :=
    slit_segment_piece (fun t ht => slit_vertical n p s hs hp ht)
  have hβ := slit_horizontal n ⟨hp.1.1.1,hp.1.1.2.1⟩ s hs
  exact ⟨((Path.segment p u).trans (Path.segment u (point 1 (s/2)))).symm,
    (hα.trans hβ).symm⟩

theorem slit_anchor_mem (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1) :
    point 1 (s/2) ∈ slit n s := by
  apply corridor_point_slit n ?_ s hs
  dsimp [a]; constructor <;> nlinarith [c_le_one n]

def squareFormula (p q : ℂ) (s : ℝ) (xy : ℝ × ℝ) : ℂ :=
  lineMap (lineMap p q xy.1) (point (lineMap p q xy.1).re (s/2)) xy.2

theorem squareFormula_contDiff (p q : ℂ) (s : ℝ) :
    ContDiff ℝ ∞ (squareFormula p q s) := by
  have hpoint : ∀ x y : ℝ,
      point x y = Complex.ofRealCLM x + y • Complex.I := by
    intro x y
    apply Complex.ext <;> simp [point]
  unfold squareFormula
  simp only [lineMap_apply_module, hpoint]
  change ContDiff ℝ ∞
    (fun xy : ℝ × ℝ =>
      (1 - xy.2) • ((1 - xy.1) • p + xy.1 • q) +
      xy.2 •
        (Complex.ofRealCLM
          (Complex.reCLM ((1 - xy.1) • p + xy.1 • q)) +
          (s / 2) • Complex.I))
  fun_prop

def verticalSquare (p q : ℂ) (s : ℝ) :
    (Path.segment p (point p.re (s/2)) : C(I,ℂ)).Homotopy
      (Path.segment q (point q.re (s/2))) where
  toFun xy := squareFormula p q s (xy.1,xy.2)
  continuous_toFun := by
    exact (squareFormula_contDiff p q s).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  map_zero_left := by intro x; simp [squareFormula]
  map_one_left := by intro x; simp [squareFormula]

theorem verticalSquare_contDiff (p q : ℂ) (s : ℝ) :
    ContDiffOn ℝ 2
      (fun xy : ℝ×ℝ => IccExtend zero_le_one ((verticalSquare p q s).extend xy.1) xy.2)
      (Icc 0 1) := by
  have he : EqOn
      (fun xy : ℝ×ℝ => IccExtend zero_le_one ((verticalSquare p q s).extend xy.1) xy.2)
      (squareFormula p q s) (Icc 0 1) := by
    rw [Icc_prod_eq]
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    lift x to I using hx
    lift y to I using hy
    simp [verticalSquare]
    rfl
  have hc : ContDiff ℝ 2 (squareFormula p q s) :=
    (squareFormula_contDiff p q s).of_le (by simp)
  exact hc.contDiffOn.congr he

theorem verticalSquare_range_slit (n : Nat) (p q : ℂ) (s : ℝ)
    (hs : s=1 ∨ s= -1)
    (hbottom : ∀ t : ℝ, 0≤t ∧ t≤1 → lineMap p q t ∈ slit n s) :
    range (verticalSquare p q s) ⊆ slit n s := by
  rintro z ⟨⟨x,y⟩,rfl⟩
  exact slit_vertical n (lineMap p q (x:ℝ)) s hs (hbottom x x.property) y.property

/- The square is genuine C2 data, not a smoothness assertion about
   arbitrary C1-piece loops. Range closure remains inside the supplied slit. -/
theorem vertical_square_boundary (n : Nat) (p q : ℂ) (s : ℝ)
    (hs : s=1 ∨ s= -1)
    (hbottom : ∀ t : ℝ, 0≤t ∧ t≤1 → lineMap p q t ∈ slit n s)
    (w : ℂ → ℂ →L[ℝ] ℝ) (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hw : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u) :
    curveIntegral w (Path.segment p (point p.re (s/2))) +
      curveIntegral w ((verticalSquare p q s).evalAt 1) =
    curveIntegral w (Path.segment q (point q.re (s/2))) +
      curveIntegral w ((verticalSquare p q s).evalAt 0) := by
  let φ := verticalSquare p q s
  have hφ : range φ ⊆ slit n s := verticalSquare_range_slit n p q s hs hbottom
  apply φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t:=range φ) (dω:=dw)
  · intros
    exact mem_range_self _
  · intro z hz
    exact (hw z (hφ hz)).hasFDerivWithinAt
  · rw [(isCompact_range (map_continuous φ)).isClosed.closure_eq]
    intro z hz
    exact (hw z (hφ hz)).continuousAt.continuousWithinAt
  · intro z hz u hu v hv
    exact hsymm z (hφ hz) u v
  · exact verticalSquare_contDiff p q s

end MirrorSlitSquare


namespace MirrorSlitPrimitive
open Set Filter MeasureTheory AffineMap
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorZeroLoopPrimitive MirrorPuncturedCorridor MirrorSlitSquare

def corridor (n : Nat) (s : ℝ) : Set ℂ :=
  {p | a n < p.re ∧ p.re < 2 ∧ p.im = s/2}
def up (s : ℝ) (p : ℂ) : ℂ := point p.re (s/2)
def chartAnchor (s : ℝ) : ℂ := point 1 (s/2)
def horizontalPotential (w : ℂ → ℂ →L[ℝ] ℝ) (s : ℝ) (p : ℂ) : ℝ :=
  curveIntegral w (Path.segment (chartAnchor s) (up s p))
def verticalLeg (w : ℂ → ℂ →L[ℝ] ℝ) (s : ℝ) (p : ℂ) : ℝ :=
  curveIntegral w (Path.segment p (up s p))
def chartPotential (w : ℂ → ℂ →L[ℝ] ℝ) (s : ℝ) (p : ℂ) : ℝ :=
  horizontalPotential w s p - verticalLeg w s p

theorem corridor_convex (n : Nat) (s : ℝ) : Convex ℝ (corridor n s) := by
  apply convex_iff_segment_subset.mpr
  intro p hp q hq
  rw [segment_eq_image_lineMap]
  rintro z ⟨t,ht,rfl⟩
  have hx := interp_bounds ⟨hp.1,hp.2.1⟩ ⟨hq.1,hq.2.1⟩ ht
  refine ⟨?_,?_,?_⟩
  · simpa [line_re] using hx.1
  · simpa [line_re] using hx.2
  · rw [line_im,hp.2.2,hq.2.2]; ring

theorem corridor_subset (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1) :
    corridor n s ⊆ slit n s := by
  intro p hp
  have he : p = point p.re (s/2) := by
    apply Complex.ext
    · rfl
    · simpa [point] using hp.2.2
  rw [he]
  exact corridor_point_slit n ⟨hp.1,hp.2.1⟩ s hs

theorem up_mem_corridor {n : Nat} {s : ℝ} {p : ℂ}
    (hp : p ∈ slit n s) : up s p ∈ corridor n s := by
  exact ⟨hp.1.1.1,hp.1.1.2.1,rfl⟩

theorem anchor_mem_corridor (n : Nat) (s : ℝ) :
    chartAnchor s ∈ corridor n s := by
  have h1 : a n<1 := by dsimp [a]; nlinarith [c_le_one n]
  exact ⟨h1,by norm_num [chartAnchor,point],rfl⟩

theorem vertical_integrable {n : Nat} {s : ℝ} {p : ℂ}
    (hs : s=1 ∨ s= -1) (hp : p ∈ slit n s)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContinuousOn w (slit n s)) :
    CurveIntegrable w (Path.segment p (up s p)) := by
  exact pieces_integrable hw
    (slit_segment_piece (fun t ht => slit_vertical n p s hs hp ht))

theorem horizontal_integrable {n : Nat} {s : ℝ} {p : ℂ}
    (hs : s=1 ∨ s= -1) (hp : p ∈ slit n s)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContinuousOn w (slit n s)) :
    CurveIntegrable w (Path.segment (chartAnchor s) (up s p)) := by
  apply pieces_integrable hw
  apply slit_segment_piece
  intro t ht
  exact corridor_subset n s hs
    ((corridor_convex n s).lineMap_mem (anchor_mem_corridor n s)
      (up_mem_corridor hp) ht)

theorem square_bottom_integral (p q : ℂ) (s : ℝ) (w : ℂ → ℂ →L[ℝ] ℝ) :
    curveIntegral w ((verticalSquare p q s).evalAt 0) =
      curveIntegral w (Path.segment p q) := by
  let γ := (verticalSquare p q s).evalAt 0
  have hp : p = (Path.segment p (point p.re (s/2))) 0 := by simp
  have hq : q = (Path.segment q (point q.re (s/2))) 0 := by simp
  have he : γ.cast hp hq = Path.segment p q := by
    ext t
    change squareFormula p q s ((t : ℝ),0) = lineMap p q (t : ℝ)
    simp [squareFormula]
  rw [← curveIntegral_cast w γ hp hq,he]

theorem square_top_integral (p q : ℂ) (s : ℝ) (w : ℂ → ℂ →L[ℝ] ℝ) :
    curveIntegral w ((verticalSquare p q s).evalAt 1) =
      curveIntegral w (Path.segment (up s p) (up s q)) := by
  let γ := (verticalSquare p q s).evalAt 1
  have hp : up s p = (Path.segment p (point p.re (s/2))) 1 := by simp [up]
  have hq : up s q = (Path.segment q (point q.re (s/2))) 1 := by simp [up]
  have he : γ.cast hp hq = Path.segment (up s p) (up s q) := by
    ext t
    change squareFormula p q s ((t : ℝ),1) =
      lineMap (point p.re (s/2)) (point q.re (s/2)) (t : ℝ)
    simp only [squareFormula,lineMap_apply_one]
    apply Complex.ext <;> simp [point,lineMap_apply_module] <;> ring
  rw [← curveIntegral_cast w γ hp hq,he]

theorem horizontal_increment (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    {p q : ℂ} (hp : p ∈ slit n s) (hq : q ∈ slit n s)
    (w : ℂ → ℂ →L[ℝ] ℝ) (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u) :
    horizontalPotential w s q =
      horizontalPotential w s p + curveIntegral w (Path.segment (up s p) (up s q)) := by
  exact ((corridor_convex n s).curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
    («ω» := w) (dω := dw)
    (fun z hz => (hd z (corridor_subset n s hs hz)).hasFDerivWithinAt)
    (fun z hz u hu v hv => hsymm z (corridor_subset n s hs hz) u v)
    (anchor_mem_corridor n s) (up_mem_corridor hp) (up_mem_corridor hq)).symm

theorem chart_increment (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    {p q : ℂ} (hp : p ∈ slit n s) (hq : q ∈ slit n s)
    (hbottom : ∀ t : ℝ, 0≤t ∧ t≤1 → lineMap p q t ∈ slit n s)
    (w : ℂ → ℂ →L[ℝ] ℝ) (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u) :
    chartPotential w s q =
      chartPotential w s p + curveIntegral w (Path.segment p q) := by
  have hH := horizontal_increment n s hs hp hq w dw hd hsymm
  have hV := vertical_square_boundary n p q s hs hbottom w dw hd hsymm
  rw [square_bottom_integral,square_top_integral] at hV
  dsimp [chartPotential,horizontalPotential,verticalLeg,up,chartAnchor] at *
  linarith

theorem chart_increment_neighbourhood (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    (w : ℂ → ℂ →L[ℝ] ℝ) (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u)
    {p : ℂ} (hp : p ∈ slit n s) :
    chartPotential w s =ᶠ[𝓝 p]
      (fun q => chartPotential w s p + curveIntegral w (Path.segment p q)) := by
  obtain ⟨r,hr,hb⟩ := Metric.isOpen_iff.mp (slit_open n s) p hp
  apply Filter.mem_of_superset (Metric.ball_mem_nhds p hr)
  intro q hq
  change chartPotential w s q =
    chartPotential w s p + curveIntegral w (Path.segment p q)
  apply chart_increment n s hs hp (hb hq) ?_ w dw hd hsymm
  intro t ht
  exact hb ((convex_ball p r).lineMap_mem (Metric.mem_ball_self hr) hq ht)

theorem chart_hasFDerivAt (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContDiffOn ℝ ∞ w (slit n s))
    (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u)
    {p : ℂ} (hp : p ∈ slit n s) :
    HasFDerivAt (chartPotential w s) (w p) p := by
  have he : ∀ᶠ q in 𝓝 p, ContinuousAt w q :=
    Filter.mem_of_superset ((slit_open n s).mem_nhds hp)
      (fun q hq => (hw.contDiffAt ((slit_open n s).mem_nhds hq)).continuousAt)
  exact ((HasFDerivAt.curveIntegral_segment_source' he).const_add
    (chartPotential w s p)).congr_of_eventuallyEq
      (chart_increment_neighbourhood n s hs w dw hd hsymm hp)

theorem chart_contDiffOn (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContDiffOn ℝ ∞ w (slit n s))
    (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u) :
    ContDiffOn ℝ ∞ (chartPotential w s) (slit n s) := by
  have hg : DifferentiableOn ℝ (chartPotential w s) (slit n s) :=
    fun p hp => (chart_hasFDerivAt n s hs w hw dw hd hsymm hp).differentiableAt.differentiableWithinAt
  have hf : ContDiffOn ℝ ∞ (fderiv ℝ (chartPotential w s)) (slit n s) :=
    hw.congr (fun p hp => (chart_hasFDerivAt n s hs w hw dw hd hsymm hp).fderiv)
  exact (contDiffOn_infty_iff_fderiv_of_isOpen (slit_open n s)).mpr ⟨hg,hf⟩

/- This primitive is on EACH actual slit. No zero marked periods or
   ALL-loop-zero hypothesis is supplied; global compatibility is separate. -/
theorem slit_primitive (n : Nat) (s : ℝ) (hs : s=1 ∨ s= -1)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hw : ContDiffOn ℝ ∞ w (slit n s))
    (dw : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hd : ∀ z ∈ slit n s, HasFDerivAt w (dw z) z)
    (hsymm : ∀ z ∈ slit n s, ∀ u v, dw z u v=dw z v u) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (slit n s) ∧
      ∀ p ∈ slit n s, HasFDerivAt g (w p) p :=
  ⟨chartPotential w s,chart_contDiffOn n s hs w hw dw hd hsymm,
    fun p hp => chart_hasFDerivAt n s hs w hw dw hd hsymm hp⟩

end MirrorSlitPrimitive


namespace MirrorClosedFieldSlit
open Set
open scoped Topology ContDiff
open MirrorGeometry MirrorSlitSquare MirrorPeriodQuotient

/- Bind the ORIGINAL declared ClosedField and native Fin1 closedness
   to the actual slit primitives. No zero-period premise is used.
   The possibly disconnected overlap is not glued here. -/
theorem slit_subset_union (n : Nat) (s : ℝ) :
    slit n s ⊆ XInfinity := by
  intro p hp
  exact mem_iUnion.mpr ⟨n, stage_nesting n hp.1⟩

theorem field_smooth_slit (w : ClosedField) (n : Nat) (s : ℝ) :
    ContDiffOn ℝ ∞ w.value (slit n s) :=
  w.smooth.mono (slit_subset_union n s)

theorem field_deriv_slit (w : ClosedField) (n : Nat) (s : ℝ)
    {p : ℂ} (hp : p ∈ slit n s) :
    HasFDerivAt w.value (fderiv ℝ w.value p) p := by
  have hd : DifferentiableOn ℝ w.value (slit n s) :=
    (field_smooth_slit w n s).differentiableOn (by simp)
  exact (hd.differentiableAt ((slit_open n s).mem_nhds hp)).hasFDerivAt

theorem field_symmetric_slit (w : ClosedField) (n : Nat) (s : ℝ)
    {p : ℂ} (hp : p ∈ slit n s) :
    ∀ u v : ℂ, fderiv ℝ w.value p u v =
      fderiv ℝ w.value p v u :=
  (MirrorLocalExactness.closed_iff_symmetric
    (field_deriv_slit w n s hp).differentiableAt).mp
      (w.closed p (slit_subset_union n s hp))

theorem field_slit_primitive (w : ClosedField) (n : Nat) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (slit n s) ∧
      ∀ p ∈ slit n s, HasFDerivAt g (w.value p) p :=
  MirrorSlitPrimitive.slit_primitive n s hs w.value
    (field_smooth_slit w n s) (fderiv ℝ w.value)
    (fun _ hp => field_deriv_slit w n s hp)
    (fun _ hp => field_symmetric_slit w n s hp)

end MirrorClosedFieldSlit

namespace MirrorPrimitiveGluing
open Set Filter
open scoped Topology ContDiff

/- Open preconnected domains are explicit. These constants do not identify
   separate connected components of a punctured-stage overlap. -/
theorem primitive_difference_constant {s : Set ℂ} (hs : IsOpen s)
    (hc : IsPreconnected s) (u v : ℂ → ℝ)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    (hd : EqOn (fderiv ℝ u) (fderiv ℝ v) s) :
    ∃ c : ℝ, EqOn u (fun p => v p + c) s := by
  exact hs.exists_eq_add_of_fderiv_eq hc
    (hu.differentiableOn (by simp)) (hv.differentiableOn (by simp)) hd

theorem primitive_normalized_unique {s : Set ℂ} (hs : IsOpen s)
    (hc : IsPreconnected s) (u v : ℂ → ℝ)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    (hd : EqOn (fderiv ℝ u) (fderiv ℝ v) s)
    {x : ℂ} (hx : x ∈ s) (he : u x = v x) : EqOn u v s := by
  exact hs.eqOn_of_fderiv_eq hc
    (hu.differentiableOn (by simp)) (hv.differentiableOn (by simp))
    (fun p hp => hd hp) hx he

noncomputable def gluePotential (U : Set ℂ) (u v : ℂ → ℝ) (p : ℂ) : ℝ := by
  classical
  exact if p ∈ U then u p else v p

theorem glue_eq_on_charts {U V : Set ℂ} (u v : ℂ → ℝ)
    (he : EqOn u v (U ∩ V)) :
    EqOn (gluePotential U u v) u U ∧ EqOn (gluePotential U u v) v V := by
  classical
  constructor
  · intro p hp
    simp [gluePotential, hp]
  · intro p hpV
    by_cases hpU : p ∈ U
    · simpa [gluePotential, hpU] using he ⟨hpU, hpV⟩
    · simp [gluePotential, hpU]

/- Chart-wide equality produces actual whole-neighbourhood equality. -/
theorem glue_eventually_eq_on_charts {U V : Set ℂ} (u v : ℂ → ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (he : EqOn u v (U ∩ V)) :
    (∀ p ∈ U, gluePotential U u v =ᶠ[𝓝 p] u) ∧
    (∀ p ∈ V, gluePotential U u v =ᶠ[𝓝 p] v) := by
  have hcharts := glue_eq_on_charts u v he
  constructor
  · intro p hp
    exact Filter.mem_of_superset (hU.mem_nhds hp) (fun q hq => hcharts.1 hq)
  · intro p hp
    exact Filter.mem_of_superset (hV.mem_nhds hp) (fun q hq => hcharts.2 hq)

theorem glue_smoothOn {U V : Set ℂ} (u v : ℂ → ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v V)
    (he : EqOn u v (U ∩ V)) :
    ContDiffOn ℝ ∞ (gluePotential U u v) (U ∪ V) := by
  have hlocal := glue_eventually_eq_on_charts u v hU hV he
  intro p hp
  rcases hp with hpU | hpV
  · exact ((hu.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
      (hlocal.1 p hpU)).contDiffWithinAt
  · exact ((hv.contDiffAt (hV.mem_nhds hpV)).congr_of_eventuallyEq
      (hlocal.2 p hpV)).contDiffWithinAt

theorem glue_hasFDerivAt {U V : Set ℂ} (u v : ℂ → ℝ)
    (w : ℂ → ℂ →L[ℝ] ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (he : EqOn u v (U ∩ V))
    (hu : ∀ p ∈ U, HasFDerivAt u (w p) p)
    (hv : ∀ p ∈ V, HasFDerivAt v (w p) p) :
    ∀ p ∈ U ∪ V, HasFDerivAt (gluePotential U u v) (w p) p := by
  have hlocal := glue_eventually_eq_on_charts u v hU hV he
  intro p hp
  rcases hp with hpU | hpV
  · exact (hu p hpU).congr_of_eventuallyEq (hlocal.1 p hpU)
  · exact (hv p hpV).congr_of_eventuallyEq (hlocal.2 p hpV)

/- One additive constant aligns primitives on a preconnected overlap.
   The actual multi-component punctured-stage cover is not supplied here. -/
theorem primitive_two_chart_gluing {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (u v : ℂ → ℝ)
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v V)
    (w : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : ∀ p ∈ U, HasFDerivAt u (w p) p)
    (hdv : ∀ p ∈ V, HasFDerivAt v (w p) p) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (U ∪ V) ∧
      ∀ p ∈ U ∪ V, HasFDerivAt g (w p) p := by
  obtain ⟨c, he⟩ := primitive_difference_constant (hU.inter hV) hc u v
    (hu.mono inter_subset_left) (hv.mono inter_subset_right)
    (fun p hp => (hdu p hp.1).fderiv.trans (hdv p hp.2).fderiv.symm)
  have hvc : ContDiffOn ℝ ∞ (fun p => v p + c) V :=
    hv.add contDiff_const.contDiffOn
  refine ⟨gluePotential U u (fun p => v p + c),
    glue_smoothOn u (fun p => v p + c) hU hV hu hvc he, ?_⟩
  exact glue_hasFDerivAt u (fun p => v p + c) w hU hV he hdu
    (fun p hp => (hdv p hp).add_const c)

end MirrorPrimitiveGluing

namespace MirrorOverlapBands
open Set MirrorGeometry MirrorSlitSquare MirrorPuncturedCorridor
open scoped Topology

def lower (n : Nat) (k : Fin (n+1)) : ℝ :=
  if k.val=n then a n else c (k.val+1)+rho (k.val+1)
def upper (n : Nat) (k : Fin (n+1)) : ℝ :=
  if k.val=0 then 2 else c k.val-rho k.val
def band (n : Nat) (k : Fin (n+1)) : Set ℂ :=
  {p | lower n k<p.re ∧ p.re<upper n k ∧ -1<p.im ∧ p.im<1}

theorem lower_lt_upper (n : Nat) (k : Fin (n+1)) :
    lower n k<upper n k := by
  by_cases h0 : k.val=0
  · rw [upper,if_pos h0]
    by_cases hn : k.val=n
    · rw [lower,if_pos hn]
      dsimp [a]
      linarith [c_le_one n]
    · rw [lower,if_neg hn]
      have hc := c_later_le_half (show 0<k.val+1 by omega)
      have hz : c 0=1 := by norm_num [c]
      rw [hz] at hc
      dsimp [rho]
      linarith
  · rw [upper,if_neg h0]
    by_cases hn : k.val=n
    · rw [lower,if_pos hn,hn]
      dsimp [a,rho]
      linarith [c_pos n]
    · rw [lower,if_neg hn]
      simp only [rho,c_succ]
      linarith [c_pos k.val]

theorem lower_ge_a (n : Nat) (k : Fin (n+1)) : a n≤lower n k := by
  by_cases hn : k.val=n
  · simp [lower,hn]
  · have hk : k.val+1≤n := by omega
    have hc := c_antitone hk
    rw [lower,if_neg hn]
    dsimp [rho,a]
    linarith [c_pos n]

theorem upper_le_two (n : Nat) (k : Fin (n+1)) : upper n k≤2 := by
  by_cases h0 : k.val=0
  · simp [upper,h0]
  · rw [upper,if_neg h0]
    dsimp [rho]
    linarith [c_le_one k.val,c_pos k.val]

theorem band_open (n : Nat) (k : Fin (n+1)) : IsOpen (band n k) := by
  have hL : IsOpen {p : ℂ | lower n k<p.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hR : IsOpen {p : ℂ | p.re<upper n k} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hB : IsOpen {p : ℂ | -1<p.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hT : IsOpen {p : ℂ | p.im<1} :=
    isOpen_lt Complex.continuous_im continuous_const
  exact hL.inter (hR.inter (hB.inter hT))

theorem band_convex (n : Nat) (k : Fin (n+1)) : Convex ℝ (band n k) := by
  apply convex_iff_segment_subset.mpr
  intro p hp q hq
  rw [segment_eq_image_lineMap]
  rintro z ⟨t,ht,rfl⟩
  have hx := interp_bounds ⟨hp.1,hp.2.1⟩ ⟨hq.1,hq.2.1⟩ ht
  have hy := interp_bounds ⟨hp.2.2.1,hp.2.2.2⟩ ⟨hq.2.2.1,hq.2.2.2⟩ ht
  change lower n k<(AffineMap.lineMap p q t).re ∧
    (AffineMap.lineMap p q t).re<upper n k ∧
    -1<(AffineMap.lineMap p q t).im ∧ (AffineMap.lineMap p q t).im<1
  rw [line_re,line_im]
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem band_nonempty (n : Nat) (k : Fin (n+1)) : (band n k).Nonempty := by
  refine ⟨⟨(lower n k+upper n k)/2,0⟩,?_⟩
  change lower n k<(lower n k+upper n k)/2 ∧
    (lower n k+upper n k)/2<upper n k ∧ (-1:ℝ)<0 ∧ (0:ℝ)<1
  have h := lower_lt_upper n k
  exact ⟨by linarith,by linarith,by norm_num,by norm_num⟩

theorem band_subset_overlap (n : Nat) (k : Fin (n+1)) :
    band n k⊆rectangle n∩verticalClear n := by
  intro p hp
  refine ⟨⟨(lower_ge_a n k).trans_lt hp.1,hp.2.1.trans_le (upper_le_two n k),
    hp.2.2.1,hp.2.2.2⟩,(mem_verticalClear n p).mpr ?_⟩
  intro j
  by_cases hj : j.val+1≤k.val
  · have h0 : k.val≠0 := by omega
    have hR : p.re<c k.val-rho k.val := by
      simpa [upper,h0] using hp.2.1
    have hc := c_antitone hj
    have hx : p.re<c (j.val+1)-rho (j.val+1) := by
      dsimp [rho] at *
      linarith
    rw [abs_of_neg (show p.re-c (j.val+1)<0 by
      dsimp [rho] at hx; linarith [c_pos (j.val+1)])]
    linarith
  · have hn : k.val≠n := by omega
    have hL : c (k.val+1)+rho (k.val+1)<p.re := by
      simpa [lower,hn] using hp.1
    have hc := c_antitone (show k.val+1≤j.val+1 by omega)
    have hx : c (j.val+1)+rho (j.val+1)<p.re := by
      dsimp [rho] at *
      linarith
    rw [abs_of_pos (show 0<p.re-c (j.val+1) by
      dsimp [rho] at hx; linarith [c_pos (j.val+1)])]
    linarith

/- Constructive finite cut at centres. Actual clearance excludes equality.
   It searches the WHOLE finite ordered population, not sampled points. -/
theorem center_cut (n : Nat) (x : ℝ) :
    (∀ j : Nat, 1≤j → j≤n → x≠c j) →
      ∃ k : Nat, k≤n ∧ (k≠0 → x<c k) ∧ (k<n → c (k+1)<x) := by
  induction n with
  | zero =>
      intro hne
      exact ⟨0,le_rfl,(by intro h; exact False.elim (h rfl)),(by intro h; omega)⟩
  | succ n ih =>
      intro hne
      obtain ⟨k,hkn,hup,hlo⟩ := ih (fun j hj hjn => hne j hj (by omega))
      by_cases hlt : k<n
      · exact ⟨k,by omega,hup,fun _ => hlo hlt⟩
      · have he : k=n := by omega
        subst k
        rcases lt_trichotomy x (c (n+1)) with hl | heq | hr
        · exact ⟨n+1,le_rfl,fun _ => hl,(by intro h; omega)⟩
        · exact False.elim ((hne (n+1) (by omega) le_rfl) heq)
        · exact ⟨n,Nat.le_succ n,hup,fun _ => hr⟩

theorem overlap_mem_band {n : Nat} {p : ℂ}
    (hp : p∈rectangle n∩verticalClear n) :
    ∃ k : Fin (n+1), p∈band n k := by
  have hne : ∀ j : Nat, 1≤j → j≤n → p.re≠c j := by
    intro j hj hjn heq
    have hd := (mem_verticalClear n p).mp hp.2 ⟨j-1,by omega⟩
    have he : j-1+1=j := by omega
    change rho (j-1+1)< |p.re-c (j-1+1)| at hd
    rw [he,heq,sub_self,abs_zero] at hd
    have hpos : 0<rho j := div_pos (c_pos j) (by norm_num)
    linarith
  obtain ⟨k,hkn,hup,hlo⟩ := center_cut n p.re hne
  let i : Fin (n+1) := ⟨k,by omega⟩
  have hL : lower n i<p.re := by
    by_cases hk : k=n
    · simpa [lower,i,hk] using hp.1.1
    · have hsmall : k<n := by omega
      have hd := (mem_verticalClear n p).mp hp.2 ⟨k,hsmall⟩
      change rho (k+1)< |p.re-c (k+1)| at hd
      rw [abs_of_pos (sub_pos.mpr (hlo hsmall))] at hd
      have hh : c (k+1)+rho (k+1)<p.re := by linarith
      simpa [lower,i,hk] using hh
  have hR : p.re<upper n i := by
    by_cases hk : k=0
    · simpa [upper,i,hk] using hp.1.2.1
    · have hd := (mem_verticalClear n p).mp hp.2 ⟨k-1,by omega⟩
      have he : k-1+1=k := by omega
      change rho (k-1+1)< |p.re-c (k-1+1)| at hd
      rw [he,abs_of_neg (sub_neg.mpr (hup hk))] at hd
      have hh : p.re<c k-rho k := by linarith
      simpa [upper,i,hk] using hh
  exact ⟨i,hL,hR,hp.1.2.2.1,hp.1.2.2.2⟩

theorem band_disjoint_ordered (n : Nat) (i j : Fin (n+1))
    (hij : i.val<j.val) : Disjoint (band n i) (band n j) := by
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  have hi : i.val≠n := by omega
  have hj : j.val≠0 := by omega
  have hL : c (i.val+1)+rho (i.val+1)<p.re := by
    simpa [lower,hi] using hpi.1
  have hR : p.re<c j.val-rho j.val := by
    simpa [upper,hj] using hpj.2.1
  have hc := c_antitone (show i.val+1≤j.val by omega)
  dsimp [rho] at *
  linarith [c_pos (i.val+1),c_pos j.val]

theorem band_unique {n : Nat} {p : ℂ} {i j : Fin (n+1)}
    (hi : p∈band n i) (hj : p∈band n j) : i=j := by
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hij | he | hji
  · exact False.elim (Set.disjoint_left.mp (band_disjoint_ordered n i j hij) hi hj)
  · exact he
  · exact False.elim (Set.disjoint_left.mp (band_disjoint_ordered n j i hji) hj hi)

theorem overlap_eq_union_bands (n : Nat) :
    rectangle n∩verticalClear n=⋃ k : Fin (n+1), band n k := by
  ext p
  constructor
  · intro hp
    exact Set.mem_iUnion.mpr (overlap_mem_band hp)
  · intro hp
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hp
    exact band_subset_overlap n k hk

theorem slit_overlap_eq_union_bands (n : Nat) :
    slit n 1∩slit n (-1)=⋃ k : Fin (n+1), band n k := by
  rw [slit_overlap,overlap_eq_union_bands]

theorem band_preconnected (n : Nat) (k : Fin (n+1)) :
    IsPreconnected (band n k) :=
  (band_convex n k).isPreconnected

end MirrorOverlapBands

namespace MirrorBandTransition
open Set
open scoped Topology ContDiff
open MirrorGeometry MirrorSlitSquare MirrorSlitPrimitive
open MirrorClosedFieldSlit MirrorOverlapBands MirrorPeriodQuotient

/- Canonical ORIGINAL ClosedField primitives agree up to a constant on
   EACH actual band. Constants on distinct bands are not aligned here. -/
theorem canonical_smooth (w : ClosedField) (n : Nat) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    ContDiffOn ℝ ∞ (chartPotential w.value s) (slit n s) :=
  chart_contDiffOn n s hs w.value
    (field_smooth_slit w n s) (fderiv ℝ w.value)
    (fun _ hp => field_deriv_slit w n s hp)
    (fun _ hp => field_symmetric_slit w n s hp)

theorem canonical_deriv (w : ClosedField) (n : Nat) (s : ℝ)
    (hs : s = 1 ∨ s = -1) {p : ℂ} (hp : p ∈ slit n s) :
    HasFDerivAt (chartPotential w.value s) (w.value p) p :=
  chart_hasFDerivAt n s hs w.value
    (field_smooth_slit w n s) (fderiv ℝ w.value)
    (fun _ hq => field_deriv_slit w n s hq)
    (fun _ hq => field_symmetric_slit w n s hq) hp

theorem band_upper (n : Nat) (k : Fin (n+1)) :
    band n k ⊆ slit n 1 := by
  intro p hp
  have h : p ∈ slit n 1 ∩ slit n (-1) := by
    rw [slit_overlap]
    exact band_subset_overlap n k hp
  exact h.1

theorem band_lower (n : Nat) (k : Fin (n+1)) :
    band n k ⊆ slit n (-1) := by
  intro p hp
  have h : p ∈ slit n 1 ∩ slit n (-1) := by
    rw [slit_overlap]
    exact band_subset_overlap n k hp
  exact h.2

theorem band_transition_constant (w : ClosedField) (n : Nat)
    (k : Fin (n+1)) :
    ∃ c : ℝ, EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + c) (band n k) := by
  apply MirrorPrimitiveGluing.primitive_difference_constant
    (band_open n k) (band_preconnected n k)
    (chartPotential w.value 1) (chartPotential w.value (-1))
    ((canonical_smooth w n 1 (Or.inl rfl)).mono (band_upper n k))
    ((canonical_smooth w n (-1) (Or.inr rfl)).mono (band_lower n k))
  intro p hp
  exact (canonical_deriv w n 1 (Or.inl rfl) (band_upper n k hp)).fderiv.trans
    (canonical_deriv w n (-1) (Or.inr rfl) (band_lower n k hp)).fderiv.symm

end MirrorBandTransition

namespace MirrorMarkedTransitionPeriods
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorPuncturedCorridor MirrorSlitSquare MirrorSlitPrimitive
open MirrorMarkedLoopDiagonal MirrorPeriodQuotient MirrorBandTransition
open MirrorOverlapBands MirrorPrimitiveGluing

/- Positive marked circles read the difference of the constants on their
   left and right bands. Finite-stage exactness below concerns restrictions
   of the ORIGINAL union ClosedField; no union-global primitive is asserted. -/
abbrev rightIndex (n j : Nat) (hjn : j ≤ n) : Fin (n+1) :=
  ⟨j-1, by omega⟩
abbrev leftIndex (n j : Nat) (hjn : j ≤ n) : Fin (n+1) :=
  ⟨j, by omega⟩

theorem param_re (j : Nat) (t : ℝ) :
    (param j t).re = c j + loopRadius j * Real.cos (2*Real.pi*t) := by
  have he : param j t - center j =
      circleMap 0 (loopRadius j) (2*Real.pi*t) :=
    by simpa only [param] using circleMap_sub_center (MirrorGeometry.center j) (loopRadius j) (2*Real.pi*t)
  have hre : (param j t).re - c j =
      loopRadius j * Real.cos (2*Real.pi*t) := by
    simpa only [Complex.sub_re, MirrorGeometry.center, Complex.ofReal_re,
      circleMap_zero_re] using congrArg Complex.re he
  linarith

theorem param_im (j : Nat) (t : ℝ) :
    (param j t).im = loopRadius j * Real.sin (2*Real.pi*t) := by
  have he : param j t - center j =
      circleMap 0 (loopRadius j) (2*Real.pi*t) :=
    by simpa only [param] using circleMap_sub_center (MirrorGeometry.center j) (loopRadius j) (2*Real.pi*t)
  simpa only [Complex.sub_im, MirrorGeometry.center, Complex.ofReal_im,
    sub_zero, circleMap_zero_im] using congrArg Complex.im he

theorem param_at_zero (j : Nat) :
    param j 0 = point (c j + loopRadius j) 0 := by
  apply Complex.ext <;> simp [param_re, param_im, point]

theorem param_at_half (j : Nat) :
    param j (1/2:ℝ) = point (c j - loopRadius j) 0 := by
  have ha : 2*Real.pi*(1/2:ℝ)=Real.pi := by ring
  apply Complex.ext
  · rw [param_re, ha]; norm_num [point]; ring
  · rw [param_im, ha]; norm_num [point]

theorem param_at_one (j : Nat) :
    param j 1 = point (c j + loopRadius j) 0 :=
  (param_endpoints j).trans (param_at_zero j)

theorem right_pole_band (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    param j 0 ∈ band n (rightIndex n j hjn) := by
  rw [param_at_zero]
  have hn : j-1 ≠ n := by omega
  have he : j-1+1 = j := by omega
  change lower n ⟨j-1, by omega⟩ < c j+loopRadius j ∧
    c j+loopRadius j < upper n ⟨j-1, by omega⟩ ∧ (-1:ℝ)<0 ∧ (0:ℝ)<1
  constructor
  · simp only [lower, if_neg hn, he]
    dsimp [rho, loopRadius]
    linarith [c_pos j]
  constructor
  · by_cases h0 : j-1=0
    · simp only [upper, if_pos h0]
      dsimp [loopRadius]
      linarith [c_le_one j]
    · simp only [upper, if_neg h0]
      have hc : c j=c (j-1)/2 := by
        simpa only [he] using c_succ (j-1)
      dsimp [loopRadius, rho]
      rw [hc]
      linarith [c_pos (j-1)]
  · exact ⟨by norm_num, by norm_num⟩

theorem left_pole_band (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    param j (1/2:ℝ) ∈ band n (leftIndex n j hjn) := by
  rw [param_at_half]
  have h0 : j≠0 := by omega
  change lower n ⟨j, by omega⟩ < c j-loopRadius j ∧
    c j-loopRadius j < upper n ⟨j, by omega⟩ ∧ (-1:ℝ)<0 ∧ (0:ℝ)<1
  constructor
  · by_cases hn : j=n
    · simp only [lower, if_pos hn]
      subst n
      dsimp [a, loopRadius]
      linarith [c_pos j]
    · simp only [lower, if_neg hn]
      simp only [rho, loopRadius, c_succ]
      linarith [c_pos j]
  constructor
  · simp only [upper, if_neg h0]
    dsimp [rho, loopRadius]
    linarith [c_pos j]
  · exact ⟨by norm_num, by norm_num⟩

theorem upper_half_slit (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/2)) :
    param j t ∈ slit n 1 := by
  have hX := param_mem_stage n j hj hjn t
  by_cases h0 : t=0
  · subst t
    exact ⟨hX, Or.inr (verticalClear_of_real hX (by simp [param_im]))⟩
  by_cases hh : t=(1/2:ℝ)
  · subst t
    have ha : 2*Real.pi*(1/2:ℝ)=Real.pi := by ring
    exact ⟨hX, Or.inr (verticalClear_of_real hX (by rw [param_at_half]; rfl))⟩
  have hlo : 0 < 2*Real.pi*t := mul_pos (by positivity) (lt_of_le_of_ne ht.1 (Ne.symm h0))
  have hhi : 2*Real.pi*t < Real.pi := by
    have hp := mul_pos (show 0 < 2*Real.pi by positivity)
      (sub_pos.mpr (lt_of_le_of_ne ht.2 hh))
    linarith
  have hy : 0 < (param j t).im := by
    rw [param_im]
    exact mul_pos (loopRadius_pos j) (Real.sin_pos_of_pos_of_lt_pi hlo hhi)
  exact ⟨hX, Or.inl (by change 0 < (1:ℝ)*(param j t).im; simpa using hy)⟩

theorem lower_half_slit (n j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n)
    {t : ℝ} (ht : t ∈ Icc (1/2:ℝ) 1) :
    param j t ∈ slit n (-1) := by
  have hX := param_mem_stage n j hj hjn t
  by_cases hh : t=(1/2:ℝ)
  · subst t
    have ha : 2*Real.pi*(1/2:ℝ)=Real.pi := by ring
    exact ⟨hX, Or.inr (verticalClear_of_real hX (by rw [param_at_half]; rfl))⟩
  by_cases h1 : t=1
  · subst t
    exact ⟨hX, Or.inr (verticalClear_of_real hX (by simp [param_im,Real.sin_two_pi]))⟩
  have hlo : -Real.pi < 2*Real.pi*t-2*Real.pi := by
    have hp := mul_pos (show 0 < 2*Real.pi by positivity)
      (sub_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm hh)))
    linarith
  have hhi : 2*Real.pi*t-2*Real.pi < 0 := by
    have hp := mul_pos (show 0 < 2*Real.pi by positivity)
      (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))
    linarith
  have hs : Real.sin (2*Real.pi*t) < 0 := by
    simpa only [Real.sin_sub_two_pi] using Real.sin_neg_of_neg_of_neg_pi_lt hhi hlo
  have hy : (param j t).im < 0 := by
    rw [param_im]
    exact mul_neg_of_pos_of_neg (loopRadius_pos j) hs
  exact ⟨hX, Or.inl (by change 0 < (-1:ℝ)*(param j t).im; linarith)⟩

noncomputable def transitionConstant (w : ClosedField) (n : Nat)
    (k : Fin (n+1)) : ℝ :=
  Classical.choose (band_transition_constant w n k)

theorem transition_eq (w : ClosedField) (n : Nat) (k : Fin (n+1)) :
    EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + transitionConstant w n k) (band n k) :=
  Classical.choose_spec (band_transition_constant w n k)

theorem transition_constant_unique (w : ClosedField) (n : Nat) (k : Fin (n+1))
    (d : ℝ) (hd : EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + d) (band n k)) :
    d = transitionConstant w n k := by
  obtain ⟨p,hp⟩ := band_nonempty n k
  have h1 := hd hp
  have h2 := transition_eq w n k hp
  linarith

theorem upper_half_hasDerivAt (w : ClosedField) (n j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/2)) :
    HasDerivAt (fun u : ℝ => chartPotential w.value 1 (param j u))
      (w.value (param j t) (velocity j t)) t :=
  (canonical_deriv w n 1 (Or.inl rfl) (upper_half_slit n j hj hjn ht)).comp_hasDerivAt
    t (param_hasDerivAt j t)

theorem lower_half_hasDerivAt (w : ClosedField) (n j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) {t : ℝ} (ht : t ∈ Icc (1/2:ℝ) 1) :
    HasDerivAt (fun u : ℝ => chartPotential w.value (-1) (param j u))
      (w.value (param j t) (velocity j t)) t :=
  (canonical_deriv w n (-1) (Or.inr rfl) (lower_half_slit n j hj hjn ht)).comp_hasDerivAt
    t (param_hasDerivAt j t)

theorem marked_integral_halves (w : ClosedField) (n j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    curveIntegral w.value (markedPath j) =
      (chartPotential w.value 1 (param j (1/2:ℝ)) - chartPotential w.value 1 (param j 0)) +
      (chartPotential w.value (-1) (param j 1) - chartPotential w.value (-1) (param j (1/2:ℝ))) := by
  let f : ℝ → ℝ := fun t => w.value (param j t) (velocity j t)
  have hc : Continuous f := field_pullback_continuous w.value w.smooth j hj
  have hi1 : IntervalIntegrable f volume (0:ℝ) (1/2) := hc.intervalIntegrable _ _
  have hi2 : IntervalIntegrable f volume (1/2:ℝ) 1 := hc.intervalIntegrable _ _
  have hu : (∫ t in (0:ℝ)..(1/2), f t) =
      chartPotential w.value 1 (param j (1/2:ℝ)) - chartPotential w.value 1 (param j 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => chartPotential w.value 1 (param j t)) (f' := f)
    · rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      intro t ht
      exact upper_half_hasDerivAt w n j hj hjn ht
    · exact hi1
  have hl : (∫ t in (1/2:ℝ)..1, f t) =
      chartPotential w.value (-1) (param j 1) - chartPotential w.value (-1) (param j (1/2:ℝ)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => chartPotential w.value (-1) (param j t)) (f' := f)
    · rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      intro t ht
      exact lower_half_hasDerivAt w n j hj hjn ht
    · exact hi2
  have he : curveIntegral w.value (markedPath j) = ∫ t in (0:ℝ)..1, f t := by
    rw [curveIntegral_def]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro t ht
    exact field_curveFun_eq w.value j ht
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hu, hl]

theorem marked_period_transition (w : ClosedField) (n j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    curveIntegral w.value (markedPath j) =
      transitionConstant w n (leftIndex n j hjn) -
        transitionConstant w n (rightIndex n j hjn) := by
  have hR := transition_eq w n (rightIndex n j hjn) (right_pole_band n j hj hjn)
  have hL := transition_eq w n (leftIndex n j hjn) (left_pole_band n j hj hjn)
  have hi := marked_integral_halves w n j hj hjn
  rw [param_endpoints] at hi
  linarith

theorem zero_period_adjacent_constant (w : ClosedField) (n j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n)
    (hz : curveIntegral w.value (markedPath j)=0) :
    transitionConstant w n (leftIndex n j hjn) =
      transitionConstant w n (rightIndex n j hjn) := by
  have he := marked_period_transition w n j hj hjn
  linarith

theorem all_constants_equal_of_zero_marked (w : ClosedField) (n : Nat)
    (hz : ∀ j : Nat, 1 ≤ j → j ≤ n → curveIntegral w.value (markedPath j)=0) :
    ∀ k : Fin (n+1), transitionConstant w n k = transitionConstant w n 0 := by
  intro k
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hle : i.val+1 ≤ n := by omega
    have he := zero_period_adjacent_constant w n (i.val+1) (by omega) hle
      (hz (i.val+1) (by omega) hle)
    have hr : rightIndex n (i.val+1) hle = i.castSucc := by apply Fin.ext; simp [rightIndex]
    have hl : leftIndex n (i.val+1) hle = i.succ := by apply Fin.ext; rfl
    rw [hr,hl] at he
    exact he.trans ih

theorem finite_stage_primitive_of_zero_marked (w : ClosedField) (n : Nat)
    (hz : ∀ j : Nat, 1 ≤ j → j ≤ n → curveIntegral w.value (markedPath j)=0) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (X n) ∧
      ∀ p ∈ X n, HasFDerivAt g (w.value p) p := by
  let u := chartPotential w.value 1
  let d := transitionConstant w n (0 : Fin (n+1))
  let v : ℂ → ℝ := fun p => chartPotential w.value (-1) p + d
  have he : EqOn u v (slit n 1 ∩ slit n (-1)) := by
    intro p hp
    rw [slit_overlap_eq_union_bands] at hp
    obtain ⟨k,hp⟩ := mem_iUnion.mp hp
    have h := transition_eq w n k hp
    rw [all_constants_equal_of_zero_marked w n hz k] at h
    exact h
  have hu := canonical_smooth w n 1 (Or.inl rfl)
  have hv : ContDiffOn ℝ ∞ v (slit n (-1)) :=
    (canonical_smooth w n (-1) (Or.inr rfl)).add contDiff_const.contDiffOn
  refine ⟨gluePotential (slit n 1) u v, ?_, ?_⟩
  · rw [slit_cover]
    exact glue_smoothOn u v (slit_open n 1) (slit_open n (-1)) hu hv he
  · rw [slit_cover]
    apply glue_hasFDerivAt u v w.value (slit_open n 1) (slit_open n (-1)) he
    · intro p hp
      exact canonical_deriv w n 1 (Or.inl rfl) hp
    · intro p hp
      exact (canonical_deriv w n (-1) (Or.inr rfl) hp).add_const d

end MirrorMarkedTransitionPeriods

namespace MirrorUnionPrimitive
open Set Filter
open scoped Topology ContDiff
open MirrorGeometry MirrorPuncturedCorridor MirrorSlitSquare MirrorSlitPrimitive
open MirrorPeriodQuotient MirrorBandTransition MirrorOverlapBands
open MirrorMarkedTransitionPeriods MirrorPrimitiveGluing

/- SAME canonical chart formulas on all levels. Stage-independent constants
   are derived at an actual common point; no whole-overlap connectedness,
   compact-closure or infinite-integration interchange is assumed. -/
theorem common_reference_in_band (n : Nat) :
    point 1 0 ∈ band n (0 : Fin (n+1)) := by
  cases n with
  | zero => norm_num [band, lower, upper, point, a, c, rho]
  | succ n => norm_num [band, lower, upper, point, a, c, rho]

theorem reference_constant_independent (w : ClosedField) (n : Nat) :
    transitionConstant w n (0 : Fin (n+1)) =
      transitionConstant w 0 (0 : Fin 1) := by
  have hn := transition_eq w n 0 (common_reference_in_band n)
  have h0 := transition_eq w 0 0 (common_reference_in_band 0)
  linarith

/- verticalClear alone is NOT asserted monotone; the actual X_n membership
   supplies clearance from the newly added disk. -/
theorem slit_stage_nesting (n : Nat) (s : ℝ) :
    slit n s ⊆ slit (n+1) s := by
  intro p hp
  refine ⟨stage_nesting n hp.1, ?_⟩
  rcases hp.2 with hpos | hclear
  · exact Or.inl hpos
  · apply Or.inr
    apply (mem_verticalClear (n+1) p).mpr
    intro j
    by_cases hj : j.val < n
    · exact (mem_verticalClear n p).mp hclear ⟨j.val, hj⟩
    · have he : j.val = n := by omega
      have hleft : a n < p.re := hp.1.1.1
      have hb : c (n+1) + rho (n+1) < p.re :=
        (next_disk_left_of_boundary n).trans hleft
      have hr : 0 < rho (n+1) := div_pos (c_pos (n+1)) (by norm_num)
      rw [he, abs_of_pos (show 0 < p.re-c (n+1) by linarith)]
      linarith

theorem slit_stages_monotone (s : ℝ) : Monotone (fun n : Nat => slit n s) :=
  monotone_nat_of_le_succ (fun n => slit_stage_nesting n s)

def slitUnion (s : ℝ) : Set ℂ := ⋃ n : Nat, slit (n+1) s

theorem slit_union_open (s : ℝ) : IsOpen (slitUnion s) :=
  isOpen_iUnion (fun n => slit_open (n+1) s)

theorem slit_union_cover : XInfinity = slitUnion 1 ∪ slitUnion (-1) := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hp⟩ := mem_iUnion.mp hp
    rw [slit_cover] at hp
    rcases hp with hp | hp
    · exact Or.inl (mem_iUnion.mpr ⟨n, hp⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨n, hp⟩)
  · rintro (hp | hp)
    · obtain ⟨n, hp⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨n, hp.1⟩
    · obtain ⟨n, hp⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨n, hp.1⟩

theorem union_overlap_one_stage {p : ℂ}
    (hp : p ∈ slitUnion 1 ∩ slitUnion (-1)) :
    ∃ n : Nat, p ∈ slit n 1 ∩ slit n (-1) := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hp.1
  obtain ⟨m, hm⟩ := mem_iUnion.mp hp.2
  exact ⟨max (n+1) (m+1),
    slit_stages_monotone 1 (le_max_left _ _) hn,
    slit_stages_monotone (-1) (le_max_right _ _) hm⟩

theorem canonical_union_smooth (w : ClosedField) (s : ℝ)
    (hs : s=1 ∨ s= -1) :
    ContDiffOn ℝ ∞ (chartPotential w.value s) (slitUnion s) := by
  intro p hp
  obtain ⟨n, hp⟩ := mem_iUnion.mp hp
  exact ((canonical_smooth w (n+1) s hs).contDiffAt
    ((slit_open (n+1) s).mem_nhds hp)).contDiffWithinAt

theorem canonical_union_deriv (w : ClosedField) (s : ℝ)
    (hs : s=1 ∨ s= -1) {p : ℂ} (hp : p ∈ slitUnion s) :
    HasFDerivAt (chartPotential w.value s) (w.value p) p := by
  obtain ⟨n, hp⟩ := mem_iUnion.mp hp
  exact canonical_deriv w (n+1) s hs hp

theorem union_overlap_eq_of_zero_marked (w : ClosedField)
    (hz : ∀ j : Nat, 1 ≤ j → curveIntegral w.value (MirrorMarkedLoopDiagonal.markedPath j)=0) :
    EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + transitionConstant w 0 (0 : Fin 1))
      (slitUnion 1 ∩ slitUnion (-1)) := by
  intro p hp
  obtain ⟨n, hp⟩ := union_overlap_one_stage hp
  rw [slit_overlap_eq_union_bands] at hp
  obtain ⟨k, hk⟩ := mem_iUnion.mp hp
  have he := transition_eq w n k hk
  rw [all_constants_equal_of_zero_marked w n (fun j hj _ => hz j hj) k,
    reference_constant_independent w n] at he
  exact he

/- Actual global primitive on the open union for the ORIGINAL carrier.
   Quotient injectivity and intrinsic/linear identification are separate. -/
theorem union_primitive_of_zero_marked (w : ClosedField)
    (hz : ∀ j : Nat, 1 ≤ j → curveIntegral w.value (MirrorMarkedLoopDiagonal.markedPath j)=0) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g XInfinity ∧
      ∀ p ∈ XInfinity, HasFDerivAt g (w.value p) p := by
  let u := chartPotential w.value 1
  let d := transitionConstant w 0 (0 : Fin 1)
  let v : ℂ → ℝ := fun p => chartPotential w.value (-1) p + d
  have he : EqOn u v (slitUnion 1 ∩ slitUnion (-1)) :=
    union_overlap_eq_of_zero_marked w hz
  have hu := canonical_union_smooth w 1 (Or.inl rfl)
  have hv : ContDiffOn ℝ ∞ v (slitUnion (-1)) :=
    (canonical_union_smooth w (-1) (Or.inr rfl)).add contDiff_const.contDiffOn
  refine ⟨gluePotential (slitUnion 1) u v, ?_, ?_⟩
  · rw [slit_union_cover]
    exact glue_smoothOn u v (slit_union_open 1) (slit_union_open (-1)) hu hv he
  · rw [slit_union_cover]
    apply glue_hasFDerivAt u v w.value (slit_union_open 1) (slit_union_open (-1)) he
    · intro p hp
      exact canonical_union_deriv w 1 (Or.inl rfl) hp
    · intro p hp
      exact (canonical_union_deriv w (-1) (Or.inr rfl) hp).add_const d

end MirrorUnionPrimitive

namespace MirrorPeriodInjectivity
open Set Filter
open scoped Topology ContDiff
open MirrorGeometry MirrorPeriodQuotient MirrorLocalExactness MirrorUnionPrimitive
open MirrorMarkedLoopDiagonal

/-- Difference in the ORIGINAL carrier, with closedness from native derivative symmetry. -/
def difference (u v : ClosedField) : ClosedField where
  value := fun p => v.value p - u.value p
  smooth := v.smooth.sub u.smooth
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt (union_open.mem_nhds hp)).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ v.value p :=
      (v.smooth.contDiffAt (union_open.mem_nhds hp)).differentiableAt (by simp)
    have su := (closed_iff_symmetric hu).mp (u.closed p hp)
    have sv := (closed_iff_symmetric hv).mp (v.closed p hp)
    apply (closed_iff_symmetric (hv.sub hu)).mpr
    intro a b
    rw [fderiv_sub hv hu]
    simp only [sub_apply]
    rw [sv a b, su a b]

theorem difference_period (u v : ClosedField) (j : Nat) (hj : 1 ≤ j) :
    curveIntegral (difference u v).value (markedPath j) =
      curveIntegral v.value (markedPath j) - curveIntegral u.value (markedPath j) := by
  exact curveIntegral_fun_sub
    (smooth_field_integrable v.value v.smooth j hj)
    (smooth_field_integrable u.value u.smooth j hj)

/-- Equal positive periods give exactly the declared union-only exact relation. -/
theorem periods_equal_exactRel (u v : ClosedField) (he : periods u = periods v) :
    ExactRel u v := by
  have hz : ∀ j : Nat, 1 ≤ j → curveIntegral (difference u v).value (markedPath j)=0 := by
    intro j hj
    have h := congrFun he (⟨j, hj⟩ : PositiveIndex)
    change curveIntegral u.value (markedPath j) = curveIntegral v.value (markedPath j) at h
    rw [difference_period u v j hj, h, sub_self]
  obtain ⟨g, hg, hd⟩ := union_primitive_of_zero_marked (difference u v) hz
  refine ⟨g, hg, ?_⟩
  intro p hp
  have hdiff : v.value p - u.value p = fderiv ℝ g p := (hd p hp).fderiv.symm
  calc
    v.value p = (v.value p - u.value p) + u.value p := (sub_add_cancel _ _).symm
    _ = fderiv ℝ g p + u.value p := congrArg (fun a => a + u.value p) hdiff
    _ = u.value p + fderiv ℝ g p := add_comm _ _

theorem exactRel_iff_periods (u v : ClosedField) :
    ExactRel u v ↔ periods u = periods v :=
  ⟨fun h => exactRel_periods h, periods_equal_exactRel u v⟩

theorem quotientPeriods_injective : Function.Injective quotientPeriods := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro u v h
  apply Quotient.sound
  exact periods_equal_exactRel u v h

theorem quotientPeriods_bijective : Function.Bijective quotientPeriods :=
  ⟨quotientPeriods_injective, quotientPeriods_surjective⟩

theorem realiseClass_quotientPeriods (q : FieldQuotient) :
    realiseClass (quotientPeriods q) = q := by
  apply quotientPeriods_injective
  exact quotientPeriods_realiseClass (quotientPeriods q)

/-- Declared SET equivalence; no intrinsic deRham, linear or topological identification. -/
def periodEquiv : FieldQuotient ≃ (PositiveIndex → ℝ) where
  toFun := quotientPeriods
  invFun := realiseClass
  left_inv := realiseClass_quotientPeriods
  right_inv := quotientPeriods_realiseClass

end MirrorPeriodInjectivity

namespace MirrorFiniteCarrier
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorSlitSquare MirrorSlitPrimitive MirrorMarkedLoopDiagonal
open MirrorPeriodQuotient MirrorOverlapBands MirrorPrimitiveGluing
open MirrorBandTransition MirrorMarkedTransitionPeriods

/-- Finite-only data on actual X_n; explicitly distinct from the original union carrier. -/
structure StageField (n : Nat) where
  value : ℂ → ℂ →L[ℝ] ℝ
  smooth : ContDiffOn ℝ ∞ value (X n)
  closed : ∀ p ∈ X n, extDeriv (MirrorExteriorClosedness.oneForm value) p = 0

theorem stage_subset_union (n : Nat) : X n ⊆ XInfinity := by
  intro p hp
  exact mem_iUnion.mpr ⟨n, stage_nesting n hp⟩

/-- Typed restriction of the ORIGINAL union object, without asserting the converse. -/
def restrictUnion (w : ClosedField) (n : Nat) : StageField n where
  value := w.value
  smooth := w.smooth.mono (stage_subset_union n)
  closed := fun p hp => w.closed p (stage_subset_union n hp)

def restrictStage {n m : Nat} (hnm : n ≤ m) (w : StageField m) : StageField n where
  value := w.value
  smooth := w.smooth.mono (stages_monotone hnm)
  closed := fun p hp => w.closed p (stages_monotone hnm hp)

theorem field_smooth_slit (n : Nat) (w : StageField n) (s : ℝ) :
    ContDiffOn ℝ ∞ w.value (slit n s) :=
  w.smooth.mono (fun _ hp => hp.1)

theorem field_deriv_slit (n : Nat) (w : StageField n) (s : ℝ)
    {p : ℂ} (hp : p ∈ slit n s) :
    HasFDerivAt w.value (fderiv ℝ w.value p) p := by
  have hd : DifferentiableOn ℝ w.value (slit n s) :=
    (field_smooth_slit n w s).differentiableOn (by simp)
  exact (hd.differentiableAt ((slit_open n s).mem_nhds hp)).hasFDerivAt

theorem field_symmetric_slit (n : Nat) (w : StageField n) (s : ℝ)
    {p : ℂ} (hp : p ∈ slit n s) :
    ∀ u v : ℂ, fderiv ℝ w.value p u v = fderiv ℝ w.value p v u :=
  (MirrorLocalExactness.closed_iff_symmetric
    (field_deriv_slit n w s hp).differentiableAt).mp (w.closed p hp.1)

theorem canonical_smooth (n : Nat) (w : StageField n) (s : ℝ)
    (hs : s=1 ∨ s= -1) :
    ContDiffOn ℝ ∞ (chartPotential w.value s) (slit n s) :=
  chart_contDiffOn n s hs w.value
    (field_smooth_slit n w s) (fderiv ℝ w.value)
    (fun _ hp => field_deriv_slit n w s hp)
    (fun _ hp => field_symmetric_slit n w s hp)

theorem canonical_deriv (n : Nat) (w : StageField n) (s : ℝ)
    (hs : s=1 ∨ s= -1) {p : ℂ} (hp : p ∈ slit n s) :
    HasFDerivAt (chartPotential w.value s) (w.value p) p :=
  chart_hasFDerivAt n s hs w.value
    (field_smooth_slit n w s) (fderiv ℝ w.value)
    (fun _ hq => field_deriv_slit n w s hq)
    (fun _ hq => field_symmetric_slit n w s hq) hp

theorem field_pullback_continuous (n : Nat) (w : StageField n)
    (j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    Continuous (fun t : ℝ => w.value (param j t) (velocity j t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : ContinuousAt (fun u : ℝ => w.value (param j u)) t :=
    (w.smooth.contDiffAt ((stage_open n).mem_nhds
      (param_mem_stage n j hj hjn t))).continuousAt.comp (param_smooth j).continuous.continuousAt
  exact hc.clm_apply (MirrorOffDiagonalPeriods.velocity_continuous j).continuousAt

theorem field_integrable (n : Nat) (w : StageField n)
    (j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    CurveIntegrable w.value (markedPath j) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => w.value (param j t) (velocity j t)) ?_).mpr
  · exact (field_pullback_continuous n w j hj hjn).intervalIntegrable 0 1
  · rw [uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro t ht
    exact field_curveFun_eq w.value j ⟨ht.1.le,ht.2.le⟩

theorem band_transition_constant (n : Nat) (w : StageField n) (k : Fin (n+1)) :
    ∃ c : ℝ, EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p+c) (band n k) := by
  apply primitive_difference_constant (band_open n k) (band_preconnected n k)
    (chartPotential w.value 1) (chartPotential w.value (-1))
    ((canonical_smooth n w 1 (Or.inl rfl)).mono (band_upper n k))
    ((canonical_smooth n w (-1) (Or.inr rfl)).mono (band_lower n k))
  intro p hp
  exact (canonical_deriv n w 1 (Or.inl rfl) (band_upper n k hp)).fderiv.trans
    (canonical_deriv n w (-1) (Or.inr rfl) (band_lower n k hp)).fderiv.symm

noncomputable def transitionConstant (n : Nat) (w : StageField n)
    (k : Fin (n+1)) : ℝ :=
  Classical.choose (band_transition_constant n w k)

theorem transition_eq (n : Nat) (w : StageField n) (k : Fin (n+1)) :
    EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + transitionConstant n w k) (band n k) :=
  Classical.choose_spec (band_transition_constant n w k)

theorem transition_constant_unique (n : Nat) (w : StageField n) (k : Fin (n+1))
    (d : ℝ) (hd : EqOn (chartPotential w.value 1)
      (fun p => chartPotential w.value (-1) p + d) (band n k)) :
    d = transitionConstant n w k := by
  obtain ⟨p,hp⟩ := band_nonempty n k
  have h1 := hd hp
  have h2 := transition_eq n w k hp
  linarith

theorem upper_half_hasDerivAt (n : Nat) (w : StageField n) (j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/2)) :
    HasDerivAt (fun u : ℝ => chartPotential w.value 1 (param j u))
      (w.value (param j t) (velocity j t)) t :=
  (canonical_deriv n w 1 (Or.inl rfl) (upper_half_slit n j hj hjn ht)).comp_hasDerivAt
    t (param_hasDerivAt j t)

theorem lower_half_hasDerivAt (n : Nat) (w : StageField n) (j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) {t : ℝ} (ht : t ∈ Icc (1/2:ℝ) 1) :
    HasDerivAt (fun u : ℝ => chartPotential w.value (-1) (param j u))
      (w.value (param j t) (velocity j t)) t :=
  (canonical_deriv n w (-1) (Or.inr rfl) (lower_half_slit n j hj hjn ht)).comp_hasDerivAt
    t (param_hasDerivAt j t)

theorem marked_integral_halves (n : Nat) (w : StageField n) (j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    curveIntegral w.value (markedPath j) =
      (chartPotential w.value 1 (param j (1/2:ℝ)) - chartPotential w.value 1 (param j 0)) +
      (chartPotential w.value (-1) (param j 1) - chartPotential w.value (-1) (param j (1/2:ℝ))) := by
  let f : ℝ → ℝ := fun t => w.value (param j t) (velocity j t)
  have hc : Continuous f := field_pullback_continuous n w j hj hjn
  have hi1 : IntervalIntegrable f volume (0:ℝ) (1/2) := hc.intervalIntegrable _ _
  have hi2 : IntervalIntegrable f volume (1/2:ℝ) 1 := hc.intervalIntegrable _ _
  have hu : (∫ t in (0:ℝ)..(1/2), f t) =
      chartPotential w.value 1 (param j (1/2:ℝ)) - chartPotential w.value 1 (param j 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => chartPotential w.value 1 (param j t)) (f' := f)
    · rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      intro t ht
      exact upper_half_hasDerivAt n w j hj hjn ht
    · exact hi1
  have hl : (∫ t in (1/2:ℝ)..1, f t) =
      chartPotential w.value (-1) (param j 1) - chartPotential w.value (-1) (param j (1/2:ℝ)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => chartPotential w.value (-1) (param j t)) (f' := f)
    · rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      intro t ht
      exact lower_half_hasDerivAt n w j hj hjn ht
    · exact hi2
  have he : curveIntegral w.value (markedPath j) = ∫ t in (0:ℝ)..1, f t := by
    rw [curveIntegral_def]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro t ht
    exact field_curveFun_eq w.value j ht
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hu, hl]

theorem marked_period_transition (n : Nat) (w : StageField n) (j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    curveIntegral w.value (markedPath j) =
      transitionConstant n w (leftIndex n j hjn) -
        transitionConstant n w (rightIndex n j hjn) := by
  have hR := transition_eq n w (rightIndex n j hjn) (right_pole_band n j hj hjn)
  have hL := transition_eq n w (leftIndex n j hjn) (left_pole_band n j hj hjn)
  have hi := marked_integral_halves n w j hj hjn
  rw [param_endpoints] at hi
  linarith

theorem zero_period_adjacent_constant (n : Nat) (w : StageField n) (j : Nat)
    (hj : 1 ≤ j) (hjn : j ≤ n)
    (hz : curveIntegral w.value (markedPath j)=0) :
    transitionConstant n w (leftIndex n j hjn) =
      transitionConstant n w (rightIndex n j hjn) := by
  have he := marked_period_transition n w j hj hjn
  linarith

theorem all_constants_equal_of_zero_marked (n : Nat) (w : StageField n)
    (hz : ∀ j : Nat, 1 ≤ j → j ≤ n → curveIntegral w.value (markedPath j)=0) :
    ∀ k : Fin (n+1), transitionConstant n w k = transitionConstant n w 0 := by
  intro k
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hle : i.val+1 ≤ n := by omega
    have he := zero_period_adjacent_constant n w (i.val+1) (by omega) hle
      (hz (i.val+1) (by omega) hle)
    have hr : rightIndex n (i.val+1) hle = i.castSucc := by apply Fin.ext; simp [rightIndex]
    have hl : leftIndex n (i.val+1) hle = i.succ := by apply Fin.ext; rfl
    rw [hr,hl] at he
    exact he.trans ih

theorem finite_stage_primitive_of_zero_marked (n : Nat) (w : StageField n)
    (hz : ∀ j : Nat, 1 ≤ j → j ≤ n → curveIntegral w.value (markedPath j)=0) :
    ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (X n) ∧
      ∀ p ∈ X n, HasFDerivAt g (w.value p) p := by
  let u := chartPotential w.value 1
  let d := transitionConstant n w (0 : Fin (n+1))
  let v : ℂ → ℝ := fun p => chartPotential w.value (-1) p + d
  have he : EqOn u v (slit n 1 ∩ slit n (-1)) := by
    intro p hp
    rw [slit_overlap_eq_union_bands] at hp
    obtain ⟨k,hp⟩ := mem_iUnion.mp hp
    have h := transition_eq n w k hp
    rw [all_constants_equal_of_zero_marked n w hz k] at h
    exact h
  have hu := canonical_smooth n w 1 (Or.inl rfl)
  have hv : ContDiffOn ℝ ∞ v (slit n (-1)) :=
    (canonical_smooth n w (-1) (Or.inr rfl)).add contDiff_const.contDiffOn
  refine ⟨gluePotential (slit n 1) u v, ?_, ?_⟩
  · rw [slit_cover]
    exact glue_smoothOn u v (slit_open n 1) (slit_open n (-1)) hu hv he
  · rw [slit_cover]
    apply glue_hasFDerivAt u v w.value (slit_open n 1) (slit_open n (-1)) he
    · intro p hp
      exact canonical_deriv n w 1 (Or.inl rfl) hp
    · intro p hp
      exact (canonical_deriv n w (-1) (Or.inr rfl) hp).add_const d


end MirrorFiniteCarrier

namespace MirrorFiniteQuotient
open Set Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval
open MirrorGeometry MirrorMarkedLoopDiagonal MirrorOffDiagonalPeriods
open MirrorFiniteCarrier

/- Finite exactness and coordinates use only X_n. The original union carrier
   and its quotient remain distinct and are used only in explicit restriction. -/
theorem scalar_smoothAt_stage (n : Nat) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) {p : ℂ} (hp : p ∈ X n) :
    ContDiffAt ℝ ∞ g p := hg.contDiffAt ((stage_open n).mem_nhds hp)

theorem scalar_path_hasDerivAt (n : Nat) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) (i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) (t : ℝ) :
    HasDerivAt (fun u => g (param i u))
      ((fderiv ℝ g (param i t)) (velocity i t)) t := by
  have hd : DifferentiableAt ℝ g (param i t) :=
    (scalar_smoothAt_stage n g hg (param_mem_stage n i hi hin t)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (param_hasDerivAt i t)

theorem gradient_pullback_continuous (n : Nat) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) (i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    Continuous (fun t : ℝ => (fderiv ℝ g (param i t)) (velocity i t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ g) (param i t) :=
    (scalar_smoothAt_stage n g hg (param_mem_stage n i hi hin t)).fderiv_right
      (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hc : ContinuousAt (fun u : ℝ => fderiv ℝ g (param i u)) t :=
    hdf.continuousAt.comp (param_smooth i).continuous.continuousAt
  exact hc.clm_apply (velocity_continuous i).continuousAt

theorem gradient_integrable (n : Nat) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) (i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    CurveIntegrable (fderiv ℝ g) (markedPath i) := by
  unfold CurveIntegrable
  apply (intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => (fderiv ℝ g (param i t)) (velocity i t)) ?_).mpr
  · exact (gradient_pullback_continuous n g hg i hi hin).intervalIntegrable 0 1
  · rw [uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro t ht
    exact MirrorExactPeriods.gradient_curveFun_eq g i ⟨ht.1.le,ht.2.le⟩

theorem gradient_period_zero (n : Nat) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) (i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    curveIntegral (fderiv ℝ g) (markedPath i)=0 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (f := fun t => g (param i t))
    (f' := fun t => (fderiv ℝ g (param i t)) (velocity i t))
    (fun t _ => scalar_path_hasDerivAt n g hg i hi hin t)
    ((gradient_pullback_continuous n g hg i hi hin).intervalIntegrable 0 1)
  rw [param_endpoints i,sub_self] at hFTC
  rw [curveIntegral_def]
  calc
    (∫ t in (0:ℝ)..1, curveIntegralFun (fderiv ℝ g) (markedPath i) t) =
        ∫ t in (0:ℝ)..1, (fderiv ℝ g (param i t)) (velocity i t) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro t ht
      exact MirrorExactPeriods.gradient_curveFun_eq g i ht
    _ = 0 := hFTC

theorem period_of_exact_difference_on_stage (n : Nat)
    (w v : ℂ → ℂ →L[ℝ] ℝ) (g : ℂ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (X n)) (i : Nat) (hi : 1 ≤ i) (hin : i ≤ n)
    (hw : CurveIntegrable w (markedPath i))
    (he : ∀ p ∈ X n, v p=w p+fderiv ℝ g p) :
    curveIntegral v (markedPath i)=curveIntegral w (markedPath i) := by
  have hEq : ∀ t ∈ Icc (0:ℝ) 1,
      curveIntegralFun v (markedPath i) t =
        curveIntegralFun (fun p => w p+fderiv ℝ g p) (markedPath i) t := by
    intro t ht
    simp only [curveIntegralFun_def,path_extend_eq i ht]
    rw [he (param i t) (param_mem_stage n i hi hin t)]
  calc
    curveIntegral v (markedPath i) =
        curveIntegral (fun p => w p+fderiv ℝ g p) (markedPath i) := by
      simp only [curveIntegral_def]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hEq
    _ = curveIntegral w (markedPath i) := by
      rw [curveIntegral_fun_add hw (gradient_integrable n g hg i hi hin),
        gradient_period_zero n g hg i hi hin,add_zero]

/-- Smooth exact difference only on the actual finite domain. -/
def ExactStageRel (n : Nat) (u v : StageField n) : Prop :=
  ∃ g : ℂ → ℝ, ContDiffOn ℝ ∞ g (X n) ∧
    ∀ p ∈ X n, v.value p=u.value p+fderiv ℝ g p

theorem exactStageRel_refl (n : Nat) (u : StageField n) : ExactStageRel n u u := by
  refine ⟨fun _ : ℂ => (0:ℝ),contDiff_const.contDiffOn,?_⟩
  intro p hp
  simp

theorem exactStageRel_symm {n : Nat} {u v : StageField n}
    (h : ExactStageRel n u v) : ExactStageRel n v u := by
  rcases h with ⟨g,hg,he⟩
  refine ⟨fun p => -g p,hg.neg,?_⟩
  intro p hp
  rw [fderiv_fun_neg,he p hp]
  simp

theorem exactStageRel_trans {n : Nat} {u v w : StageField n}
    (huv : ExactStageRel n u v) (hvw : ExactStageRel n v w) : ExactStageRel n u w := by
  rcases huv with ⟨g,hg,he⟩
  rcases hvw with ⟨h,hh,hf⟩
  refine ⟨fun p => g p+h p,hg.add hh,?_⟩
  intro p hp
  have hdg := (scalar_smoothAt_stage n g hg hp).differentiableAt (by simp)
  have hdh := (scalar_smoothAt_stage n h hh hp).differentiableAt (by simp)
  rw [fderiv_fun_add hdg hdh,hf p hp,he p hp]
  exact add_assoc _ _ _

theorem exactStageRel_equivalence (n : Nat) : Equivalence (ExactStageRel n) :=
  ⟨exactStageRel_refl n,fun h => exactStageRel_symm h,fun h₁ h₂ => exactStageRel_trans h₁ h₂⟩

def exactStageSetoid (n : Nat) : Setoid (StageField n) where
  r := ExactStageRel n
  iseqv := exactStageRel_equivalence n
abbrev StageQuotient (n : Nat) := Quotient (exactStageSetoid n)

def stagePeriods (n : Nat) (u : StageField n) : Fin n → ℝ :=
  fun i => curveIntegral u.value (markedPath (i.val+1))

theorem exactStageRel_periods {n : Nat} {u v : StageField n}
    (h : ExactStageRel n u v) : stagePeriods n u=stagePeriods n v := by
  rcases h with ⟨g,hg,he⟩
  funext i
  exact (period_of_exact_difference_on_stage n u.value v.value g hg (i.val+1)
    (by omega) (by omega) (field_integrable n u (i.val+1) (by omega) (by omega)) he).symm

def quotientStagePeriods (n : Nat) : StageQuotient n → (Fin n → ℝ) :=
  Quotient.lift (s := exactStageSetoid n) (stagePeriods n) (fun _ _ h => exactStageRel_periods h)

def stageDifference (n : Nat) (u v : StageField n) : StageField n where
  value := fun p => v.value p-u.value p
  smooth := v.smooth.sub u.smooth
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt ((stage_open n).mem_nhds hp)).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ v.value p :=
      (v.smooth.contDiffAt ((stage_open n).mem_nhds hp)).differentiableAt (by simp)
    have su := (MirrorLocalExactness.closed_iff_symmetric hu).mp (u.closed p hp)
    have sv := (MirrorLocalExactness.closed_iff_symmetric hv).mp (v.closed p hp)
    apply (MirrorLocalExactness.closed_iff_symmetric (hv.sub hu)).mpr
    intro a b
    rw [fderiv_sub hv hu]
    simp only [sub_apply]
    rw [sv a b,su a b]

theorem stageDifference_period (n : Nat) (u v : StageField n)
    (j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    curveIntegral (stageDifference n u v).value (markedPath j)=
      curveIntegral v.value (markedPath j)-curveIntegral u.value (markedPath j) :=
  curveIntegral_fun_sub (field_integrable n v j hj hjn) (field_integrable n u j hj hjn)

theorem periods_equal_exactStageRel (n : Nat) (u v : StageField n)
    (he : stagePeriods n u=stagePeriods n v) : ExactStageRel n u v := by
  have hz : ∀ j : Nat, 1 ≤ j → j ≤ n →
      curveIntegral (stageDifference n u v).value (markedPath j)=0 := by
    intro j hj hjn
    let i : Fin n := ⟨j-1,by omega⟩
    have h := congrFun he i
    change curveIntegral u.value (markedPath (i.val+1))=
      curveIntegral v.value (markedPath (i.val+1)) at h
    have hi : i.val+1=j := by dsimp [i];omega
    rw [hi] at h
    rw [stageDifference_period n u v j hj hjn,h,sub_self]
  obtain ⟨g,hg,hd⟩ := finite_stage_primitive_of_zero_marked n (stageDifference n u v) hz
  refine ⟨g,hg,?_⟩
  intro p hp
  have hdiff : v.value p-u.value p=fderiv ℝ g p := (hd p hp).fderiv.symm
  calc
    v.value p=(v.value p-u.value p)+u.value p := (sub_add_cancel _ _).symm
    _=fderiv ℝ g p+u.value p := congrArg (fun a => a+u.value p) hdiff
    _=u.value p+fderiv ℝ g p := add_comm _ _

theorem exactStageRel_iff_periods (n : Nat) (u v : StageField n) :
    ExactStageRel n u v ↔ stagePeriods n u=stagePeriods n v :=
  ⟨fun h => exactStageRel_periods h,periods_equal_exactStageRel n u v⟩

theorem quotientStagePeriods_injective (n : Nat) : Function.Injective (quotientStagePeriods n) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro u v h
  apply Quotient.sound
  exact periods_equal_exactStageRel n u v h

def finiteExtend (n : Nat) (b : Fin n → ℝ)
    (j : MirrorPeriodQuotient.PositiveIndex) : ℝ :=
  if hj : j.val ≤ n then b ⟨j.val-1,by have hp := j.property;omega⟩ else 0

theorem finiteExtend_apply (n : Nat) (b : Fin n → ℝ) (i : Fin n) :
    finiteExtend n b ⟨i.val+1,by omega⟩=b i := by
  have hle : i.val+1 ≤ n := by omega
  unfold finiteExtend
  rw [dif_pos hle]
  congr 1

noncomputable def stageRealise (n : Nat) (b : Fin n → ℝ) : StageField n :=
  restrictUnion (MirrorPeriodQuotient.realise (finiteExtend n b)) n

theorem stageRealise_periods (n : Nat) (b : Fin n → ℝ) :
    stagePeriods n (stageRealise n b)=b := by
  funext i
  change curveIntegral (MirrorPeriodQuotient.realise (finiteExtend n b)).value
    (markedPath (i.val+1))=b i
  have h := congrFun (MirrorPeriodQuotient.realise_periods (finiteExtend n b))
    (⟨i.val+1,by omega⟩ : MirrorPeriodQuotient.PositiveIndex)
  change curveIntegral (MirrorPeriodQuotient.realise (finiteExtend n b)).value
    (markedPath (i.val+1))=finiteExtend n b ⟨i.val+1,by omega⟩ at h
  rw [h,finiteExtend_apply]

noncomputable def stageRealiseClass (n : Nat) (b : Fin n → ℝ) : StageQuotient n :=
  Quotient.mk (exactStageSetoid n) (stageRealise n b)

theorem quotientStagePeriods_realiseClass (n : Nat) (b : Fin n → ℝ) :
    quotientStagePeriods n (stageRealiseClass n b)=b := stageRealise_periods n b

theorem quotientStagePeriods_surjective (n : Nat) : Function.Surjective (quotientStagePeriods n) := by
  intro b
  exact ⟨stageRealiseClass n b,quotientStagePeriods_realiseClass n b⟩

theorem quotientStagePeriods_bijective (n : Nat) : Function.Bijective (quotientStagePeriods n) :=
  ⟨quotientStagePeriods_injective n,quotientStagePeriods_surjective n⟩

theorem stageRealiseClass_quotientPeriods (n : Nat) (q : StageQuotient n) :
    stageRealiseClass n (quotientStagePeriods n q)=q := by
  apply quotientStagePeriods_injective n
  exact quotientStagePeriods_realiseClass n (quotientStagePeriods n q)

/-- Finite SET equivalence; no linear/intrinsic/topological identification asserted. -/
noncomputable def stagePeriodEquiv (n : Nat) : StageQuotient n ≃ (Fin n → ℝ) where
  toFun := quotientStagePeriods n
  invFun := stageRealiseClass n
  left_inv := stageRealiseClass_quotientPeriods n
  right_inv := quotientStagePeriods_realiseClass n

theorem restrictStage_exactRel {n m : Nat} (hnm : n ≤ m)
    {u v : StageField m} (h : ExactStageRel m u v) :
    ExactStageRel n (restrictStage hnm u) (restrictStage hnm v) := by
  rcases h with ⟨g,hg,he⟩
  exact ⟨g,hg.mono (stages_monotone hnm),fun p hp => he p (stages_monotone hnm hp)⟩

def quotientRestriction (n m : Nat) (hnm : n ≤ m) : StageQuotient m → StageQuotient n :=
  Quotient.map (restrictStage hnm) (fun _ _ h => restrictStage_exactRel hnm h)

theorem quotientRestriction_coordinates (n m : Nat) (hnm : n ≤ m) (q : StageQuotient m) :
    quotientStagePeriods n (quotientRestriction n m hnm q)=
      fun i : Fin n => quotientStagePeriods m q ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ := by
  refine Quotient.inductionOn q ?_
  intro w
  rfl

theorem restrictUnion_exactRel (n : Nat) {u v : MirrorPeriodQuotient.ClosedField}
    (h : MirrorPeriodQuotient.ExactRel u v) :
    ExactStageRel n (restrictUnion u n) (restrictUnion v n) := by
  rcases h with ⟨g,hg,he⟩
  exact ⟨g,hg.mono (stage_subset_union n),fun p hp => he p (stage_subset_union n hp)⟩

def quotientUnionRestriction (n : Nat) : MirrorPeriodQuotient.FieldQuotient → StageQuotient n :=
  Quotient.map (fun w => restrictUnion w n) (fun _ _ h => restrictUnion_exactRel n h)

theorem quotientUnionRestriction_coordinates (n : Nat) (q : MirrorPeriodQuotient.FieldQuotient) :
    quotientStagePeriods n (quotientUnionRestriction n q)=
      fun i : Fin n => MirrorPeriodQuotient.quotientPeriods q ⟨i.val+1,by omega⟩ := by
  refine Quotient.inductionOn q ?_
  intro w
  rfl

end MirrorFiniteQuotient


/- Algebraic coordinate inverse limit only. R needs no field or topology.
   Adjacent compatibility is the sole compatibility premise. -/
namespace MirrorInverseLimit
universe u v

def nextIndex {n : Nat} (k : Fin n) : Fin (n + 1) :=
  ⟨k.val, by omega⟩

def upIndex {n m : Nat} (h : n ≤ m) (k : Fin n) : Fin m :=
  ⟨k.val, by omega⟩

def truncate {R : Type u} (n : Nat) (v : Fin (n + 1) → R) :
    Fin n → R := fun k => v (nextIndex k)

def Compatible {R : Type u} (c : (n : Nat) → Fin n → R) : Prop :=
  ∀ n k, truncate n (c (n + 1)) k = c n k

def InverseLimit (R : Type u) :=
  {c : (n : Nat) → Fin n → R // Compatible c}

theorem truncation_coordinate {R : Type u} (n : Nat)
    (v : Fin (n + 1) → R) (k : Fin n) :
    truncate n v k = v (nextIndex k) := rfl

/- All-level stability is derived, not added as a stronger axiom. -/
theorem stable_coordinate {R : Type u}
    (c : (n : Nat) → Fin n → R) (hc : Compatible c)
    (n m : Nat) (hnm : n ≤ m) (k : Fin n) :
    c m (upIndex hnm k) = c n k := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact Fin.elim0 k
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      rfl
    · have hnm' : n ≤ m := by omega
      calc
        c (m + 1) (upIndex hnm k) =
            c m (upIndex hnm' k) := by
          exact hc m (upIndex hnm' k)
        _ = c n k := ih n hnm' k

def fromSequence {R : Type u} (b : Nat → R) : InverseLimit R :=
  ⟨fun _ k => b k.val, by
    intro n k
    rfl⟩

def toSequence {R : Type u} (c : InverseLimit R) (j : Nat) : R :=
  c.val (j + 1) ⟨j, by omega⟩

theorem sequence_reconstructs_coordinate {R : Type u}
    (c : InverseLimit R) (n : Nat) (k : Fin n) :
    toSequence c k.val = c.val n k := by
  have hkn : k.val + 1 ≤ n := by omega
  have hs := stable_coordinate c.val c.property
    (k.val + 1) n hkn ⟨k.val, Nat.lt_succ_self k.val⟩
  simpa [toSequence, upIndex] using hs.symm

theorem sequence_roundtrip {R : Type u} (b : Nat → R) :
    toSequence (fromSequence b) = b := by
  funext j
  rfl

theorem inverse_limit_roundtrip {R : Type u} (c : InverseLimit R) :
    fromSequence (toSequence c) = c := by
  apply Subtype.ext
  funext n k
  exact sequence_reconstructs_coordinate c n k

theorem toSequence_injective {R : Type u} (c d : InverseLimit R)
    (h : toSequence c = toSequence d) : c = d := by
  calc
    c = fromSequence (toSequence c) := (inverse_limit_roundtrip c).symm
    _ = fromSequence (toSequence d) := congrArg fromSequence h
    _ = d := inverse_limit_roundtrip d

theorem toSequence_surjective {R : Type u} (b : Nat → R) :
    ∃ c : InverseLimit R, toSequence c = b :=
  ⟨fromSequence b, sequence_roundtrip b⟩

/- Explicit equivalence record avoids an additional library import. -/
structure CoordinateEquivalence (A : Type u) (B : Type v) where
  forward : A → B
  backward : B → A
  left_inverse : ∀ a, backward (forward a) = a
  right_inverse : ∀ b, forward (backward b) = b

def coordinateEquivalence (R : Type u) :
    CoordinateEquivalence (InverseLimit R) (Nat → R) where
  forward := toSequence
  backward := fromSequence
  left_inverse := inverse_limit_roundtrip
  right_inverse := sequence_roundtrip

theorem M4_coordinate_equivalence (R : Type u) :
    ∃ F : InverseLimit R → (Nat → R),
      ∃ G : (Nat → R) → InverseLimit R,
        (∀ c, G (F c) = c) ∧ (∀ b, F (G b) = b) :=
  ⟨toSequence, fromSequence, inverse_limit_roundtrip, sequence_roundtrip⟩

/- Pointwise operations are preserved without assuming ring/module axioms. -/
def mapLimit {R : Type u} {S : Type v} (f : R → S)
    (c : InverseLimit R) : InverseLimit S :=
  ⟨fun n k => f (c.val n k), by
    intro n k
    exact congrArg f (c.property n k)⟩

theorem toSequence_map {R : Type u} {S : Type v}
    (f : R → S) (c : InverseLimit R) :
    toSequence (mapLimit f c) = (fun j => f (toSequence c j)) := rfl

def combineLimit {R : Type u} (op : R → R → R)
    (c d : InverseLimit R) : InverseLimit R :=
  ⟨fun n k => op (c.val n k) (d.val n k), by
    intro n k
    have hc : c.val (n + 1) (nextIndex k) = c.val n k := c.property n k
    have hd : d.val (n + 1) (nextIndex k) = d.val n k := d.property n k
    change op (c.val (n + 1) (nextIndex k))
      (d.val (n + 1) (nextIndex k)) = op (c.val n k) (d.val n k)
    rw [hc, hd]⟩

theorem toSequence_combine {R : Type u}
    (op : R → R → R) (c d : InverseLimit R) :
    toSequence (combineLimit op c d) =
      (fun j => op (toSequence c j) (toSequence d j)) := rfl


end MirrorInverseLimit


namespace MirrorQuotientInverseLimit
open MirrorFiniteQuotient MirrorFiniteCarrier
noncomputable section

/-- Sequential inverse limit of the ACTUAL finite exact quotients. -/
def StageInverseLimit :=
  {c : (n : Nat) → StageQuotient n //
    ∀ n, quotientRestriction n (n+1) (by omega) (c (n+1))=c n}

def toCoordinates (c : StageInverseLimit) : MirrorInverseLimit.InverseLimit ℝ :=
  ⟨fun n => quotientStagePeriods n (c.val n),by
    intro n k
    have h := congrFun (quotientRestriction_coordinates n (n+1) (by omega) (c.val (n+1))) k
    calc
      MirrorInverseLimit.truncate n (quotientStagePeriods (n+1) (c.val (n+1))) k =
          quotientStagePeriods n (quotientRestriction n (n+1) (by omega) (c.val (n+1))) k := h.symm
      _ = quotientStagePeriods n (c.val n) k :=
        congrFun (congrArg (quotientStagePeriods n) (c.property n)) k⟩

def fromCoordinates (x : MirrorInverseLimit.InverseLimit ℝ) : StageInverseLimit :=
  ⟨fun n => stageRealiseClass n (x.val n),by
    intro n
    apply quotientStagePeriods_injective n
    simp only [quotientRestriction_coordinates,quotientStagePeriods_realiseClass]
    funext k
    exact x.property n k⟩

theorem to_fromCoordinates (x : MirrorInverseLimit.InverseLimit ℝ) :
    toCoordinates (fromCoordinates x)=x := by
  apply Subtype.ext
  funext n
  exact quotientStagePeriods_realiseClass n (x.val n)

theorem from_toCoordinates (c : StageInverseLimit) :
    fromCoordinates (toCoordinates c)=c := by
  apply Subtype.ext
  funext n
  exact stageRealiseClass_quotientPeriods n (c.val n)

def coordinateEquiv : StageInverseLimit ≃ MirrorInverseLimit.InverseLimit ℝ where
  toFun := toCoordinates
  invFun := fromCoordinates
  left_inv := from_toCoordinates
  right_inv := to_fromCoordinates

/-- Adjacent quotient compatibility entails ACTUAL all-level restrictions. -/
theorem all_level_compatibility (c : StageInverseLimit) (n m : Nat) (hnm : n ≤ m) :
    quotientRestriction n m hnm (c.val m)=c.val n := by
  apply quotientStagePeriods_injective n
  rw [quotientRestriction_coordinates]
  funext k
  exact MirrorInverseLimit.stable_coordinate (toCoordinates c).val (toCoordinates c).property n m hnm k

/-- Nat coordinate zero denotes positive marked period one, not hole zero. -/
def positiveToNat (b : MirrorPeriodQuotient.PositiveIndex → ℝ) (j : Nat) : ℝ :=
  b ⟨j+1,by omega⟩

def natToPositive (b : Nat → ℝ) (j : MirrorPeriodQuotient.PositiveIndex) : ℝ := b (j.val-1)

theorem positive_roundtrip (b : MirrorPeriodQuotient.PositiveIndex → ℝ) :
    natToPositive (positiveToNat b)=b := by
  funext j
  have h : (⟨j.val-1+1,by have hj:=j.property;omega⟩ : MirrorPeriodQuotient.PositiveIndex)=j := by
    apply Subtype.ext
    change j.val-1+1=j.val
    have hj:=j.property
    omega
  exact congrArg b h

theorem nat_roundtrip (b : Nat → ℝ) : positiveToNat (natToPositive b)=b := by
  funext j
  change b (j+1-1)=b j
  simp

def positiveEquiv : StageInverseLimit ≃ (MirrorPeriodQuotient.PositiveIndex → ℝ) where
  toFun := fun c => natToPositive (MirrorInverseLimit.toSequence (toCoordinates c))
  invFun := fun b => fromCoordinates (MirrorInverseLimit.fromSequence (positiveToNat b))
  left_inv := by
    intro c
    change fromCoordinates (MirrorInverseLimit.fromSequence
      (positiveToNat (natToPositive (MirrorInverseLimit.toSequence (toCoordinates c)))))=c
    rw [nat_roundtrip,MirrorInverseLimit.inverse_limit_roundtrip,from_toCoordinates]
  right_inv := by
    intro b
    change natToPositive (MirrorInverseLimit.toSequence (toCoordinates
      (fromCoordinates (MirrorInverseLimit.fromSequence (positiveToNat b)))))=b
    rw [to_fromCoordinates,MirrorInverseLimit.sequence_roundtrip,positive_roundtrip]

def unionRestricts (q : MirrorPeriodQuotient.FieldQuotient) : StageInverseLimit :=
  ⟨fun n => quotientUnionRestriction n q,by
    intro n
    apply quotientStagePeriods_injective n
    simp only [quotientRestriction_coordinates,quotientUnionRestriction_coordinates]⟩

theorem unionRestricts_coordinates (q : MirrorPeriodQuotient.FieldQuotient) :
    toCoordinates (unionRestricts q)=
      MirrorInverseLimit.fromSequence (positiveToNat (MirrorPeriodQuotient.quotientPeriods q)) := by
  apply Subtype.ext
  funext n k
  exact congrFun (quotientUnionRestriction_coordinates n q) k

theorem unionRestriction_periods (q : MirrorPeriodQuotient.FieldQuotient) :
    positiveEquiv (unionRestricts q)=MirrorPeriodQuotient.quotientPeriods q := by
  change natToPositive (MirrorInverseLimit.toSequence (toCoordinates (unionRestricts q)))=_
  rw [unionRestricts_coordinates,MirrorInverseLimit.sequence_roundtrip,positive_roundtrip]

theorem unionRestriction_injective : Function.Injective unionRestricts := by
  intro q r h
  apply MirrorPeriodInjectivity.quotientPeriods_injective
  have he:=congrArg (fun c => positiveEquiv c) h
  simpa only [unionRestriction_periods] using he

theorem unionRestriction_surjective : Function.Surjective unionRestricts := by
  intro c
  refine ⟨MirrorPeriodQuotient.realiseClass (positiveEquiv c),?_⟩
  apply positiveEquiv.injective
  rw [unionRestriction_periods,MirrorPeriodQuotient.quotientPeriods_realiseClass]

theorem unionRestriction_bijective : Function.Bijective unionRestricts :=
  ⟨unionRestriction_injective,unionRestriction_surjective⟩

/-- SET equivalence for the specified smooth exact quotients and actual restrictions. -/
def unionRestrictionEquiv : MirrorPeriodQuotient.FieldQuotient ≃ StageInverseLimit where
  toFun := unionRestricts
  invFun := fun c => MirrorPeriodQuotient.realiseClass (positiveEquiv c)
  left_inv := by
    intro q
    change MirrorPeriodQuotient.realiseClass (positiveEquiv (unionRestricts q))=q
    rw [unionRestriction_periods,MirrorPeriodInjectivity.realiseClass_quotientPeriods]
  right_inv := by
    intro c
    apply positiveEquiv.injective
    rw [unionRestriction_periods,MirrorPeriodQuotient.quotientPeriods_realiseClass]

end
end MirrorQuotientInverseLimit

namespace MirrorNativeForms
open Set Filter
open scoped Topology ContDiff
open MirrorGeometry MirrorExteriorClosedness MirrorPeriodQuotient
noncomputable section

/- Native smooth closed 1-forms on this specific open union. Exactness below
   quantifies over ALL smooth native 0-form potentials. Equality and smoothness
   are required only on the union. This component constructs SET equivalences;
   no vector-space or topological identification is asserted here. -/
structure NativeClosedOne where
  value : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ
  smooth : ContDiffOn ℝ ∞ value XInfinity
  closed : ∀ p ∈ XInfinity, extDeriv value p = 0

theorem native_ext {α β : NativeClosedOne} (h : α.value = β.value) : α = β := by
  cases α
  cases β
  cases h
  rfl

theorem field_ext {u v : ClosedField} (h : u.value = v.value) : u = v := by
  cases u
  cases v
  cases h
  rfl

def toNative (w : ClosedField) : NativeClosedOne where
  value := oneForm w.value
  smooth := liftCovector.contDiff.comp_contDiffOn w.smooth
  closed := w.closed

def toCovector (α : NativeClosedOne) : ClosedField where
  value := fun p => liftCovector.symm (α.value p)
  smooth := liftCovector.symm.contDiff.comp_contDiffOn α.smooth
  closed := by
    intro p hp
    have h : oneForm (fun q => liftCovector.symm (α.value q)) = α.value := by
      funext q
      exact liftCovector.apply_symm_apply (α.value q)
    rw [h]
    exact α.closed p hp

theorem oneForm_toCovector (α : NativeClosedOne) :
    oneForm (toCovector α).value = α.value := by
  funext p
  exact liftCovector.apply_symm_apply (α.value p)

theorem toCovector_toNative (w : ClosedField) : toCovector (toNative w) = w := by
  apply field_ext
  funext p
  exact liftCovector.symm_apply_apply (w.value p)

theorem toNative_toCovector (α : NativeClosedOne) : toNative (toCovector α) = α := by
  apply native_ext
  exact oneForm_toCovector α

def carrierEquiv : NativeClosedOne ≃ ClosedField where
  toFun := toCovector
  invFun := toNative
  left_inv := toNative_toCovector
  right_inv := toCovector_toNative

def NativeExactRel (α β : NativeClosedOne) : Prop :=
  ∃ A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ, ContDiffOn ℝ ∞ A XInfinity ∧
    ∀ p ∈ XInfinity, β.value p = α.value p + extDeriv A p

def scalarPotential (A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ) (p : ℂ) : ℝ :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).symm (A p)

theorem scalarPotential_smooth (A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ)
    (hA : ContDiffOn ℝ ∞ A XInfinity) :
    ContDiffOn ℝ ∞ (scalarPotential A) XInfinity := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).symm.contDiff.comp_contDiffOn hA

theorem zeroForm_scalarPotential (A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ) :
    zeroForm (scalarPotential A) = A := by
  funext p
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).apply_symm_apply (A p)

theorem nativeExact_iff (α β : NativeClosedOne) :
    NativeExactRel α β ↔ ExactRel (toCovector α) (toCovector β) := by
  constructor
  · rintro ⟨A,hA,he⟩
    refine ⟨scalarPotential A,scalarPotential_smooth A hA,?_⟩
    intro p hp
    have hd : extDeriv A p = liftCovector (fderiv ℝ (scalarPotential A) p) := by
      have h := congrFun (exact_form_bridge (scalarPotential A)) p
      rw [zeroForm_scalarPotential A] at h
      exact h
    apply liftCovector.injective
    rw [liftCovector.map_add]
    change liftCovector (liftCovector.symm (β.value p)) =
      liftCovector (liftCovector.symm (α.value p)) + liftCovector (fderiv ℝ (scalarPotential A) p)
    rw [liftCovector.apply_symm_apply,liftCovector.apply_symm_apply,← hd]
    exact he p hp
  · rintro ⟨g,hg,he⟩
    refine ⟨zeroForm g,?_,?_⟩
    · exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).contDiff.comp_contDiffOn hg
    · intro p hp
      have hd := congrFun (exact_form_bridge g) p
      rw [hd]
      have h := congrArg liftCovector (he p hp)
      rw [liftCovector.map_add] at h
      change liftCovector (liftCovector.symm (β.value p)) =
        liftCovector (liftCovector.symm (α.value p)) + liftCovector (fderiv ℝ g p) at h
      simpa only [oneForm, liftCovector.apply_symm_apply] using h

theorem toNative_exact_iff (u v : ClosedField) :
    NativeExactRel (toNative u) (toNative v) ↔ ExactRel u v := by
  rw [nativeExact_iff,toCovector_toNative,toCovector_toNative]

theorem nativeExact_refl (α : NativeClosedOne) : NativeExactRel α α :=
  (nativeExact_iff α α).mpr (exactRel_refl (toCovector α))

theorem nativeExact_symm {α β : NativeClosedOne} (h : NativeExactRel α β) :
    NativeExactRel β α :=
  (nativeExact_iff β α).mpr (exactRel_symm ((nativeExact_iff α β).mp h))

theorem nativeExact_trans {α β γ : NativeClosedOne}
    (h : NativeExactRel α β) (h' : NativeExactRel β γ) : NativeExactRel α γ :=
  (nativeExact_iff α γ).mpr (exactRel_trans ((nativeExact_iff α β).mp h)
    ((nativeExact_iff β γ).mp h'))

def nativeSetoid : Setoid NativeClosedOne where
  r := NativeExactRel
  iseqv := ⟨nativeExact_refl,nativeExact_symm,nativeExact_trans⟩

abbrev NativeFormQuotient := Quotient nativeSetoid

def toFieldClass : NativeFormQuotient → FieldQuotient :=
  Quotient.map toCovector (fun α β h => (nativeExact_iff α β).mp h)

def toNativeClass : FieldQuotient → NativeFormQuotient :=
  Quotient.map toNative (fun u v h => (toNative_exact_iff u v).mpr h)

theorem toFieldClass_mk (α : NativeClosedOne) :
    toFieldClass (Quotient.mk nativeSetoid α) = Quotient.mk exactSetoid (toCovector α) := rfl

theorem toNativeClass_mk (w : ClosedField) :
    toNativeClass (Quotient.mk exactSetoid w) = Quotient.mk nativeSetoid (toNative w) := rfl

theorem toFieldClass_toNativeClass (q : FieldQuotient) :
    toFieldClass (toNativeClass q) = q := by
  refine Quotient.inductionOn q ?_
  intro w
  change Quotient.mk exactSetoid (toCovector (toNative w)) = Quotient.mk exactSetoid w
  rw [toCovector_toNative]

theorem toNativeClass_toFieldClass (q : NativeFormQuotient) :
    toNativeClass (toFieldClass q) = q := by
  refine Quotient.inductionOn q ?_
  intro α
  change Quotient.mk nativeSetoid (toNative (toCovector α)) = Quotient.mk nativeSetoid α
  rw [toNative_toCovector]

def quotientEquiv : NativeFormQuotient ≃ FieldQuotient where
  toFun := toFieldClass
  invFun := toNativeClass
  left_inv := toNativeClass_toFieldClass
  right_inv := toFieldClass_toNativeClass

/-- Periods integrate the covector obtained by the existing native Fin1 inverse. -/
def nativePeriods (q : NativeFormQuotient) : PositiveIndex → ℝ :=
  quotientPeriods (toFieldClass q)

theorem nativePeriods_mk (α : NativeClosedOne) (i : PositiveIndex) :
    nativePeriods (Quotient.mk nativeSetoid α) i =
      curveIntegral (fun p => liftCovector.symm (α.value p)) (MirrorMarkedLoopDiagonal.markedPath i.val) := rfl

def nativePeriodEquiv : NativeFormQuotient ≃ (PositiveIndex → ℝ) :=
  quotientEquiv.trans MirrorPeriodInjectivity.periodEquiv

theorem nativePeriodEquiv_apply (q : NativeFormQuotient) :
    nativePeriodEquiv q = nativePeriods q := rfl

/-- Only the actual finite exact-quotient restrictions already established. -/
def nativeInverseLimitEquiv : NativeFormQuotient ≃ MirrorQuotientInverseLimit.StageInverseLimit :=
  quotientEquiv.trans MirrorQuotientInverseLimit.unionRestrictionEquiv

end
end MirrorNativeForms

namespace MirrorPointwiseLinear
open Set Filter
open scoped Topology ContDiff
open MirrorGeometry MirrorPeriodQuotient MirrorLocalExactness MirrorMarkedLoopDiagonal
open MirrorNativeForms MirrorExteriorClosedness
noncomputable section

/- These transported module instances are tied below to ACTUAL pointwise
   field/form addition and real scalar multiplication on quotient classes.
   This is the union quotient only; finite/native restriction linearity and
   topology are separate obligations. No regularity outside the union. -/
def fieldAdd (u v : ClosedField) : ClosedField where
  value := u.value + v.value
  smooth := u.smooth.add v.smooth
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt (union_open.mem_nhds hp)).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ v.value p :=
      (v.smooth.contDiffAt (union_open.mem_nhds hp)).differentiableAt (by simp)
    have su := (closed_iff_symmetric hu).mp (u.closed p hp)
    have sv := (closed_iff_symmetric hv).mp (v.closed p hp)
    apply (closed_iff_symmetric (hu.add hv)).mpr
    intro a b
    rw [fderiv_add hu hv]
    simp only [add_apply]
    rw [su a b,sv a b]

def fieldSMul (c : ℝ) (u : ClosedField) : ClosedField where
  value := c • u.value
  smooth := u.smooth.const_smul c
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt (union_open.mem_nhds hp)).differentiableAt (by simp)
    have su := (closed_iff_symmetric hu).mp (u.closed p hp)
    apply (closed_iff_symmetric (hu.const_smul c)).mpr
    intro a b
    rw [fderiv_const_smul hu c]
    simp only [smul_apply]
    rw [su a b]

theorem fieldAdd_periods (u v : ClosedField) :
    periods (fieldAdd u v) = periods u + periods v := by
  funext i
  exact curveIntegral_fun_add
    (smooth_field_integrable u.value u.smooth i.val i.property)
    (smooth_field_integrable v.value v.smooth i.val i.property)

theorem fieldSMul_periods (c : ℝ) (u : ClosedField) :
    periods (fieldSMul c u) = c • periods u := by
  funext i
  change curveIntegral (c • u.value) (markedPath i.val) = c • curveIntegral u.value (markedPath i.val)
  rw [curveIntegral_smul]

instance quotientAddCommGroup : AddCommGroup FieldQuotient :=
  MirrorPeriodInjectivity.periodEquiv.addCommGroup

def periodAddEquiv : FieldQuotient ≃+ (PositiveIndex → ℝ) :=
  MirrorPeriodInjectivity.periodEquiv.addEquiv

instance quotientModule : Module ℝ FieldQuotient := periodAddEquiv.module ℝ

def periodLinearEquiv : FieldQuotient ≃ₗ[ℝ] (PositiveIndex → ℝ) :=
  periodAddEquiv.linearEquiv ℝ

theorem periodLinearEquiv_apply (q : FieldQuotient) :
    periodLinearEquiv q = quotientPeriods q := rfl

theorem fieldClass_add (u v : ClosedField) :
    Quotient.mk exactSetoid (fieldAdd u v) =
      Quotient.mk exactSetoid u + Quotient.mk exactSetoid v := by
  apply periodLinearEquiv.injective
  rw [periodLinearEquiv.map_add]
  exact fieldAdd_periods u v

theorem fieldClass_smul (c : ℝ) (u : ClosedField) :
    Quotient.mk exactSetoid (fieldSMul c u) = c • Quotient.mk exactSetoid u := by
  apply periodLinearEquiv.injective
  rw [periodLinearEquiv.map_smul]
  exact fieldSMul_periods c u

theorem fieldClass_zero (u : ClosedField) :
    Quotient.mk exactSetoid (fieldSMul 0 u) = 0 := by
  rw [fieldClass_smul,zero_smul]

theorem fieldAdd_exact_compatible {u u' v v' : ClosedField}
    (hu : ExactRel u u') (hv : ExactRel v v') :
    ExactRel (fieldAdd u v) (fieldAdd u' v') := by
  apply MirrorPeriodInjectivity.periods_equal_exactRel
  rw [fieldAdd_periods,fieldAdd_periods,exactRel_periods hu,exactRel_periods hv]

theorem fieldSMul_exact_compatible {u u' : ClosedField} (c : ℝ)
    (hu : ExactRel u u') : ExactRel (fieldSMul c u) (fieldSMul c u') := by
  apply MirrorPeriodInjectivity.periods_equal_exactRel
  rw [fieldSMul_periods,fieldSMul_periods,exactRel_periods hu]

def nativeAdd (α β : NativeClosedOne) : NativeClosedOne :=
  toNative (fieldAdd (toCovector α) (toCovector β))

def nativeSMul (c : ℝ) (α : NativeClosedOne) : NativeClosedOne :=
  toNative (fieldSMul c (toCovector α))

theorem nativeAdd_value (α β : NativeClosedOne) :
    (nativeAdd α β).value = α.value + β.value := by
  funext p
  change liftCovector (liftCovector.symm (α.value p) + liftCovector.symm (β.value p)) =
    α.value p + β.value p
  rw [liftCovector.map_add,liftCovector.apply_symm_apply,liftCovector.apply_symm_apply]

theorem nativeSMul_value (c : ℝ) (α : NativeClosedOne) :
    (nativeSMul c α).value = c • α.value := by
  funext p
  change liftCovector (c • liftCovector.symm (α.value p)) = c • α.value p
  rw [liftCovector.map_smul,liftCovector.apply_symm_apply]

instance nativeQuotientAddCommGroup : AddCommGroup NativeFormQuotient :=
  nativePeriodEquiv.addCommGroup

def nativePeriodAddEquiv : NativeFormQuotient ≃+ (PositiveIndex → ℝ) :=
  nativePeriodEquiv.addEquiv

instance nativeQuotientModule : Module ℝ NativeFormQuotient :=
  nativePeriodAddEquiv.module ℝ

def nativePeriodLinearEquiv : NativeFormQuotient ≃ₗ[ℝ] (PositiveIndex → ℝ) :=
  nativePeriodAddEquiv.linearEquiv ℝ

theorem nativePeriodLinearEquiv_apply (q : NativeFormQuotient) :
    nativePeriodLinearEquiv q = nativePeriods q := rfl

def nativeCovectorLinearEquiv : NativeFormQuotient ≃ₗ[ℝ] FieldQuotient where
  __ := quotientEquiv
  map_add' := by
    intro q r
    apply periodLinearEquiv.injective
    rw [periodLinearEquiv.map_add]
    exact nativePeriodLinearEquiv.map_add q r
  map_smul' := by
    intro c q
    apply periodLinearEquiv.injective
    rw [periodLinearEquiv.map_smul]
    exact nativePeriodLinearEquiv.map_smul c q

theorem nativeCovectorLinearEquiv_apply (q : NativeFormQuotient) :
    nativeCovectorLinearEquiv q = toFieldClass q := rfl

theorem nativeClass_add (α β : NativeClosedOne) :
    Quotient.mk nativeSetoid (nativeAdd α β) =
      Quotient.mk nativeSetoid α + Quotient.mk nativeSetoid β := by
  apply nativeCovectorLinearEquiv.injective
  rw [nativeCovectorLinearEquiv.map_add]
  simp only [nativeCovectorLinearEquiv_apply,toFieldClass_mk,nativeAdd,toCovector_toNative]
  exact fieldClass_add (toCovector α) (toCovector β)

theorem nativeClass_smul (c : ℝ) (α : NativeClosedOne) :
    Quotient.mk nativeSetoid (nativeSMul c α) = c • Quotient.mk nativeSetoid α := by
  apply nativeCovectorLinearEquiv.injective
  rw [nativeCovectorLinearEquiv.map_smul]
  simp only [nativeCovectorLinearEquiv_apply,toFieldClass_mk,nativeSMul,toCovector_toNative]
  exact fieldClass_smul c (toCovector α)

theorem nativeClass_zero (α : NativeClosedOne) :
    Quotient.mk nativeSetoid (nativeSMul 0 α) = 0 := by
  rw [nativeClass_smul,zero_smul]

end
end MirrorPointwiseLinear

namespace MirrorFiniteLinear
open Set Filter
open scoped Topology ContDiff
open MirrorGeometry MirrorPeriodQuotient MirrorLocalExactness MirrorMarkedLoopDiagonal
open MirrorFiniteCarrier MirrorFiniteQuotient MirrorPointwiseLinear
open MirrorQuotientInverseLimit MirrorNativeForms
noncomputable section

/- Finite-only fields, actual pointwise operations and ACTUAL quotient restrictions.
   Compatible CLASS families carry the ordinary Pi-module operations. The carrier
   below is tied to the existing StageInverseLimit; representatives are not
   asserted pointwise compatible. Finite native-form binding and topology remain
   separate. All finite statements include n=0, whose coordinate type is Fin 0. -/
def stageAdd {n : Nat} (u v : StageField n) : StageField n where
  value := u.value + v.value
  smooth := u.smooth.add v.smooth
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt ((stage_open n).mem_nhds hp)).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ v.value p :=
      (v.smooth.contDiffAt ((stage_open n).mem_nhds hp)).differentiableAt (by simp)
    have su := (closed_iff_symmetric hu).mp (u.closed p hp)
    have sv := (closed_iff_symmetric hv).mp (v.closed p hp)
    apply (closed_iff_symmetric (hu.add hv)).mpr
    intro a b
    rw [fderiv_add hu hv]
    simp only [add_apply]
    rw [su a b,sv a b]

def stageSMul {n : Nat} (c : ℝ) (u : StageField n) : StageField n where
  value := c • u.value
  smooth := u.smooth.const_smul c
  closed := by
    intro p hp
    have hu : DifferentiableAt ℝ u.value p :=
      (u.smooth.contDiffAt ((stage_open n).mem_nhds hp)).differentiableAt (by simp)
    have su := (closed_iff_symmetric hu).mp (u.closed p hp)
    apply (closed_iff_symmetric (hu.const_smul c)).mpr
    intro a b
    rw [fderiv_const_smul hu c]
    simp only [smul_apply]
    rw [su a b]

theorem stageAdd_periods {n : Nat} (u v : StageField n) :
    stagePeriods n (stageAdd u v)=stagePeriods n u+stagePeriods n v := by
  funext i
  exact curveIntegral_fun_add
    (field_integrable n u (i.val+1) (by omega) (by omega))
    (field_integrable n v (i.val+1) (by omega) (by omega))

theorem stageSMul_periods {n : Nat} (c : ℝ) (u : StageField n) :
    stagePeriods n (stageSMul c u)=c • stagePeriods n u := by
  funext i
  change curveIntegral (c • u.value) (markedPath (i.val+1))=
    c • curveIntegral u.value (markedPath (i.val+1))
  rw [curveIntegral_smul]

instance stageQuotientAddCommGroup (n : Nat) : AddCommGroup (StageQuotient n) :=
  (stagePeriodEquiv n).addCommGroup

def stagePeriodAddEquiv (n : Nat) : StageQuotient n ≃+ (Fin n → ℝ) :=
  (stagePeriodEquiv n).addEquiv

instance stageQuotientModule (n : Nat) : Module ℝ (StageQuotient n) :=
  (stagePeriodAddEquiv n).module ℝ

def stagePeriodLinearEquiv (n : Nat) : StageQuotient n ≃ₗ[ℝ] (Fin n → ℝ) :=
  (stagePeriodAddEquiv n).linearEquiv ℝ

theorem stagePeriodLinearEquiv_apply (n : Nat) (q : StageQuotient n) :
    stagePeriodLinearEquiv n q=quotientStagePeriods n q := rfl

theorem stageClass_add {n : Nat} (u v : StageField n) :
    Quotient.mk (exactStageSetoid n) (stageAdd u v)=
      Quotient.mk (exactStageSetoid n) u+Quotient.mk (exactStageSetoid n) v := by
  apply (stagePeriodLinearEquiv n).injective
  rw [(stagePeriodLinearEquiv n).map_add]
  exact stageAdd_periods u v

theorem stageClass_smul {n : Nat} (c : ℝ) (u : StageField n) :
    Quotient.mk (exactStageSetoid n) (stageSMul c u)=c • Quotient.mk (exactStageSetoid n) u := by
  apply (stagePeriodLinearEquiv n).injective
  rw [(stagePeriodLinearEquiv n).map_smul]
  exact stageSMul_periods c u

theorem stageClass_zero {n : Nat} (u : StageField n) :
    Quotient.mk (exactStageSetoid n) (stageSMul 0 u)=0 := by
  rw [stageClass_smul,zero_smul]

theorem stageAdd_exact_compatible {n : Nat} {u u' v v' : StageField n}
    (hu : ExactStageRel n u u') (hv : ExactStageRel n v v') :
    ExactStageRel n (stageAdd u v) (stageAdd u' v') := by
  apply periods_equal_exactStageRel n
  rw [stageAdd_periods,stageAdd_periods,exactStageRel_periods hu,exactStageRel_periods hv]

theorem stageSMul_exact_compatible {n : Nat} (c : ℝ) {u u' : StageField n}
    (hu : ExactStageRel n u u') : ExactStageRel n (stageSMul c u) (stageSMul c u') := by
  apply periods_equal_exactStageRel n
  rw [stageSMul_periods,stageSMul_periods,exactStageRel_periods hu]

def restrictionLinearMap (n m : Nat) (hnm : n ≤ m) :
    StageQuotient m →ₗ[ℝ] StageQuotient n where
  toFun := quotientRestriction n m hnm
  map_add' := by
    intro q r
    apply (stagePeriodLinearEquiv n).injective
    rw [(stagePeriodLinearEquiv n).map_add]
    change quotientStagePeriods n (quotientRestriction n m hnm (q+r))=
      quotientStagePeriods n (quotientRestriction n m hnm q)+
      quotientStagePeriods n (quotientRestriction n m hnm r)
    simp only [quotientRestriction_coordinates]
    funext i
    exact congrFun ((stagePeriodLinearEquiv m).map_add q r) ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩
  map_smul' := by
    intro c q
    apply (stagePeriodLinearEquiv n).injective
    rw [(stagePeriodLinearEquiv n).map_smul]
    change quotientStagePeriods n (quotientRestriction n m hnm (c • q))=
      c • quotientStagePeriods n (quotientRestriction n m hnm q)
    simp only [quotientRestriction_coordinates]
    funext i
    exact congrFun ((stagePeriodLinearEquiv m).map_smul c q) ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩

theorem restrictionLinearMap_apply (n m : Nat) (hnm : n ≤ m) (q : StageQuotient m) :
    restrictionLinearMap n m hnm q=quotientRestriction n m hnm q := rfl

def unionRestrictionLinearMap (n : Nat) : FieldQuotient →ₗ[ℝ] StageQuotient n where
  toFun := quotientUnionRestriction n
  map_add' := by
    intro q r
    apply (stagePeriodLinearEquiv n).injective
    rw [(stagePeriodLinearEquiv n).map_add]
    change quotientStagePeriods n (quotientUnionRestriction n (q+r))=
      quotientStagePeriods n (quotientUnionRestriction n q)+
      quotientStagePeriods n (quotientUnionRestriction n r)
    simp only [quotientUnionRestriction_coordinates]
    funext i
    exact congrFun (periodLinearEquiv.map_add q r) ⟨i.val+1,by omega⟩
  map_smul' := by
    intro c q
    apply (stagePeriodLinearEquiv n).injective
    rw [(stagePeriodLinearEquiv n).map_smul]
    change quotientStagePeriods n (quotientUnionRestriction n (c • q))=
      c • quotientStagePeriods n (quotientUnionRestriction n q)
    simp only [quotientUnionRestriction_coordinates]
    funext i
    exact congrFun (periodLinearEquiv.map_smul c q) ⟨i.val+1,by omega⟩

theorem unionRestrictionLinearMap_apply (n : Nat) (q : FieldQuotient) :
    unionRestrictionLinearMap n q=quotientUnionRestriction n q := rfl

/-- Actual subspace of compatible finite exact-quotient CLASS families. -/
def compatibleClasses : Submodule ℝ ((n : Nat) → StageQuotient n) where
  carrier := {c | ∀ n, quotientRestriction n (n+1) (by omega) (c (n+1))=c n}
  zero_mem' := by
    intro n
    exact (restrictionLinearMap n (n+1) (by omega)).map_zero
  add_mem' := by
    intro c d hc hd n
    change restrictionLinearMap n (n+1) (by omega) (c (n+1)+d (n+1))=c n+d n
    rw [(restrictionLinearMap n (n+1) (by omega)).map_add]
    change quotientRestriction n (n+1) (by omega) (c (n+1))+
      quotientRestriction n (n+1) (by omega) (d (n+1))=c n+d n
    rw [hc n,hd n]
  smul_mem' := by
    intro a c hc n
    change restrictionLinearMap n (n+1) (by omega) (a • c (n+1))=a • c n
    rw [(restrictionLinearMap n (n+1) (by omega)).map_smul]
    change a • quotientRestriction n (n+1) (by omega) (c (n+1))=a • c n
    rw [hc n]

def compatibleCarrierEquiv : compatibleClasses ≃ StageInverseLimit where
  toFun := fun c => ⟨c.val,c.property⟩
  invFun := fun c => ⟨c.val,c.property⟩
  left_inv := by intro c;apply Subtype.ext;rfl
  right_inv := by intro c;apply Subtype.ext;rfl

theorem compatibleCarrierEquiv_family (c : compatibleClasses) :
    (compatibleCarrierEquiv c).val=c.val := rfl

def unionToCompatible : FieldQuotient →ₗ[ℝ] compatibleClasses where
  toFun := fun q => ⟨fun n => quotientUnionRestriction n q,(unionRestricts q).property⟩
  map_add' := by
    intro q r
    apply Subtype.ext
    funext n
    exact (unionRestrictionLinearMap n).map_add q r
  map_smul' := by
    intro c q
    apply Subtype.ext
    funext n
    exact (unionRestrictionLinearMap n).map_smul c q

theorem unionToCompatible_apply (q : FieldQuotient) (n : Nat) :
    (unionToCompatible q).val n=quotientUnionRestriction n q := rfl

/-- Uses the existing SET bijection with unchanged forward and inverse families. -/
def unionLimitLinearEquiv : FieldQuotient ≃ₗ[ℝ] compatibleClasses where
  __ := unionRestrictionEquiv.trans compatibleCarrierEquiv.symm
  map_add' := by intro q r;exact unionToCompatible.map_add q r
  map_smul' := by intro c q;exact unionToCompatible.map_smul c q

theorem unionLimitLinearEquiv_agrees (q : FieldQuotient) :
    compatibleCarrierEquiv (unionLimitLinearEquiv q)=unionRestrictionEquiv q := rfl

def nativeLimitLinearEquiv : NativeFormQuotient ≃ₗ[ℝ] compatibleClasses :=
  nativeCovectorLinearEquiv.trans unionLimitLinearEquiv

theorem nativeLimitLinearEquiv_agrees (q : NativeFormQuotient) :
    compatibleCarrierEquiv (nativeLimitLinearEquiv q)=nativeInverseLimitEquiv q := rfl

theorem compatible_all_level (c : compatibleClasses) (n m : Nat) (hnm : n ≤ m) :
    restrictionLinearMap n m hnm (c.val m)=c.val n :=
  all_level_compatibility (compatibleCarrierEquiv c) n m hnm

/-- Nat coordinate zero is positive period one; uses the existing index roundtrips. -/
def positiveNatLinearEquiv : (PositiveIndex → ℝ) ≃ₗ[ℝ] (Nat → ℝ) where
  toFun := positiveToNat
  invFun := natToPositive
  left_inv := positive_roundtrip
  right_inv := nat_roundtrip
  map_add' := by intro b d;rfl
  map_smul' := by intro c b;rfl

def nativeNatPeriodLinearEquiv : NativeFormQuotient ≃ₗ[ℝ] (Nat → ℝ) :=
  nativePeriodLinearEquiv.trans positiveNatLinearEquiv

theorem nativeNat_period_apply (q : NativeFormQuotient) (j : Nat) :
    nativeNatPeriodLinearEquiv q j=nativePeriods q ⟨j+1,by omega⟩ := rfl

end
end MirrorFiniteLinear


namespace MirrorFiniteNativeForms
noncomputable section
open MirrorGeometry MirrorExteriorClosedness MirrorFiniteCarrier MirrorFiniteQuotient
open MirrorNativeForms

/- Finite-only native 1-forms, with arbitrary native 0-form potentials.
   Each object is smooth and closed only on its actual finite open domain.
   The finite native quotient is new; no extension to the open union is required. -/
structure NativeClosedStage (n : Nat) where
  value : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ
  smooth : ContDiffOn ℝ ∞ value (X n)
  closed : ∀ p ∈ X n, extDeriv value p = 0

variable {n : Nat}

theorem native_ext {α β : NativeClosedStage n} (h : α.value = β.value) : α = β := by
  cases α
  cases β
  cases h
  rfl

theorem stage_ext {u v : StageField n} (h : u.value = v.value) : u = v := by
  cases u
  cases v
  cases h
  rfl

def toNative (w : StageField n) : NativeClosedStage n where
  value := oneForm w.value
  smooth := liftCovector.contDiff.comp_contDiffOn w.smooth
  closed := w.closed

def toCovector (α : NativeClosedStage n) : StageField n where
  value := fun p => liftCovector.symm (α.value p)
  smooth := liftCovector.symm.contDiff.comp_contDiffOn α.smooth
  closed := by
    intro p hp
    have h : oneForm (fun q => liftCovector.symm (α.value q)) = α.value := by
      funext q
      exact liftCovector.apply_symm_apply (α.value q)
    rw [h]
    exact α.closed p hp

theorem oneForm_toCovector (α : NativeClosedStage n) :
    oneForm (toCovector α).value = α.value := by
  funext p
  exact liftCovector.apply_symm_apply (α.value p)

theorem toCovector_toNative (w : StageField n) : toCovector (toNative w) = w := by
  apply stage_ext
  funext p
  exact liftCovector.symm_apply_apply (w.value p)

theorem toNative_toCovector (α : NativeClosedStage n) : toNative (toCovector α) = α := by
  apply native_ext
  exact oneForm_toCovector α

def carrierEquiv (n : Nat) : NativeClosedStage n ≃ StageField n where
  toFun := toCovector
  invFun := toNative
  left_inv := toNative_toCovector
  right_inv := toCovector_toNative

def NativeExactStageRel (n : Nat) (α β : NativeClosedStage n) : Prop :=
  ∃ A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ, ContDiffOn ℝ ∞ A (X n) ∧
    ∀ p ∈ X n, β.value p = α.value p + extDeriv A p

theorem scalarPotential_smooth_stage (A : ℂ → ℂ [⋀^Fin 0]→L[ℝ] ℝ)
    (hA : ContDiffOn ℝ ∞ A (X n)) :
    ContDiffOn ℝ ∞ (scalarPotential A) (X n) := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).symm.contDiff.comp_contDiffOn hA

theorem nativeExact_iff (α β : NativeClosedStage n) :
    NativeExactStageRel n α β ↔ ExactStageRel n (toCovector α) (toCovector β) := by
  constructor
  · rintro ⟨A,hA,he⟩
    refine ⟨scalarPotential A,scalarPotential_smooth_stage A hA,?_⟩
    intro p hp
    have hd : extDeriv A p = liftCovector (fderiv ℝ (scalarPotential A) p) := by
      have h := congrFun (exact_form_bridge (scalarPotential A)) p
      rw [zeroForm_scalarPotential A] at h
      exact h
    apply liftCovector.injective
    rw [liftCovector.map_add]
    change liftCovector (liftCovector.symm (β.value p)) =
      liftCovector (liftCovector.symm (α.value p)) + liftCovector (fderiv ℝ (scalarPotential A) p)
    rw [liftCovector.apply_symm_apply,liftCovector.apply_symm_apply,← hd]
    exact he p hp
  · rintro ⟨g,hg,he⟩
    refine ⟨zeroForm g,?_,?_⟩
    · exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).contDiff.comp_contDiffOn hg
    · intro p hp
      have hd := congrFun (exact_form_bridge g) p
      rw [hd]
      have h := congrArg liftCovector (he p hp)
      rw [liftCovector.map_add] at h
      change liftCovector (liftCovector.symm (β.value p)) =
        liftCovector (liftCovector.symm (α.value p)) + liftCovector (fderiv ℝ g p) at h
      simpa only [oneForm,liftCovector.apply_symm_apply] using h

theorem toNative_exact_iff (u v : StageField n) :
    NativeExactStageRel n (toNative u) (toNative v) ↔ ExactStageRel n u v := by
  rw [nativeExact_iff,toCovector_toNative,toCovector_toNative]

theorem nativeExact_equivalence (n : Nat) : Equivalence (NativeExactStageRel n) := by
  refine ⟨?_,?_,?_⟩
  · intro α
    exact (nativeExact_iff α α).mpr (exactStageRel_refl n (toCovector α))
  · intro α β h
    exact (nativeExact_iff β α).mpr (exactStageRel_symm ((nativeExact_iff α β).mp h))
  · intro α β γ h h'
    exact (nativeExact_iff α γ).mpr (exactStageRel_trans
      ((nativeExact_iff α β).mp h) ((nativeExact_iff β γ).mp h'))

def nativeStageSetoid (n : Nat) : Setoid (NativeClosedStage n) where
  r := NativeExactStageRel n
  iseqv := nativeExact_equivalence n

abbrev NativeStageQuotient (n : Nat) := Quotient (nativeStageSetoid n)

def toFieldClass (n : Nat) : NativeStageQuotient n → StageQuotient n :=
  Quotient.map toCovector (fun α β h => (nativeExact_iff α β).mp h)

def toNativeClass (n : Nat) : StageQuotient n → NativeStageQuotient n :=
  Quotient.map toNative (fun u v h => (toNative_exact_iff u v).mpr h)

theorem toFieldClass_mk (α : NativeClosedStage n) :
    toFieldClass n (Quotient.mk (nativeStageSetoid n) α) =
      Quotient.mk (exactStageSetoid n) (toCovector α) := rfl

theorem toNativeClass_mk (w : StageField n) :
    toNativeClass n (Quotient.mk (exactStageSetoid n) w) =
      Quotient.mk (nativeStageSetoid n) (toNative w) := rfl

theorem toFieldClass_toNativeClass (q : StageQuotient n) :
    toFieldClass n (toNativeClass n q) = q := by
  refine Quotient.inductionOn q ?_
  intro w
  change Quotient.mk (exactStageSetoid n) (toCovector (toNative w)) =
    Quotient.mk (exactStageSetoid n) w
  rw [toCovector_toNative]

theorem toNativeClass_toFieldClass (q : NativeStageQuotient n) :
    toNativeClass n (toFieldClass n q) = q := by
  refine Quotient.inductionOn q ?_
  intro α
  change Quotient.mk (nativeStageSetoid n) (toNative (toCovector α)) =
    Quotient.mk (nativeStageSetoid n) α
  rw [toNative_toCovector]

def quotientEquiv (n : Nat) : NativeStageQuotient n ≃ StageQuotient n where
  toFun := toFieldClass n
  invFun := toNativeClass n
  left_inv := toNativeClass_toFieldClass
  right_inv := toFieldClass_toNativeClass

def nativeStagePeriods (n : Nat) (q : NativeStageQuotient n) : Fin n → ℝ :=
  quotientStagePeriods n (toFieldClass n q)

theorem nativeStagePeriods_mk (α : NativeClosedStage n) (i : Fin n) :
    nativeStagePeriods n (Quotient.mk (nativeStageSetoid n) α) i =
      curveIntegral (fun p => liftCovector.symm (α.value p))
        (MirrorMarkedLoopDiagonal.markedPath (i.val+1)) := rfl

def nativeStagePeriodEquiv (n : Nat) : NativeStageQuotient n ≃ (Fin n → ℝ) :=
  (quotientEquiv n).trans (stagePeriodEquiv n)

instance nativeStageAddCommGroup (n : Nat) : AddCommGroup (NativeStageQuotient n) :=
  (nativeStagePeriodEquiv n).addCommGroup

def nativeStagePeriodAddEquiv (n : Nat) : NativeStageQuotient n ≃+ (Fin n → ℝ) :=
  (nativeStagePeriodEquiv n).addEquiv

instance nativeStageModule (n : Nat) : Module ℝ (NativeStageQuotient n) :=
  (nativeStagePeriodAddEquiv n).module ℝ

def nativeStagePeriodLinearEquiv (n : Nat) : NativeStageQuotient n ≃ₗ[ℝ] (Fin n → ℝ) :=
  (nativeStagePeriodAddEquiv n).linearEquiv ℝ

theorem nativeStagePeriodLinearEquiv_apply (q : NativeStageQuotient n) :
    nativeStagePeriodLinearEquiv n q = nativeStagePeriods n q := rfl

def nativeCovectorLinearEquiv (n : Nat) : NativeStageQuotient n ≃ₗ[ℝ] StageQuotient n where
  __ := quotientEquiv n
  map_add' := by
    intro q r
    apply (MirrorFiniteLinear.stagePeriodLinearEquiv n).injective
    rw [(MirrorFiniteLinear.stagePeriodLinearEquiv n).map_add]
    exact (nativeStagePeriodLinearEquiv n).map_add q r
  map_smul' := by
    intro c q
    apply (MirrorFiniteLinear.stagePeriodLinearEquiv n).injective
    rw [(MirrorFiniteLinear.stagePeriodLinearEquiv n).map_smul]
    exact (nativeStagePeriodLinearEquiv n).map_smul c q

theorem nativeCovectorLinearEquiv_apply (q : NativeStageQuotient n) :
    nativeCovectorLinearEquiv n q = toFieldClass n q := rfl

def nativeAdd (α β : NativeClosedStage n) : NativeClosedStage n :=
  toNative (MirrorFiniteLinear.stageAdd (toCovector α) (toCovector β))

def nativeSMul (c : ℝ) (α : NativeClosedStage n) : NativeClosedStage n :=
  toNative (MirrorFiniteLinear.stageSMul c (toCovector α))

theorem nativeAdd_value (α β : NativeClosedStage n) :
    (nativeAdd α β).value = α.value + β.value := by
  funext p
  change liftCovector (liftCovector.symm (α.value p) + liftCovector.symm (β.value p)) =
    α.value p + β.value p
  rw [liftCovector.map_add,liftCovector.apply_symm_apply,liftCovector.apply_symm_apply]

theorem nativeSMul_value (c : ℝ) (α : NativeClosedStage n) :
    (nativeSMul c α).value = c • α.value := by
  funext p
  change liftCovector (c • liftCovector.symm (α.value p)) = c • α.value p
  rw [liftCovector.map_smul,liftCovector.apply_symm_apply]

theorem nativeClass_add (α β : NativeClosedStage n) :
    Quotient.mk (nativeStageSetoid n) (nativeAdd α β) =
      Quotient.mk (nativeStageSetoid n) α + Quotient.mk (nativeStageSetoid n) β := by
  apply (nativeCovectorLinearEquiv n).injective
  rw [(nativeCovectorLinearEquiv n).map_add]
  simp only [nativeCovectorLinearEquiv_apply,toFieldClass_mk,nativeAdd,toCovector_toNative]
  exact MirrorFiniteLinear.stageClass_add (toCovector α) (toCovector β)

theorem nativeClass_smul (c : ℝ) (α : NativeClosedStage n) :
    Quotient.mk (nativeStageSetoid n) (nativeSMul c α) =
      c • Quotient.mk (nativeStageSetoid n) α := by
  apply (nativeCovectorLinearEquiv n).injective
  rw [(nativeCovectorLinearEquiv n).map_smul]
  simp only [nativeCovectorLinearEquiv_apply,toFieldClass_mk,nativeSMul,toCovector_toNative]
  exact MirrorFiniteLinear.stageClass_smul c (toCovector α)

theorem nativeClass_zero (α : NativeClosedStage n) :
    Quotient.mk (nativeStageSetoid n) (nativeSMul 0 α) = 0 := by
  rw [nativeClass_smul,zero_smul]

def restrictStage {n m : Nat} (hnm : n ≤ m) (α : NativeClosedStage m) : NativeClosedStage n where
  value := α.value
  smooth := α.smooth.mono (stages_monotone hnm)
  closed := fun p hp => α.closed p (stages_monotone hnm hp)

def restrictUnion (α : MirrorNativeForms.NativeClosedOne) (n : Nat) : NativeClosedStage n where
  value := α.value
  smooth := α.smooth.mono (stage_subset_union n)
  closed := fun p hp => α.closed p (stage_subset_union n hp)

theorem toCovector_restrictStage {n m : Nat} (hnm : n ≤ m) (α : NativeClosedStage m) :
    toCovector (restrictStage hnm α) = MirrorFiniteCarrier.restrictStage hnm (toCovector α) := by
  apply stage_ext
  rfl

theorem toCovector_restrictUnion (α : MirrorNativeForms.NativeClosedOne) (n : Nat) :
    toCovector (restrictUnion α n) =
      MirrorFiniteCarrier.restrictUnion (MirrorNativeForms.toCovector α) n := by
  apply stage_ext
  rfl

theorem restrictStage_exact {n m : Nat} (hnm : n ≤ m) {α β : NativeClosedStage m}
    (h : NativeExactStageRel m α β) :
    NativeExactStageRel n (restrictStage hnm α) (restrictStage hnm β) := by
  rcases h with ⟨A,hA,he⟩
  exact ⟨A,hA.mono (stages_monotone hnm),fun p hp => he p (stages_monotone hnm hp)⟩

theorem restrictUnion_exact (n : Nat) {α β : MirrorNativeForms.NativeClosedOne}
    (h : MirrorNativeForms.NativeExactRel α β) :
    NativeExactStageRel n (restrictUnion α n) (restrictUnion β n) := by
  rcases h with ⟨A,hA,he⟩
  exact ⟨A,hA.mono (stage_subset_union n),fun p hp => he p (stage_subset_union n hp)⟩

def quotientRestriction (n m : Nat) (hnm : n ≤ m) :
    NativeStageQuotient m → NativeStageQuotient n :=
  Quotient.map (restrictStage hnm) (fun _ _ h => restrictStage_exact hnm h)

def quotientUnionRestriction (n : Nat) :
    MirrorNativeForms.NativeFormQuotient → NativeStageQuotient n :=
  Quotient.map (fun α => restrictUnion α n) (fun _ _ h => restrictUnion_exact n h)

theorem restriction_commutes (n m : Nat) (hnm : n ≤ m) (q : NativeStageQuotient m) :
    toFieldClass n (quotientRestriction n m hnm q) =
      MirrorFiniteQuotient.quotientRestriction n m hnm (toFieldClass m q) := by
  refine Quotient.inductionOn q ?_
  intro α
  change Quotient.mk (exactStageSetoid n) (toCovector (restrictStage hnm α)) =
    Quotient.mk (exactStageSetoid n) (MirrorFiniteCarrier.restrictStage hnm (toCovector α))
  rw [toCovector_restrictStage]

theorem unionRestriction_commutes (n : Nat) (q : MirrorNativeForms.NativeFormQuotient) :
    toFieldClass n (quotientUnionRestriction n q) =
      MirrorFiniteQuotient.quotientUnionRestriction n (MirrorNativeForms.toFieldClass q) := by
  refine Quotient.inductionOn q ?_
  intro α
  change Quotient.mk (exactStageSetoid n) (toCovector (restrictUnion α n)) =
    Quotient.mk (exactStageSetoid n)
      (MirrorFiniteCarrier.restrictUnion (MirrorNativeForms.toCovector α) n)
  rw [toCovector_restrictUnion]

def restrictionLinearMap (n m : Nat) (hnm : n ≤ m) :
    NativeStageQuotient m →ₗ[ℝ] NativeStageQuotient n where
  toFun := quotientRestriction n m hnm
  map_add' := by
    intro q r
    apply (nativeCovectorLinearEquiv n).injective
    rw [(nativeCovectorLinearEquiv n).map_add]
    change toFieldClass n (quotientRestriction n m hnm (q+r)) =
      toFieldClass n (quotientRestriction n m hnm q)+toFieldClass n (quotientRestriction n m hnm r)
    rw [restriction_commutes,restriction_commutes,restriction_commutes]
    change MirrorFiniteLinear.restrictionLinearMap n m hnm (nativeCovectorLinearEquiv m (q+r)) =
      MirrorFiniteLinear.restrictionLinearMap n m hnm (nativeCovectorLinearEquiv m q)+
        MirrorFiniteLinear.restrictionLinearMap n m hnm (nativeCovectorLinearEquiv m r)
    rw [(nativeCovectorLinearEquiv m).map_add,(MirrorFiniteLinear.restrictionLinearMap n m hnm).map_add]
  map_smul' := by
    intro c q
    apply (nativeCovectorLinearEquiv n).injective
    rw [(nativeCovectorLinearEquiv n).map_smul]
    change toFieldClass n (quotientRestriction n m hnm (c • q)) =
      c • toFieldClass n (quotientRestriction n m hnm q)
    rw [restriction_commutes,restriction_commutes]
    change MirrorFiniteLinear.restrictionLinearMap n m hnm (nativeCovectorLinearEquiv m (c • q)) =
      c • MirrorFiniteLinear.restrictionLinearMap n m hnm (nativeCovectorLinearEquiv m q)
    rw [(nativeCovectorLinearEquiv m).map_smul,(MirrorFiniteLinear.restrictionLinearMap n m hnm).map_smul]

def unionRestrictionLinearMap (n : Nat) :
    MirrorNativeForms.NativeFormQuotient →ₗ[ℝ] NativeStageQuotient n where
  toFun := quotientUnionRestriction n
  map_add' := by
    intro q r
    apply (nativeCovectorLinearEquiv n).injective
    rw [(nativeCovectorLinearEquiv n).map_add]
    change toFieldClass n (quotientUnionRestriction n (q+r)) =
      toFieldClass n (quotientUnionRestriction n q)+toFieldClass n (quotientUnionRestriction n r)
    rw [unionRestriction_commutes,unionRestriction_commutes,unionRestriction_commutes]
    change MirrorFiniteLinear.unionRestrictionLinearMap n
        (MirrorPointwiseLinear.nativeCovectorLinearEquiv (q+r)) =
      MirrorFiniteLinear.unionRestrictionLinearMap n (MirrorPointwiseLinear.nativeCovectorLinearEquiv q)+
        MirrorFiniteLinear.unionRestrictionLinearMap n (MirrorPointwiseLinear.nativeCovectorLinearEquiv r)
    rw [MirrorPointwiseLinear.nativeCovectorLinearEquiv.map_add,
      (MirrorFiniteLinear.unionRestrictionLinearMap n).map_add]
  map_smul' := by
    intro c q
    apply (nativeCovectorLinearEquiv n).injective
    rw [(nativeCovectorLinearEquiv n).map_smul]
    change toFieldClass n (quotientUnionRestriction n (c • q)) =
      c • toFieldClass n (quotientUnionRestriction n q)
    rw [unionRestriction_commutes,unionRestriction_commutes]
    change MirrorFiniteLinear.unionRestrictionLinearMap n
        (MirrorPointwiseLinear.nativeCovectorLinearEquiv (c • q)) =
      c • MirrorFiniteLinear.unionRestrictionLinearMap n (MirrorPointwiseLinear.nativeCovectorLinearEquiv q)
    rw [MirrorPointwiseLinear.nativeCovectorLinearEquiv.map_smul,
      (MirrorFiniteLinear.unionRestrictionLinearMap n).map_smul]

theorem quotientRestriction_coordinates (n m : Nat) (hnm : n ≤ m) (q : NativeStageQuotient m) :
    nativeStagePeriods n (quotientRestriction n m hnm q) =
      fun i : Fin n => nativeStagePeriods m q ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ := by
  unfold nativeStagePeriods
  rw [restriction_commutes]
  exact MirrorFiniteQuotient.quotientRestriction_coordinates n m hnm (toFieldClass m q)

theorem quotientUnionRestriction_coordinates (n : Nat) (q : MirrorNativeForms.NativeFormQuotient) :
    nativeStagePeriods n (quotientUnionRestriction n q) =
      fun i : Fin n => MirrorNativeForms.nativePeriods q ⟨i.val+1,by omega⟩ := by
  unfold nativeStagePeriods MirrorNativeForms.nativePeriods
  rw [unionRestriction_commutes]
  exact MirrorFiniteQuotient.quotientUnionRestriction_coordinates n (MirrorNativeForms.toFieldClass q)

theorem native_zero_stage_unique (q r : NativeStageQuotient 0) : q = r := by
  apply (nativeStagePeriodLinearEquiv 0).injective
  funext i
  exact Fin.elim0 i

end
end MirrorFiniteNativeForms

namespace MirrorHausdorff
open Set Filter Topology MirrorGeometry
def point (x y : ℝ) : ℂ := ⟨x, y⟩
def Kn (n : Nat) : Set ℂ := closure (X n)
def KInfinity : Set ℂ := closure XInfinity
def project (n : Nat) (p : ℂ) : ℂ := point (max (a n) p.re) p.im

theorem a_pos (n : Nat) : 0 < a n := by
  dsimp [a]
  linarith [c_pos n]

theorem stage_subset_union (n : Nat) : X n ⊆ XInfinity := by
  intro p hp
  exact mem_iUnion.mpr ⟨n, stages_monotone (Nat.le_succ n) hp⟩

/- The left collar is clear of EVERY excluded positive disk. -/
theorem left_collar (n : Nat) (p : ℂ)
    (hl : a n < p.re) (hr : p.re < 7 * c n / 8)
    (hy0 : -1 < p.im) (hy1 : p.im < 1) : p ∈ X n := by
  apply (mem_X n p).mpr
  refine ⟨⟨hl, ?_, hy0, hy1⟩, ?_⟩
  · linarith [c_le_one n]
  · intro j
    have hc := c_antitone (show j.val + 1 ≤ n by omega)
    have hd := (neg_le_abs (p.re - c (j.val + 1))).trans
      (real_coordinate_bound p (j.val + 1))
    dsimp [rho]
    linarith

theorem left_edge_mem (n : Nat) (y : ℝ)
    (hy0 : -1 < y) (hy1 : y < 1) : point (a n) y ∈ Kn n := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min (ε / 2) (c n / 16)
  have hδ : 0 < δ := lt_min (by linarith) (by have hc := c_pos n; linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδc : δ ≤ c n / 16 := min_le_right _ _
  let q := point (a n + δ) y
  have hq : q ∈ X n := by
    apply left_collar n q
    · change a n < a n + δ
      linarith
    · change a n + δ < 7 * c n / 8
      dsimp [a]
      linarith [c_pos n]
    · exact hy0
    · exact hy1
  refine ⟨q, hq, ?_⟩
  rw [Complex.dist_of_im_eq (by simp [q, point]), Real.dist_eq]
  change |a n - (a n + δ)| < ε
  rw [show a n - (a n + δ) = -δ by ring, abs_neg, abs_of_pos hδ]
  exact hδε

theorem union_bounds {p : ℂ} (hp : p ∈ XInfinity) :
    0 < p.re ∧ p.re < 2 ∧ -1 < p.im ∧ p.im < 1 := by
  obtain ⟨m, hm⟩ := mem_iUnion.mp hp
  have h := (mem_X (m+1) p).mp hm
  exact ⟨(a_pos (m+1)).trans h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩

theorem union_high_mem_stage (n : Nat) {p : ℂ}
    (hp : p ∈ XInfinity) (hl : a n < p.re) : p ∈ X n := by
  obtain ⟨m, hm⟩ := mem_iUnion.mp hp
  rcases le_total n (m+1) with hnm | hmn
  · have h := (mem_X (m+1) p).mp hm
    apply (mem_X n p).mpr
    refine ⟨⟨hl, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩, ?_⟩
    intro j
    exact h.2 ⟨j.val, by omega⟩
  · exact stages_monotone hmn hm

theorem project_continuous (n : Nat) : Continuous (project n) := by
  unfold project point
  simp_rw [Complex.mk_eq_add_mul_I]
  exact (Complex.continuous_ofReal.comp
    (continuous_const.max Complex.continuous_re)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

theorem project_mem_on_union (n : Nat) {p : ℂ} (hp : p ∈ XInfinity) :
    project n p ∈ Kn n := by
  by_cases hl : a n < p.re
  · have he : project n p = p := by
      apply Complex.ext <;> simp [project, point, max_eq_right hl.le]
    rw [he]
    exact subset_closure (union_high_mem_stage n hp hl)
  · have h := union_bounds hp
    simpa [project, max_eq_left (le_of_not_gt hl)] using
      left_edge_mem n p.im h.2.2.1 h.2.2.2

theorem project_mem_closure (n : Nat) {p : ℂ} (hp : p ∈ KInfinity) :
    project n p ∈ Kn n := by
  have h : XInfinity ⊆ (project n) ⁻¹' Kn n := fun _ hx => project_mem_on_union n hx
  exact closure_minimal h (isClosed_closure.preimage (project_continuous n)) hp

theorem closures_nested (n : Nat) : Kn n ⊆ KInfinity :=
  closure_mono (stage_subset_union n)

theorem Kn_real_bound (n : Nat) {p : ℂ} (hp : p ∈ Kn n) : a n ≤ p.re := by
  have h : X n ⊆ {q : ℂ | a n ≤ q.re} :=
    fun q hq => ((mem_X n q).mp hq).1.1.le
  exact closure_minimal h (isClosed_le continuous_const Complex.continuous_re) hp

theorem KInfinity_bounds {p : ℂ} (hp : p ∈ KInfinity) :
    0 ≤ p.re ∧ p.re ≤ 2 ∧ -1 ≤ p.im ∧ p.im ≤ 1 := by
  have h0 : XInfinity ⊆ {q : ℂ | 0 ≤ q.re} := fun _ hq => (union_bounds hq).1.le
  have h2 : XInfinity ⊆ {q : ℂ | q.re ≤ 2} := fun _ hq => (union_bounds hq).2.1.le
  have hy0 : XInfinity ⊆ {q : ℂ | -1 ≤ q.im} := fun _ hq => (union_bounds hq).2.2.1.le
  have hy1 : XInfinity ⊆ {q : ℂ | q.im ≤ 1} := fun _ hq => (union_bounds hq).2.2.2.le
  exact ⟨closure_minimal h0 (isClosed_le continuous_const Complex.continuous_re) hp,
    closure_minimal h2 (isClosed_le Complex.continuous_re continuous_const) hp,
    closure_minimal hy0 (isClosed_le continuous_const Complex.continuous_im) hp,
    closure_minimal hy1 (isClosed_le Complex.continuous_im continuous_const) hp⟩

theorem Kn_nonempty (n : Nat) : (Kn n).Nonempty :=
  ⟨point (a n) 0, left_edge_mem n 0 (by norm_num) (by norm_num)⟩

theorem KInfinity_nonempty : KInfinity.Nonempty := by
  obtain ⟨p, hp⟩ := Kn_nonempty 0
  exact ⟨p, closures_nested 0 hp⟩

theorem KInfinity_bounded : Bornology.IsBounded KInfinity := by
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset
  intro p hp
  have h := KInfinity_bounds hp
  have hi : |p.im| ≤ 1 := abs_le.mpr ⟨by linarith, h.2.2.2⟩
  have hn := Complex.norm_le_abs_re_add_abs_im p
  rw [abs_of_nonneg h.1] at hn
  change dist p 0 ≤ 3
  rw [dist_zero_right]
  linarith

theorem Kn_bounded (n : Nat) : Bornology.IsBounded (Kn n) :=
  KInfinity_bounded.subset (closures_nested n)

theorem project_dist_bound (n : Nat) {p : ℂ} (hp : p ∈ KInfinity) :
    dist p (project n p) ≤ a n := by
  rw [Complex.dist_of_im_eq (by simp [project, point]), Real.dist_eq]
  change |p.re - max (a n) p.re| ≤ a n
  by_cases h : a n ≤ p.re
  · rw [max_eq_right h]
    simpa using (a_pos n).le
  · rw [max_eq_left (le_of_not_ge h), abs_of_nonpos (by linarith)]
    linarith [(KInfinity_bounds hp).1]

theorem hausdorff_upper (n : Nat) :
    Metric.hausdorffDist (Kn n) KInfinity ≤ a n := by
  apply Metric.hausdorffDist_le_of_mem_dist (a_pos n).le
  · intro p hp
    exact ⟨p, closures_nested n hp, by simpa using (a_pos n).le⟩
  · intro p hp
    exact ⟨project n p, project_mem_closure n hp, project_dist_bound n hp⟩

theorem c_tendsto_zero : Tendsto c atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem origin_mem : (0 : ℂ) ∈ KInfinity := by
  have ht : Tendsto (fun m : Nat => point (13 * c m / 16) 0) atTop (𝓝 (0 : ℂ)) := by
    have hr : Tendsto (fun m : Nat => 13 * c m / 16) atTop (𝓝 (0 : ℝ)) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : Nat => (13 : ℝ)) atTop (𝓝 13)).mul c_tendsto_zero).div_const 16
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa [point, Complex.mk_eq_add_mul_I, Function.comp_def] using hc
  apply mem_closure_of_tendsto ht
  exact Eventually.of_forall fun m => stage_subset_union m (by
    apply left_collar m (point (13 * c m / 16) 0)
    · change a m < 13 * c m / 16
      dsimp [a]
      linarith [c_pos m]
    · change 13 * c m / 16 < 7 * c m / 8
      linarith [c_pos m]
    · norm_num [point]
    · norm_num [point])

theorem origin_infDist (n : Nat) : Metric.infDist (0 : ℂ) (Kn n) = a n := by
  apply le_antisymm
  · have he := left_edge_mem n 0 (by norm_num) (by norm_num)
    have hd : dist (0 : ℂ) (point (a n) 0) = a n := by
      rw [Complex.dist_of_im_eq (by simp [point]), Real.dist_eq]
      change |0 - a n| = a n
      rw [zero_sub, abs_neg, abs_of_pos (a_pos n)]
    simpa [hd] using (Metric.infDist_le_dist_of_mem (x := (0 : ℂ)) he)
  · apply (Metric.le_infDist (Kn_nonempty n)).mpr
    intro p hp
    have h := Kn_real_bound n hp
    have hn := (le_abs_self p.re).trans (Complex.abs_re_le_norm p)
    rw [dist_zero_left]
    exact h.trans hn

theorem hausdorff_finite (n : Nat) :
    Metric.hausdorffEDist (Kn n) KInfinity ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (Kn_nonempty n) KInfinity_nonempty (Kn_bounded n) KInfinity_bounded

/- The stated value is a conclusion on the ACTUAL closures, including n=0.
   Finiteness is established before using the totalised real lower-bound API. -/
theorem hausdorff_exact (n : Nat) : Metric.hausdorffDist (Kn n) KInfinity = a n := by
  apply le_antisymm (hausdorff_upper n)
  have hf : Metric.hausdorffEDist KInfinity (Kn n) ≠ ⊤ := by
    rw [Metric.hausdorffEDist_comm]
    exact hausdorff_finite n
  have h := Metric.infDist_le_hausdorffDist_of_mem origin_mem hf
  rw [origin_infDist, Metric.hausdorffDist_comm] at h
  exact h
end MirrorHausdorff

namespace MirrorNumericalInterfaces
open Filter Topology

/- Finite ranks of the classified smooth closed/exact quotients.
   These are statements on the declared carriers, not singular Betti definitions. -/
theorem stage_finrank (n : Nat) :
    Module.finrank ℝ (MirrorFiniteQuotient.StageQuotient n) = n := by
  rw [(MirrorFiniteLinear.stagePeriodLinearEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℝ

theorem native_stage_finrank (n : Nat) :
    Module.finrank ℝ (MirrorFiniteNativeForms.NativeStageQuotient n) = n := by
  rw [(MirrorFiniteNativeForms.nativeStagePeriodLinearEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℝ

/- The distance is the native Hausdorff distance of the literal closures. -/
theorem geometric_halving (n : Nat) :
    Metric.hausdorffDist (MirrorHausdorff.Kn (n + 1)) MirrorHausdorff.KInfinity =
      Metric.hausdorffDist (MirrorHausdorff.Kn n) MirrorHausdorff.KInfinity / 2 := by
  simp only [MirrorHausdorff.hausdorff_exact, MirrorGeometry.a, MirrorGeometry.c_succ]
  ring

theorem geometric_tendsto_zero :
    Tendsto (fun n : Nat =>
      Metric.hausdorffDist (MirrorHausdorff.Kn n) MirrorHausdorff.KInfinity)
      atTop (𝓝 0) := by
  simpa only [MirrorHausdorff.hausdorff_exact, MirrorGeometry.a, mul_zero, zero_div] using
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (3 : ℝ)) atTop (𝓝 3)).mul
      MirrorHausdorff.c_tendsto_zero).div_const 4

end MirrorNumericalInterfaces

#print axioms MirrorNumericalInterfaces.stage_finrank
#print axioms MirrorNumericalInterfaces.native_stage_finrank
#print axioms MirrorNumericalInterfaces.geometric_halving
#print axioms MirrorNumericalInterfaces.geometric_tendsto_zero
