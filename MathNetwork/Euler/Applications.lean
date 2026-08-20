import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathNetwork.Euler

/-!
# Euler applications

The checked entries are applications of the complex exponential.  The
unproved entries are explicit comparison targets: each should eventually have
an Euler/complex proof and a real sine/cosine proof recorded separately.
-/

def phasorQuarterTurn : Prop :=
  Complex.exp (Real.pi / 2 * Complex.I) * (3 + 4 * Complex.I) = -4 + 3 * Complex.I

theorem phasorQuarterTurn_mathlib : phasorQuarterTurn := by
  unfold phasorQuarterTurn
  rw [Complex.exp_pi_div_two_mul_I]
  norm_num [mul_add]
  rw [show Complex.I * (4 * Complex.I) = 4 * (Complex.I * Complex.I) by ring]
  rw [Complex.I_mul_I]
  ring

def phasorHalfTurn : Prop :=
  Complex.exp (Real.pi * Complex.I) * (3 + 4 * Complex.I) = -3 - 4 * Complex.I

theorem phasorHalfTurn_mathlib : phasorHalfTurn := by
  unfold phasorHalfTurn
  rw [Complex.exp_pi_mul_I]
  ring

theorem trig_addition_real_route (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
  exact Real.cos_add x y

theorem trig_addition_sine_real_route (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  exact Real.sin_add x y

theorem trig_subtraction_real_cos_route (x y : ℝ) :
    Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
  exact Real.cos_sub x y

theorem trig_subtraction_real_sin_route (x y : ℝ) :
    Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
  exact Real.sin_sub x y

theorem trig_addition_euler_route (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y ∧
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  have h := Complex.exp_add ((x : ℂ) * Complex.I) ((y : ℂ) * Complex.I)
  have hsum : (x : ℂ) * Complex.I + (y : ℂ) * Complex.I =
      ((x + y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_add]
    ring
  rw [hsum] at h
  constructor
  · have hr := congrArg Complex.re h
    rw [Complex.exp_ofReal_mul_I_re (x + y)] at hr
    simpa [Complex.mul_re] using hr
  · have hi := congrArg Complex.im h
    rw [Complex.exp_ofReal_mul_I_im (x + y)] at hi
    simpa [Complex.mul_im, add_comm] using hi

/-- The cosine addition formula derived through the complex-exponential
route.  Its statement is deliberately identical to `Real.cos_add`, allowing
the proof landscapes to meet at one Lean-checked proposition. -/
theorem trig_addition_euler_cos_route (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y :=
  (trig_addition_euler_route x y).1

/-- The sine addition formula derived through the same complex-exponential
route. -/
theorem trig_addition_euler_sin_route (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y :=
  (trig_addition_euler_route x y).2

/-- The cosine subtraction formula, obtained from the complex-derived
addition formula by the geometric reversal `y ↦ -y`. -/
theorem trig_subtraction_euler_cos_route (x y : ℝ) :
    Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
  have h := trig_addition_euler_cos_route x (-y)
  simpa [sub_eq_add_neg, mul_neg, sub_neg_eq_add] using h

/-- The sine subtraction formula, obtained from the same complex route by
reversing the second angle. -/
theorem trig_subtraction_euler_sin_route (x y : ℝ) :
    Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
  have h := trig_addition_euler_sin_route x (-y)
  simpa [sub_eq_add_neg, mul_neg] using h

def trigAdditionEulerRoute : Prop :=
  ∀ x y : ℝ,
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y ∧
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y

structure ApplicationEntry where
  id : String
  label : String
  statement : String
  routes : List String
  status : String
deriving Repr

def applicationCatalogue : List ApplicationEntry :=
  [ { id := "phasor-quarter-turn"
      label := "AC phasor quarter-turn"
      statement := "exp(i*pi/2) rotates 3+4i to -4+3i"
      routes := ["mathlib complex exponential", "geometric rotation"]
      status := "kernel-checked baseline" }
    , { id := "trig-addition"
        label := "Trigonometric addition identities"
        statement := "derive sine and cosine addition from one complex exponential"
        routes := ["Euler/complex", "real rotation" ]
        status := "both routes kernel-checked" }
    , { id := "trig-integrals"
        label := "Integrals of damped sinusoids"
        statement := "integrate exp(a*x) times sine or cosine"
        routes := ["complex antiderivative", "real undetermined coefficients"]
        status := "planned" }
    , { id := "constant-coefficient-ode"
        label := "Constant-coefficient linear ODE"
        statement := "solve a damped oscillator using complex roots or a real system"
        routes := ["characteristic roots", "real rotation-dilation system"]
        status := "planned" }
    , { id := "fourier-complex-basis"
        label := "Fourier complex basis"
        statement := "replace paired sine/cosine coefficients by one complex family"
        routes := ["complex exponentials", "real Fourier basis"]
        status := "planned" } ]

end MathNetwork.Euler
