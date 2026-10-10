import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A phase-budget inequality for any finite number of regions

The proof works over any linearly ordered commutative ring, including
integers, rationals and reals. It uses only interval budgets: cap the
smaller directed counts, then concentrate the nonnegative excesses.
There is no lattice, integrality or congruence hypothesis here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Tantrix

variable {R : Type*} [CommRing R]

/-- Nine times the directed area bound g(p,q). -/
def areaNumerator (p q : R) : R := p^2 + 4*p*q + q^2

/-- Nine times the two-phase bound, with its remainder supplied explicitly. -/
def phaseNumerator (P k h : R) : R :=
  P^2 + 2*P*k + 4*k^2 - 4*(P-2*k)*h - 2*h^2

/-- After capping the smaller count, lowering a to h leaves one product. -/
theorem phase_cap_certificate (k a h t : R) :
    (t-h)^2 + 6*k*t + 6*k^2 - 3*h^2 -
      areaNumerator (t+k+a) (k-a) = 2*(a-h)*(t+a+h) := by
  unfold areaNumerator
  ring

/-- The two-phase bound is attained at a=h, t₀=h, t₁=T-h, q₀=q₁=k-h.
These choices are feasible whenever 0≤h≤k and 2h≤T. -/
theorem two_phase_sharp (T k h : R) :
    areaNumerator (k+2*h) (k-h) + areaNumerator (T+k) (k-h) =
      phaseNumerator (T+2*k) k h := by
  unfold areaNumerator phaseNumerator
  ring

/-- Concentrating all excess in one phase attains the finite bound.
With 0≤h≤k and card(s)*h≤T, the displayed allocation is feasible.
This is a numerical witness, not a geometric construction. -/
theorem finite_phase_sharp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (i : ι) (hi : i ∈ s) (T k h : R) :
    (∑ j ∈ s, areaNumerator
      ((if j=i then T-(s.card : R)*h else 0)+k+2*h) (k-h)) =
    (T-(s.card : R)*h)^2 + 6*k*T + 3*(s.card : R)*(2*k^2-h^2) := by
  have he (j : ι) : areaNumerator
      ((if j=i then T-(s.card : R)*h else 0)+k+2*h) (k-h) =
      areaNumerator (k+2*h) (k-h) +
        (if j=i then areaNumerator (T-(s.card : R)*h+k+2*h) (k-h) -
          areaNumerator (k+2*h) (k-h) else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  simp [Finset.sum_add_distrib,hi]
  unfold areaNumerator
  ring

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Increasing either nonnegative directed count increases its area bound. -/
theorem areaNumerator_mono (p q p' q' : R)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') :
    areaNumerator p q ≤ areaNumerator p' q' := by
  have h1 := mul_self_le_mul_self hp hpp
  have h2 := mul_self_le_mul_self hq hqq
  have h3 := mul_le_mul hpp hqq hq (hp.trans hpp)
  unfold areaNumerator
  nlinarith only [h1,h2,h3]

/-- A single region needs only a lower surplus and an upper smaller count. -/
theorem phase_cap_bound (k a h t q : R)
    (hh : 0 ≤ h) (ha : h ≤ a) (ht : h ≤ t)
    (hq : 0 ≤ q) (hqk : q ≤ k-a) :
    areaNumerator (t+2*a+q) q ≤ (t-h)^2 + 6*k*t + 6*k^2 - 3*h^2 := by
  have hm := areaNumerator_mono (t+2*a+q) q (t+k+a) (k-a)
    (by linarith) hq (by linarith) hqk
  have hp := mul_nonneg (show 0 ≤ a-h by linarith)
    (show 0 ≤ t+a+h by linarith)
  have hc := phase_cap_certificate k a h t
  linarith

/-- Any finite number of phases, under interval budgets alone.
The sum of squares of their nonnegative excesses is at most the square
of their sum. Empty families are included. -/
theorem finite_phase_bound {ι : Type*} (s : Finset ι) (k a h : R) (t q : ι → R)
    (hh : 0 ≤ h) (ha : h ≤ a) (ht : ∀ i ∈ s, h ≤ t i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hqk : ∀ i ∈ s, q i ≤ k-a) :
    ∑ i ∈ s, areaNumerator (t i+2*a+q i) (q i) ≤
      ((∑ i ∈ s, t i) - (s.card : R)*h)^2 +
      6*k*(∑ i ∈ s, t i) + 3*(s.card : R)*(2*k^2-h^2) := by
  have hb := Finset.sum_le_sum (fun i hi =>
    phase_cap_bound k a h (t i) (q i) hh ha (ht i hi) (hq i hi) (hqk i hi))
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i hi => sub_nonneg.mpr (ht i hi))
  have he : (∑ i ∈ s, (t i-h)) = (∑ i ∈ s, t i) - (s.card : R)*h := by
    simp [Finset.sum_sub_distrib]
  have he' : (∑ i ∈ s, ((t i-h)^2 + 6*k*t i + 6*k^2 - 3*h^2)) =
      (∑ i ∈ s, (t i-h)^2) + 6*k*(∑ i ∈ s, t i) +
      3*(s.card : R)*(2*k^2-h^2) := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he'] at hb
  rw [he] at hs
  linarith

/-- The finite bound is attained by a feasible allocation whenever the
family is nonempty and its common minimum budgets fit. -/
theorem finite_phase_attained {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (i : ι) (hi : i ∈ s) (T k h : R)
    (hh : 0 ≤ h) (hk : h ≤ k) (hT : (s.card : R)*h ≤ T) :
    ∃ (a : R) (t q : ι → R),
      0 ≤ h ∧ h ≤ a ∧ (∀ j ∈ s, h ≤ t j) ∧
      (∀ j ∈ s, 0 ≤ q j ∧ q j ≤ k-a) ∧ (∑ j ∈ s, t j) = T ∧
      (∑ j ∈ s, areaNumerator (t j+2*a+q j) (q j)) =
        (T-(s.card : R)*h)^2 + 6*k*T + 3*(s.card : R)*(2*k^2-h^2) := by
  refine ⟨h,(fun j => h + if j=i then T-(s.card : R)*h else 0),
    (fun _ => k-h),hh,le_rfl,?_,?_,?_,?_⟩
  · intro j _
    dsimp only
    split_ifs <;> linarith
  · intro j _
    exact ⟨sub_nonneg.mpr hk,le_rfl⟩
  · simp [Finset.sum_add_distrib,hi]
  · convert finite_phase_sharp s i hi T k h using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

/-- The original two-phase bound is the two-element instance of the finite theorem.
No integrality, congruence or allocation partition is assumed. -/
theorem two_phase_bound (T k a h t q₀ q₁ : R)
    (hh : 0 ≤ h) (ha : h ≤ a) (ht : h ≤ t) (hT : t ≤ T-h)
    (hq₀ : 0 ≤ q₀) (hq₀k : q₀ ≤ k-a)
    (hq₁ : 0 ≤ q₁) (hq₁k : q₁ ≤ k-a) :
    areaNumerator (t+2*a+q₀) q₀ +
      areaNumerator (T-t+2*a+q₁) q₁ ≤ phaseNumerator (T+2*k) k h := by
  have hb := finite_phase_bound ({false,true} : Finset Bool) k a h
    (fun i => if i then T-t else t) (fun i => if i then q₁ else q₀) hh ha
    (by intro i _; cases i <;> simp <;> linarith)
    (by intro i _; cases i <;> simp <;> assumption)
    (by intro i _; cases i <;> simp <;> assumption)
  simp at hb
  convert hb using 1
  unfold phaseNumerator
  ring

end Tantrix
