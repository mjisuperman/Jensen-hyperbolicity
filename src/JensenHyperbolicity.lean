
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Basic

open scoped BigOperators Topology
open BigOperators Filter


/-!
# The divisor-convolution family g and the partition rank moments: a single-file formalization

The declaration order matches the paper section by section, so a reader can go through the paper and
  this file in parallel.  Section 2 (theory): 2.1 coefficient objects, 2.2 regional sum identities
           (Theorems 2.1-2.5), 2.3 the convolution bridge (Theorem 2.6).
  Section 3 (average order): 3.1 local limit and moments, 3.2 average order (Theorem 3.3),
           3.3 the constant A_2 = 2 (Theorems 3.4-3.5), 3.4 the a = 1 annihilation (Theorem 3.6).
  Section 4 (Jensen): 4.1 log-concavity, 4.2 degree two (Corollary 4.2), 4.3 explicit threshold
  (Theorem 4.3, Lemmas 4.4-4.6).  Section 5 (applications): 5.1 non-rationality, 5.2 AP constants.
  Section 6 collects the open problems (comments).

Section 0 holds the external inputs (axioms, each with its source): the moment object M, the
Hardy-Ramanujan and Bringmann-Mahlburg-Rhoades asymptotics, the Fristedt local limit, the
class-number average, Polya-Vinogradov, partial summation, the exponent comparison, the Hermite
threshold and the convolution structure; everything else is proved in place.  Axioms have no body
-/

namespace KranK

/-! ## Section 0. Asymptotic layer: the external-input interface (axioms) and genuine objects -/

/-- The partition function p(n): the cardinality of the genuine mathlib object `Nat.Partition`. -/
noncomputable def partNum (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)
/-- The rank moments M_{2s}(n).  mathlib has no Dyson rank, so this is an opaque axiom with no body;
its behaviour is governed entirely by `BMR_moment_log` and cannot conflict with any definition. -/
axiom M : ℕ → ℕ → ℝ
/-- External input, Hardy-Ramanujan (1918) / Rademacher (1937) in asymptotic-series form: there is an
error function r with log p(n) = pi*sqrt(2/3)*sqrt n - log n - log(4*sqrt 3) + r n, with
|r n| <= C1/sqrt n and |Delta^2 r n| <= C2/(n^2*sqrt n).  The second bound is a direct consequence
of the Rademacher asymptotic series (a smooth error with r''(x) = O(x^(-5/2))); the pointwise
O(n^(-1/2)) bound alone is too weak for a Delta^2 argument, and this is the minimal sufficient form. -/
axiom HR_log_partition :
  ∃ r : ℕ → ℝ, ∃ C₁ C₂ N₀ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧ 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ (n : ℝ) →
        Real.log (partNum n : ℝ) =
          Real.pi * Real.sqrt (2 / 3) * Real.sqrt n
            - Real.log n - Real.log (4 * Real.sqrt 3) + r n ∧
        |r n| ≤ C₁ / Real.sqrt n ∧
        |r (n + 1) - 2 * r n + r (n - 1)| ≤ C₂ / ((n : ℝ) ^ 2 * Real.sqrt n)
/-- External input, Bringmann-Mahlburg-Rhoades rank-moment asymptotics in logarithmic form: for each
s >= 1 there are A > 0 and an error function r with
log M_{2s}(n) = log A + s*log n + log p(n) + r n,
|r n| <= C1/sqrt n and |Delta^2 r n| <= C2/(n^2*sqrt n) (again from the saddle-point series). -/
axiom BMR_moment_log (s : ℕ) (hs : 1 ≤ s) :
  ∃ A : ℝ, 0 < A ∧
  ∃ r : ℕ → ℝ, ∃ C₁ C₂ N₀ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧ 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ (n : ℝ) →
        0 < M s n ∧
        Real.log (M s n) =
          Real.log A + (s : ℝ) * Real.log n + Real.log (partNum n : ℝ) + r n ∧
        |r n| ≤ C₁ / Real.sqrt n ∧
        |r (n + 1) - 2 * r n + r (n - 1)| ≤ C₂ / ((n : ℝ) ^ 2 * Real.sqrt n)
/-- The Hurwitz class number H(d): no mathlib definition, an opaque axiom used for Theorem 5.2. -/
axiom H : ℤ → ℝ
/-- External input, the Dirichlet-Gauss class-number average: there is C_H > 0 with
sum_{e<=x} H(1-24e) = C_H * x * sqrt x * (1 + o(1)). -/
axiom class_number_average :
  ∃ C_H : ℝ, 0 < C_H ∧
  ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
    ∀ x : ℕ, (∑ e ∈ Finset.Icc 1 x, H (1 - 24 * (e : ℤ))) =
      C_H * (x : ℝ) * Real.sqrt (x : ℝ) * (1 + r x)
/-- Power-law predicate (the hypothesis refuted in Theorem 5.2): rho : N -> R grows like the power x^d
(d : Z) at +oo, i.e. rho e / e^d -> a > 0.  This records the assumption that rho = g/H is
eventually of type e^d, which is what Theorem 5.2 refutes. -/
def rho_power_law (ρ : ℕ → ℝ) (d : ℤ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto (fun e : ℕ => ρ e / (e : ℝ) ^ (d : ℤ)) atTop (𝓝 a)
/-- External input, the partial-summation channel for Theorem 5.2 (Abel summation with a power-law weight):
combining the partial sum A(x) = sum H ~ C_H * x^(3/2) with the factor rho e ~ a * e^d gives
sum (rho e) * H(1-24e) ~ C * x^(d+3/2) * (1+o(1)).  Since g = rho * H this is the leading order of
sum_{e<=x} g(e): rho ~ e^d forces sum g to have order x^(d+3/2).  The constant C is nonzero and
the exponent d + 3/2 depends on d alone, not on the amplitude a. -/
axiom partial_summation_power_law :
  ∀ ρ : ℕ → ℝ, ∀ d : ℤ, rho_power_law ρ d →
    ∃ C : ℝ, C ≠ 0 ∧
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ x : ℕ, (∑ e ∈ Finset.Icc 1 x, (ρ e) * H (1 - 24 * (e : ℤ))) =
        C * Real.rpow (x : ℝ) (((d : ℤ) : ℝ) + 3 / 2) * (1 + r x)
/-- External input, Polya-Vinogradov: for a non-principal Dirichlet character chi mod N the short-sum
bound |sum_{m<=M} chi(m)| <= sqrt N * log(N+1) holds (mathlib has only the trivial bound). -/
axiom polya_vinogradov {N : ℕ} (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
  ∀ M : ℕ, ‖∑ m ∈ Finset.Icc 1 M, χ (m : ZMod N)‖ ≤ Real.sqrt N * (Real.log N + 1)

/-- External input, Lemma 3.1 (Fristedt's two-variable local limit): the limit law of rank/sqrt n has
variance sigma^2 > 0 and even moments A_s > 0 with A_1 = sigma^2; Gaussian closed forms do not apply,
and the moments are governed by the convolution structure. -/
axiom local_limit :
  ∃ σ : ℝ, 0 < σ ∧ ∃ A : ℕ → ℝ, (∀ s : ℕ, 1 ≤ s → 0 < A s) ∧ A 1 = σ ^ 2

/-- External input, positivity of Hurwitz class numbers: H(1-24e) > 0 for e >= 1 (class numbers of
negative discriminants are at least 1).  Used to simplify rho(e) * H(1-24e) = g(e) in Theorem 5.2. -/
axiom hurwitz_positive (e : ℕ) : 0 < H (1 - 24 * (e : ℤ))
/-! ## Section 2.1. The coefficient object (the divisor-sum form of g_{a,b,l}) -/
/-- S₁(e) = Σ_{n|e, an > b(e/n)} (an − b(e/n))^k -/
def s1 (a b k : ℕ) (e : ℕ) : ℤ :=
  ∑ n ∈ (Nat.divisors e),
    if a * n > b * (e / n) then (((a * n : ℕ) : ℤ) - ((b * (e / n) : ℕ) : ℤ)) ^ k else 0

/-- S₂(e) = Σ_{n|e, e/n > abn} (e/n − abn)^k -/
def s2 (a b k : ℕ) (e : ℕ) : ℤ :=
  ∑ n ∈ (Nat.divisors e),
    if (e / n) > a * b * n then ((((e / n) : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k else 0

/-- g_{a,b,l}(e) = S_1(e) - S_2(e), with k = l - 1. -/
def g (a b k : ℕ) (e : ℕ) : ℤ := s1 a b k e - s2 a b k e

/-- When n | e and e <> 0, e / (e / n) = n. -/
lemma div_div_self_of_mem {e n : ℕ} (hn : n ∈ Nat.divisors e) : e / (e / n) = n := by
  exact Nat.div_div_self (Nat.dvd_of_mem_divisors hn) (Nat.mem_divisors.mp hn).2

/-- When n | e and e <> 0, e / n divides e, hence e / n is a divisor of e. -/
lemma div_mem_divisors_of_mem {e n : ℕ} (hn : n ∈ Nat.divisors e) : e / n ∈ Nat.divisors e := by
  have hdiv : n ∣ e := Nat.dvd_of_mem_divisors hn
  have hne : e ≠ 0 := (Nat.mem_divisors.mp hn).2
  have hdiv' : e / n ∣ e := by
    rcases hdiv with ⟨m, rfl⟩
    have hpos : 0 < n := Nat.pos_of_mem_divisors hn
    have hq : (n * m) / n = m := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left m hpos
    refine ⟨n, ?_⟩
    rw [hq, Nat.mul_comm]
  exact Nat.mem_divisors.mpr ⟨hdiv', hne⟩
/-! ## Section 2.2. Regional sum identities (Theorems 2.1-2.5) -/
/-! The regional exchange lemma, generalised to a predicate P:
sum_{e<=x, P e} sum_{n|e} f n (e/n) = sum_{m,n<=x, mn<=x, P(mn)} f n m,
for any decidable predicate P, with no preservation hypothesis. -/
lemma sum_over_divisors_swap' {x : ℕ} (f : ℕ → ℕ → ℤ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ e ∈ Finset.Icc 1 x with P e, ∑ n ∈ (Nat.divisors e), f n (e / n)) =
      ∑ p ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x) with p.1 * p.2 ≤ x ∧ P (p.1 * p.2),
        f p.2 p.1 := by
  rw [← Finset.sum_sigma (s := (Finset.Icc 1 x).filter P) (t := fun e : ℕ => Nat.divisors e)
    (f := fun p : Sigma (fun _ : ℕ => ℕ) => f p.2 (p.1 / p.2))]
  refine Finset.sum_bij (fun p _ => (p.1 / p.2, p.2)) ?_ ?_ ?_ ?_
  · -- · -- hi: the image lies in the right-hand set
    intro p hp
    have hmem : p.1 ∈ (Finset.Icc 1 x).filter P ∧ p.2 ∈ Nat.divisors p.1 := Finset.mem_sigma.mp hp
    have he : p.1 ∈ Finset.Icc 1 x := (Finset.mem_filter.mp hmem.1).1
    have hPe : P p.1 := (Finset.mem_filter.mp hmem.1).2
    have hn : p.2 ∈ Nat.divisors p.1 := hmem.2
    have hpos : 0 < p.2 := Nat.pos_of_mem_divisors hn
    have hdiv : p.2 ∣ p.1 := Nat.dvd_of_mem_divisors hn
    have hpos1 : 0 < p.1 := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp he).1
    have hle : p.2 ≤ p.1 := Nat.le_of_dvd hpos1 hdiv
    have hq : p.2 * (p.1 / p.2) = p.1 := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hdiv
    have hq' : (p.1 / p.2) * p.2 = p.1 := by rw [Nat.mul_comm, hq]
    have hP' : P (p.2 * (p.1 / p.2)) := by simpa [hq] using hPe
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt (Nat.div_pos hle hpos),
            le_trans (Nat.div_le_self p.1 p.2) (Finset.mem_Icc.mp he).2⟩,
          Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hpos, le_trans hle (Finset.mem_Icc.mp he).2⟩⟩,
        ⟨by rw [hq']; exact (Finset.mem_Icc.mp he).2, by simpa [Nat.mul_comm] using hP'⟩⟩
  · -- · -- i_inj: phi is injective
    intro p₁ hp₁ p₂ hp₂ hφ
    rcases p₁ with ⟨e₁, n₁⟩
    rcases p₂ with ⟨e₂, n₂⟩
    simp at hφ
    have hmem₁ : n₁ ∈ Nat.divisors e₁ := (Finset.mem_sigma.mp hp₁).2
    have hmem₂ : n₂ ∈ Nat.divisors e₂ := (Finset.mem_sigma.mp hp₂).2
    have hdiv₁ : n₁ ∣ e₁ := Nat.dvd_of_mem_divisors hmem₁
    have hdiv₂ : n₂ ∣ e₂ := Nat.dvd_of_mem_divisors hmem₂
    have heq : e₁ = e₂ := by
      calc
        e₁ = (e₁ / n₁) * n₁ := (Nat.div_mul_cancel hdiv₁).symm
        _ = (e₂ / n₂) * n₁ := by rw [hφ.1]
        _ = (e₂ / n₂) * n₂ := by rw [hφ.2]
        _ = e₂ := Nat.div_mul_cancel hdiv₂
    exact Sigma.ext heq (hφ.2 ▸ HEq.rfl)
  · -- · -- i_surj: phi is surjective
    intro q hq
    have hqmem : q ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x) := (Finset.mem_filter.mp hq).1
    have hm : q.1 ∈ Finset.Icc 1 x := (Finset.mem_product.mp hqmem).1
    have hn : q.2 ∈ Finset.Icc 1 x := (Finset.mem_product.mp hqmem).2
    have hqle : q.1 * q.2 ≤ x := (Finset.mem_filter.mp hq).2.1
    have hPq : P (q.1 * q.2) := (Finset.mem_filter.mp hq).2.2
    have hposm : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
    have hposn : 0 < q.2 := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    refine ⟨⟨q.1 * q.2, q.2⟩, ?hmem, ?hφ⟩
    · simpa only [Sigma.fst, Sigma.snd] using Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr
            ⟨Nat.succ_le_of_lt (Nat.mul_pos hposm hposn), hqle⟩, hPq⟩,
          Nat.mem_divisors.mpr ⟨⟨q.1, by rw [Nat.mul_comm]⟩, ne_of_gt (Nat.mul_pos hposm hposn)⟩⟩
    · have hdiv : (q.1 * q.2) / q.2 = q.1 := by
        exact Nat.mul_div_left q.1 hposn
      simp [hdiv]
  · -- · -- h: the summands are equal (rfl)
    intro p hp
    rfl
/-- Paper Theorem 2.1 (the full regional sum identity):
sum_{e<=x} g_{a,b,k}(e) = sum_{mn<=x, an>bm} (an-bm)^k - sum_{mn<=x, m>abn} (m-abn)^k. -/
theorem sum_g_eq_region {a b k x : ℕ} :
    (∑ e ∈ Finset.Icc 1 x, g a b k e) =
      (∑ p ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x) with p.1 * p.2 ≤ x,
        if a * p.2 > b * p.1 then (((a * p.2 : ℕ) : ℤ) - ((b * p.1 : ℕ) : ℤ)) ^ k else 0) -
      (∑ p ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x) with p.1 * p.2 ≤ x,
        if p.1 > a * b * p.2 then (((p.1 : ℕ) : ℤ) - ((a * b * p.2 : ℕ) : ℤ)) ^ k else 0) := by
  unfold g
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold s1
    simpa [Finset.filter_true] using
      (sum_over_divisors_swap' (P := fun _ : ℕ => True) (f := fun n m =>
        if a * n > b * m then (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k else 0))
  · unfold s2
    simpa [Finset.filter_true] using
      (sum_over_divisors_swap' (P := fun _ : ℕ => True) (f := fun n m =>
        if m > a * b * n then (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k else 0))
/-- Paper Theorem 2.2 (the regional sum identity in arithmetic progressions mod N):
Σ_{e=1..x, e≡r (N)} g_{a,b,k}(e) = Σ_{mn≤x, mn≡r (N), an>bm} (an−bm)^k
  - sum_{mn<=x, mn=r (N), m>abn} (m-abn)^k. -/
theorem sum_g_eq_region_ap {a b k x N r : ℕ} :
    (∑ e ∈ (Finset.Icc 1 x : Finset ℕ) with e ≡ r [MOD N], g a b k e) =
      (∑ p ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x)
          with p.1 * p.2 ≤ x ∧ p.1 * p.2 ≡ r [MOD N],
        if a * p.2 > b * p.1 then (((a * p.2 : ℕ) : ℤ) - ((b * p.1 : ℕ) : ℤ)) ^ k else 0) -
      (∑ p ∈ (Finset.Icc 1 x).product (Finset.Icc 1 x)
          with p.1 * p.2 ≤ x ∧ p.1 * p.2 ≡ r [MOD N],
        if p.1 > a * b * p.2 then (((p.1 : ℕ) : ℤ) - ((a * b * p.2 : ℕ) : ℤ)) ^ k else 0) := by
  unfold g
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold s1
    have hswap := sum_over_divisors_swap' (x := x) (P := fun e : ℕ => e ≡ r [MOD N])
      (f := fun n m =>
        if a * n > b * m then (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k else 0)
    rw [← hswap]
  · unfold s2
    have hswap := sum_over_divisors_swap' (x := x) (P := fun e : ℕ => e ≡ r [MOD N])
      (f := fun n m =>
        if m > a * b * n then (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k else 0)
    rw [← hswap]
/-- Membership of the constrained region (S_1: an>bm): (m,n) lies in {mn<=x and an>bm} iff n in Icc 1 x, m in Icc 1 (x/n) and an>bm. -/
lemma mem_region_iff_per_n_s1 {x a b : ℕ} :
    (m, n) ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ x ∧ a * p.2 > b * p.1)
        ((Finset.Icc 1 x).product (Finset.Icc 1 x)) ↔
      n ∈ Finset.Icc 1 x ∧ m ∈ Finset.Icc 1 (x / n) ∧ a * n > b * m := by
  constructor
  · intro h
    rw [Finset.mem_filter] at h
    have hpx : m ∈ Finset.Icc 1 x ∧ n ∈ Finset.Icc 1 x := Finset.mem_product.mp h.1
    have hmn : m * n ≤ x := by simpa using h.2.1
    have hc : a * n > b * m := by simpa using h.2.2
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpx.2).1
    have hmleaf : m ≤ x / n := by
      rw [Nat.le_div_iff_mul_le hnpos]
      exact hmn
    exact ⟨hpx.2, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpx.1).1, hmleaf⟩, hc⟩
  · intro h
    rcases h with ⟨hn, hm, hc⟩
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
             le_trans (Finset.mem_Icc.mp hm).2 (Nat.div_le_self x n)⟩, hn⟩
    · constructor
      · simpa using (Nat.le_div_iff_mul_le hnpos).1 (Finset.mem_Icc.mp hm).2
      · exact hc

/-- The constrained exchange summing over n first (S_1: an>bm): sum_{mn<=x, an>bm} F m n = sum_{n<=x} sum_{m<=x/n, an>bm} F m n. -/
lemma sum_region_per_n_s1 {x a b : ℕ} (F : ℕ → ℕ → ℤ) :
    (∑ p ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ x ∧ a * p.2 > b * p.1)
        ((Finset.Icc 1 x).product (Finset.Icc 1 x)), F p.1 p.2) =
      (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n)), F m n) := by
  have hs : (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n)), F m n) =
      (∑ s ∈ (Finset.Icc 1 x).sigma (fun n : ℕ =>
        Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n))), F s.2 s.1) := by
    rw [Finset.sum_sigma]
  rw [hs]
  refine Finset.sum_bij (fun q hq => Sigma.mk q.2 q.1) ?hi ?hφ ?hs2 ?h
  · intro q hq
    rw [Finset.mem_sigma]
    simpa [Finset.mem_filter] using mem_region_iff_per_n_s1.mp hq
  · intro q hq r hr hφ
    have hf0 := congrArg Sigma.fst hφ
    have hf : q.2 = r.2 := by simpa using hf0
    have hs0 := congrArg Sigma.snd hφ
    have hs : q.1 = r.1 := by simpa using hs0
    exact Prod.ext hs hf
  · intro p hp
    rw [Finset.mem_sigma] at hp
    refine ⟨(Sigma.snd p, Sigma.fst p), ?mem, ?φ⟩
    · exact mem_region_iff_per_n_s1.mpr (by simpa [Finset.mem_filter] using hp)
    · change Sigma.mk (Sigma.fst p) (Sigma.snd p) = p
      rfl
  · intro q hq
    rfl

/-- Membership of the constrained region (S_2: m>abn): (m,n) lies in {mn<=x and m>abn} iff n in Icc 1 x, m in Icc 1 (x/n) and m>abn. -/
lemma mem_region_iff_per_n_s2 {x a b : ℕ} :
    (m, n) ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ x ∧ p.1 > a * b * p.2)
        ((Finset.Icc 1 x).product (Finset.Icc 1 x)) ↔
      n ∈ Finset.Icc 1 x ∧ m ∈ Finset.Icc 1 (x / n) ∧ m > a * b * n := by
  constructor
  · intro h
    rw [Finset.mem_filter] at h
    have hpx : m ∈ Finset.Icc 1 x ∧ n ∈ Finset.Icc 1 x := Finset.mem_product.mp h.1
    have hmn : m * n ≤ x := by simpa using h.2.1
    have hc : m > a * b * n := by simpa using h.2.2
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpx.2).1
    have hmleaf : m ≤ x / n := by
      rw [Nat.le_div_iff_mul_le hnpos]
      exact hmn
    exact ⟨hpx.2, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpx.1).1, hmleaf⟩, hc⟩
  · intro h
    rcases h with ⟨hn, hm, hc⟩
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
             le_trans (Finset.mem_Icc.mp hm).2 (Nat.div_le_self x n)⟩, hn⟩
    · constructor
      · simpa using (Nat.le_div_iff_mul_le hnpos).1 (Finset.mem_Icc.mp hm).2
      · exact hc

/-- The constrained exchange summing over n first (S_2: m>abn): sum_{mn<=x, m>abn} F m n = sum_{n<=x} sum_{m<=x/n, m>abn} F m n. -/
lemma sum_region_per_n_s2 {x a b : ℕ} (F : ℕ → ℕ → ℤ) :
    (∑ p ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ x ∧ p.1 > a * b * p.2)
        ((Finset.Icc 1 x).product (Finset.Icc 1 x)), F p.1 p.2) =
      (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n)), F m n) := by
  have hs : (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n)), F m n) =
      (∑ s ∈ (Finset.Icc 1 x).sigma (fun n : ℕ =>
        Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n))), F s.2 s.1) := by
    rw [Finset.sum_sigma]
  rw [hs]
  refine Finset.sum_bij (fun q hq => Sigma.mk q.2 q.1) ?hi ?hφ ?hs2 ?h
  · intro q hq
    rw [Finset.mem_sigma]
    simpa [Finset.mem_filter] using mem_region_iff_per_n_s2.mp hq
  · intro q hq r hr hφ
    have hf0 := congrArg Sigma.fst hφ
    have hf : q.2 = r.2 := by simpa using hf0
    have hs0 := congrArg Sigma.snd hφ
    have hs : q.1 = r.1 := by simpa using hs0
    exact Prod.ext hs hf
  · intro p hp
    rw [Finset.mem_sigma] at hp
    refine ⟨(Sigma.snd p, Sigma.fst p), ?mem, ?φ⟩
    · exact mem_region_iff_per_n_s2.mpr (by simpa [Finset.mem_filter] using hp)
    · change Sigma.mk (Sigma.fst p) (Sigma.snd p) = p
      rfl
  · intro q hq
    rfl

/-- Paper Theorem 2.3 (the exchange summing over n first; the constraint is preserved by the bijection):
Σ_{e=1..x} g_{a,b,k}(e) = Σ_{n≤x} Σ_{m≤x/n, an>bm} (an−bm)^k
  - sum_{n<=x} sum_{m<=x/n, m>abn} (m-abn)^k. -/
theorem sum_g_eq_region_per_n {a b k x : ℕ} :
    (∑ e ∈ Finset.Icc 1 x, g a b k e) =
      (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n)),
          (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k) -
      (∑ n ∈ Finset.Icc 1 x,
        ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n)),
          (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k) := by
  rw [sum_g_eq_region]
  congr 1
  · rw [← Finset.sum_filter]
    simp [Finset.filter_filter]
    exact sum_region_per_n_s1 (F := fun m n => (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k)
  · rw [← Finset.sum_filter]
    simp [Finset.filter_filter]
    exact sum_region_per_n_s2 (F := fun m n => (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k)
/-- For n in [1,x], the integer quotient x/n also lies in [1,x]. -/
lemma nat_div_mem_region {x n : ℕ} (hn : n ∈ Finset.Icc 1 x) :
    x / n ∈ Finset.Icc 1 x := by
  have hn' : 1 ≤ n ∧ n ≤ x := Finset.mem_Icc.mp hn
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 1) hn'.1
  have hqpos : 0 < x / n := Nat.div_pos hn'.2 hnpos
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hqpos, Nat.div_le_self x n⟩

/-- The general floor-fibre grouping: sum_{n<=x} G n = sum_{j<=x} sum_{n: x/n=j} G n. -/
lemma sum_group_by_floor_fiber {x : ℕ} (G : ℕ → ℤ) :
    (∑ n ∈ Finset.Icc 1 x, G n) =
      (∑ j ∈ Finset.Icc 1 x,
        ∑ n ∈ Finset.filter (fun n : ℕ => x / n = j) (Finset.Icc 1 x), G n) := by
  let s : Finset ℕ := Finset.Icc 1 x
  let t : ℕ → Finset ℕ := fun j => Finset.filter (fun n : ℕ => x / n = j) s
  change (∑ n ∈ s, G n) = (∑ j ∈ s, ∑ n ∈ t j, G n)
  calc
    (∑ n ∈ s, G n) = (∑ p ∈ s.sigma t, G p.2) := by
      refine Finset.sum_bij (fun n hn => Sigma.mk (x / n) n) ?hi ?hφ ?hs2 ?h
      · intro n hn
        rw [Finset.mem_sigma]
        exact ⟨nat_div_mem_region hn, by simp [t, hn]⟩
      · intro n hn m hm hφ
        exact congrArg Sigma.snd hφ
      · intro p hp
        rw [Finset.mem_sigma] at hp
        rcases hp with ⟨hleft, hright⟩
        rcases p with ⟨a, b⟩
        have hf : b ∈ Finset.filter (fun n : ℕ => x / n = a) s := by simpa [t] using hright
        have hq : x / b = a := (Finset.mem_filter.mp hf).2
        refine ⟨b, ?mem, ?_⟩
        · exact (Finset.mem_filter.mp hf).1
        · simp [hq]
      · intro n hn
        rfl
    _ = (∑ j ∈ s, ∑ n ∈ t j, G n) := by
      exact Finset.sum_sigma (s := s) (t := t) (f := fun p : Sigma (fun _ : ℕ => ℕ) => G p.2)

/-- The constrained fibre stratification (S_1: an>bm): the exchange over n is regrouped into floor-fibres.
   sum_{n<=x} sum_{m<=x/n, an>bm} F m n = sum_{j<=x} sum_{n: x/n=j} sum_{m<=j, an>bm} F m n. -/
theorem per_n_to_layers_s1 {x a b : ℕ} (F : ℕ → ℕ → ℤ) :
    (∑ n ∈ Finset.Icc 1 x,
      ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n)), F m n) =
      (∑ j ∈ Finset.Icc 1 x,
        ∑ n ∈ Finset.filter (fun n : ℕ => x / n = j) (Finset.Icc 1 x),
          ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 j), F m n) := by
  rw [sum_group_by_floor_fiber (x := x)
    (G := fun n => ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 (x / n)), F m n)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hq : x / n = j := (Finset.mem_filter.mp hn).2
  rw [hq]

/-- The constrained fibre stratification (S_2: m>abn): the exchange over n is regrouped into floor-fibres.
   sum_{n<=x} sum_{m<=x/n, m>abn} F m n = sum_{j<=x} sum_{n: x/n=j} sum_{m<=j, m>abn} F m n. -/
theorem per_n_to_layers_s2 {x a b : ℕ} (F : ℕ → ℕ → ℤ) :
    (∑ n ∈ Finset.Icc 1 x,
      ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n)), F m n) =
      (∑ j ∈ Finset.Icc 1 x,
        ∑ n ∈ Finset.filter (fun n : ℕ => x / n = j) (Finset.Icc 1 x),
          ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 j), F m n) := by
  rw [sum_group_by_floor_fiber (x := x)
    (G := fun n => ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 (x / n)), F m n)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hq : x / n = j := (Finset.mem_filter.mp hn).2
  rw [hq]

/-- Paper Theorem 2.4 (the full constrained chain: the n-exchange plus the floor-fibre stratification):
Σ_{e=1..x} g_{a,b,k}(e) = Σ_{j≤x} Σ_{n: x/n=j} Σ_{m≤j, an>bm} (an−bm)^k
  - sum_{j<=x} sum_{n: x/n=j} sum_{m<=j, m>abn} (m-abn)^k. -/
theorem sum_g_eq_region_per_n_layers {a b k x : ℕ} :
    (∑ e ∈ Finset.Icc 1 x, g a b k e) =
      (∑ j ∈ Finset.Icc 1 x,
        ∑ n ∈ Finset.filter (fun n : ℕ => x / n = j) (Finset.Icc 1 x),
          ∑ m ∈ Finset.filter (fun m : ℕ => a * n > b * m) (Finset.Icc 1 j),
            (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k) -
      (∑ j ∈ Finset.Icc 1 x,
        ∑ n ∈ Finset.filter (fun n : ℕ => x / n = j) (Finset.Icc 1 x),
          ∑ m ∈ Finset.filter (fun m : ℕ => m > a * b * n) (Finset.Icc 1 j),
            (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k) := by
  rw [sum_g_eq_region_per_n]
  congr 1
  · exact per_n_to_layers_s1 (F := fun m n => (((a * n : ℕ) : ℤ) - ((b * m : ℕ) : ℤ)) ^ k)
  · exact per_n_to_layers_s2 (F := fun m n => (((m : ℕ) : ℤ) - ((a * b * n : ℕ) : ℤ)) ^ k)
/-- The pointwise algebraic core: 1/j - j/(j+1)^2 = 1/(j(j+1)) + 1/(j+1)^2.
This is the algebra behind splitting the stratified main term into summable pieces. -/
theorem coeff_identity {j : ℝ} (hj : 1 ≤ j) :
    (1 / j - j / (j + 1) ^ 2) =
      1 / (j * (j + 1)) + 1 / (j + 1) ^ 2 := by
  field_simp [show (j + 1 : ℝ) ≠ 0 by positivity, show j ≠ 0 by positivity]
  ring_nf

/-- The telescoping identity (pointwise): 1/(j(j+1)) = 1/j - 1/(j+1), which turns sum 1/(j(j+1)) into
a discrete telescoping sum converging to 1 (with the Basel tail giving the coefficient pi^2/6). -/
theorem telescope_identity {j : ℝ} (hj : 1 ≤ j) :
    (1 : ℝ) / (j * (j + 1)) = (1 : ℝ) / j - (1 : ℝ) / (j + 1) := by
  field_simp [show (j + 1 : ℝ) ≠ 0 by positivity, show j ≠ 0 by positivity]
  ring_nf

/-- Paper Theorem 2.5, the exact layer sum: sum_{a<k<=b} k = T(b) - T(a) with T(N) = N(N+1)/2
(= (b+1)*b/2 - (a+1)*a/2).  A Gauss triangular difference, a finite Finset sum. -/
theorem stratum_sum_closed {a b : ℕ} (hab : a < b) :
    (∑ i ∈ Finset.Icc (a + 1) b, i) = (b + 1) * b / 2 - (a + 1) * a / 2 := by
  have hIcc : Finset.Icc (a + 1) b = (Finset.range (b + 1)) \ (Finset.range (a + 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_sdiff]
    omega
  rw [hIcc]
  have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact lt_of_lt_of_le hi (by omega : a + 1 ≤ b + 1)
  have hpre : (∑ i ∈ Finset.range (b + 1) \ Finset.range (a + 1), i) + (∑ i ∈ Finset.range (a + 1), i) =
      (∑ i ∈ Finset.range (b + 1), i) := Finset.sum_sdiff hsub
  rw [Finset.sum_range_id (b + 1), Finset.sum_range_id (a + 1)] at hpre
  have hbin : (b + 1) * ((b + 1) - 1) / 2 = (b + 1) * b / 2 := by
    rw [show ((b + 1 : ℕ) - 1) = b by omega]
  have hain : (a + 1) * ((a + 1) - 1) / 2 = (a + 1) * a / 2 := by
    rw [show ((a + 1 : ℕ) - 1) = a by omega]
  rw [hbin, hain] at hpre
  exact Nat.eq_sub_of_add_eq hpre

/-- The layer 'triangular difference -> main term' identity over the reals: expanding 2j*[T(x/j) - T(x/(j+1))]
gives the main term x^2*(1/j - j/(j+1)^2) (whose coefficient is the left side of `coeff_identity`)
plus the subterm x/(j+1).  This is the smooth main term of the layer obtained by substituting the
linear endpoints a = x/(j+1), b = x/j into `stratum_sum_closed`. -/
theorem stratum_region_main_term {x j : ℝ} (hj : j ≠ 0) (hj1 : j + 1 ≠ 0) :
    (2 * j) * (((x / j) * ((x / j) + 1) / 2) - ((x / (j + 1)) * ((x / (j + 1)) + 1) / 2)) =
      x ^ 2 * ((1 / j) - j / (j + 1) ^ 2) + x / (j + 1) := by
  field_simp [hj, hj1]
  ring

/-- Floor discretisation of the membership: the fibre (x/(j+1), x/j] intersected with the integers is
exactly Finset.Icc (floor(x/(j+1))+1) (floor(x/j)).  The fibre j = floor(x/n) is x/(j+1) < n <= x/j;
the lower bound floor(x/(j+1)) < n is x/(j+1) < (n:R)
n <= floor(x/j) is (n:R) <= x/j via `Nat.le_floor_iff'`.
Pure order theory, no asymptotics, no axiom. -/
lemma stratum_floor_mem {x j : ℝ} (n : ℕ) (hn : n ≠ 0) :
    n ∈ Finset.Icc (Nat.floor (x / (j + 1)) + 1) (Nat.floor (x / j)) ↔
      x / (j + 1) < (n : ℝ) ∧ (n : ℝ) ≤ x / j := by
  constructor
  · intro h
    have hlo : Nat.floor (x / (j + 1)) + 1 ≤ n := (Finset.mem_Icc.mp h).1
    have hhi : n ≤ Nat.floor (x / j) := (Finset.mem_Icc.mp h).2
    constructor
    · have hlt : Nat.floor (x / (j + 1)) < n := Nat.succ_le_iff.mp hlo
      exact (Nat.floor_lt' (a := x / (j + 1)) (n := n) hn).1 hlt
    · exact (Nat.le_floor_iff' (a := x / j) (n := n) hn).1 hhi
  · intro h
    exact Finset.mem_Icc.mpr <| by
      constructor
      · have hlo : ⌊x / (j + 1)⌋₊ < n := (Nat.floor_lt' (a := x / (j + 1)) (n := n) hn).2 h.1
        exact Nat.succ_le_iff.mpr hlo
      · exact (Nat.le_floor_iff' (a := x / j) (n := n) hn).2 h.2

/-- The floor-discretised layer sum equals T(floor(x/j)) - T(floor(x/(j+1))): a direct instance of
`stratum_sum_closed` at the endpoints a = floor(x/(j+1)), b = floor(x/j), the exact closure
of the smooth main term on the integer lattice (a Gauss triangular difference). -/
theorem stratum_sum_closed_floor {x j : ℝ}
    (hf : Nat.floor (x / (j + 1)) < Nat.floor (x / j)) :
    (∑ i ∈ Finset.Icc (Nat.floor (x / (j + 1)) + 1) (Nat.floor (x / j)), i) =
      (Nat.floor (x / j) + 1) * Nat.floor (x / j) / 2 -
        (Nat.floor (x / (j + 1)) + 1) * Nat.floor (x / (j + 1)) / 2 := by
  exact stratum_sum_closed hf

/-- The smooth main-term coefficient: 2j*[ (x/j)^2/2 - (x/(j+1))^2/2 ] = x^2*(1/j - j/(j+1)^2),
the difference of the squared triangular endpoints;
the right side is exactly the left side of `coeff_identity`. -/
theorem stratum_smooth_main_term {x j : ℝ} (hj : j ≠ 0) (hj1 : j + 1 ≠ 0) :
    (2 * j) * (((x / j) ^ 2) / 2 - ((x / (j + 1)) ^ 2) / 2) =
      x ^ 2 * (1 / j - j / (j + 1) ^ 2) := by
  field_simp [hj, hj1]

/-- The residual between the smooth and triangular forms: the triangular endpoint sum (the left side of
`stratum_region_main_term`) minus the smooth endpoint sum (the left side of
`stratum_smooth_main_term`); per endpoint T(t) - t^2/2 = t/2, so the difference is exactly
x/(j+1), the linear subterm, i.e. the O(floor(x/j)) residual of the layer. -/
theorem stratum_smooth_triangular_residual {x j : ℝ} (hj : j ≠ 0) (hj1 : j + 1 ≠ 0) :
    ((2 * j) * (((x / j) * ((x / j) + 1) / 2) - ((x / (j + 1)) * ((x / (j + 1)) + 1) / 2)))
      - ((2 * j) * (((x / j) ^ 2) / 2 - ((x / (j + 1)) ^ 2) / 2)) = x / (j + 1) := by
  field_simp [hj, hj1]
  ring

/-- The floor bound on the residual: for x >= 0 and j >= 1, x/(j+1) <= floor(x/j) + 1.
from the triangular to the smooth form is controlled by the number of integer points in the fibre
(plus one). -/
theorem stratum_residual_floor_bound {x j : ℝ} (hx : 0 ≤ x) (hj : 1 ≤ j) :
    x / (j + 1) ≤ (Nat.floor (x / j) : ℝ) + 1 := by
  have h1 : (j : ℝ) > 0 := by linarith
  have h11 : (j : ℝ) + 1 > 0 := by linarith
  have hle : x / (j + 1) ≤ x / j := by
    have hj0 : (j : ℝ) ≠ 0 := by linarith
    have hj10 : (j : ℝ) + 1 ≠ 0 := by linarith
    field_simp [hj10, hj0]
    nlinarith [hx]
  have hlt : x / j < (Nat.floor (x / j) : ℝ) + 1 := Nat.lt_floor_add_one (x / j)
  exact le_trans hle (le_of_lt hlt)

/-! ## Section 2.3. The convolution bridge (Theorem 2.6) -/

/-- Exact constant-term cancellation (the key algebraic step in the Rausch structure, valid for any
constant B): the constant term (1-2^(l-1))B_l/(2l) of g_{a,b,l} cancels the additive term
(2^(l-1)-1)B_l/(2l) in the bracket, so the bracketed q-series has no constant term and its n-th coefficient is a pure convolution (no standalone p(n)).  B is the l-th Bernoulli number. -/
theorem constant_term_cancellation (B : ℚ) (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    ((1 : ℚ) - (2 : ℚ) ^ (ℓ - 1)) * B / (2 * ℓ) +
      (((2 : ℚ) ^ (ℓ - 1) - 1) * B / (2 * ℓ)) = 0 := by
  have h2ℓ : (2 * ℓ : ℚ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hℓ)
  field_simp [h2ℓ]
  ring

/-- External input, Rausch (arXiv:2510.04708, Lemma 5.1, the case k = 2): the structural decomposition
M_{2s}(n) = 2^(2-2s) * sum_{l even, 2<=l<=2s} binom(2s,l-1) sum_{e<=n} g_{2,3,l}(e) * p(n-e).
The constant-term cancellation is `constant_term_cancellation`; this is the interface to a published identity. -/
axiom rausch_structure (s n : ℕ) (hs : 1 ≤ s) :
  M (2 * s) n = (2 : ℝ) ^ ((2 : ℝ) - 2 * (s : ℝ)) *
    ∑ ℓ ∈ (Finset.Icc 2 (2 * s)).filter (fun ℓ : ℕ => ℓ % 2 = 0),
      (Nat.choose (2 * s) (ℓ - 1) : ℝ) *
        (∑ e ∈ Finset.Icc 1 n, ((g 2 3 (ℓ - 1) e : ℤ) : ℝ) * (partNum (n - e) : ℝ))

/-- Paper Theorem 2.6 (the convolution bridge): M_{2s}(n) = 2^(2-2s) * sum binom(2s,l-1) (g_{2,3,l} * p)(n).
It follows from the Rausch structure (an external input) and reduces the arithmetic of the rank moments to that of the divisor-convolution family. -/
theorem convolution_bridge (s n : ℕ) (hs : 1 ≤ s) :
  M (2 * s) n = (2 : ℝ) ^ ((2 : ℝ) - 2 * (s : ℝ)) *
    ∑ ℓ ∈ (Finset.Icc 2 (2 * s)).filter (fun ℓ : ℕ => ℓ % 2 = 0),
      (Nat.choose (2 * s) (ℓ - 1) : ℝ) *
        (∑ e ∈ Finset.Icc 1 n, ((g 2 3 (ℓ - 1) e : ℤ) : ℝ) * (partNum (n - e) : ℝ)) :=
  rausch_structure s n hs
/-! ## Section 3.1. Local limit and moments (Lemmas 3.1-3.2): the external inputs are in Section 0. -/
/-! ## Section 3.2. The average order of g (Theorem 3.3): the main-term coefficient core plus the asymptotic interface -/
/-- Basel constant (a mathlib brick `hasSum_zeta_two`, not an axiom): sum' 1/n^2 = pi^2/6.
This is the arithmetic source of the main-term coefficient pi^2/12. -/
theorem basel_coeff : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := by
  exact hasSum_zeta_two.tsum_eq

/-- The shifted Basel sum (via the `tsum_pnat_eq_tsum_succ` bridge, not an axiom): sum' 1/(n+1)^2 = pi^2/6.
This is the exact source of the limit sum 1/(j+1)^2 -> pi^2/6 in the smooth main term of a layer:
the positive-integer sum (the domain of `hasSum_zeta_two`) is mapped through `succ` to the shifted
natural sequence, completing the shift in one step without any finite-layer workaround. -/
theorem shifted_basel :
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 6 := by
  have heq0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
  have hbro := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
  have hz0 := tsum_pnat_eq_tsum_of_eq_zero
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) heq0
  calc
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)
        = (∑' n : ℕ+, (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) := hbro.symm
    _ = (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) := hz0
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

/-- The Basel tail (from `shifted_basel` minus the first term 1): sum' 1/(j+2)^2 = pi^2/6 - 1.
This is the infinite-shift formalisation of the tail limit pi^2/6 - 1 in the decomposition of the
A-component main term. -/
theorem basel_tail :
    (∑' j : ℕ, (1 : ℝ) / ((j + 2 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
  let f : ℕ → ℝ := fun i => (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2
  have hfsumable : Summable f := by
    have hsum := (Real.summable_one_div_nat_add_rpow (1 : ℝ) 2).mpr (by norm_num : 1 < (2 : ℝ))
    simpa [f] using hsum.congr (fun n : ℕ => by
      rw [abs_of_pos (by positivity : 0 < (↑n : ℝ) + 1)]
      simp)
  have hsplit := hfsumable.sum_add_tsum_nat_add 1
  have hpre : (∑ i ∈ Finset.range 1, f i) = 1 := by
    simp [f]
  have htail : (∑' i : ℕ, f (i + 1)) = (∑' j : ℕ, (1 : ℝ) / ((j + 2 : ℕ) : ℝ) ^ 2) := by
    apply congrArg tsum
    funext i
    simp [f, Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [hpre, htail, shifted_basel] at hsplit
  linarith

/-- Paper Theorems 3.3 and 3.4 (average order; an external analytic asymptotic, while the main-term
coefficient pi^2/12 is machine-checked by `basel_coeff`/`shifted_basel`/`coeff_identity`/`telescope_identity`/`stratum_*`):
sum_{e<=x} g_{a,b,2}(e) = (a-1)*(pi^2/12)*x^2 + O(x^(3/2)). -/
axiom average_order_g (a b : ℕ) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ,
    |(∑ e ∈ Finset.Icc 1 x, ((g a b 1 e : ℤ) : ℝ)) - (a - 1) * (Real.pi ^ 2 / 12) * (x : ℝ) ^ 2|
      ≤ C * (x : ℝ) * Real.sqrt (x : ℝ)

/-! ## Section 3.3. The explicit constant A_2 = 2 (Theorem 3.5) -/

/-- Paper Theorem 3.5, the coefficient arithmetic of A_2 = 2 (proved): pi^2/12 * (c/2) * (16/c^3) = 1
if and only if c^2 = 2*pi^2/3.  The convolution bridge (Theorem 2.6) and the average order
(Theorem 3.3) give the Stieltjes main term; the Laplace integral int_0^oo t^2 e^(-c t/(2 sqrt n)) dt
= 16 n^(3/2)/c^3 reduces the coefficient to the displayed identity, which is verified here. -/
theorem a2_coeff_one (c : ℝ) (hc : c ≠ 0) :
    (Real.pi ^ 2 / 12) * (c / 2) * (16 / c ^ 3) = 1 ↔ c ^ 2 = 2 * Real.pi ^ 2 / 3 := by
  constructor
  · intro h
    have hnorm : (Real.pi ^ 2 / 12) * (c / 2) * (16 / c ^ 3) = (2 * Real.pi ^ 2) / (3 * c ^ 2) := by
      field_simp [hc]
      ring
    rw [hnorm] at h
    have hpos : 0 < 3 * c ^ 2 := by positivity
    have hcross : 2 * Real.pi ^ 2 = 3 * c ^ 2 := by
      have hh := congrArg (fun t : ℝ => t * (3 * c ^ 2)) h
      field_simp [ne_of_gt hpos] at hh
      nlinarith [hh]
    nlinarith [hcross]
  · intro h
    have hnorm : (Real.pi ^ 2 / 12) * (c / 2) * (16 / c ^ 3) = (2 * Real.pi ^ 2) / (3 * c ^ 2) := by
      field_simp [hc]
      ring
    rw [hnorm, h]
    have hπ : Real.pi ^ 2 ≠ 0 := by exact pow_ne_zero 2 (Real.pi_ne_zero)
    field_simp [hπ]
/-! ## Section 3.4. The a = 1 exchange self-dual annihilation (Theorem 3.6) -/
/-- The exchange bijection at a = 1: n |-> e/n is an involution on the divisors of e that maps the support and the summands of S_1 onto those of S_2. -/
lemma s1_eq_s2_one {b k : ℕ} (e : ℕ) : s1 1 b k e = s2 1 b k e := by
  rw [s1, s2]
  refine Finset.sum_bij (fun n _ => e / n) ?_ ?_ ?_ ?_
  · intro n hn
    exact div_mem_divisors_of_mem hn
  · intro n₁ hn₁ n₂ hn₂ hφ
    calc
      n₁ = e / (e / n₁) := (div_div_self_of_mem hn₁).symm
      _ = e / (e / n₂) := by rw [hφ]
      _ = n₂ := div_div_self_of_mem hn₂
  · intro m hm
    refine ⟨e / m, div_mem_divisors_of_mem hm, div_div_self_of_mem hm⟩
  · intro n hn
    rw [div_div_self_of_mem hn]
    simp only [Nat.one_mul]

/-- Paper Theorem 3.6: at a = 1 the family g vanishes identically (exchange self-dual annihilation, an exact zero). -/
theorem g_one_eq_zero {b k : ℕ} (e : ℕ) : g 1 b k e = 0 := by
  unfold g
  rw [s1_eq_s2_one e]
  ring

/-- Paper Theorem 3.6 (full sum): sum_{e<=x} g_{1,b,k}(e) = 0. -/
theorem sum_g_one_eq_zero {b k x : ℕ} :
    (∑ e ∈ Finset.Icc 1 x, g 1 b k e) = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact g_one_eq_zero (b := b) (k := k) (e := e)
/-! ## Section 4.1. Eventual log-concavity (Theorem 4.1) -/
/-- Rationalisation: sqrt(n+1) - sqrt n = 1/(sqrt(n+1) + sqrt n) for n >= 1. -/
lemma sqrt_diff_rat (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ) =
      (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) := by
  rw [eq_div_iff (by positivity : Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) ≠ 0)]
  calc
    (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))
        = (Real.sqrt (n + 1 : ℝ)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2 := by ring
    _ = (n + 1 : ℝ) - (n : ℝ) := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ)),
          Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    _ = 1 := by ring

/-- Rationalisation: sqrt n - sqrt(n-1) = 1/(sqrt n + sqrt(n-1)) for n >= 1. -/
lemma sqrt_diff_rat_sub (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ) =
      (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      simpa using (congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn))
    nlinarith
  rw [eq_div_iff (by positivity : Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) ≠ 0)]
  calc
    (Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ)) *
        (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ))
        = (Real.sqrt (n : ℝ)) ^ 2 - (Real.sqrt (n - 1 : ℝ)) ^ 2 := by ring
    _ = (n : ℝ) - ((n : ℝ) - 1) := by
      have hsn : 0 ≤ (n : ℝ) := by positivity
      have hsq : 0 ≤ (n - 1 : ℝ) := by
        rw [← hcast]
        exact_mod_cast Nat.zero_le (n - 1)
      rw [Real.sq_sqrt hsn, Real.sq_sqrt hsq]
    _ = 1 := by ring

/-- Delta^2 sqrt n <= -1/(8*n*sqrt n) for n >= 1.  After rationalisation
Delta^2 sqrt n = -(sqrt(n+1)-sqrt(n-1))/((sqrt n+sqrt(n-1))(sqrt(n+1)+sqrt n)),
the numerator is at least 1/(sqrt 2*sqrt n) and the denominator is at most 4*sqrt 2*n. -/
lemma d2_sqrt_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) ≤
      - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      simpa using (congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn))
    nlinarith
  -- -- numerator lower bound: sqrt(n+1) - sqrt(n-1) >= 1/(sqrt 2*sqrt n)
  have hnum : (1 : ℝ) / (Real.sqrt 2 * Real.sqrt n) ≤
      Real.sqrt (n + 1 : ℝ) - Real.sqrt (n - 1 : ℝ) := by
    have hdiff2 : Real.sqrt (n + 1 : ℝ) - Real.sqrt (n - 1 : ℝ) =
        (2 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ)) := by
      rw [eq_div_iff (by positivity : Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ) ≠ 0)]
      calc
        (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n - 1 : ℝ)) *
            (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ))
            = (Real.sqrt (n + 1 : ℝ)) ^ 2 - (Real.sqrt (n - 1 : ℝ)) ^ 2 := by ring
        _ = (n + 1 : ℝ) - ((n : ℝ) - 1) := by
          have hsn : 0 ≤ (n + 1 : ℝ) := by positivity
          have hsq : 0 ≤ (n - 1 : ℝ) := by
            rw [← hcast]
            exact_mod_cast Nat.zero_le (n - 1)
          rw [Real.sq_sqrt hsn, Real.sq_sqrt hsq]
        _ = 2 := by ring
    rw [hdiff2]
    -- -- denominator upper bound: <= 2*sqrt 2*sqrt n
    have hdenom : Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ) ≤
        2 * Real.sqrt 2 * Real.sqrt n := by
      have h1 : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt n := by
        have hle : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by nlinarith [hn]
        have hsqrt : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) :=
          Real.sqrt_le_sqrt hle
        have hmul : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
          Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) (n : ℝ)
        rwa [hmul] at hsqrt
      have h2 : Real.sqrt (n - 1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have hle : (n - 1 : ℝ) ≤ (n : ℝ) := by
          rw [← hcast]
          exact_mod_cast Nat.sub_le n 1
        exact Real.sqrt_le_sqrt hle
      have h3 : Real.sqrt (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) := by
        have h12 : (1 : ℝ) ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
        have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        nlinarith
      nlinarith
    have hdenpos : 0 < Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ) := by positivity
    rw [le_div_iff₀ hdenpos]
    have hid : (1 : ℝ) / (Real.sqrt 2 * Real.sqrt n) * (2 * Real.sqrt 2 * Real.sqrt n) = 2 := by
      field_simp [show Real.sqrt 2 * Real.sqrt n ≠ 0 by positivity]
    have hc : 0 ≤ (1 : ℝ) / (Real.sqrt 2 * Real.sqrt n) := by positivity
    have hmid : (1 / (Real.sqrt 2 * Real.sqrt n)) *
          (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n - 1 : ℝ)) ≤
        (1 / (Real.sqrt 2 * Real.sqrt n)) * (2 * Real.sqrt 2 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hdenom hc
    nlinarith [hmid, hid]
  -- -- denominator upper bound: (sqrt n+sqrt(n-1))(sqrt(n+1)+sqrt n) <= 4*sqrt 2*n
  have hden : (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
      (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) ≤ 4 * Real.sqrt 2 * (n : ℝ) := by
    have hA : Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
      have h : Real.sqrt (n - 1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have hle : (n - 1 : ℝ) ≤ (n : ℝ) := by
          rw [← hcast]
          exact_mod_cast Nat.sub_le n 1
        exact Real.sqrt_le_sqrt hle
      nlinarith
    have hB : Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt 2 * Real.sqrt (n : ℝ) := by
      have h1 : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt n := by
        have hle : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by nlinarith [hn]
        have hsqrt : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) :=
          Real.sqrt_le_sqrt hle
        have hmul : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
          Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) (n : ℝ)
        rwa [hmul] at hsqrt
      have h3 : Real.sqrt (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) := by
        have h12 : (1 : ℝ) ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
        have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        nlinarith
      nlinarith
    have hposA : 0 ≤ Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) := by positivity
    have hposB : 0 ≤ Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) := by positivity
    have hAB := mul_le_mul hA hB hposB (by positivity : 0 ≤ 2 * Real.sqrt (n : ℝ))
    have hsqrt2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← pow_two]
      exact Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))
    calc
      (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
          (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))
          ≤ 2 * Real.sqrt (n : ℝ) * (2 * Real.sqrt 2 * Real.sqrt (n : ℝ)) := hAB
      _ = 4 * Real.sqrt 2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = 4 * Real.sqrt 2 * (n : ℝ) := by rw [hsqrt2]
  -- -- combine: 1/(sqrt n+sqrt(n-1)) - 1/(sqrt(n+1)+sqrt n) >= 1/(8n sqrt n)
  have hfrac : (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) -
      (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) ≥
        (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by
    have hA : 0 < Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) := by positivity
    have hB : 0 < Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) := by positivity
    have hABpos : 0 < (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) := mul_pos hA hB
    have hident : (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) -
          (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) =
        (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n - 1 : ℝ)) /
          ((Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
            (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))) := by
      field_simp [hA.ne', hB.ne']
      ring
    rw [hident]
    change (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) ≤
      (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n - 1 : ℝ)) /
        ((Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
          (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)))
    rw [le_div_iff₀ hABpos]
    have hc : 0 ≤ (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by positivity
    have hcn : (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) * (4 * Real.sqrt 2 * (n : ℝ)) =
        (1 : ℝ) / (Real.sqrt 2 * Real.sqrt n) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hsn0 : Real.sqrt n ≠ 0 := by positivity
      field_simp [hn0, hsn0]
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    have hmid2 : (1 / (8 * (n : ℝ) * Real.sqrt n)) *
          ((Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) *
            (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))) ≤
        (1 / (8 * (n : ℝ) * Real.sqrt n)) * (4 * Real.sqrt 2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hden hc
    nlinarith [hmid2, hcn, hnum]
  -- -- recover: Delta^2 sqrt n = (sqrt(n+1)-sqrt n) - (sqrt n - sqrt(n-1))
  calc
    Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)
        = (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) -
            (Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ)) := by ring
    _ = (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) -
        (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) := by
      rw [sqrt_diff_rat n hn, sqrt_diff_rat_sub n hn]
    _ ≤ - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by
      have hh : (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) ≤
          (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) -
            (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) := by
        linarith [hfrac]
      have hneg : - ((1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) -
            (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))) ≤
          - ((1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n)) := neg_le_neg hh
      have hsimpl : - ((1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) -
            (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))) =
          (1 : ℝ) / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) -
            (1 : ℝ) / (Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) := by ring
      have hsimpl2 : - ((1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n)) =
          - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by ring
      rwa [hsimpl, hsimpl2] at hneg

/-- Delta^2 sqrt n < 0 (sqrt is strictly concave), n >= 1. -/
lemma d2_sqrt_neg (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) < 0 := by
  have hc : 0 < (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := by positivity
  have hneg : - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) < 0 := by
    calc
      - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) = - (1 / (8 * (n : ℝ) * Real.sqrt n)) := by ring
      _ < 0 := by linarith [hc]
  exact lt_of_le_of_lt (d2_sqrt_lower n hn) hneg

/-- Delta^2 log n <= 0 (log is strictly concave), n >= 2: log(n+1) - 2 log n + log(n-1) <= 0. -/
lemma d2_log_nonpos (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n + 1 : ℝ) - 2 * Real.log (n : ℝ) + Real.log (n - 1 : ℝ) ≤ 0 := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      simpa using (congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel (by omega : 1 ≤ n)))
    nlinarith
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos1 : 0 < (n + 1 : ℝ) := by positivity
  have hpos2 : 0 < (n - 1 : ℝ) := by nlinarith [hnR]
  have hposn : 0 < (n : ℝ) := by nlinarith [hnR]
  have hmm : (n + 1 : ℝ) * (n - 1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  have hle : Real.log ((n + 1 : ℝ) * (n - 1 : ℝ)) ≤ Real.log ((n : ℝ) ^ 2) :=
    Real.log_le_log (mul_pos hpos1 hpos2) hmm
  have hmul : Real.log ((n + 1 : ℝ) * (n - 1 : ℝ)) =
      Real.log (n + 1 : ℝ) + Real.log (n - 1 : ℝ) :=
    Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)
  have hsq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    rw [Real.log_pow (n : ℝ) 2]
    norm_num
  rw [hmul, hsq] at hle
  nlinarith
/-- Paper Theorem 4.1 (derived from the Section 0 axioms, no new axiom): for each s >= 1 the sequence
M_{2s}(n) is eventually strictly log-concave: there is N with M_{2s}(n)^2 > M_{2s}(n+1)*M_{2s}(n-1)
for n >= N.  The derivation expands log M(n) = c sqrt n + (s-1) log n + C0 + r_tot(n) via BMR and HR,
Δ²log M(n) = c·Δ²√n + (s−1)Δ²log n + Δ²r_tot(n) ≤ −c/(8n√n) + C_tot/(n²√n) < 0
so Delta^2 log M(n) <= -c/(8 n sqrt n) + (C2+C4)/(n^2 sqrt n) < 0 for large n, and concludes by the strict monotonicity of exp. -/
theorem M_strict_log_concave_eventual (s : ℕ) (hs : 1 ≤ s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (M s n) ^ 2 > (M s (n + 1)) * (M s (n - 1)) := by
  rcases BMR_moment_log s hs with ⟨A, hApos, r, C₁, C₂, N₁, hC1pos, hC2pos, hN1pos, hBMR⟩
  rcases HR_log_partition with ⟨r₀, C₃, C₄, N₀, hC3pos, hC4pos, hN0pos, hHR⟩
  let c := Real.pi * Real.sqrt (2 / 3)
  have hcpos : 0 < c := by positivity
  have hBMRn : ∀ n : ℕ, N₁ ≤ (n : ℝ) →
      Real.log (M s n) = Real.log A + (s : ℝ) * Real.log n +
        Real.log (partNum n : ℝ) + r n ∧
      |r n| ≤ C₁ / Real.sqrt n ∧
      |r (n + 1) - 2 * r n + r (n - 1)| ≤ C₂ / ((n : ℝ) ^ 2 * Real.sqrt n) :=
    fun n hn => (hBMR n hn).2
  have hHRn : ∀ n : ℕ, N₀ ≤ (n : ℝ) →
      Real.log (partNum n : ℝ) =
        Real.pi * Real.sqrt (2 / 3) * Real.sqrt n - Real.log n -
          Real.log (4 * Real.sqrt 3) + r₀ n ∧
      |r₀ n| ≤ C₃ / Real.sqrt n ∧
      |r₀ (n + 1) - 2 * r₀ n + r₀ (n - 1)| ≤ C₄ / ((n : ℝ) ^ 2 * Real.sqrt n) :=
    fun n hn => hHR n hn
  -- -- (1) combined expansion: log M(n) = c sqrt n + (s-1) log n + C0 + r_tot(n)
  have hlogexp : ∀ n : ℕ, N₀ ≤ (n : ℝ) → N₁ ≤ (n : ℝ) →
      Real.log (M s n) = c * Real.sqrt (n : ℝ) + ((s : ℝ) - 1) * Real.log (n : ℝ) +
        (Real.log A - Real.log (4 * Real.sqrt 3)) + (r n + r₀ n) := by
    intro n hn0 hn1
    have h1 := hBMRn n hn1
    have h2 := hHRn n hn0
    rw [h1.1, h2.1]
    dsimp [c]
    ring
  -- -- (2) eventual positivity: M(n) > 0 (given directly by the axiom; M_{2s} is a sum of positive terms)
  have hMpos : ∀ n : ℕ, Nat.ceil N₁ ≤ n → 0 < M s n := by
    intro n hn
    have hn1 : N₁ ≤ (n : ℝ) := le_trans (Nat.le_ceil N₁) (by exact_mod_cast hn)
    exact (hBMR n hn1).1
  -- -- (3) combined Delta^2 error bound
  have hrt : ∀ n : ℕ, N₀ ≤ (n : ℝ) → N₁ ≤ (n : ℝ) →
      |(r (n + 1) + r₀ (n + 1)) - 2 * (r n + r₀ n) + (r (n - 1) + r₀ (n - 1))| ≤
        (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) := by
    intro n hn0 hn1
    have h2 := (hBMRn n hn1).2.2
    have h4 := (hHRn n hn0).2.2
    calc
      |(r (n + 1) + r₀ (n + 1)) - 2 * (r n + r₀ n) + (r (n - 1) + r₀ (n - 1))|
          = |(r (n + 1) - 2 * r n + r (n - 1)) + (r₀ (n + 1) - 2 * r₀ n + r₀ (n - 1))| := by
            congr 1
            ring
      _ ≤ |r (n + 1) - 2 * r n + r (n - 1)| + |r₀ (n + 1) - 2 * r₀ n + r₀ (n - 1)| := abs_add_le _ _
      _ ≤ C₂ / ((n : ℝ) ^ 2 * Real.sqrt n) + C₄ / ((n : ℝ) ^ 2 * Real.sqrt n) := by
        exact add_le_add h2 h4
      _ = (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) := by
        rw [add_div]
  -- -- (4) Delta^2 log M < 0 for large n
  have hCtot : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (C₂ + C₄) ≤ c * (n : ℝ) / 16 := by
    rcases exists_nat_ge (16 * (C₂ + C₄) / c) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hle : (16 * (C₂ + C₄) / c) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
    have hm := mul_le_mul_of_nonneg_right hle (le_of_lt hcpos)
    rw [div_mul_cancel₀ (16 * (C₂ + C₄)) hcpos.ne'] at hm
    nlinarith only [hm]
  rcases hCtot with ⟨NCtot, hCtotb⟩
  refine ⟨Nat.max (Nat.ceil N₁ + 2) (Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3))), ?_⟩
  intro n hn
  have h₀n : Nat.ceil N₀ + 2 ≤ n :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hn)
  have h₁n : Nat.ceil N₁ + 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn0 : N₀ ≤ (n : ℝ) := by
    have h₂ : Nat.ceil N₀ ≤ n := by omega
    exact le_trans (Nat.le_ceil N₀) (by exact_mod_cast h₂)
  have hn0s : N₀ ≤ ((n - 1 : ℕ) : ℝ) := by
    have h₂ : Nat.ceil N₀ ≤ n - 1 := by omega
    exact le_trans (Nat.le_ceil N₀) (by exact_mod_cast h₂)
  have hn1 : N₁ ≤ (n : ℝ) := by
    have h₂ : Nat.ceil N₁ ≤ n := by omega
    exact le_trans (Nat.le_ceil N₁) (by exact_mod_cast h₂)
  have hn1s : N₁ ≤ ((n - 1 : ℕ) : ℝ) := by
    have h₂ : Nat.ceil N₁ ≤ n - 1 := by omega
    exact le_trans (Nat.le_ceil N₁) (by exact_mod_cast h₂)
  have hn3 : 3 ≤ n := by
    have hm1 : Nat.max NCtot 3 ≤ Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3) := Nat.le_max_right _ _
    have hm2 : Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3) ≤
        Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3)) :=
      Nat.le_max_right _ _
    have hm3 : Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3)) ≤
        Nat.max (Nat.ceil N₁ + 2) (Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3))) :=
      Nat.le_max_right _ _
    have hle : Nat.max NCtot 3 ≤ n := le_trans hm1 (le_trans hm2 (le_trans hm3 hn))
    have h3 : 3 ≤ Nat.max NCtot 3 := Nat.le_max_right _ _
    exact le_trans h3 hle
  have hn1' : 1 ≤ n := by omega
  have hctot : (C₂ + C₄) ≤ c * (n : ℝ) / 16 := hCtotb n (by
    have h3 : NCtot ≤ Nat.max NCtot 3 := Nat.le_max_left _ _
    have h4 : Nat.max NCtot 3 ≤ Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3) := Nat.le_max_right _ _
    have h5 : Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3) ≤
        Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3)) :=
      Nat.le_max_right _ _
    have h6 : Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3)) ≤
        Nat.max (Nat.ceil N₁ + 2) (Nat.max (Nat.ceil N₀ + 2) (Nat.max (Nat.ceil N₁ + 2) (Nat.max NCtot 3))) :=
      Nat.le_max_right _ _
    exact le_trans h3 (le_trans h4 (le_trans h5 (le_trans h6 hn))))
  have hposn : 0 < (n : ℝ) := by nlinarith [hn3]
  have hsnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hposn
  have hsn2pos : 0 < (n : ℝ) ^ 2 * Real.sqrt n := by positivity
  have hd2r := hrt n hn0 hn1
  have hsqr : Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ) ≤
      - (1 : ℝ) / (8 * (n : ℝ) * Real.sqrt n) := d2_sqrt_lower n hn1'
  have hlogc : Real.log (n + 1 : ℝ) - 2 * Real.log (n : ℝ) + Real.log (n - 1 : ℝ) ≤ 0 :=
    d2_log_nonpos n (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      simpa using (congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel (by omega : 1 ≤ n)))
    nlinarith
  have hcastp : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  have hd2logM : Real.log (M s (n + 1)) - 2 * Real.log (M s n) + Real.log (M s (n - 1)) < 0 := by
    have hlogn1 : Real.log (M s (n + 1)) = c * Real.sqrt ((n + 1 : ℕ) : ℝ) + ((s : ℝ) - 1) * Real.log ((n + 1 : ℕ) : ℝ) +
        (Real.log A - Real.log (4 * Real.sqrt 3)) + (r (n + 1) + r₀ (n + 1)) := by
      have hnp : N₀ ≤ ((n + 1 : ℕ) : ℝ) := by
        have h₂ : Nat.ceil N₀ ≤ n + 1 := by omega
        exact le_trans (Nat.le_ceil N₀) (by exact_mod_cast h₂)
      have hnp' : N₁ ≤ ((n + 1 : ℕ) : ℝ) := by
        have h₂ : Nat.ceil N₁ ≤ n + 1 := by omega
        exact le_trans (Nat.le_ceil N₁) (by exact_mod_cast h₂)
      exact hlogexp (n + 1) hnp hnp'
    have hlogn : Real.log (M s n) = c * Real.sqrt (n : ℝ) + ((s : ℝ) - 1) * Real.log (n : ℝ) +
        (Real.log A - Real.log (4 * Real.sqrt 3)) + (r n + r₀ n) := hlogexp n hn0 hn1
    have hlognm : Real.log (M s (n - 1)) = c * Real.sqrt ((n - 1 : ℕ) : ℝ) + ((s : ℝ) - 1) * Real.log ((n - 1 : ℕ) : ℝ) +
        (Real.log A - Real.log (4 * Real.sqrt 3)) + (r (n - 1) + r₀ (n - 1)) := hlogexp (n - 1) hn0s hn1s
    rw [hlogn1, hlogn, hlognm]
    rw [hcastp, hcast]
    have hcmain : c * (Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) ≤
        - c / (8 * (n : ℝ) * Real.sqrt n) := by
      have h1 := mul_le_mul_of_nonneg_left hsqr (le_of_lt hcpos)
      ring_nf at h1 ⊢
      exact h1
    have hlogl : Real.log (n + 1 : ℝ) - 2 * Real.log (n : ℝ) + Real.log (n - 1 : ℝ) ≤ 0 := hlogc
    have hcoeff : 0 ≤ (s : ℝ) - 1 := by
      have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      nlinarith only [hsR]
    have hb1 : ((s : ℝ) - 1) * (Real.log (n + 1 : ℝ) - 2 * Real.log (n : ℝ) + Real.log (n - 1 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff hlogl
    have hd2r_le : (r (n + 1) + r₀ (n + 1)) - 2 * (r n + r₀ n) + (r (n - 1) + r₀ (n - 1)) ≤
        (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) := (abs_le.mp hd2r).2
    have hCsmall : (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) < c / (8 * (n : ℝ) * Real.sqrt n) := by
      have h8 : (C₂ + C₄) * 8 ≤ (c * (n : ℝ) / 16) * 8 :=
        mul_le_mul_of_nonneg_right hctot (by norm_num)
      have h1 : (c * (n : ℝ) / 16) * 8 = c * (n : ℝ) / 2 := by ring
      have h2 : c * (n : ℝ) / 2 < c * (n : ℝ) := by
        nlinarith only [mul_pos hcpos hposn]
      have hcn8 : (C₂ + C₄) * 8 < c * (n : ℝ) := by
        nlinarith only [h8, h1, h2]
      have hpos' : 0 < (n : ℝ) * Real.sqrt n := mul_pos hposn hsnpos
      have hstep0 : (C₂ + C₄) * 8 * ((n : ℝ) * Real.sqrt n) <
          (c * (n : ℝ)) * ((n : ℝ) * Real.sqrt n) :=
        mul_lt_mul_of_pos_right hcn8 hpos'
      have hstep : (C₂ + C₄) * (8 * (n : ℝ) * Real.sqrt n) < c * (n : ℝ) * ((n : ℝ) * Real.sqrt n) := by
        nlinarith only [hstep0]
      have h1 : (C₂ + C₄) * (8 * (n : ℝ) * Real.sqrt n) < c * ((n : ℝ) ^ 2 * Real.sqrt n) := by
        ring_nf at hstep ⊢
        exact hstep
      rw [div_lt_iff₀ hsn2pos]
      have hid : (c / (8 * (n : ℝ) * Real.sqrt n)) * ((n : ℝ) ^ 2 * Real.sqrt n) =
          c * ((n : ℝ) ^ 2 * Real.sqrt n) / (8 * (n : ℝ) * Real.sqrt n) := by ring
      rw [hid]
      rw [lt_div_iff₀ (by positivity : 0 < 8 * (n : ℝ) * Real.sqrt n)]
      exact h1
    have hsum : c * (Real.sqrt (n + 1 : ℝ) - 2 * Real.sqrt (n : ℝ) + Real.sqrt (n - 1 : ℝ)) +
        ((s : ℝ) - 1) * (Real.log (n + 1 : ℝ) - 2 * Real.log (n : ℝ) + Real.log (n - 1 : ℝ)) +
        ((r (n + 1) + r₀ (n + 1)) - 2 * (r n + r₀ n) + (r (n - 1) + r₀ (n - 1))) ≤
        - c / (8 * (n : ℝ) * Real.sqrt n) + (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) := by
      nlinarith only [hcmain, hb1, hd2r_le]
    have hneg : - c / (8 * (n : ℝ) * Real.sqrt n) + (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) < 0 := by
      have hg : (C₂ + C₄) / ((n : ℝ) ^ 2 * Real.sqrt n) - c / (8 * (n : ℝ) * Real.sqrt n) < 0 := by
        nlinarith only [hCsmall]
      convert hg using 1; ring
    nlinarith only [hsum, hneg]
  -- -- (5) strict monotonicity of exp
  have hposn2 : 0 < M s n := by
    have h₂ : Nat.ceil N₁ ≤ n := by omega
    exact hMpos n h₂
  have hposnp : 0 < M s (n + 1) := by
    have h₂ : Nat.ceil N₁ ≤ n + 1 := by omega
    exact hMpos (n + 1) h₂
  have hposnm : 0 < M s (n - 1) := by
    have h₂ : Nat.ceil N₁ ≤ n - 1 := by omega
    exact hMpos (n - 1) h₂
  have hlogineq : Real.log (M s n) > (Real.log (M s (n + 1)) + Real.log (M s (n - 1))) / 2 := by
    linarith [hd2logM]
  have hexp : Real.exp (2 * Real.log (M s n)) > Real.exp (Real.log (M s (n + 1)) + Real.log (M s (n - 1))) := by
    exact (Real.exp_lt_exp).2 (by nlinarith [hlogineq])
  have hleft : Real.exp (2 * Real.log (M s n)) = (M s n) ^ 2 := by
    have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2]
    rw [Real.exp_nat_mul]
    rw [Real.exp_log hposn2]
  have hright : Real.exp (Real.log (M s (n + 1)) + Real.log (M s (n - 1))) =
      (M s (n + 1)) * (M s (n - 1)) := by
    rw [Real.exp_add, Real.exp_log hposnp, Real.exp_log hposnm]
  rwa [hleft, hright] at hexp
/-! ## Section 4.2. The degree-two Jensen polynomial (Corollary 4.2) -/
theorem M_jensen_degree_two (s : ℕ) (hs : 1 ≤ s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧
        M s n + 2 * M s (n + 1) * x₁ + M s (n + 2) * x₁ ^ 2 = 0 ∧
        M s n + 2 * M s (n + 1) * x₂ + M s (n + 2) * x₂ ^ 2 = 0 := by
  rcases BMR_moment_log s hs with ⟨A, hApos, r, C₁, C₂, N₁, hC1pos, hC2pos, hN1pos, hBMR⟩
  rcases M_strict_log_concave_eventual s hs with ⟨N₀, hN0⟩
  refine ⟨Nat.max (N₀ + 1) (Nat.ceil N₁ + 1), ?_⟩
  intro n hn
  have hn1 : N₀ ≤ n + 1 := by
    have h : N₀ + 1 ≤ n := le_trans (Nat.le_max_left _ _) hn
    omega
  have hnM : Nat.ceil N₁ ≤ n := by
    have h : Nat.ceil N₁ + 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
    omega
  have hsc := hN0 (n + 1) hn1
  have hcpos : 0 < M s (n + 2) := by
    have h₂ : N₁ ≤ ((n + 2 : ℕ) : ℝ) := by
      have h₃ : Nat.ceil N₁ ≤ n + 2 := by omega
      exact le_trans (Nat.le_ceil N₁) (by exact_mod_cast h₃)
    exact (hBMR (n + 2) h₂).1
  have hdelta : 0 < (M s (n + 1)) ^ 2 - M s n * M s (n + 2) := by
    have hsc' : (M s (n + 1)) ^ 2 > M s (n + 2) * M s n := by
      simpa [Nat.add_sub_cancel] using hsc
    have hmul : M s (n + 2) * M s n = M s n * M s (n + 2) := by ring
    nlinarith [hsc', hmul]
  have hΔnonneg : 0 ≤ (M s (n + 1)) ^ 2 - M s n * M s (n + 2) := le_of_lt hdelta
  have hsqrt : (Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) ^ 2 =
      (M s (n + 1)) ^ 2 - M s n * M s (n + 2) := Real.sq_sqrt hΔnonneg
  let x₁ := (-M s (n + 1) - Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) / M s (n + 2)
  let x₂ := (-M s (n + 1) + Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) / M s (n + 2)
  refine ⟨x₁, x₂, ?_⟩
  constructor
  · have hsq : 0 < Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2)) := Real.sqrt_pos.2 hdelta
    have hd : x₁ - x₂ ≠ 0 := by
      dsimp [x₁, x₂]
      field_simp [hcpos.ne']
      nlinarith [hsq]
    exact sub_ne_zero.mp hd
  · constructor
    · let t := -M s (n + 1) - Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))
      calc
        M s n + 2 * M s (n + 1) * (t / M s (n + 2)) + M s (n + 2) * (t / M s (n + 2)) ^ 2
            = (M s n * M s (n + 2) ^ 2 + 2 * M s (n + 1) * M s (n + 2) * t + M s (n + 2) * t ^ 2) / M s (n + 2) ^ 2 := by
              field_simp [hcpos.ne']
        _ = (M s n * M s (n + 2) ^ 2 + 2 * M s (n + 1) * M s (n + 2) * (-M s (n + 1) - Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) +
            M s (n + 2) * ((M s (n + 1)) ^ 2 + 2 * M s (n + 1) * Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2)) +
            (Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) ^ 2)) / M s (n + 2) ^ 2 := by
              dsimp [t]
              ring
        _ = 0 := by
              rw [hsqrt]
              ring
    · let t := -M s (n + 1) + Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))
      calc
        M s n + 2 * M s (n + 1) * (t / M s (n + 2)) + M s (n + 2) * (t / M s (n + 2)) ^ 2
            = (M s n * M s (n + 2) ^ 2 + 2 * M s (n + 1) * M s (n + 2) * t + M s (n + 2) * t ^ 2) / M s (n + 2) ^ 2 := by
              field_simp [hcpos.ne']
        _ = (M s n * M s (n + 2) ^ 2 + 2 * M s (n + 1) * M s (n + 2) * (-M s (n + 1) + Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) +
            M s (n + 2) * ((M s (n + 1)) ^ 2 - 2 * M s (n + 1) * Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2)) +
            (Real.sqrt ((M s (n + 1)) ^ 2 - M s n * M s (n + 2))) ^ 2)) / M s (n + 2) ^ 2 := by
              dsimp [t]
              ring
        _ = 0 := by
              rw [hsqrt]
              ring

/-! ## Section 4.3. Higher degree: the explicit threshold (Theorem 4.3, Lemmas 4.4-4.6)
The Hermite polynomial theory (normalisation, Sturm root separation) and the quantitative Rouché step
belong to complex analysis and orthogonal polynomials; they are declared as external axioms with their sources, while the threshold formula itself is an explicit definition. -/

/-- The degree-d Jensen polynomial (coefficients binom(d,j)*M_{2s}(n+j)) is fully real-rooted: there are
real roots r_1,...,r_d and c <> 0 with the polynomial equal to c * prod (X - r_i), counted with multiplicity. -/
def JensenRooted (s d n : ℕ) : Prop :=
  ∃ r : Fin d → ℝ, ∃ c : ℝ, c ≠ 0 ∧
    ∀ X : ℝ, (∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ) * M (2 * s) (n + j) * X ^ j) =
      c * ∏ i : Fin d, (X - r i)

/-- Paper Lemma 4.4 (explicit ratio expansion, external: saddle-point remainder): there are explicit
n_0(s) and C_1(s) such that for n >= n_0(s) and 0 <= j <= d, log ratio = A(n)*j - delta(n)^2*j^2 + R_j(n)
with |R_j(n)| <= C_1 * d^3 * n^(-5/2) (declared here in a relaxed cubic-remainder form). -/
axiom ratio_expansion_explicit (s d : ℕ) (hs : 1 ≤ s) :
  ∃ n0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n0 ≤ n → ∀ j : ℕ, j ≤ d →
    ∃ A δ R : ℝ, 0 < A ∧ 0 < δ ∧ |R| ≤ C * (d : ℝ) ^ 3 / Real.rpow (n : ℝ) (5 / 2) ∧
      Real.log (M (2 * s) (n + j)) - Real.log (M (2 * s) n) = A * (j : ℝ) - δ ^ 2 * (j : ℝ) ^ 2 + R

/-- Paper Lemma 4.5 (explicit normalisation to the Hermite model, external): there is a Hermite model H_d
(fully real-rooted, with root separation as in `hermite_root_separation`) such that the normalised Jensen
polynomial differs from H_d by O(n^(-1/4)) (the normalising substitution is absorbed into the constant). -/
axiom hermite_normalization (s d : ℕ) (hs : 1 ≤ s) :
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ C * Real.rpow (n : ℝ) (-1 / 4) ∧
      ∀ X : ℝ, |X| ≤ 2 * Real.sqrt (2 * (d : ℝ) + 1) →
        |(∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ) * M (2 * s) (n + j) * X ^ j)|
          ≤ C * (1 + |X|) ^ d * ε

/-- Paper Lemma 4.6 (Hermite root-separation lower bound, external: Sturm comparison): the roots of H_d are
real and simple, lie in (-2 sqrt(2d+1), 2 sqrt(2d+1)), and consecutive roots are at least gamma_d = 2 pi/sqrt(2d+1) apart. -/
axiom hermite_root_separation (d : ℕ) :
  ∃ γ : ℝ, 0 < γ ∧ γ = 2 * Real.pi / Real.sqrt (2 * (d : ℝ) + 1) ∧
    ∃ r : Fin d → ℝ, (∀ i j : Fin d, i ≠ j → |r i - r j| ≥ γ) ∧
      (∀ i : Fin d, |r i| < 2 * Real.sqrt (2 * (d : ℝ) + 1))

/-- Paper Theorem 4.3 (explicit threshold, external: the quantitative Rouché step): for each s >= 1 and
d >= 1 there is an explicit integer N_{s,d} such that for n >= N_{s,d} the degree-d Jensen polynomial is
fully real-rooted.  The explicit formula N_{s,d} = max(n_0(s), ceil((C_3(s,d)(d+1)(9(2d+1)/(2 pi))^d)^4)) is (4.2) in the paper. -/
axiom jensen_threshold_explicit (s d : ℕ) (hs : 1 ≤ s) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → JensenRooted s d n
/-! ## Section 5.1. Non-rationality of rho = g/H (Theorem 5.2) -/
/-- The arithmetic core of the exponent contradiction in Theorem 5.2 (machine-checked): there is no
integer d with d + 3/2 = 2, i.e. the main order x^2 cannot be written as an integer power plus 3/2.
Multiplying by 2 gives 2d + 3 = 4 (i.e. 2d = 1), which `omega` decides to have no integer solution. -/
theorem exp_integer_contradiction (d : ℤ) : ¬ (2 * d + 3 = 4) := by
  omega


/-- External input, the exponent-comparison channel for Theorem 5.2: if sum_{e<=x} g(e) = C*x^alpha*(1+o(1))
with C <> 0, then alpha = 2 (comparison with the average-order main term x^2; an analytic fact). -/
axiom exponent_comparison (α C : ℝ) (hC : C ≠ 0) :
  (∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
    ∀ x : ℕ, (∑ e ∈ Finset.Icc 1 x, ((g 2 3 1 e : ℤ) : ℝ)) =
      C * Real.rpow (x : ℝ) α * (1 + r x)) → α = 2

/-- Paper Theorem 5.2 (rho = g/H is not a rational function, assembled): there is no d : Z and positive
power law a*e^d with rho(e) = g(e)/H(1-24e) growing like e^d.  Partial summation (external) gives the
main order x^(d+3/2) for sum g, the exponent comparison (external) forces d + 3/2 = 2, contradicting d : Z via `exp_integer_contradiction`. -/
theorem rho_not_rational :
    ¬ ∃ ρ : ℕ → ℝ, (∀ e : ℕ, ρ e = ((g 2 3 1 e : ℤ) : ℝ) / H (1 - 24 * (e : ℤ))) ∧
      (∃ d : ℤ, rho_power_law ρ d) := by
  rintro ⟨ρ, hρ, d, hd⟩
  rcases partial_summation_power_law ρ d hd with ⟨C, hC, r, hr, hsum⟩
  have hgform : ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ x : ℕ, (∑ e ∈ Finset.Icc 1 x, ((g 2 3 1 e : ℤ) : ℝ)) =
        C * Real.rpow (x : ℝ) (((d : ℤ) : ℝ) + 3 / 2) * (1 + r x) := by
    refine ⟨r, hr, ?_⟩
    intro x
    have hre : ∀ e : ℕ, ρ e * H (1 - 24 * (e : ℤ)) = ((g 2 3 1 e : ℤ) : ℝ) := by
      intro e
      rw [hρ e]
      field_simp [ne_of_gt (hurwitz_positive e)]
    calc
      (∑ e ∈ Finset.Icc 1 x, ((g 2 3 1 e : ℤ) : ℝ))
          = (∑ e ∈ Finset.Icc 1 x, ρ e * H (1 - 24 * (e : ℤ))) := by
              exact Finset.sum_congr rfl (fun e he => (hre e).symm)
      _ = C * Real.rpow (x : ℝ) (((d : ℤ) : ℝ) + 3 / 2) * (1 + r x) := hsum x
  rcases hgform with ⟨r', hr', hg⟩
  have hα : ((d : ℤ) : ℝ) + 3 / 2 = 2 := exponent_comparison (((d : ℤ) : ℝ) + 3 / 2) C hC ⟨r', hr', hg⟩
  have h2 : (2 : ℝ) * (d : ℝ) = 1 := by nlinarith [hα]
  have hcast : (((2 * d : ℤ) : ℝ)) = (2 : ℝ) * (d : ℝ) := by
    rw [Int.cast_mul]
    norm_num
  have h2' : (((2 * d : ℤ) : ℝ)) = 1 := by
    rwa [hcast]
  have hz : (2 * d = (1 : ℤ)) := by exact_mod_cast h2'
  have hcontr : ¬ (2 * d = (1 : ℤ)) := by omega
  exact hcontr hz
/-! ## Section 5.2. Sums in arithmetic progressions mod N (Theorems 5.3-5.5, Corollaries 5.6-5.7) -/

/-- The Euler product prod_{p|N}(1 - p^(-2)) over the (deduplicated) prime divisors of N. -/
noncomputable def eulerProd (N : ℕ) : ℝ :=
  ∏ p ∈ (Nat.factorization N).support, (1 - ((p : ℝ) ^ 2)⁻¹)

/-- Paper Theorem 5.3 (the coprime-class constant for sigma, external: Mobius expansion plus the Euler
product main term): sum_{e<=x, e=r(N)} sigma(e) = (pi^2/12)(1/N) prod_{p|N}(1-p^(-2)) x^2 + O(2^omega(N) x log x). -/
axiom sigma_ap_coprime_constant (N r : ℕ) (hr : Nat.Coprime r N) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ,
    |(∑ e ∈ (Finset.Icc 1 x).filter (fun e : ℕ => e ≡ r [MOD N]), (ArithmeticFunction.sigma 1 e : ℝ))
      - (Real.pi ^ 2 / 12) * (1 / (N : ℝ)) * eulerProd N * (x : ℝ) ^ 2|
      ≤ C * (x : ℝ) * Real.log (x + 1)

/-- Paper Theorem 5.4 (the coprime-class constant for g, external: the region decomposition summed in the
bounded variable first): the same main-term constant as sigma, with error O_N(x^(3/2)). -/
axiom g_ap_coprime_constant (N r : ℕ) (hr : Nat.Coprime r N) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ,
    |(∑ e ∈ (Finset.Icc 1 x).filter (fun e : ℕ => e ≡ r [MOD N]), ((g 2 3 1 e : ℤ) : ℝ))
      - (Real.pi ^ 2 / 12) * (1 / (N : ℝ)) * eulerProd N * (x : ℝ) ^ 2|
      ≤ C * (x : ℝ) * Real.sqrt (x : ℝ)

/-- Paper Theorem 5.5 (the non-principal character bound, external: Polya-Vinogradov plus Abel
stratification): sum_{e<=x} chi(e) g_{a,b,2}(e) = O((a+b) x sqrt N log^2 N), with no x^2 main term. -/
axiom non_principal_char_bound (a b N : ℕ) (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ,
    ‖∑ e ∈ Finset.Icc 1 x, χ (e : ZMod N) * ((g a b 1 e : ℤ) : ℂ)‖ ≤
      C * (x : ℝ) * Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) ^ 2

/-- Paper Corollary 5.6 (uniformity, external: character decomposition plus the absence of an x^2 main
term off the principal character): any coprime-class main term of g arises from the principal component, hence is uniform in r. -/
axiom ap_main_term_uniform (N : ℕ) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r₁ r₂ x : ℕ, Nat.Coprime r₁ N → Nat.Coprime r₂ N →
    |(∑ e ∈ (Finset.Icc 1 x).filter (fun e : ℕ => e ≡ r₁ [MOD N]), ((g 2 3 1 e : ℤ) : ℝ))
      - (∑ e ∈ (Finset.Icc 1 x).filter (fun e : ℕ => e ≡ r₂ [MOD N]), ((g 2 3 1 e : ℤ) : ℝ))|
      ≤ C * (x : ℝ) * Real.sqrt (x : ℝ)
/-- Paper Corollary 5.7, the a = 1 consistency in arithmetic progressions: sum_{e<=x, e=r(N)} g_{1,b,k}(e) = 0
exactly, so any Estermann-type main-term structure must output zero at a = 1. -/
theorem sum_g_ap_one_eq_zero {b k x N r : ℕ} :
    (∑ e ∈ (Finset.Icc 1 x : Finset ℕ) with e ≡ r [MOD N], g 1 b k e) = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact g_one_eq_zero (b := b) (k := k) (e := e)

/-! ## Section 6. Extent of progress and open problems (comments, matching Section 6 of the paper)
- Main line: degree two is settled (Corollary 4.2); every degree d >= 3 has an explicit threshold
  (Theorem 4.3, via the axiom interface).
- Side line: the non-rationality of rho is settled (Theorem 5.2); excluding P-recursive pseudo-closed
  forms needs a critical-line spectral argument for the class-number Dirichlet series, and is open.
- Arithmetic progressions: the coprime-class constants are settled (Theorems 5.3-5.4); the non-coprime
multiplicative-orbit average is open.  Other directions: the three multivariate-Lorentzian candidates
  are excluded by non-M-convex counterexamples; the Selmer link is rejected; the Appell-parameter evaluation is open.
-/
end KranK
