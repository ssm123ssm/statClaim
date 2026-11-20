"""Monte Carlo estimates of rejection rates: estimates with Monte Carlo error, never proofs.

Each simulated study draws its summary statistics directly, so one run costs the same at
any sample size: the difference in means is normal and each sum of squares is a scaled
chi-square, as they are for normal outcomes. The test is then applied exactly as it would
be to the data: Student's pooled t-test or Welch's test, with t quantiles, not normal ones.

Reproducible by construction. A stream is seeded from SHA-256 of the seed and a label, and
only `random.Random(...).random()` is used, the part of Python's generator that Python
keeps the same across versions. Normal and gamma draws are written here, not taken from
the random module, whose other methods may change. Bump ENGINE_VERSION whenever anything
here could change a result for the same seed.
"""

import hashlib
import math
import random
from collections.abc import Callable
from dataclasses import dataclass

ENGINE_VERSION = 1
GENERATOR = "Mersenne Twister (Python random.random), seeded from SHA-256 of the seed and a label"
INTERVAL = "Clopper-Pearson"
CONFIDENCE = 0.95
DEFAULT_RUNS = 10_000
MIN_RUNS = 1_000
MAX_RUNS = 200_000
# A sample-size search may simulate at most this many studies, so a run stays within
# about half a minute.
MAX_SIMULATED_STUDIES = 20_000_000

MARSAGLIA_BRAY = (
    "Marsaglia, G. and Bray, T. A. (1964). A convenient method for generating normal "
    "variables. SIAM Review 6(3), 260-264."
)
MARSAGLIA_TSANG = (
    "Marsaglia, G. and Tsang, W. W. (2000). A simple method for generating gamma variables. "
    "ACM Transactions on Mathematical Software 26(3), 363-372."
)
CLOPPER_PEARSON = (
    "Clopper, C. J. and Pearson, E. S. (1934). The use of confidence or fiducial limits "
    "illustrated in the case of the binomial. Biometrika 26(4), 404-413."
)
MORRIS = (
    "Morris, T. P., White, I. R. and Crowther, M. J. (2019). Using simulation studies to "
    "evaluate statistical methods. Statistics in Medicine 38(11), 2074-2102."
)
REFERENCES = (MORRIS, CLOPPER_PEARSON, MARSAGLIA_BRAY, MARSAGLIA_TSANG)


class Stream:
    """Uniform, normal and gamma draws from one seeded stream."""

    def __init__(self, seed: int, *labels: object):
        text = ":".join(str(part) for part in (seed, *labels))
        state = int.from_bytes(hashlib.sha256(text.encode()).digest()[:16], "big")
        self._random = random.Random(state).random
        self._spare: float | None = None

    def uniform(self) -> float:
        """In (0, 1]: never zero, so its logarithm is finite."""
        return 1.0 - self._random()

    def normal(self) -> float:
        """Marsaglia's polar method; each accepted pair gives two draws."""
        if self._spare is not None:
            value, self._spare = self._spare, None
            return value
        while True:
            x = 2.0 * self._random() - 1.0
            y = 2.0 * self._random() - 1.0
            s = x * x + y * y
            if 0.0 < s < 1.0:
                scale = math.sqrt(-2.0 * math.log(s) / s)
                self._spare = y * scale
                return x * scale

    def gamma(self, shape: float) -> float:
        """Marsaglia and Tsang's method; a shape below one is boosted by one."""
        if shape < 1.0:
            return self.gamma(shape + 1.0) * self.uniform() ** (1.0 / shape)
        d = shape - 1.0 / 3.0
        c = 1.0 / math.sqrt(9.0 * d)
        while True:
            x = self.normal()
            v = 1.0 + c * x
            if v <= 0.0:
                continue
            v = v * v * v
            u = self.uniform()
            if u < 1.0 - 0.0331 * x**4 or math.log(u) < 0.5 * x * x + d * (1.0 - v + math.log(v)):
                return d * v

    def chi_square(self, df: float) -> float:
        return 2.0 * self.gamma(df / 2.0)


def _beta_fraction(x: float, a: float, b: float) -> float:
    """The continued fraction of the incomplete beta function, by Lentz's method."""
    tiny = 1e-300
    c, d = 1.0, 1.0 - (a + b) * x / (a + 1.0)
    d = 1.0 / (d if abs(d) > tiny else tiny)
    result = d
    for m in range(1, 400):
        step = m * (b - m) * x / ((a + 2 * m - 1) * (a + 2 * m))
        d = 1.0 + step * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + step / c if abs(1.0 + step / c) > tiny else tiny
        result *= d * c
        step = -(a + m) * (a + b + m) * x / ((a + 2 * m) * (a + 2 * m + 1))
        d = 1.0 + step * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + step / c if abs(1.0 + step / c) > tiny else tiny
        change = d * c
        result *= change
        if abs(change - 1.0) < 1e-15:
            return result
    raise ArithmeticError("The incomplete beta function did not converge.")


def beta_cdf(x: float, a: float, b: float) -> float:
    """The regularized incomplete beta function I_x(a, b)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    log_front = (
        math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log1p(-x)
    )
    front = math.exp(log_front)
    if x < (a + 1.0) / (a + b + 2.0):
        return front * _beta_fraction(x, a, b) / a
    return 1.0 - front * _beta_fraction(1.0 - x, b, a) / b


def t_tail(t: float, df: float) -> float:
    """P(T > |t|) for Student's t with df degrees of freedom: one tail."""
    return 0.5 * beta_cdf(df / (df + t * t), df / 2.0, 0.5)


def t_quantile(probability: float, df: float) -> float:
    """The t value with P(T <= t) = probability, for probability above one half."""
    if not 0.5 < probability < 1.0:
        raise ValueError("The t quantile is computed for probabilities between 1/2 and 1.")
    low, high = 0.0, 1.0
    while t_tail(high, df) > 1.0 - probability:
        high *= 2.0
    for _ in range(200):
        middle = (low + high) / 2.0
        if t_tail(middle, df) > 1.0 - probability:
            low = middle
        else:
            high = middle
        if high - low < 1e-13 * max(1.0, high):
            break
    return (low + high) / 2.0


def _beta_quantile(probability: float, a: float, b: float) -> float:
    low, high = 0.0, 1.0
    for _ in range(200):
        middle = (low + high) / 2.0
        if beta_cdf(middle, a, b) < probability:
            low = middle
        else:
            high = middle
        if high - low < 1e-14:
            break
    return (low + high) / 2.0


def clopper_pearson(successes: int, runs: int, confidence: float = CONFIDENCE) -> tuple:
    """The exact two-sided interval for a binomial proportion."""
    tail = (1.0 - confidence) / 2.0
    lower = 0.0 if successes == 0 else _beta_quantile(tail, successes, runs - successes + 1)
    upper = (
        1.0 if successes == runs else _beta_quantile(1.0 - tail, successes + 1, runs - successes)
    )
    return lower, upper


@dataclass(frozen=True)
class Estimate:
    """How often the test rejected in `runs` simulated studies, with a 95% interval."""

    rejected: int
    runs: int
    lower: float
    upper: float

    @property
    def rate(self) -> float:
        return self.rejected / self.runs


def estimate(trial: Callable[[Stream], bool], runs: int, stream: Stream) -> Estimate:
    rejected = sum(1 for _ in range(runs) if trial(stream))
    return Estimate(rejected, runs, *clopper_pearson(rejected, runs))


SIDES = ("higher", "lower", "both")


def two_means_trial(
    difference: float,
    sd: float,
    n_control: int,
    n_treatment: int,
    null_value: float,
    alpha: float,
    side: str,
    welch: bool,
) -> Callable[[Stream], bool]:
    """One simulated study of normal outcomes with a common SD: does the t-test reject?

    `side` is "higher" (the null says the difference is at most null_value), "lower" (at
    least) or "both" (equal). The pooled test uses n_control + n_treatment - 2 degrees of
    freedom; Welch's uses the Welch-Satterthwaite degrees of freedom of each study.
    """
    if side not in SIDES:
        raise ValueError(f"Unknown side {side!r}.")
    if sd <= 0:
        raise ValueError("A t-test needs a positive standard deviation.")
    if welch and min(n_control, n_treatment) < 2 or min(n_control, n_treatment) < 1:
        raise ValueError("Welch's test needs two participants per arm; Student's, one.")
    if n_control + n_treatment < 3:
        raise ValueError("A t-test needs at least three participants in all.")
    spread = sd * math.sqrt(1.0 / n_control + 1.0 / n_treatment)
    tail = alpha / 2.0 if side == "both" else alpha

    def rejects(t: float, df: float) -> bool:
        if side == "higher" and t <= 0 or side == "lower" and t >= 0:
            return False
        return t_tail(t, df) <= tail

    if not welch:
        df = n_control + n_treatment - 2
        critical = t_quantile(1.0 - tail, df)

        def pooled(stream: Stream) -> bool:
            shift = difference - null_value + spread * stream.normal()
            pooled_sd = sd * math.sqrt(stream.chi_square(df) / df)
            t = shift / (pooled_sd * math.sqrt(1.0 / n_control + 1.0 / n_treatment))
            if side == "higher":
                return t > critical
            if side == "lower":
                return t < -critical
            return abs(t) > critical

        return pooled

    # Welch's degrees of freedom lie between the smaller arm's n - 1 and n_control +
    # n_treatment - 2, so most studies are decided by these two quantiles alone.
    sure = t_quantile(1.0 - tail, min(n_control, n_treatment) - 1)
    never = t_quantile(1.0 - tail, n_control + n_treatment - 2)

    def welch_study(stream: Stream) -> bool:
        shift = difference - null_value + spread * stream.normal()
        var_c = sd * sd * stream.chi_square(n_control - 1) / (n_control - 1) / n_control
        var_t = sd * sd * stream.chi_square(n_treatment - 1) / (n_treatment - 1) / n_treatment
        t = shift / math.sqrt(var_c + var_t)
        size = abs(t) if side == "both" else (t if side == "higher" else -t)
        if size > sure:
            return True
        if size <= never:
            return False
        df = (var_c + var_t) ** 2 / (var_c**2 / (n_control - 1) + var_t**2 / (n_treatment - 1))
        return rejects(t, df)

    return welch_study
