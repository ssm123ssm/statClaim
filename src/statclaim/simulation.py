"""Monte Carlo estimates of rejection rates: estimates with Monte Carlo error, never proofs.

For normal outcomes each simulated study draws its summary statistics directly, so one run
costs the same at any sample size: the difference in means is normal and each sum of
squares is a scaled chi-square. Skewed outcomes are drawn participant by participant. The
test is then applied exactly as it would be to the data: Student's pooled t-test or
Welch's test, with t quantiles, not normal ones.

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
from fractions import Fraction
from functools import lru_cache
from statistics import NormalDist

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
# Skewed outcomes are drawn one participant at a time, about 4 million a second. The check
# counts each size of a search once and one confirmation; more confirmations, when Type I
# fails at sizes whose power passes, can take longer.
MAX_SIMULATED_PARTICIPANTS = 120_000_000
MAX_SKEWNESS = 4  # a gamma shape of at least 1/4

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

    def beta(self, a: float, b: float) -> float:
        """A beta draw as the share of two gamma draws."""
        x = self.gamma(a)
        return x / (x + self.gamma(b))

    def binomial(self, n: int, p: float) -> int:
        """Successes in n trials by geometric skips between them, so the cost grows with the
        smaller of the successes and the failures, not with n."""
        if p <= 0.0 or n <= 0:
            return 0
        if p >= 1.0:
            return n
        if p > 0.5:
            return n - self.binomial(n, 1.0 - p)
        log_q = math.log1p(-p)
        count, position = 0, 0
        while True:
            position += int(math.log(self.uniform()) / log_q) + 1
            if position > n:
                return count
            count += 1

    def cluster_size(self, mean: float, cv: float) -> int:
        """A cluster's size: the mean when cv is 0, else a gamma draw with that mean and
        coefficient of variation, rounded, and at least 1."""
        if cv <= 0.0:
            return max(1, round(mean))
        shape = 1.0 / (cv * cv)
        return max(1, round(self.gamma(shape) * mean / shape))


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


def pooled_t(first: list[float], second: list[float]) -> float:
    """Student's pooled t statistic, second minus first; 0 when there is no spread."""
    k1, k2 = len(first), len(second)
    m1, m2 = sum(first) / k1, sum(second) / k2
    ss = sum((x - m1) ** 2 for x in first) + sum((x - m2) ** 2 for x in second)
    df = k1 + k2 - 2
    if ss <= 0.0 or df <= 0:
        return 0.0 if m1 == m2 else math.copysign(math.inf, m2 - m1)
    return (m2 - m1) / math.sqrt(ss / df * (1.0 / k1 + 1.0 / k2))


def cluster_trial(
    summary: Callable[[Stream, int, float], float],
    clusters: tuple[int, int],
    sizes: tuple[float, float],
    cv: float,
    alpha: float,
) -> Callable[[Stream], bool]:
    """One simulated cluster-randomised study: each arm's clusters, each drawn with a size and
    summarised by `summary(stream, size, arm)`, compared by the two-sided pooled t-test of
    the cluster summaries with k_control + k_treatment - 2 degrees of freedom."""
    k_c, k_t = clusters
    critical = t_quantile(1.0 - alpha / 2.0, k_c + k_t - 2)

    def study(stream: Stream) -> bool:
        arms = []
        for arm, (k, mean) in enumerate(zip(clusters, sizes, strict=True)):
            arms.append([summary(stream, stream.cluster_size(mean, cv), arm) for _ in range(k)])
        return abs(pooled_t(arms[0], arms[1])) > critical

    return study


def two_means_trial(
    difference: float,
    sd: float,
    n_control: int,
    n_treatment: int,
    null_value: float,
    alpha: float,
    side: str,
    welch: bool,
    *,
    sd_treatment: float | None = None,
    skewness: float = 0.0,
) -> Callable[[Stream], bool]:
    """One simulated study of two arms: does the t-test reject?

    `side` is "higher" (the null says the difference is at most null_value), "lower" (at
    least) or "both" (equal). `sd` is the control arm's SD, and the treatment arm's unless
    `sd_treatment` is given. With `skewness`, each arm's outcomes are a gamma distribution
    shifted and scaled to the arm's mean and SD, mirrored when the skewness is negative.
    The pooled test uses n_control + n_treatment - 2 degrees of freedom; Welch's uses the
    Welch-Satterthwaite degrees of freedom of each study.
    """
    if side not in SIDES:
        raise ValueError(f"Unknown side {side!r}.")
    sd_t = sd if sd_treatment is None else sd_treatment
    if sd <= 0 or sd_t <= 0:
        raise ValueError("A t-test needs a positive standard deviation.")
    if welch and min(n_control, n_treatment) < 2 or min(n_control, n_treatment) < 1:
        raise ValueError("Welch's test needs two participants per arm; Student's, one.")
    if n_control + n_treatment < 3:
        raise ValueError("A t-test needs at least three participants in all.")
    equal = sd_t == sd
    # Kept as it was for equal SDs, so a seed gives the same numbers as before.
    spread = (
        sd * math.sqrt(1.0 / n_control + 1.0 / n_treatment)
        if equal
        else math.sqrt(sd * sd / n_control + sd_t * sd_t / n_treatment)
    )
    tail = alpha / 2.0 if side == "both" else alpha
    df_pooled = n_control + n_treatment - 2

    def rejects(t: float, df: float) -> bool:
        if side == "higher" and t <= 0 or side == "lower" and t >= 0:
            return False
        return t_tail(t, df) <= tail

    def beyond(t: float, critical: float) -> bool:
        if side == "higher":
            return t > critical
        if side == "lower":
            return t < -critical
        return abs(t) > critical

    if welch:
        # Welch's degrees of freedom lie between the smaller arm's n - 1 and n_control +
        # n_treatment - 2, so most studies are decided by these two quantiles alone.
        sure = t_quantile(1.0 - tail, min(n_control, n_treatment) - 1)
        never = t_quantile(1.0 - tail, df_pooled)

        def welch_decision(shift: float, var_c: float, var_t: float) -> bool:
            t = shift / math.sqrt(var_c + var_t)
            size = abs(t) if side == "both" else (t if side == "higher" else -t)
            if size > sure:
                return True
            if size <= never:
                return False
            df = (var_c + var_t) ** 2 / (var_c**2 / (n_control - 1) + var_t**2 / (n_treatment - 1))
            return rejects(t, df)

    critical = t_quantile(1.0 - tail, df_pooled)
    factor = 1.0 / n_control + 1.0 / n_treatment

    if skewness:
        shape = 4.0 / (skewness * skewness)
        sign = 1.0 if skewness > 0 else -1.0
        root = math.sqrt(shape)

        def arm(stream: Stream, n: int) -> tuple[float, float]:
            """The mean and sum of squares of n gamma draws of the arm's shape."""
            draws = [stream.gamma(shape) for _ in range(n)]
            mean = sum(draws) / n
            return mean, sum((x - mean) ** 2 for x in draws)

        def skewed_study(stream: Stream) -> bool:
            mean_c, ss_c = arm(stream, n_control)
            mean_t, ss_t = arm(stream, n_treatment)
            shift = (
                difference
                - null_value
                + sign * (sd_t * (mean_t - shape) - sd * (mean_c - shape)) / root
            )
            ss_c, ss_t = sd * sd * ss_c / shape, sd_t * sd_t * ss_t / shape
            if welch:
                return welch_decision(
                    shift,
                    ss_c / (n_control - 1) / n_control,
                    ss_t / (n_treatment - 1) / n_treatment,
                )
            pooled = (ss_c + ss_t) / df_pooled * factor
            if pooled <= 0.0:
                return False
            return beyond(shift / math.sqrt(pooled), critical)

        return skewed_study

    def chi(stream: Stream, df: int) -> float:
        return stream.chi_square(df) if df > 0 else 0.0

    if not welch and equal:

        def pooled(stream: Stream) -> bool:
            shift = difference - null_value + spread * stream.normal()
            pooled_sd = sd * math.sqrt(stream.chi_square(df_pooled) / df_pooled)
            return beyond(shift / (pooled_sd * math.sqrt(factor)), critical)

        return pooled

    if not welch:

        def unequal_pooled(stream: Stream) -> bool:
            shift = difference - null_value + spread * stream.normal()
            ss = sd * sd * chi(stream, n_control - 1) + sd_t * sd_t * chi(stream, n_treatment - 1)
            return beyond(shift / math.sqrt(ss / df_pooled * factor), critical)

        return unequal_pooled

    def welch_study(stream: Stream) -> bool:
        shift = difference - null_value + spread * stream.normal()
        var_c = sd * sd * stream.chi_square(n_control - 1) / (n_control - 1) / n_control
        var_t = sd_t * sd_t * stream.chi_square(n_treatment - 1) / (n_treatment - 1) / n_treatment
        return welch_decision(shift, var_c, var_t)

    return welch_study


def log_rank_trial(
    hazard_ratio: float,
    control_median: float,
    accrual: float,
    follow_up: float,
    n_control: int,
    n_treatment: int,
    alpha: float,
    *,
    dropout: float = 0.0,
    dropout_time: float = 1.0,
    delay: float = 0.0,
) -> Callable[[Stream], bool]:
    """One simulated survival trial: does the two-sided log-rank test reject?

    Each participant enters uniformly over the accrual period and is followed to its end
    plus the follow-up. Event times are exponential with the control hazard log 2 / median;
    in the treatment arm the hazard is multiplied by the hazard ratio from `delay` after
    entry on. Dropout is exponential, with probability `dropout` by `dropout_time`. The test
    compares the log-rank score with its variance against the normal quantile; continuous
    times have no ties.
    """
    if min(n_control, n_treatment) < 1:
        raise ValueError("The log-rank test needs a participant in each arm.")
    control = math.log(2.0) / control_median
    loss = -math.log1p(-dropout) / dropout_time if dropout else 0.0
    critical = NormalDist().inv_cdf(1.0 - alpha / 2.0) ** 2
    end = accrual + follow_up
    before = control * delay  # cumulative hazard before the effect starts

    def event_time(stream: Stream, treated: bool) -> float:
        total = -math.log(stream.uniform())  # a unit exponential cumulative hazard
        if not treated:
            return total / control
        if total <= before:
            return total / control
        return delay + (total - before) / (control * hazard_ratio)

    def study(stream: Stream) -> bool:
        times = []
        for arm, n in ((0, n_control), (1, n_treatment)):
            for _ in range(n):
                window = end - accrual * stream.uniform()
                time = event_time(stream, arm == 1)
                if loss:
                    lost = -math.log(stream.uniform()) / loss
                    if lost < time:
                        times.append((min(lost, window), 0, arm))
                        continue
                times.append((time, 1, arm) if time <= window else (window, 0, arm))
        times.sort()
        at_risk = [n_control, n_treatment]
        score = variance = 0.0
        for _, event, arm in times:
            if event:
                share = at_risk[1] / (at_risk[0] + at_risk[1])
                score += arm - share
                variance += share * (1.0 - share)
            at_risk[arm] -= 1
        return variance > 0.0 and score * score / variance > critical

    return study


def standardised(skewness: float) -> Callable[[Stream], float]:
    """Draws with mean 0 and SD 1: normal, or for a skewness g a gamma distribution with
    shape 4 / g^2, shifted and scaled, and mirrored when g is negative."""
    if not skewness:
        return lambda stream: stream.normal()
    shape = 4.0 / (skewness * skewness)
    scale = (1.0 if skewness > 0 else -1.0) / math.sqrt(shape)
    return lambda stream: scale * (stream.gamma(shape) - shape)


def correlation_trial(
    rho: float, n: int, alpha: float, *, skewness: float = 0.0, exposure_skewness: float = 0.0
) -> Callable[[Stream], bool]:
    """One simulated study of two measured variables: does the two-sided t-test of Pearson's
    correlation reject? It is also the t-test of a simple regression's slope.

    The exposure and the outcome's error each have mean 0 and SD 1, normal or skewed, and the
    outcome is rho times the exposure plus the root of 1 - rho^2 times the error, so the
    correlation is rho. The test rejects when |r| passes t_c / sqrt(t_c^2 + n - 2).
    """
    if n < 4:
        raise ValueError("The correlation test needs at least four participants.")
    df = n - 2
    critical = t_quantile(1.0 - alpha / 2.0, df)
    passes = critical / math.sqrt(critical * critical + df)
    exposure, error = standardised(exposure_skewness), standardised(skewness)
    rest = math.sqrt(1.0 - rho * rho)

    def study(stream: Stream) -> bool:
        sx = sy = sxx = syy = sxy = 0.0
        for _ in range(n):
            x = exposure(stream)
            y = rho * x + rest * error(stream)
            sx += x
            sy += y
            sxx += x * x
            syy += y * y
            sxy += x * y
        cxx, cyy, cxy = sxx - sx * sx / n, syy - sy * sy / n, sxy - sx * sy / n
        if cxx <= 0.0 or cyy <= 0.0:
            return False
        return abs(cxy) > passes * math.sqrt(cxx * cyy)

    return study


@dataclass(frozen=True)
class LookEstimate:
    """How often a design with looks stopped at each look, in `runs` simulated studies."""

    stopped: tuple[int, ...]  # rejections at each look
    runs: int

    @property
    def overall(self) -> Estimate:
        rejected = sum(self.stopped)
        return Estimate(rejected, self.runs, *clopper_pearson(rejected, self.runs))


def estimate_looks(trial: Callable[[Stream], int | None], looks: int, runs: int, stream: Stream):
    """Tally the look at which each simulated study rejected; None means it never did."""
    stopped = [0] * looks
    for _ in range(runs):
        look = trial(stream)
        if look is not None:
            stopped[look] += 1
    return LookEstimate(tuple(stopped), runs)


def sequential_two_means_trial(
    difference: float,
    sd: float,
    looks: list[tuple[int, int, float]],
    null_value: float,
    side: str,
    welch: bool,
    *,
    sd_treatment: float | None = None,
    skewness: float = 0.0,
) -> Callable[[Stream], int | None]:
    """One simulated study with interim looks: the look at which the t-test first rejects.

    `looks` lists each look's cumulative arm sizes and the level spent there. Each stage adds
    the participants that reach the next look's sizes. Normal outcomes are drawn as each
    stage's mean and sum of squares, combined exactly with what came before; skewed outcomes
    one participant at a time. Outcomes are as for two_means_trial.
    """
    if side not in SIDES:
        raise ValueError(f"Unknown side {side!r}.")
    sd_t = sd if sd_treatment is None else sd_treatment
    spreads, means = (sd, sd_t), (0.0, difference)
    shape = 4.0 / (skewness * skewness) if skewness else 0.0
    sign = 1.0 if skewness >= 0 else -1.0
    decisions = []
    for n_c, n_t, level in looks:
        tail = level / 2.0 if side == "both" else level
        df = n_c + n_t - 2
        decisions.append((tail, t_quantile(1.0 - tail, df) if not welch else None))

    def stage(stream: Stream, arm: int, m: int) -> tuple[float, float]:
        """The mean and sum of squares of m new participants in one arm."""
        if skewness:
            draws = [stream.gamma(shape) for _ in range(m)]
            mean = sum(draws) / m
            ss = sum((x - mean) ** 2 for x in draws)
            scale = spreads[arm] * sign / math.sqrt(shape)
            return means[arm] + scale * (mean - shape), scale * scale * ss
        mean = means[arm] + spreads[arm] / math.sqrt(m) * stream.normal()
        ss = spreads[arm] ** 2 * stream.chi_square(m - 1) if m > 1 else 0.0
        return mean, ss

    def rejects(t: float, df: float, tail: float, critical: float | None) -> bool:
        if side == "higher" and t <= 0 or side == "lower" and t >= 0:
            return False
        if critical is not None:
            return abs(t) > critical
        return t_tail(t, df) <= tail

    def study(stream: Stream) -> int | None:
        counts, centres, squares = [0, 0], [0.0, 0.0], [0.0, 0.0]
        for index, (n_c, n_t, _) in enumerate(looks):
            for arm, target in enumerate((n_c, n_t)):
                m = target - counts[arm]
                if m <= 0:
                    continue
                mean, ss = stage(stream, arm, m)
                n = counts[arm]
                total = n + m
                squares[arm] += ss + n * m / total * (centres[arm] - mean) ** 2
                centres[arm] = (n * centres[arm] + m * mean) / total
                counts[arm] = total
            shift = centres[1] - centres[0] - null_value
            tail, critical = decisions[index]
            if welch:
                var_c = squares[0] / (n_c - 1) / n_c
                var_t = squares[1] / (n_t - 1) / n_t
                if var_c + var_t <= 0.0:
                    continue
                t = shift / math.sqrt(var_c + var_t)
                df = (var_c + var_t) ** 2 / (var_c**2 / (n_c - 1) + var_t**2 / (n_t - 1))
            else:
                df = n_c + n_t - 2
                pooled = (squares[0] + squares[1]) / df * (1.0 / n_c + 1.0 / n_t)
                if pooled <= 0.0:
                    continue
                t = shift / math.sqrt(pooled)
            if rejects(t, df, tail, critical):
                return index
        return None

    return study


KIESER_FRIEDE = (
    "Kieser, M. and Friede, T. (2003). Simple procedures for blinded sample size adjustment "
    "that do not affect the type I error rate. Statistics in Medicine 22(23), 3571-3581."
)


def reestimated_size(variance: float, difference: float, power: float, tail: float) -> int:
    """Participants per arm for a normal approximation at this variance: the ceiling of
    2 variance (z_(1 - tail) + z_power)^2 / difference^2."""
    normal = NormalDist()
    z = normal.inv_cdf(1.0 - tail) + normal.inv_cdf(power)
    return math.ceil(2.0 * variance * z * z / (difference * difference))


def blinded_reestimation_trial(
    difference: float,
    sd: float,
    initial: int,
    interim: int,
    largest: int,
    planned_difference: float,
    power: float,
    null_value: float,
    alpha: float,
    side: str,
) -> Callable[[Stream], tuple[bool, int]]:
    """One simulated trial with blinded sample-size re-estimation: does Student's t-test
    reject, and how many participants per arm did the trial end with?

    After `interim` participants per arm, the variance is estimated from all of them with
    the arms pooled (the one-sample variance, which needs no unblinding), and the size per
    arm is recomputed for `planned_difference` and `power`. The trial never ends below the
    `initial` size per arm nor above `largest`. Normal outcomes are drawn as each stage's
    summaries; the final test uses every participant at level alpha.
    """
    if side not in SIDES:
        raise ValueError(f"Unknown side {side!r}.")
    tail = alpha / 2.0 if side == "both" else alpha
    means = (0.0, difference)
    normal = NormalDist()
    z = normal.inv_cdf(1.0 - tail) + normal.inv_cdf(power)
    factor = 2.0 * z * z / (planned_difference * planned_difference)
    criticals: dict[int, float] = {}  # by the final size per arm

    def stage(stream: Stream, arm: int, m: int) -> tuple[float, float]:
        mean = means[arm] + sd / math.sqrt(m) * stream.normal()
        return mean, sd * sd * stream.chi_square(m - 1) if m > 1 else 0.0

    def study(stream: Stream) -> tuple[bool, int]:
        first = [stage(stream, arm, interim) for arm in (0, 1)]
        (mean_c, ss_c), (mean_t, ss_t) = first
        lumped = (ss_c + ss_t + interim * (mean_c - mean_t) ** 2 / 2.0) / (2 * interim - 1)
        n = min(max(math.ceil(factor * lumped), initial), largest)
        totals = []
        for arm, (mean, ss) in enumerate(first):
            m = n - interim
            if m > 0:
                later, later_ss = stage(stream, arm, m)
                ss += later_ss + interim * m / n * (mean - later) ** 2
                mean = (interim * mean + m * later) / n
            totals.append((mean, ss))
        (mean_c, ss_c), (mean_t, ss_t) = totals
        df = 2 * n - 2
        pooled = (ss_c + ss_t) / df * (2.0 / n)
        t = (mean_t - mean_c - null_value) / math.sqrt(pooled)
        critical = criticals.get(n)
        if critical is None:
            critical = criticals[n] = t_quantile(1.0 - tail, df)
        if side == "higher":
            return t > critical, n
        if side == "lower":
            return t < -critical, n
        return abs(t) > critical, n

    return study


@dataclass(frozen=True)
class SizedEstimate:
    """Rejections in `runs` simulated trials of varying size, and their mean size per arm."""

    found: Estimate
    mean_per_arm: Fraction


def estimate_sized(trial: Callable[[Stream], tuple[bool, int]], runs: int, stream: Stream):
    rejected, sizes = 0, 0
    for _ in range(runs):
        rejects, n = trial(stream)
        rejected += rejects
        sizes += n
    return SizedEstimate(
        Estimate(rejected, runs, *clopper_pearson(rejected, runs)), Fraction(sizes, runs)
    )


@lru_cache(maxsize=4096)
def _fisher_tails(n_control: int, n_treatment: int, total: int, alternative: str) -> tuple:
    """For one pooled total: each table's exact tail weight, by control successes, over
    the number of tables C(n_control + n_treatment, total)."""
    lower, upper = max(0, total - n_treatment), min(n_control, total)
    weights = [
        math.comb(n_control, k) * math.comb(n_treatment, total - k) for k in range(lower, upper + 1)
    ]
    if alternative == "greater":
        # Fewer control successes favour treatment: the tail at k is every table with at most k.
        tails, running = [], 0
        for weight in weights:
            running += weight
            tails.append(running)
    else:
        # Two-sided: every table no more likely than this one, ties included exactly.
        tails = [sum(w for w in weights if w <= weight) for weight in weights]
    return lower, tuple(tails), math.comb(n_control + n_treatment, total)


def fisher_p_value(
    n_control: int, n_treatment: int, control: int, treatment: int, alternative: str
) -> Fraction:
    """The exact p-value of Fisher's test for one table, as fisher_exact computes it."""
    lower, tails, tables = _fisher_tails(n_control, n_treatment, control + treatment, alternative)
    return Fraction(tails[control - lower], tables)


def graphical_rejections(p_values: list, alpha: Fraction, weights, transitions) -> list[bool]:
    """Bretz et al.'s algorithm: reject a hypothesis whose p-value is at most its weight times
    alpha, pass its weight on along the graph, and repeat. Exact in Fractions."""
    k = len(p_values)
    weights = [Fraction(w) for w in weights]
    graph = [[Fraction(g) for g in row] for row in transitions]
    active, rejected = set(range(k)), [False] * k
    while True:
        chosen = next((j for j in sorted(active) if p_values[j] <= weights[j] * alpha), None)
        if chosen is None:
            return rejected
        rejected[chosen] = True
        active.discard(chosen)
        new_weights = list(weights)
        for low in active:
            new_weights[low] = weights[low] + weights[chosen] * graph[chosen][low]
        new_graph = [row[:] for row in graph]
        for low in active:
            for high in active:
                if low == high:
                    new_graph[low][high] = Fraction(0)
                    continue
                denominator = 1 - graph[low][chosen] * graph[chosen][low]
                new_graph[low][high] = (
                    (graph[low][high] + graph[low][chosen] * graph[chosen][high]) / denominator
                    if denominator > 0
                    else Fraction(0)
                )
        new_weights[chosen] = Fraction(0)
        weights, graph = new_weights, new_graph


def family_trial(
    endpoints: list[dict], correlation: float, procedure: str, alpha: Fraction, graph=None
) -> Callable[[Stream], tuple[bool, ...]]:
    """One simulated trial with several endpoints: which of them does the procedure reject?

    Each endpoint is a dict with `test` ("fisher" or "student"/"welch"), `sizes`
    (n_control, n_treatment), `side`, `level` (its own alpha) and its point: `rates` for a
    yes-or-no outcome, or `difference`, `sd` and `null_value` for a measured one. With a
    correlation above 0 the endpoints are measured on the same participants: each has a
    latent normal with that exchangeable correlation; a yes-or-no outcome is a success when
    its latent is above the normal quantile at 1 - rate, and a measured outcome rises with its
    latent, so a positive correlation moves both the same way. With 0 the endpoints are drawn
    independently, as summaries.
    The procedure is "bonferroni" (each at its level), "fixed_sequence" (in order at alpha,
    stopping at the first failure) or "graphical" (graph is (weights, transitions)).
    """
    normal = NormalDist()
    shared = correlation > 0.0
    common, own = math.sqrt(correlation), math.sqrt(1.0 - correlation)
    plans = []
    for endpoint in endpoints:
        if endpoint["test"] == "fisher":
            p_c, p_t = endpoint["rates"]
            cuts = tuple(
                normal.inv_cdf(1.0 - p) if 0 < p < 1 else (-math.inf if p >= 1 else math.inf)
                for p in (p_c, p_t)
            )
            plans.append(("binary", cuts))
        else:
            plans.append(("measured", (0.0, endpoint["difference"])))

    def draw(stream: Stream) -> list:
        """Each endpoint's data: success counts, or each arm's (n, mean, sum of squares)."""
        if not shared:
            data = []
            for endpoint, (kind, values) in zip(endpoints, plans, strict=True):
                n_c, n_t = endpoint["sizes"]
                if kind == "binary":
                    p_c, p_t = endpoint["rates"]
                    data.append((stream.binomial(n_c, p_c), stream.binomial(n_t, p_t)))
                else:
                    arms = []
                    for n, mean in zip((n_c, n_t), values, strict=True):
                        centre = mean + endpoint["sd"] / math.sqrt(n) * stream.normal()
                        ss = endpoint["sd"] ** 2 * stream.chi_square(n - 1) if n > 1 else 0.0
                        arms.append((n, centre, ss))
                    data.append(tuple(arms))
            return data
        n_c, n_t = endpoints[0]["sizes"]
        sums = [[[0, 0.0, 0.0], [0, 0.0, 0.0]] for _ in endpoints]
        for arm, n in ((0, n_c), (1, n_t)):
            for _ in range(n):
                factor = common * stream.normal()
                for index, (endpoint, (kind, values)) in enumerate(
                    zip(endpoints, plans, strict=True)
                ):
                    z = factor + own * stream.normal()
                    cell = sums[index][arm]
                    if kind == "binary":
                        cell[0] += z > values[arm]
                    else:
                        y = values[arm] + endpoint["sd"] * z
                        cell[1] += y
                        cell[2] += y * y
        data = []
        for (kind, _), cells in zip(plans, sums, strict=True):
            if kind == "binary":
                data.append((cells[0][0], cells[1][0]))
            else:
                arms = []
                for n, cell in zip((n_c, n_t), cells, strict=True):
                    mean = cell[1] / n
                    arms.append((n, mean, max(cell[2] - n * mean * mean, 0.0)))
                data.append(tuple(arms))
        return data

    def p_value(endpoint: dict, data) -> Fraction | float:
        if endpoint["test"] == "fisher":
            n_c, n_t = endpoint["sizes"]
            alternative = "greater" if endpoint["side"] == "higher" else "two_sided"
            return fisher_p_value(n_c, n_t, data[0], data[1], alternative)
        (n_c, mean_c, ss_c), (n_t, mean_t, ss_t) = data
        shift = mean_t - mean_c - endpoint["null_value"]
        if endpoint["test"] == "welch":
            var_c, var_t = ss_c / (n_c - 1) / n_c, ss_t / (n_t - 1) / n_t
            if var_c + var_t <= 0.0:
                return 1.0
            t = shift / math.sqrt(var_c + var_t)
            df = (var_c + var_t) ** 2 / (var_c**2 / (n_c - 1) + var_t**2 / (n_t - 1))
        else:
            df = n_c + n_t - 2
            pooled = (ss_c + ss_t) / df * (1.0 / n_c + 1.0 / n_t)
            if pooled <= 0.0:
                return 1.0
            t = shift / math.sqrt(pooled)
        side = endpoint["side"]
        if side == "both":
            return min(1.0, 2.0 * t_tail(t, df))
        tail = t_tail(t, df)
        towards = t > 0 if side == "higher" else t < 0
        return tail if towards else 1.0 - tail

    def study(stream: Stream) -> tuple[bool, ...]:
        p_values = [p_value(e, d) for e, d in zip(endpoints, draw(stream), strict=True)]
        if procedure == "bonferroni":
            return tuple(p <= e["level"] for p, e in zip(p_values, endpoints, strict=True))
        if procedure == "fixed_sequence":
            rejected = []
            for p in p_values:
                if rejected and not rejected[-1] or p > alpha:
                    rejected.append(False)
                    continue
                rejected.append(True)
            # Once one fails, every later hypothesis is retained.
            for index in range(1, len(rejected)):
                rejected[index] = rejected[index] and rejected[index - 1]
            return tuple(rejected)
        return tuple(graphical_rejections(p_values, alpha, *graph))

    return study


@dataclass(frozen=True)
class FamilyEstimate:
    """How often each endpoint, any endpoint and every endpoint was rejected."""

    each: tuple[int, ...]
    any: int
    all: int
    runs: int

    def interval(self, count: int) -> tuple[float, float]:
        return clopper_pearson(count, self.runs)


def estimate_family(trial, endpoints: int, runs: int, stream: Stream) -> FamilyEstimate:
    each, any_count, all_count = [0] * endpoints, 0, 0
    for _ in range(runs):
        rejected = trial(stream)
        for index, flag in enumerate(rejected):
            each[index] += flag
        any_count += any(rejected)
        all_count += all(rejected)
    return FamilyEstimate(tuple(each), any_count, all_count, runs)
