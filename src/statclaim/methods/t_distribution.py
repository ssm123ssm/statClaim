"""Student's t distribution, central and noncentral, in plain floating point.

Used for the power of t-tests on cluster summaries, where the number of clusters is small
and a normal approximation overstates power. The noncentral distribution is the Poisson
mixture of Lenth (1989), summed outward from the Poisson mode as Benton and Krishnamoorthy
(2003) recommend, so large noncentralities do not underflow. Results agree with R's pt and
qt to about twelve decimals.
"""

import math
from statistics import NormalDist

# Bump whenever this file changes: every power that uses it may change.
VERSION = 2  # 2: random_design_power for slopes and correlations

_NORMAL = NormalDist()
_TINY = 1e-300
_EPSILON = 1e-15

LENTH = (
    "Lenth, R. V. (1989). Algorithm AS 243: cumulative distribution function of the "
    "non-central t distribution. Applied Statistics 38(1), 185-189."
)
BENTON_KRISHNAMOORTHY = (
    "Benton, D. and Krishnamoorthy, K. (2003). Computing discrete mixtures of continuous "
    "distributions: noncentral chisquare, noncentral t and the distribution of the square of "
    "the sample multiple correlation coefficient. Computational Statistics and Data Analysis "
    "43(2), 249-267."
)


def _log_beta(a: float, b: float) -> float:
    return math.lgamma(a) + math.lgamma(b) - math.lgamma(a + b)


def _beta_fraction(x: float, a: float, b: float) -> float:
    """The continued fraction for the incomplete beta function, by Lentz's method."""
    c, d = 1.0, 1 - (a + b) * x / (a + 1)
    d = 1 / (d if abs(d) > _TINY else _TINY)
    h = d
    for m in range(1, 10_000):
        for numerator in (
            m * (b - m) * x / ((a + 2 * m - 1) * (a + 2 * m)),
            -(a + m) * (a + b + m) * x / ((a + 2 * m) * (a + 2 * m + 1)),
        ):
            d = 1 + numerator * d
            d = 1 / (d if abs(d) > _TINY else _TINY)
            c = 1 + numerator / c
            c = c if abs(c) > _TINY else _TINY
            h *= d * c
        if abs(d * c - 1) < _EPSILON:
            return h
    raise ArithmeticError("The incomplete beta function did not converge.")


def regularized_beta(x: float, a: float, b: float) -> float:
    """I_x(a, b), the regularized incomplete beta function."""
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    front = math.exp(a * math.log(x) + b * math.log1p(-x) - _log_beta(a, b))
    if x < (a + 1) / (a + b + 2):
        return front * _beta_fraction(x, a, b) / a
    return 1 - front * _beta_fraction(1 - x, b, a) / b


def t_cdf(t: float, df: float) -> float:
    """P(T <= t) for Student's t with df degrees of freedom."""
    tail = 0.5 * regularized_beta(df / (df + t * t), df / 2, 0.5)
    return 1 - tail if t > 0 else tail


def _t_density(t: float, df: float) -> float:
    return math.exp(
        math.lgamma((df + 1) / 2)
        - math.lgamma(df / 2)
        - 0.5 * math.log(df * math.pi)
        - (df + 1) / 2 * math.log1p(t * t / df)
    )


def t_quantile(p: float, df: float) -> float:
    """The t with P(T <= t) = p, by Newton's method kept inside a shrinking bracket."""
    if not 0 < p < 1:
        raise ValueError("p must lie strictly between 0 and 1.")
    if p < 0.5:
        return -t_quantile(1 - p, df)
    if p == 0.5:
        return 0.0
    low, high = 0.0, 1.0
    while t_cdf(high, df) < p:
        low, high = high, 2 * high
    guess = _NORMAL.inv_cdf(p)
    t = guess if low < guess < high else (low + high) / 2
    for _ in range(200):
        gap = t_cdf(t, df) - p
        if abs(gap) <= _EPSILON * p:
            return t
        if gap > 0:
            high = t
        else:
            low = t
        step = t - gap / _t_density(t, df)
        if abs(step - t) <= 4 * _EPSILON * t:
            return step
        t = step if low < step < high else (low + high) / 2
    return t


def noncentral_t_cdf(t: float, df: float, noncentrality: float) -> float:
    """P(T <= t) for the noncentral t with df degrees of freedom and the given noncentrality.

    For t >= 0, P(T <= t) = Phi(-delta) + 1/2 sum_j [P_j I_x(j + 1/2, df/2) +
    Q_j I_x(j + 1, df/2)] with x = t^2 / (t^2 + df), P_j the Poisson(delta^2 / 2) weights and
    Q_j = delta e^(-delta^2/2) (delta^2/2)^j / (sqrt 2 Gamma(j + 3/2)). Negative t uses
    P(T <= t; delta) = 1 - P(T <= -t; -delta).
    """
    if t < 0:
        return 1 - noncentral_t_cdf(-t, df, -noncentrality)
    delta = noncentrality
    base = _NORMAL.cdf(-delta)
    if t == 0:
        return base
    x = t * t / (t * t + df)
    half_df = df / 2
    lam = delta * delta / 2
    mode = int(lam)
    # The Poisson weights at the mode, in logarithms so that large delta does not underflow.
    log_lam = math.log(lam) if lam > 0 else 0.0
    p_mode = math.exp(-lam + mode * log_lam - math.lgamma(mode + 1)) if lam > 0 else 1.0
    q_mode = (
        delta / math.sqrt(2) * math.exp(-lam + mode * log_lam - math.lgamma(mode + 1.5))
        if lam > 0
        else delta / math.sqrt(2) / math.gamma(1.5)
    )
    # I_x(a, b) falls by g(a) = x^a (1 - x)^b / (a B(a, b)) as a rises by one.
    a1, a2 = mode + 0.5, mode + 1.0
    i1, i2 = regularized_beta(x, a1, half_df), regularized_beta(x, a2, half_df)
    log_x, log_1x = math.log(x), math.log1p(-x)

    def gap(a: float) -> float:
        return math.exp(a * log_x + half_df * log_1x - math.log(a) - _log_beta(a, half_df))

    g1, g2 = gap(a1), gap(a2)
    total = p_mode * i1 + q_mode * i2
    # Upward from the mode.
    p, q, b1, b2, h1, h2 = p_mode, q_mode, i1, i2, g1, g2
    for j in range(mode + 1, mode + 100_000):
        b1, b2 = b1 - h1, b2 - h2
        h1 *= x * (j - 0.5 + half_df) / (j + 0.5)
        h2 *= x * (j + half_df) / (j + 1)
        p *= lam / j
        q *= lam / (j + 0.5)
        term = p * b1 + q * b2
        total += term
        if j > lam and p < 1e-17 and abs(term) < 1e-18:
            break
    # Downward from the mode.
    p, q, b1, b2, h1, h2 = p_mode, q_mode, i1, i2, g1, g2
    for j in range(mode - 1, -1, -1):
        h1 *= (j + 1.5) / (x * (j + 0.5 + half_df))
        h2 *= (j + 2) / (x * (j + 1 + half_df))
        b1, b2 = b1 + h1, b2 + h2
        p *= (j + 1) / lam
        q *= (j + 1.5) / lam
        term = p * b1 + q * b2
        total += term
        if p < 1e-17 and abs(term) < 1e-18:
            break
    return min(1.0, max(0.0, base + total / 2))


def noncentral_t_sf(t: float, df: float, noncentrality: float) -> float:
    """P(T > t) for the noncentral t."""
    return 1 - noncentral_t_cdf(t, df, noncentrality)


# Gauss-Legendre nodes and weights on [-1, 1], by Newton's method on the Legendre polynomial.
def _legendre(points: int) -> tuple[tuple[float, float], ...]:
    pairs = []
    for i in range(1, points + 1):
        x = math.cos(math.pi * (i - 0.25) / (points + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, x
            for k in range(2, points + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            derivative = points * (x * p1 - p0) / (x * x - 1)
            step = p1 / derivative
            x -= step
            if abs(step) < 1e-15:
                break
        pairs.append((x, 2 / ((1 - x * x) * derivative * derivative)))
    return tuple(pairs)


_NODES = _legendre(16)


def random_design_power(critical: float, df: float, effect: float, chi_df: float) -> float:
    """P(T > critical) when, given W, T is noncentral t with df degrees of freedom and
    noncentrality effect * sqrt(W), and W is chi-square with chi_df degrees of freedom.

    This is the exact power of the t-test of a slope, or of a correlation, when the exposure
    is random and normal: given the exposure, the statistic is noncentral t, and the
    exposure's sum of squares is chi-square. With W = s^2, W's density becomes
    2 s^(chi_df - 1) e^(-s^2 / 2) / (2^(chi_df / 2) Gamma(chi_df / 2)), smooth in s, which
    is integrated by Gauss-Legendre over panels of width 1/2 where it is not negligible.
    """
    centre = math.sqrt(max(chi_df - 0.5, 0.0))
    low, high = max(0.0, centre - 9), centre + 9
    log_scale = math.log(2) - (chi_df / 2) * math.log(2) - math.lgamma(chi_df / 2)
    panels = int(math.ceil((high - low) / 0.5))
    width = (high - low) / panels
    total = 0.0
    for panel in range(panels):
        middle = low + (panel + 0.5) * width
        for node, weight in _NODES:
            s = middle + node * width / 2
            if s <= 0:
                continue
            density = math.exp(log_scale + (chi_df - 1) * math.log(s) - s * s / 2)
            total += weight * width / 2 * density * noncentral_t_sf(critical, df, effect * s)
    return min(1.0, max(0.0, total))
