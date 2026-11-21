# Power of the t-test of a correlation and of a regression slope against R. Run from the
# repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/regression_power_r.R
# Needs pwr and jsonlite. It regenerates tests/fixtures/regression_power_r.json, which
# tests/test_regression_power.py compares with StatClaim offline, and writes
# regression_power_r.txt beside this file with the values and the R session.
#
# Given the exposure, the t statistic of the slope is noncentral t with n - k - 2 degrees of
# freedom and noncentrality effect * sqrt(W), where W, the exposure's residual sum of
# squares in its own standard deviations, is chi-square with n - k - 1 degrees of freedom
# when the exposure is normal given the k covariates. For a correlation rho, k = 0 and the
# effect is rho / sqrt(1 - rho^2); for a slope it is slope * sd(x) sqrt(1 - exposure_r2) /
# residual_sd. Power is two-sided, ignoring the far tail, as power.t.test does.
#   integrate   that mixture, by numerical integration over W where it is not negligible
#   simulation  raw data: normal exposure and covariates, the t-test of the slope from lm's
#               formulas, 40,000 studies per case with a fixed seed
#   pwr         pwr.r.test (Fisher's z) and pwr.f2.test (exposure fixed), for context
# Spearman's rank correlation, by Fisher's z with Bonett and Wright's variance:
#   formula     pnorm((|atanh r| - z / sqrt(n - 3)) / sqrt((1 + r^2 / 2) / (n - 3)))
#   simulation  bivariate normal data with Pearson's correlation 2 sin(pi r / 6), whose
#               Spearman correlation is r, and cor.test's exact test, 4,000 studies
# Linear regression on a yes-or-no exposure, the t-test of two means:
#   pt          noncentral t with the groups fixed, and averaged over the binomial number
#               exposed when only the total is fixed
#   pwr         pwr.t2n.test, which adds the far tail
#   formula     a survey's Wald test at n / deff
suppressMessages({
  library(pwr)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))

mixture <- function(effect, n, k, alpha) {
  df <- n - k - 2
  chi <- n - k - 1
  critical <- qt(1 - alpha / 2, df)
  integrand <- function(w) pt(critical, df, ncp = effect * sqrt(w), lower.tail = FALSE) *
    dchisq(w, chi)
  # Where all but 2e-16 of W lies; integrate misses the peak over [0, Inf) for large n.
  integrate(integrand, qchisq(1e-16, chi), qchisq(1e-16, chi, lower.tail = FALSE),
            rel.tol = 1e-12, abs.tol = 1e-14, subdivisions = 5000)$value
}

# Raw-data simulation: the slope's two-sided t-test with k independent normal covariates
# and an exposure that shares exposure_r2 of its variance with the first of them.
simulate <- function(slope, sd_x, sd_e, r2, k, n, alpha, runs = 40000) {
  set.seed(2026)
  critical <- qt(1 - alpha / 2, n - k - 2)
  hits <- 0
  for (run in seq_len(runs)) {
    z <- if (k > 0) matrix(rnorm(n * k), n, k) else matrix(0, n, 0)
    shared <- if (k > 0) z[, 1] * sqrt(r2) else 0
    x <- sd_x * (shared + sqrt(1 - r2) * rnorm(n))
    y <- slope * x + sd_e * rnorm(n)
    design <- cbind(1, x, z)
    fit <- lm.fit(design, y)
    sigma2 <- sum(fit$residuals^2) / (n - k - 2)
    se <- sqrt(sigma2 * chol2inv(qr.R(fit$qr))[2, 2])
    t <- fit$coefficients[2] / se
    hits <- hits + (abs(t) > critical)
  }
  hits / runs
}

correlations <- list(
  list(rho = "3/10", n = 30, alpha = "1/20"),
  list(rho = "3/10", n = 85, alpha = "1/20"),
  list(rho = "1/5", n = 193, alpha = "1/20"),
  list(rho = "-1/4", n = 100, alpha = "1/100"),
  list(rho = "1/2", n = 10, alpha = "1/20"),
  list(rho = "1/10", n = 782, alpha = "1/20")
)
correlation_rows <- lapply(correlations, function(case) {
  rho <- value(case$rho)
  alpha <- value(case$alpha)
  row <- c(case, list(
    integrate = mixture(abs(rho) / sqrt(1 - rho^2), case$n, 0, alpha),
    pwr = pwr.r.test(n = case$n, r = rho, sig.level = alpha)$power
  ))
  if (case$n <= 100) row$simulation <- simulate(rho, 1, sqrt(1 - rho^2), 0, 0, case$n, alpha)
  row
})

slopes <- list(
  list(slope = "1/2", exposure_sd = "4", residual_sd = "15", exposure_r2 = "1/10", k = 2,
       n = 250, alpha = "1/20"),
  list(slope = "1/2", exposure_sd = "4", residual_sd = "15", exposure_r2 = "0", k = 0,
       n = 100, alpha = "1/20"),
  list(slope = "2", exposure_sd = "1", residual_sd = "10", exposure_r2 = "3/10", k = 5,
       n = 300, alpha = "1/100"),
  list(slope = "-3/10", exposure_sd = "2", residual_sd = "3", exposure_r2 = "0", k = 1,
       n = 40, alpha = "1/20")
)
slope_rows <- lapply(slopes, function(case) {
  beta <- value(case$slope)
  sd_x <- value(case$exposure_sd)
  sd_e <- value(case$residual_sd)
  r2 <- value(case$exposure_r2)
  alpha <- value(case$alpha)
  effect <- abs(beta) * sd_x * sqrt(1 - r2) / sd_e
  c(case, list(
    integrate = mixture(effect, case$n, case$k, alpha),
    simulation = simulate(beta, sd_x, sd_e, r2, case$k, case$n, alpha),
    pwr_f2 = pwr.f2.test(u = 1, v = case$n - case$k - 2, f2 = effect^2,
                         sig.level = alpha)$power
  ))
})

# The fewest participants with power at least the target, by bisection on the mixture.
search_cases <- list(
  list(kind = "correlation", rho = "1/5", alpha = "1/20", power = "4/5", k = 0),
  list(kind = "slope", slope = "1/2", exposure_sd = "4", residual_sd = "15",
       exposure_r2 = "1/10", k = 2, alpha = "1/20", power = "9/10")
)
search_rows <- lapply(search_cases, function(case) {
  effect <- if (case$kind == "correlation") {
    abs(value(case$rho)) / sqrt(1 - value(case$rho)^2)
  } else {
    abs(value(case$slope)) * value(case$exposure_sd) * sqrt(1 - value(case$exposure_r2)) /
      value(case$residual_sd)
  }
  power_at <- function(n) mixture(effect, n, case$k, value(case$alpha))
  low <- case$k + 2
  high <- 10000
  while (high - low > 1) {
    middle <- (low + high) %/% 2
    if (power_at(middle) >= value(case$power)) high <- middle else low <- middle
  }
  row <- c(case, list(n = high, power_at = power_at(high)))
  if (case$kind == "correlation") {
    row$pwr_n <- pwr.r.test(r = value(case$rho), sig.level = value(case$alpha),
                            power = value(case$power))$n
  }
  row
})

spearman <- function(r, n, alpha) {
  pnorm((abs(atanh(r)) - qnorm(1 - alpha / 2) / sqrt(n - 3)) / sqrt((1 + r^2 / 2) / (n - 3)))
}
simulate_spearman <- function(r, n, runs = 4000) {
  set.seed(2026)
  rho <- 2 * sin(pi * r / 6)
  hits <- 0
  for (run in seq_len(runs)) {
    x <- rnorm(n)
    y <- rho * x + sqrt(1 - rho^2) * rnorm(n)
    hits <- hits + (cor.test(x, y, method = "spearman", exact = TRUE)$p.value <= 0.05)
  }
  hits / runs
}
spearman_cases <- list(list(rho = "3/10", n = 87), list(rho = "1/2", n = 30),
                       list(rho = "-1/5", n = 200))
spearman_rows <- lapply(spearman_cases, function(case) {
  r <- value(case$rho)
  c(case, list(formula = spearman(r, case$n, 0.05), simulation = simulate_spearman(r, case$n)))
})

means_power <- function(difference, sd, n0, n1, k, alpha) {
  df <- n0 + n1 - k - 2
  pt(qt(1 - alpha / 2, df), df, ncp = abs(difference) / (sd * sqrt(1 / n0 + 1 / n1)),
     lower.tail = FALSE)
}
means_cases <- list(
  list(difference = "5", sd = "15", unexposed = 200, exposed = 100, k = 0, alpha = "1/20"),
  list(difference = "-2", sd = "6", unexposed = 300, exposed = 300, k = 3, alpha = "1/100"),
  list(difference = "5", sd = "15", n = 300, share = "1/3", k = 0, alpha = "1/20"),
  list(difference = "1", sd = "4", n = 500, share = "1/10", k = 2, alpha = "1/20")
)
means_rows <- lapply(means_cases, function(case) {
  difference <- value(case$difference)
  sd <- value(case$sd)
  alpha <- value(case$alpha)
  if (!is.null(case$exposed)) {
    power <- means_power(difference, sd, case$unexposed, case$exposed, case$k, alpha)
    two_tails <- if (case$k == 0) {
      pwr.t2n.test(n1 = case$exposed, n2 = case$unexposed, d = difference / sd,
                   sig.level = alpha)$power
    } else NULL
    return(c(case, list(power = power, pwr = two_tails)))
  }
  q <- value(case$share)
  k <- 1:(case$n - 1)
  power <- sum(dbinom(k, case$n, q) *
                 vapply(k, function(e) means_power(difference, sd, case$n - e, e, case$k, alpha),
                        numeric(1)))
  c(case, list(power = power))
})
survey_means <- list(list(difference = "5", sd = "15", n = 600, share = "1/3", deff = "2"))
survey_rows <- lapply(survey_means, function(case) {
  q <- value(case$share)
  se <- value(case$sd) / sqrt(case$n / value(case$deff) * q * (1 - q))
  c(case, list(power = pnorm(abs(value(case$difference)) / se - qnorm(0.975))))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(pwr = as.character(packageVersion("pwr"))),
  spearman = spearman_rows,
  means = means_rows,
  survey_means = survey_rows,
  correlations = correlation_rows,
  slopes = slope_rows,
  searches = search_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/regression_power_r.json")

sink("replication/comparison/regression_power_r.txt")
cat("Power of the t-tests of a correlation and a slope, written to",
    "tests/fixtures/regression_power_r.json\n\n")
cat("Correlations\n")
for (row in correlation_rows) {
  cat(sprintf("rho %s, n %d, alpha %s: integrate %.12f, pwr %.6f", row$rho, row$n, row$alpha,
              row$integrate, row$pwr),
      if (is.null(row$simulation)) "\n" else sprintf(", simulation %.4f\n", row$simulation),
      sep = "")
}
cat("\nSlopes\n")
for (row in slope_rows) {
  cat(sprintf("slope %s, sd(x) %s, residual sd %s, r2 %s, %d covariates, n %d, alpha %s:",
              row$slope, row$exposure_sd, row$residual_sd, row$exposure_r2, row$k, row$n,
              row$alpha),
      sprintf(" integrate %.12f, simulation %.4f, pwr.f2.test %.6f\n", row$integrate,
              row$simulation, row$pwr_f2), sep = "")
}
cat("\nSpearman's rank correlation\n")
for (row in spearman_rows) {
  cat(sprintf("rho_s %s, n %d: formula %.12f, simulation %.4f\n", row$rho, row$n, row$formula,
              row$simulation))
}
cat("\nTwo means, by a yes-or-no exposure\n")
for (row in means_rows) {
  groups <- if (is.null(row$exposed)) sprintf("n %d, share exposed %s", row$n, row$share) else
    sprintf("groups (%d, %d)", row$unexposed, row$exposed)
  cat(sprintf("difference %s, sd %s, %s, %d covariates, alpha %s: power %.12f", row$difference,
              row$sd, groups, row$k, row$alpha, row$power),
      if (is.null(row$pwr)) "\n" else sprintf(", pwr.t2n.test %.12f\n", row$pwr), sep = "")
}
for (row in survey_rows) {
  cat(sprintf("survey: difference %s, sd %s, n %d, share %s, deff %s: power %.12f\n",
              row$difference, row$sd, row$n, row$share, row$deff, row$power))
}
cat("\nSearches\n")
for (row in search_rows) {
  cat(sprintf("%s, power %s: n = %d (power %.6f)", row$kind, row$power, row$n, row$power_at),
      if (is.null(row$pwr_n)) "\n" else sprintf("; pwr.r.test n = %.3f\n", row$pwr_n), sep = "")
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/regression_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
