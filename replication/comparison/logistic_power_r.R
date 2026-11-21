# Power of the cited regression tests of observational studies against R: logistic
# regression (Hsieh), Poisson regression of rates (Signorini) and conditional logistic
# regression of matched pairs (Connor). Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/logistic_power_r.R
# Needs pwrss, MESS, sandwich and jsonlite. It regenerates tests/fixtures/logistic_power_r.json, which
# tests/test_logistic_power.py compares with StatClaim offline, and writes
# logistic_power_r.txt beside this file with the values and the R session.
#
#   pwrss       power.z.logistic(method = "hsieh"): participants needed, not rounded, for a
#               binary exposure (a share exposed) or a normal one (an odds ratio per SD);
#               power.z.poisreg(method = "signorini") for a binary exposure, both tails
#   formula     Signorini's power without the far tail, as StatClaim reports it
#   MESS        power_mcnemar_test(method = "normal"), Connor's formula
#   simulation  raw data and glm's Wald test, 4,000 studies per case with a fixed seed, to
#               show how close the formulas are to the test itself
# Modified Poisson regression, the Wald test of the log risk ratio:
#   formula     with variance (1 - p1) / n1 p1 + (1 - p0) / n0 p0, and under the null the
#               pooled probability's
#   simulation  glm(family = poisson) with sandwich's robust variance (HC0), 4,000 studies
suppressMessages({
  library(pwrss)
  library(MESS)
  library(sandwich)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))

binary <- list(
  list(p_reference = "1/10", p_other = "1/5", share_other = "3/10", power = "4/5", r2 = "0"),
  list(p_reference = "1/5", p_other = "1/3", share_other = "1/2", power = "9/10", r2 = "0"),
  list(p_reference = "1/20", p_other = "1/10", share_other = "1/3", power = "4/5", r2 = "1/5")
)
binary_rows <- lapply(binary, function(case) {
  n <- power.z.logistic(base.prob = value(case$p_reference), prob = value(case$p_other),
                        power = value(case$power), r.squared.predictor = value(case$r2),
                        distribution = list(dist = "binomial", size = 1,
                                            prob = value(case$share_other)),
                        method = "hsieh", ceil.n = FALSE, verbose = 0)$n
  c(case, list(n = n))
})

normal <- list(
  list(odds_ratio = "3/2", baseline = "1/10", power = "4/5", r2 = "0"),
  list(odds_ratio = "2", baseline = "1/4", power = "9/10", r2 = "0"),
  list(odds_ratio = "4/5", baseline = "3/10", power = "4/5", r2 = "1/10")
)
normal_rows <- lapply(normal, function(case) {
  n <- power.z.logistic(base.prob = value(case$baseline), odds.ratio = value(case$odds_ratio),
                        power = value(case$power), r.squared.predictor = value(case$r2),
                        method = "hsieh", ceil.n = FALSE, verbose = 0)$n
  c(case, list(n = n))
})

# Signorini, in the expected events: with a share s exposed and rate ratio r, the events are
# base rate * n * mean exposure * (1 - s + s r).
rates <- list(
  list(base_rate = "4/5", rate_ratio = "2", n = 100, share = "1/4", alpha = "1/20"),
  list(base_rate = "1/50", rate_ratio = "3/2", n = 10000, share = "1/2", alpha = "1/20"),
  list(base_rate = "1/10", rate_ratio = "1/2", n = 2000, share = "1/5", alpha = "1/100")
)
rate_rows <- lapply(rates, function(case) {
  base <- value(case$base_rate)
  ratio <- value(case$rate_ratio)
  share <- value(case$share)
  alpha <- value(case$alpha)
  null_variance <- 1 / (share * (1 - share))
  variance <- 1 / (1 - share) + 1 / (share * ratio)
  baseline <- base * case$n
  formula <- pnorm((abs(log(ratio)) * sqrt(baseline) - qnorm(1 - alpha / 2) *
                      sqrt(null_variance)) / sqrt(variance))
  pwrss <- power.z.poisreg(base.rate = base, rate.ratio = ratio, n = case$n, mean.exposure = 1,
                           distribution = list(dist = "bernoulli", prob = share),
                           method = "signorini", alpha = alpha, verbose = 0)$power
  c(case, list(events = baseline * (1 - share + share * ratio), formula = formula,
               pwrss = pwrss))
})

pairs <- list(
  list(pairs = 220, share = "1/4", odds_ratio = "2", alpha = "1/20"),
  list(pairs = 500, share = "1/10", odds_ratio = "3/2", alpha = "1/20"),
  list(pairs = 150, share = "2/5", odds_ratio = "1/3", alpha = "1/100")
)
pair_rows <- lapply(pairs, function(case) {
  ratio <- value(case$odds_ratio)
  psi <- max(ratio, 1 / ratio)
  smaller <- value(case$share) / (1 + psi)
  c(case, list(mess = power_mcnemar_test(n = case$pairs, paid = smaller, psi = psi,
                                         sig.level = value(case$alpha),
                                         method = "normal")$power))
})

# The Wald test of glm on simulated studies of fixed size.
simulate_binary <- function(n, p0, p1, share, runs = 4000) {
  set.seed(2026)
  hits <- 0
  for (run in seq_len(runs)) {
    x <- rbinom(n, 1, share)
    y <- rbinom(n, 1, ifelse(x == 1, p1, p0))
    fit <- suppressWarnings(glm(y ~ x, family = binomial))
    z <- summary(fit)$coefficients[2, 3]
    hits <- hits + (!is.na(z) && abs(z) > qnorm(0.975))
  }
  hits / runs
}
simulations <- list(
  list(n = 451, p_reference = "1/10", p_other = "1/5", share_other = "3/10"),
  list(n = 600, p_reference = "1/5", p_other = "1/3", share_other = "1/2")
)
simulation_rows <- lapply(simulations, function(case) {
  c(case, list(simulation = simulate_binary(case$n, value(case$p_reference),
                                            value(case$p_other), value(case$share_other))))
})

risk_ratio <- function(n0, n1, p0, p1, alpha) {
  pooled <- (n1 * p1 + n0 * p0) / (n0 + n1)
  variance <- (1 - p1) / (n1 * p1) + (1 - p0) / (n0 * p0)
  null_variance <- (1 - pooled) / pooled * (1 / n1 + 1 / n0)
  pnorm((abs(log(p1 / p0)) - qnorm(1 - alpha / 2) * sqrt(null_variance)) / sqrt(variance))
}
simulate_ratio <- function(n0, n1, p0, p1, runs = 4000) {
  set.seed(2026)
  x <- rep(c(0, 1), c(n0, n1))
  hits <- 0
  for (run in seq_len(runs)) {
    y <- rbinom(n0 + n1, 1, ifelse(x == 1, p1, p0))
    fit <- glm(y ~ x, family = poisson)
    z <- coef(fit)[2] / sqrt(vcovHC(fit, type = "HC0")[2, 2])
    hits <- hits + (abs(z) > qnorm(0.975))
  }
  hits / runs
}
ratios <- list(
  list(unexposed = 1050, exposed = 525, p_reference = "1/10", p_other = "3/20", alpha = "1/20"),
  list(unexposed = 400, exposed = 400, p_reference = "1/5", p_other = "3/10", alpha = "1/20"),
  list(unexposed = 900, exposed = 300, p_reference = "1/4", p_other = "1/5", alpha = "1/100")
)
ratio_rows <- lapply(ratios, function(case) {
  p0 <- value(case$p_reference)
  p1 <- value(case$p_other)
  row <- c(case, list(formula = risk_ratio(case$unexposed, case$exposed, p0, p1,
                                           value(case$alpha))))
  if (case$alpha == "1/20") row$simulation <- simulate_ratio(case$unexposed, case$exposed, p0, p1)
  row
})

fixture <- list(
  r_version = R.version.string,
  packages = list(pwrss = as.character(packageVersion("pwrss")),
                  MESS = as.character(packageVersion("MESS")),
                  sandwich = as.character(packageVersion("sandwich"))),
  risk_ratios = ratio_rows,
  logistic_binary = binary_rows,
  logistic_normal = normal_rows,
  poisson_rates = rate_rows,
  matched_pairs = pair_rows,
  simulations = simulation_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/logistic_power_r.json")

sink("replication/comparison/logistic_power_r.txt")
cat("Power of the cited regression tests, written to tests/fixtures/logistic_power_r.json\n\n")
cat("Logistic regression on a binary exposure (pwrss, Hsieh)\n")
for (row in binary_rows) {
  cat(sprintf("p = (%s, %s), share exposed %s, R2 %s, power %s: n = %.6f\n", row$p_reference,
              row$p_other, row$share_other, row$r2, row$power, row$n))
}
cat("\nLogistic regression on a normal exposure (pwrss, Hsieh)\n")
for (row in normal_rows) {
  cat(sprintf("OR per SD %s, baseline %s, R2 %s, power %s: n = %.6f\n", row$odds_ratio,
              row$baseline, row$r2, row$power, row$n))
}
cat("\nPoisson regression of rates (Signorini)\n")
for (row in rate_rows) {
  cat(sprintf("rate ratio %s, share %s, %.4f events, alpha %s: formula %.12f, pwrss %.12f\n",
              row$rate_ratio, row$share, row$events, row$alpha, row$formula, row$pwrss))
}
cat("\nMatched pairs (MESS, Connor)\n")
for (row in pair_rows) {
  cat(sprintf("%d pairs, discordant %s, odds ratio %s, alpha %s: %.12f\n", row$pairs,
              row$share, row$odds_ratio, row$alpha, row$mess))
}
cat("\nModified Poisson regression, Wald test of the log risk ratio\n")
for (row in ratio_rows) {
  cat(sprintf("groups (%d, %d), p = (%s, %s), alpha %s: formula %.12f", row$unexposed,
              row$exposed, row$p_reference, row$p_other, row$alpha, row$formula),
      if (is.null(row$simulation)) "\n" else sprintf(", simulation %.4f\n", row$simulation),
      sep = "")
}
cat("\nSimulation, glm Wald test\n")
for (row in simulation_rows) {
  cat(sprintf("n %d, p = (%s, %s), share %s: %.4f\n", row$n, row$p_reference, row$p_other,
              row$share_other, row$simulation))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/logistic_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
