# Writes power_r.json: base R power values used to cross-check StatClaim's normal formulas.
# Run from the repository root: Rscript tests/fixtures/power_r.R
# Needs base R only. The tests read the JSON and do not need R.
t_cases <- list(
  list(n = 440, delta = 40, sd = 167, alpha = 0.025, sided = "one.sided"),
  list(n = 440, delta = 40, sd = 167, alpha = 0.0125, sided = "one.sided"),
  list(n = 500, delta = 50, sd = 188, alpha = 0.0125, sided = "one.sided"),
  list(n = 440, delta = 0.75, sd = 3, alpha = 0.025, sided = "one.sided"),
  list(n = 400, delta = 3, sd = 12, alpha = 0.05, sided = "two.sided")
)
prop_cases <- list(
  list(n = 100, p1 = 0.3, p2 = 0.5, alpha = 0.05, sided = "two.sided"),
  list(n = 100, p1 = 0.3, p2 = 0.5, alpha = 0.025, sided = "one.sided"),
  list(n = 500, p1 = 0.40, p2 = 0.48, alpha = 0.025, sided = "one.sided"),
  list(n = 50, p1 = 0.1, p2 = 0.4, alpha = 0.05, sided = "two.sided")
)
num <- function(x) formatC(x, digits = 12, format = "f")
rows <- c()
for (case in t_cases) {
  power <- power.t.test(n = case$n, delta = case$delta, sd = case$sd, sig.level = case$alpha,
                        type = "two.sample", alternative = case$sided)$power
  rows <- c(rows, sprintf(
    '    {"function": "power.t.test", "n": %d, "delta": %s, "sd": %s, "alpha": %s, "alternative": "%s", "power": %s}',
    case$n, case$delta, case$sd, case$alpha, case$sided, num(power)))
}
for (case in prop_cases) {
  power <- power.prop.test(n = case$n, p1 = case$p1, p2 = case$p2, sig.level = case$alpha,
                           alternative = case$sided)$power
  rows <- c(rows, sprintf(
    '    {"function": "power.prop.test", "n": %d, "p1": %s, "p2": %s, "alpha": %s, "alternative": "%s", "power": %s}',
    case$n, case$p1, case$p2, case$alpha, case$sided, num(power)))
}
cat("{\n",
    sprintf('  "r_version": "%s",\n', R.version.string),
    '  "cases": [\n', paste(rows, collapse = ",\n"), "\n  ]\n}\n",
    sep = "", file = "tests/fixtures/power_r.json")
