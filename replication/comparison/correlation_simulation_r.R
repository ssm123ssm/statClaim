# Simulated Type I error and power of the t-tests of Pearson's correlation and of a simple
# regression slope with skewed data, against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/correlation_simulation_r.R
# Needs jsonlite. It regenerates tests/fixtures/correlation_simulation_r.json, which
# tests/test_correlation_simulation.py compares with StatClaim offline, and writes
# correlation_simulation_r.txt beside this file with the values and the R session.
#
# The exposure and the outcome's error have mean 0 and SD 1: normal, or for skewness g a
# gamma distribution with shape 4 / g^2, shifted and scaled (mirrored when g is negative).
# A correlation case sets outcome = rho x + sqrt(1 - rho^2) e and uses cor.test; a slope
# case sets outcome = slope * exposure_sd * x + residual_sd * e and uses lm. The two
# simulations must agree within their Monte Carlo error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
standard <- function(n, skewness) {
  if (skewness == 0) return(rnorm(n))
  shape <- 4 / skewness^2
  sign(skewness) * (rgamma(n, shape) - shape) / sqrt(shape)
}
simulate <- function(case, runs) {
  set.seed(2026)
  hits <- 0
  for (run in seq_len(runs)) {
    x <- standard(case$n, value(case$exposure_skewness))
    e <- standard(case$n, value(case$skewness))
    if (case$kind == "correlation") {
      rho <- value(case$value)
      y <- rho * x + sqrt(1 - rho^2) * e
      p <- cor.test(x, y)$p.value
    } else {
      exposure <- value(case$exposure_sd) * x
      y <- value(case$value) * exposure + value(case$residual_sd) * e
      p <- summary(lm(y ~ exposure))$coefficients[2, 4]
    }
    hits <- hits + (p <= 0.05)
  }
  hits / runs
}
cases <- list(
  list(kind = "correlation", n = 30, value = "1/2", skewness = "3", exposure_skewness = "3"),
  list(kind = "correlation", n = 20, value = "0", skewness = "3", exposure_skewness = "3"),
  list(kind = "correlation", n = 10, value = "0", skewness = "4", exposure_skewness = "4"),
  list(kind = "correlation", n = 50, value = "-3/10", skewness = "0", exposure_skewness = "-2"),
  list(kind = "slope", n = 30, value = "1/2", exposure_sd = "4", residual_sd = "4",
       skewness = "2", exposure_skewness = "0")
)
runs <- 20000
rows <- lapply(cases, function(case) c(case, list(rate = simulate(case, runs), runs = runs)))

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/correlation_simulation_r.json")

sink("replication/comparison/correlation_simulation_r.txt")
cat("Rejection rates with skewed data, written to tests/fixtures/correlation_simulation_r.json\n\n")
for (row in rows) {
  cat(sprintf("%s: n %d, value %s, skewness (exposure %s, error %s): %.4f of %d\n",
              row$kind, row$n, row$value, row$exposure_skewness, row$skewness, row$rate, row$runs))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/correlation_simulation_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
