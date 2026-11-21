# Simulated Type I error and power of Student's and Welch's t-tests when the outcome has
# unequal SDs or is skewed, against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/t_scenarios_r.R
# Needs jsonlite. It regenerates tests/fixtures/t_scenarios_r.json, which
# tests/test_t_scenarios.py compares with StatClaim offline, and writes t_scenarios_r.txt
# beside this file with the values and the R session.
#
# Each simulated study draws every participant: normal outcomes with each arm's SD, or for
# skewness g a gamma distribution with shape 4 / g^2, shifted and scaled to the arm's mean
# and SD (mirrored when g is negative). The test is t.test, pooled or Welch, with the
# alternative of the null's side. StatClaim draws normal summaries directly and skewed
# outcomes one at a time; the two must agree within their Monte Carlo error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
outcomes <- function(n, mean, sd, skewness) {
  if (skewness == 0) return(mean + sd * rnorm(n))
  shape <- 4 / skewness^2
  mean + sign(skewness) * sd * (rgamma(n, shape) - shape) / sqrt(shape)
}
simulate <- function(case, runs) {
  set.seed(2026)
  sd <- value(case$sd)
  sd_treatment <- value(case$sd_treatment)
  skewness <- value(case$skewness)
  alternative <- c(both = "two.sided", higher = "greater", lower = "less")[[case$side]]
  hits <- 0
  for (run in seq_len(runs)) {
    control <- outcomes(case$n_control, 0, sd, skewness)
    treated <- outcomes(case$n_treatment, value(case$difference), sd_treatment, skewness)
    test <- t.test(treated, control, alternative = alternative, var.equal = case$test == "student")
    hits <- hits + (test$p.value <= 0.05)
  }
  hits / runs
}
cases <- list(
  list(test = "student", side = "both", n_control = 20, n_treatment = 40, difference = "0",
       sd = "20", sd_treatment = "10", skewness = "0"),
  list(test = "welch", side = "both", n_control = 20, n_treatment = 40, difference = "0",
       sd = "20", sd_treatment = "10", skewness = "0"),
  list(test = "student", side = "both", n_control = 20, n_treatment = 40, difference = "8",
       sd = "20", sd_treatment = "10", skewness = "0"),
  list(test = "welch", side = "both", n_control = 20, n_treatment = 40, difference = "8",
       sd = "20", sd_treatment = "10", skewness = "0"),
  list(test = "student", side = "higher", n_control = 10, n_treatment = 10, difference = "0",
       sd = "10", sd_treatment = "10", skewness = "2"),
  list(test = "welch", side = "higher", n_control = 10, n_treatment = 30, difference = "0",
       sd = "10", sd_treatment = "10", skewness = "2"),
  list(test = "student", side = "both", n_control = 65, n_treatment = 65, difference = "5",
       sd = "10", sd_treatment = "10", skewness = "2"),
  list(test = "welch", side = "lower", n_control = 30, n_treatment = 30, difference = "-4",
       sd = "10", sd_treatment = "15", skewness = "-3/2")
)
runs <- 20000
rows <- lapply(cases, function(case) c(case, list(rate = simulate(case, runs), runs = runs)))

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/t_scenarios_r.json")

sink("replication/comparison/t_scenarios_r.txt")
cat("Rejection rates of t-tests in other scenarios, written to tests/fixtures/t_scenarios_r.json\n\n")
for (row in rows) {
  cat(sprintf("%s (%s): n (%d, %d), difference %s, SDs (%s, %s), skewness %s: %.4f of %d\n",
              row$test, row$side, row$n_control, row$n_treatment, row$difference, row$sd,
              row$sd_treatment, row$skewness, row$rate, row$runs))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/t_scenarios_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
