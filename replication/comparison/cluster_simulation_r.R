# Simulated power of the t-test on cluster summaries against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/cluster_simulation_r.R
# Needs jsonlite. It regenerates tests/fixtures/cluster_simulation_r.json, which
# tests/test_cluster_simulation.py compares with StatClaim offline, and writes
# cluster_simulation_r.txt beside this file with the values and the R session.
#
# Each simulated study draws every participant: cluster sizes from a gamma distribution with
# the arm's mean size and the given coefficient of variation (rounded, at least 1), a normal
# cluster effect with variance icc sd^2 and normal participants about it, or for proportions
# a beta cluster rate with intracluster correlation icc and binomial responses. The test is
# t.test(var.equal = TRUE) on the cluster means or proportions. StatClaim draws each
# cluster's mean directly, which is the same distribution; the two must agree within their
# Monte Carlo error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
size_of <- function(mean, cv) {
  if (cv == 0) return(max(1, round(mean)))
  max(1, round(rgamma(1, shape = 1 / cv^2, scale = mean * cv^2)))
}
cluster_means <- function(case, runs) {
  set.seed(2026)
  sd <- value(case$sd)
  icc <- value(case$icc)
  cv <- value(case$cv)
  hits <- 0
  for (run in seq_len(runs)) {
    arm <- function(k, shift) vapply(seq_len(k), function(i) {
      m <- size_of(case$m, cv)
      mean(shift + sd * sqrt(icc) * rnorm(1) + sd * sqrt(1 - icc) * rnorm(m))
    }, numeric(1))
    test <- t.test(arm(case$k, value(case$difference)), arm(case$k, 0), var.equal = TRUE)
    hits <- hits + (test$p.value <= 0.05)
  }
  hits / runs
}
cluster_proportions <- function(case, runs) {
  set.seed(2026)
  icc <- value(case$icc)
  cv <- value(case$cv)
  hits <- 0
  for (run in seq_len(runs)) {
    arm <- function(k, p) vapply(seq_len(k), function(i) {
      m <- size_of(case$m, cv)
      rate <- rbeta(1, p * (1 - icc) / icc, (1 - p) * (1 - icc) / icc)
      rbinom(1, m, rate) / m
    }, numeric(1))
    test <- t.test(arm(case$k, value(case$p_treatment)), arm(case$k, value(case$p_control)),
                   var.equal = TRUE)
    hits <- hits + (!is.na(test$p.value) && test$p.value <= 0.05)
  }
  hits / runs
}
runs <- 20000
means <- list(
  list(k = 6, m = 20, difference = "5", sd = "10", icc = "1/20", cv = "0"),
  list(k = 6, m = 20, difference = "5", sd = "10", icc = "1/20", cv = "3/5"),
  list(k = 10, m = 10, difference = "3", sd = "8", icc = "1/10", cv = "1")
)
mean_rows <- lapply(means, function(case) c(case, list(power = cluster_means(case, runs), runs = runs)))
proportions <- list(
  list(k = 8, m = 30, p_control = "3/10", p_treatment = "1/2", icc = "1/50", cv = "2/5"),
  list(k = 6, m = 20, p_control = "3/10", p_treatment = "1/2", icc = "1/50", cv = "0")
)
proportion_rows <- lapply(proportions, function(case) {
  c(case, list(power = cluster_proportions(case, runs), runs = runs))
})

fixture <- list(r_version = R.version.string, means = mean_rows, proportions = proportion_rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/cluster_simulation_r.json")

sink("replication/comparison/cluster_simulation_r.txt")
cat("Simulated power of the cluster t-test, written to tests/fixtures/cluster_simulation_r.json\n\n")
for (row in mean_rows) {
  cat(sprintf("means: %d clusters of %d per arm, cv %s, icc %s, difference %s, sd %s: %.4f of %d\n",
              row$k, row$m, row$cv, row$icc, row$difference, row$sd, row$power, row$runs))
}
for (row in proportion_rows) {
  cat(sprintf("proportions: %d clusters of %d per arm, cv %s, icc %s, rates (%s, %s): %.4f of %d\n",
              row$k, row$m, row$cv, row$icc, row$p_control, row$p_treatment, row$power, row$runs))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/cluster_simulation_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
