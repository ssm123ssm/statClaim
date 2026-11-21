# Simulated power, Type I error and expected size of Student's t-test with blinded
# sample-size re-estimation (Kieser and Friede, 2003), against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/reestimation_r.R
# Needs jsonlite. It regenerates tests/fixtures/reestimation_r.json, which
# tests/test_reestimation.py compares with StatClaim offline, and writes reestimation_r.txt
# beside this file with the values and the R session.
#
# After `interim` participants per arm, the variance is var() of all of them with the arms
# pooled. The size per arm is ceiling(2 s^2 (z_(1 - alpha/2) + z_power)^2 / difference^2),
# kept between the initial size and the maximum; t.test(var.equal = TRUE) then uses every
# participant. StatClaim draws each stage's summaries; the two must agree within their
# Monte Carlo error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
simulate <- function(case, difference, sd, runs) {
  set.seed(2026)
  planned <- value(case$difference)
  z <- qnorm(1 - value(case$alpha) / 2) + qnorm(value(case$power))
  hits <- 0
  sizes <- 0
  for (run in seq_len(runs)) {
    control <- rnorm(case$interim, 0, sd)
    treated <- rnorm(case$interim, difference, sd)
    s2 <- var(c(control, treated))
    n <- min(max(ceiling(2 * s2 * z^2 / planned^2), case$initial), case$largest)
    if (n > case$interim) {
      control <- c(control, rnorm(n - case$interim, 0, sd))
      treated <- c(treated, rnorm(n - case$interim, difference, sd))
    }
    hits <- hits + (t.test(treated, control, var.equal = TRUE)$p.value <= value(case$alpha))
    sizes <- sizes + n
  }
  list(rate = hits / runs, mean_per_arm = sizes / runs)
}
case <- list(initial = 64, interim = 30, largest = 200, difference = "5", power = "4/5",
             alpha = "1/20")
runs <- 20000
rows <- list()
for (sd in c(6, 10, 14)) {
  null <- simulate(case, 0, sd, runs)
  alternative <- simulate(case, 5, sd, runs)
  rows[[length(rows) + 1]] <- list(sd = sd, typeI = null$rate, null_per_arm = null$mean_per_arm,
                                   power = alternative$rate,
                                   power_per_arm = alternative$mean_per_arm, runs = runs)
}

fixture <- list(r_version = R.version.string, design = case, scenarios = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/reestimation_r.json")

sink("replication/comparison/reestimation_r.txt")
cat("Blinded re-estimation after 30 per arm (64 to 200 per arm, difference 5, power 4/5),\n")
cat("written to tests/fixtures/reestimation_r.json\n\n")
for (row in rows) {
  cat(sprintf("sd %g: Type I %.4f (mean %.2f per arm); power at difference 5 %.4f (mean %.2f per arm); %d runs\n",
              row$sd, row$typeI, row$null_per_arm, row$power, row$power_per_arm, row$runs))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/reestimation_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
