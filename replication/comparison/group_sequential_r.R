# Simulated power, stopping probabilities and Type I error of designs with interim looks,
# against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/group_sequential_r.R
# Needs jsonlite. It regenerates tests/fixtures/group_sequential_r.json, which
# tests/test_group_sequential.py compares with StatClaim offline, and writes
# group_sequential_r.txt beside this file with the values and the R session.
#
# Each simulated trial draws every participant of the final look, normal or, for skewness
# g, a gamma distribution with shape 4 / g^2 shifted and scaled to the arm's mean and SD.
# At each look t.test is applied to the participants enrolled by then, with that look's
# level, and the trial stops at the first rejection. StatClaim draws each stage's
# summaries; the two simulations must agree within their Monte Carlo error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
outcomes <- function(n, mean, sd, skewness) {
  if (skewness == 0) return(mean + sd * rnorm(n))
  shape <- 4 / skewness^2
  mean + sign(skewness) * sd * (rgamma(n, shape) - shape) / sqrt(shape)
}
simulate <- function(case, difference, runs) {
  set.seed(2026)
  looks <- case$looks
  final <- looks[[length(looks)]]
  alternative <- c(both = "two.sided", higher = "greater")[[case$side]]
  stopped <- rep(0, length(looks))
  for (run in seq_len(runs)) {
    control <- outcomes(final$n_control, 0, value(case$sd), value(case$skewness))
    treated <- outcomes(final$n_treatment, difference, value(case$sd), value(case$skewness))
    for (k in seq_along(looks)) {
      look <- looks[[k]]
      test <- t.test(treated[seq_len(look$n_treatment)], control[seq_len(look$n_control)],
                     alternative = alternative, var.equal = case$test == "student")
      if (test$p.value <= value(look$alpha)) {
        stopped[k] <- stopped[k] + 1
        break
      }
    }
  }
  stopped / runs
}
cases <- list(
  list(test = "student", side = "both", difference = "4", sd = "10", skewness = "0",
       looks = list(list(n_control = 50, n_treatment = 50, alpha = "1/200"),
                    list(n_control = 100, n_treatment = 100, alpha = "9/200"))),
  list(test = "welch", side = "higher", difference = "5", sd = "12", skewness = "0",
       looks = list(list(n_control = 30, n_treatment = 30, alpha = "1/1000"),
                    list(n_control = 60, n_treatment = 60, alpha = "1/100"),
                    list(n_control = 90, n_treatment = 90, alpha = "39/1000"))),
  list(test = "student", side = "both", difference = "4", sd = "10", skewness = "2",
       looks = list(list(n_control = 40, n_treatment = 80, alpha = "1/100"),
                    list(n_control = 80, n_treatment = 160, alpha = "1/25")))
)
runs <- 20000
rows <- lapply(cases, function(case) {
  c(case, list(stopped = simulate(case, value(case$difference), runs),
               stopped_null = simulate(case, 0, runs), runs = runs))
})

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/group_sequential_r.json")

sink("replication/comparison/group_sequential_r.txt")
cat("Stopping at each look, written to tests/fixtures/group_sequential_r.json\n\n")
for (row in rows) {
  sizes <- paste(vapply(row$looks, function(l) sprintf("(%d, %d) at %s", l$n_control,
                                                       l$n_treatment, l$alpha), ""),
                 collapse = ", ")
  cat(sprintf("%s (%s), difference %s, sd %s, skewness %s, looks %s\n", row$test, row$side,
              row$difference, row$sd, row$skewness, sizes))
  cat(sprintf("  stopped at each look: %s; power %.4f\n",
              paste(sprintf("%.4f", row$stopped), collapse = ", "), sum(row$stopped)))
  cat(sprintf("  under the null: %s; Type I %.4f\n",
              paste(sprintf("%.4f", row$stopped_null), collapse = ", "), sum(row$stopped_null)))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/group_sequential_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
