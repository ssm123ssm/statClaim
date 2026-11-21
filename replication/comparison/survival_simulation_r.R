# Simulated power and Type I error of the log-rank test against a simulation in R that
# analyses each trial with survival::survdiff.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/survival_simulation_r.R
# Needs jsonlite and survival. It regenerates tests/fixtures/survival_simulation_r.json,
# which tests/test_survival_simulation.py compares with StatClaim offline, and writes
# survival_simulation_r.txt beside this file with the values and the R session.
#
# Each participant enters uniformly over the accrual period and is followed to its end plus
# the follow-up. Event times are exponential with the control hazard log 2 / median; in the
# treatment arm the hazard is multiplied by the hazard ratio from the delay after entry on.
# Dropout is exponential, with probability `dropout` by `dropout_time`. survdiff's
# chi-square is compared with qchisq(0.95, 1). The two simulations must agree within their
# Monte Carlo error; Schoenfeld's formula is printed beside them.
suppressMessages({
  library(jsonlite)
  library(survival)
})

value <- function(text) eval(parse(text = text))
event_times <- function(n, control, ratio, delay) {
  total <- rexp(n)
  late <- total > control * delay
  ifelse(late, delay + (total - control * delay) / (control * ratio), total / control)
}
simulate <- function(case, runs) {
  set.seed(2026)
  control <- log(2) / value(case$control_median)
  accrual <- value(case$accrual)
  follow_up <- value(case$follow_up)
  dropout <- value(case$dropout)
  loss <- if (dropout > 0) -log1p(-dropout) / value(case$dropout_time) else 0
  ratio <- value(case$hazard_ratio)
  delay <- value(case$effect_delay)
  hits <- 0
  for (run in seq_len(runs)) {
    n <- c(case$n_control, case$n_treatment)
    arm <- rep(0:1, n)
    window <- accrual + follow_up - accrual * runif(sum(n))
    time <- c(event_times(n[1], control, 1, 0), event_times(n[2], control, ratio, delay))
    lost <- if (loss > 0) rexp(sum(n), loss) else rep(Inf, sum(n))
    observed <- pmin(time, lost, window)
    event <- as.integer(time <= pmin(lost, window))
    test <- survdiff(Surv(observed, event) ~ arm)
    hits <- hits + (test$chisq > qchisq(0.95, 1))
  }
  hits / runs
}
cases <- list(
  list(n_control = 150, n_treatment = 150, hazard_ratio = "7/10", control_median = "12",
       accrual = "12", follow_up = "12", dropout = "0", dropout_time = "1", effect_delay = "0"),
  list(n_control = 100, n_treatment = 200, hazard_ratio = "13/20", control_median = "10",
       accrual = "18", follow_up = "6", dropout = "1/10", dropout_time = "12", effect_delay = "0"),
  list(n_control = 215, n_treatment = 215, hazard_ratio = "7/10", control_median = "12",
       accrual = "12", follow_up = "12", dropout = "0", dropout_time = "1", effect_delay = "3"),
  list(n_control = 30, n_treatment = 30, hazard_ratio = "1", control_median = "12",
       accrual = "0", follow_up = "24", dropout = "0", dropout_time = "1", effect_delay = "0")
)
runs <- 10000
rows <- lapply(cases, function(case) c(case, list(rate = simulate(case, runs), runs = runs)))

fixture <- list(r_version = R.version.string,
                survival_version = as.character(packageVersion("survival")), cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/survival_simulation_r.json")

sink("replication/comparison/survival_simulation_r.txt")
cat("Rejection rates of the log-rank test (survdiff), written to",
    "tests/fixtures/survival_simulation_r.json\n\n")
for (row in rows) {
  cat(sprintf("n (%d, %d), HR %s, median %s, accrual %s, follow-up %s, dropout %s by %s, delay %s: %.4f of %d\n",
              row$n_control, row$n_treatment, row$hazard_ratio, row$control_median, row$accrual,
              row$follow_up, row$dropout, row$dropout_time, row$effect_delay, row$rate, row$runs))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/survival_simulation_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
