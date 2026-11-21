# Power of the log-rank test planned from survival times, against R. Run from the
# repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/survival_power_r.R
# Needs gsDesign, rpact and jsonlite. It regenerates tests/fixtures/survival_power_r.json,
# which tests/test_survival_power.py compares with StatClaim offline, and writes
# survival_power_r.txt beside this file with the values and the R session.
#
# Times are exponential, the control hazard log(2) / median and the treatment hazard the
# hazard ratio times it. Participants enter uniformly over the accrual period and the
# analysis is at its end plus the follow-up. Dropout is exponential with probability
# `dropout` by `dropout_time`. Power is Schoenfeld's formula at the expected events.
#   eEvents    gsDesign's expected events for each arm (Lachin and Foulkes)
#   integrate  the probability of an event by the analysis, by numerical integration over
#              entry time, as an independent check
#   rpact      getSampleSizeSurvival with typeOfComputation = "Schoenfeld": participants
#              needed in all, not rounded
#   nSurv      gsDesign's nSurv with method = "Schoenfeld", the same
suppressMessages({
  library(gsDesign)
  library(rpact)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))
loss_rate <- function(case) {
  if (is.null(case$dropout)) 0 else -log(1 - value(case$dropout)) / value(case$dropout_time)
}

# The probability that a participant has an event by the analysis, by integration.
event_probability <- function(hazard, loss, accrual, follow_up) {
  observed <- function(entry) hazard / (hazard + loss) * (1 - exp(-(hazard + loss) * (accrual + follow_up - entry)))
  if (accrual == 0) return(observed(0))
  integrate(observed, 0, accrual, rel.tol = 1e-12)$value / accrual
}

# gsDesign's expected events in each arm, at accrual rate n / accrual.
expected_events <- function(n, hazard, loss, accrual, follow_up) {
  if (accrual == 0) return(n * event_probability(hazard, loss, 0, follow_up))
  eEvents(lambda = hazard, eta = loss, gamma = n / accrual, R = accrual, T = accrual + follow_up)$d
}

schoenfeld <- function(events, share, ratio, alpha) {
  pnorm(abs(log(ratio)) * sqrt(events * share * (1 - share)) - qnorm(1 - alpha / 2))
}

power_cases <- list(
  list(n_c = 200, n_t = 200, hazard_ratio = "7/10", control_median = "12", accrual = "24",
       follow_up = "12", dropout = "1/10", dropout_time = "12", alpha = "1/20"),
  list(n_c = 100, n_t = 100, hazard_ratio = "3/5", control_median = "6", accrual = "12",
       follow_up = "6", alpha = "1/20"),
  list(n_c = 150, n_t = 150, hazard_ratio = "7/5", control_median = "24", accrual = "0",
       follow_up = "36", dropout = "1/20", dropout_time = "12", alpha = "1/20"),
  list(n_c = 150, n_t = 300, hazard_ratio = "3/4", control_median = "18", accrual = "18",
       follow_up = "24", dropout = "1/5", dropout_time = "24", alpha = "1/20"),
  list(n_c = 400, n_t = 400, hazard_ratio = "4/5", control_median = "10", accrual = "30",
       follow_up = "0", alpha = "1/100")
)
power_rows <- lapply(power_cases, function(case) {
  control <- log(2) / value(case$control_median)
  treated <- value(case$hazard_ratio) * control
  loss <- loss_rate(case)
  a <- value(case$accrual)
  f <- value(case$follow_up)
  events <- expected_events(case$n_c, control, loss, a, f) +
    expected_events(case$n_t, treated, loss, a, f)
  share <- case$n_c / (case$n_c + case$n_t)
  c(case, list(
    probability_control = event_probability(control, loss, a, f),
    probability_treatment = event_probability(treated, loss, a, f),
    expected_events = events,
    power = schoenfeld(events, share, value(case$hazard_ratio), value(case$alpha))
  ))
})

# The fewest controls, with treatment_per_control treated participants for each, whose power
# reaches the target; and what rpact and nSurv ask for in all.
search_cases <- list(
  list(hazard_ratio = "7/10", control_median = "12", accrual = "24", follow_up = "12",
       dropout = "1/10", dropout_time = "12", alpha = "1/20", power = "4/5", ratio = 1),
  list(hazard_ratio = "3/5", control_median = "6", accrual = "12", follow_up = "6",
       alpha = "1/20", power = "9/10", ratio = 1),
  list(hazard_ratio = "3/4", control_median = "18", accrual = "18", follow_up = "24",
       dropout = "1/5", dropout_time = "24", alpha = "1/20", power = "4/5", ratio = 2)
)
search_rows <- lapply(search_cases, function(case) {
  control <- log(2) / value(case$control_median)
  treated <- value(case$hazard_ratio) * control
  loss <- loss_rate(case)
  a <- value(case$accrual)
  f <- value(case$follow_up)
  alpha <- value(case$alpha)
  power_at <- function(k) {
    events <- expected_events(k, control, loss, a, f) +
      expected_events(case$ratio * k, treated, loss, a, f)
    schoenfeld(events, 1 / (1 + case$ratio), value(case$hazard_ratio), alpha)
  }
  k <- 1
  while (power_at(k) < value(case$power)) k <- k + 1
  dropout <- if (is.null(case$dropout)) 0 else value(case$dropout)
  dropout_time <- if (is.null(case$dropout_time)) 12 else value(case$dropout_time)
  sized <- getSampleSizeSurvival(
    design = getDesignGroupSequential(kMax = 1, alpha = alpha, sided = 2,
                                      beta = 1 - value(case$power)),
    typeOfComputation = "Schoenfeld", lambda2 = control, hazardRatio = value(case$hazard_ratio),
    accrualTime = c(0, a), followUpTime = f, dropoutRate1 = dropout, dropoutRate2 = dropout,
    dropoutTime = dropout_time, allocationRatioPlanned = case$ratio)
  surv <- nSurv(lambdaC = control, hr = value(case$hazard_ratio), eta = loss, R = a,
                minfup = f, T = a + f, alpha = alpha / 2, beta = 1 - value(case$power), sided = 1,
                ratio = case$ratio, method = "Schoenfeld")
  c(case, list(controls = k, power_at = power_at(k), rpact = sized$maxNumberOfSubjects,
               nsurv = surv$n))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(gsDesign = as.character(packageVersion("gsDesign")),
                  rpact = as.character(packageVersion("rpact"))),
  powers = power_rows,
  searches = search_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/survival_power_r.json")

sink("replication/comparison/survival_power_r.txt")
cat("Log-rank power from survival times, written to tests/fixtures/survival_power_r.json\n\n")
for (row in power_rows) {
  lost <- if (is.null(row$dropout)) "no dropout" else
    sprintf("dropout %s by %s", row$dropout, row$dropout_time)
  cat(sprintf("arms (%d, %d), HR %s, median %s, accrual %s, follow-up %s, %s, alpha %s:",
              row$n_c, row$n_t, row$hazard_ratio, row$control_median, row$accrual,
              row$follow_up, lost, row$alpha),
      sprintf("events %.10f, power %.12f\n", row$expected_events, row$power))
}
cat("\nSearches\n")
for (row in search_rows) {
  cat(sprintf("HR %s, median %s, accrual %s, follow-up %s, power %s, 1:%d:", row$hazard_ratio,
              row$control_median, row$accrual, row$follow_up, row$power, row$ratio),
      sprintf("%d controls (power %.6f); rpact %.3f in all, nSurv %.3f\n", row$controls,
              row$power_at, row$rpact, row$nsurv))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/survival_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
