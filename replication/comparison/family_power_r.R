# Simulated power of families of tests (Bonferroni, fixed sequence, graphical) with
# correlated endpoints, against a raw-data simulation in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/family_power_r.R
# Needs jsonlite. It regenerates tests/fixtures/family_power_r.json, which
# tests/test_family_power.py compares with StatClaim offline, and writes family_power_r.txt
# beside this file with the values and the R session.
#
# Each participant has a latent normal per endpoint with an exchangeable correlation: a
# yes-or-no outcome is a success when its latent is above qnorm(1 - rate), and a measured
# outcome is the mean plus the SD times its latent. Endpoints are tested with fisher.test
# and t.test(var.equal = TRUE); the graphical procedure is Bretz et al.'s algorithm, written
# here independently of StatClaim. The two simulations must agree within their Monte Carlo
# error.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
graphical <- function(p, alpha, weights, transitions) {
  k <- length(p)
  active <- rep(TRUE, k)
  rejected <- rep(FALSE, k)
  repeat {
    candidates <- which(active & p <= weights * alpha)
    if (length(candidates) == 0) return(rejected)
    j <- candidates[1]
    rejected[j] <- TRUE
    active[j] <- FALSE
    new_weights <- weights
    new_graph <- transitions
    for (l in which(active)) {
      new_weights[l] <- weights[l] + weights[j] * transitions[j, l]
      for (m in which(active)) {
        if (l == m) {
          new_graph[l, m] <- 0
        } else {
          denominator <- 1 - transitions[l, j] * transitions[j, l]
          new_graph[l, m] <- if (denominator > 0) {
            (transitions[l, m] + transitions[l, j] * transitions[j, m]) / denominator
          } else 0
        }
      }
    }
    new_weights[j] <- 0
    weights <- new_weights
    transitions <- new_graph
  }
}
simulate <- function(case, at_null, runs) {
  set.seed(2026)
  endpoints <- case$endpoints
  k <- length(endpoints)
  rho <- value(case$correlation)
  alpha <- value(case$alpha)
  counts <- rep(0, k)
  any_count <- 0
  all_count <- 0
  for (run in seq_len(runs)) {
    p <- numeric(k)
    if (rho > 0) {
      n <- c(endpoints[[1]]$n_control, endpoints[[1]]$n_treatment)
      latent <- lapply(1:2, function(arm) {
        w <- rnorm(n[arm])
        sapply(seq_len(k), function(i) sqrt(rho) * w + sqrt(1 - rho) * rnorm(n[arm]))
      })
    }
    for (i in seq_len(k)) {
      e <- endpoints[[i]]
      n <- c(e$n_control, e$n_treatment)
      z <- lapply(1:2, function(arm) if (rho > 0) latent[[arm]][, i] else rnorm(n[arm]))
      if (e$test == "fisher") {
        rates <- c(value(e$p_control), if (at_null) value(e$p_control) else value(e$p_treatment))
        successes <- sapply(1:2, function(arm) sum(z[[arm]] > qnorm(1 - rates[arm])))
        table <- matrix(c(successes, n - successes), nrow = 2)
        p[i] <- fisher.test(table)$p.value
      } else {
        shift <- if (at_null) 0 else value(e$difference)
        y <- list(value(e$sd) * z[[1]], shift + value(e$sd) * z[[2]])
        p[i] <- t.test(y[[2]], y[[1]], var.equal = TRUE)$p.value
      }
    }
    if (case$procedure == "bonferroni") {
      rejected <- p <= sapply(endpoints, function(e) value(e$alpha))
    } else if (case$procedure == "fixed_sequence") {
      rejected <- cumprod(p <= alpha) == 1
    } else {
      weights <- sapply(case$weights, value)
      transitions <- matrix(sapply(unlist(case$transitions), value), nrow = k, byrow = TRUE)
      rejected <- graphical(p, alpha, weights, transitions)
    }
    counts <- counts + rejected
    any_count <- any_count + any(rejected)
    all_count <- all_count + all(rejected)
  }
  list(each = counts / runs, any = any_count / runs, all = all_count / runs)
}
binary <- function(n, alpha, p_control, p_treatment) {
  list(test = "fisher", n_control = n, n_treatment = n, alpha = alpha,
       p_control = p_control, p_treatment = p_treatment)
}
measured <- function(n, alpha, difference, sd) {
  list(test = "student", n_control = n, n_treatment = n, alpha = alpha,
       difference = difference, sd = sd)
}
cases <- list(
  list(procedure = "bonferroni", alpha = "1/20", correlation = "1/2",
       endpoints = list(binary(120, "1/40", "3/10", "1/2"), measured(120, "1/40", "4", "10"))),
  list(procedure = "fixed_sequence", alpha = "1/20", correlation = "3/10",
       endpoints = list(measured(100, "1/20", "4", "10"), measured(100, "1/20", "3", "10"))),
  list(procedure = "graphical", alpha = "1/20", correlation = "2/5",
       weights = list("1/2", "1/2", "0"),
       transitions = list(list("0", "1/2", "1/2"), list("1/2", "0", "1/2"), list("0", "1", "0")),
       endpoints = list(binary(100, "1/20", "3/10", "1/2"), measured(100, "1/20", "4", "10"),
                        measured(100, "1/20", "3", "10"))),
  list(procedure = "bonferroni", alpha = "1/20", correlation = "0",
       endpoints = list(binary(80, "1/40", "1/5", "2/5"), binary(100, "1/40", "3/10", "1/2")))
)
runs <- 10000
rows <- lapply(cases, function(case) {
  c(case, list(power = simulate(case, FALSE, runs), null = simulate(case, TRUE, runs), runs = runs))
})

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/family_power_r.json")

sink("replication/comparison/family_power_r.txt")
cat("Rejection rates of families of tests, written to tests/fixtures/family_power_r.json\n\n")
for (row in rows) {
  cat(sprintf("%s, correlation %s, %d endpoints: each %s; any %.4f; all %.4f; familywise error %.4f\n",
              row$procedure, row$correlation, length(row$endpoints),
              paste(sprintf("%.4f", row$power$each), collapse = ", "), row$power$any,
              row$power$all, row$null$any))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/family_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
