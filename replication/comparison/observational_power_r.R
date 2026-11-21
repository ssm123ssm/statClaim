# Exact power of the proved observational tests against R: Fisher's test of no association
# for cohort and case-control studies, McNemar's test for matched pairs, and the rate test
# given the total number of events. Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/observational_power_r.R
# Needs exact2x2, epiR and jsonlite. It regenerates tests/fixtures/observational_power_r.json,
# which tests/test_observational_planning.py compares with StatClaim offline, and writes
# observational_power_r.txt beside this file with the values and the R session.
#
# Each case is (first group size, second group size, probability in each, alpha): the
# unexposed and exposed groups of a cohort with their risks, or the controls and cases of
# a case-control study with their probabilities of exposure.
#   enumeration  every table, with base R's fisher.test (two-sided, the default method)
#   exact2x2     exact2x2::power2x2 with strict = TRUE and tsmethod = "minlike", the same
#                test, exact up to its error bound of 1e-6. Its default (strict = FALSE)
#                is the power of a one-sided test at alpha/2 instead, which is lower when
#                the groups differ in size.
#   epiR         epiR's normal-approximation power (epi.sscohortc, epi.sscc), for context
# McNemar's test, at the share of discordant pairs and the conditional odds ratio:
#   enumeration  every number discordant and every split, with binom.test at one half
#   exact2x2     exact2x2::powerPaired2x2 with strict = TRUE, within its error bound
# The rate test given n events, at the person-time in each group and the rate ratio:
#   enumeration  every split of the events, with exactci::poisson.exact (central method)
suppressMessages({
  library(exact2x2)
  library(epiR)
  library(jsonlite)
})

# Probabilities and levels are exact fractions, written as text so the fixture keeps them.
cases <- list(
  list(design = "cohort", first = 40, second = 40, p_first = "1/10", p_second = "3/10",
       alpha = "1/20"),
  list(design = "cohort", first = 300, second = 150, p_first = "1/10", p_second = "1/5",
       alpha = "1/20"),
  list(design = "cohort", first = 100, second = 50, p_first = "1/20", p_second = "1/5",
       alpha = "1/40"),
  list(design = "case_control", first = 240, second = 120, p_first = "1/5", p_second = "1/3",
       alpha = "1/20"),
  list(design = "case_control", first = 264, second = 132, p_first = "1/5", p_second = "1/3",
       alpha = "1/20"),
  list(design = "case_control", first = 266, second = 133, p_first = "1/5", p_second = "1/3",
       alpha = "1/20"),
  list(design = "case_control", first = 60, second = 60, p_first = "3/10", p_second = "3/5",
       alpha = "1/100")
)
value <- function(text) eval(parse(text = text))

enumerate <- function(n1, n2, p1, p2, alpha) {
  power <- 0
  for (x in 0:n1) {
    for (y in 0:n2) {
      table <- matrix(c(x, n1 - x, y, n2 - y), 2)
      if (fisher.test(table)$p.value <= alpha) {
        power <- power + dbinom(x, n1, p1) * dbinom(y, n2, p2)
      }
    }
  }
  power
}

approximate <- function(case) {
  if (case$design == "cohort") {
    epi.sscohortc(N = NA, irexp1 = case$p_second, irexp0 = case$p_first, pexp = NA,
                  n = case$first + case$second, power = NA, r = case$first / case$second,
                  design = 1, sided.test = 2, nfractional = TRUE,
                  conf.level = 1 - case$alpha)$power
  } else {
    odds <- function(p) p / (1 - p)
    epi.sscc(N = NA, OR = odds(case$p_second) / odds(case$p_first), p1 = NA,
             p0 = case$p_first, n = case$first + case$second, power = NA,
             r = case$first / case$second, phi.coef = 0, design = 1, sided.test = 2,
             nfractional = TRUE, conf.level = 1 - case$alpha, method = "unmatched")$power
  }
}

rows <- lapply(cases, function(text) {
  case <- text
  for (name in c("p_first", "p_second", "alpha")) case[[name]] <- value(text[[name]])
  c(text, list(
    enumeration = enumerate(case$first, case$second, case$p_first, case$p_second, case$alpha),
    exact2x2 = power2x2(case$p_first, case$p_second, case$first, case$second,
                        sig.level = case$alpha, strict = TRUE, tsmethod = "minlike")$power,
    epiR = approximate(case)
  ))
})
matched <- list(
  list(pairs = 150, discordant = "1/4", odds_ratio = "2", alpha = "1/20"),
  list(pairs = 297, discordant = "1/4", odds_ratio = "2", alpha = "1/20"),
  list(pairs = 298, discordant = "1/4", odds_ratio = "2", alpha = "1/20"),
  list(pairs = 60, discordant = "1/2", odds_ratio = "3", alpha = "1/40"),
  list(pairs = 400, discordant = "1/10", odds_ratio = "3/2", alpha = "1/20")
)
mcnemar <- function(n, delta, psi, alpha) {
  share <- psi / (1 + psi)
  total <- 0
  for (d in seq_len(n)) {  # with no discordant pair the test cannot reject
    inner <- 0
    for (x in 0:d) {
      if (binom.test(x, d, 0.5)$p.value <= alpha) inner <- inner + dbinom(x, d, share)
    }
    total <- total + dbinom(d, n, delta) * inner
  }
  total
}
matched_rows <- lapply(matched, function(text) {
  delta <- value(text$discordant)
  psi <- value(text$odds_ratio)
  alpha <- value(text$alpha)
  share <- psi / (1 + psi)
  c(text, list(
    enumeration = mcnemar(text$pairs, delta, psi, alpha),
    exact2x2 = powerPaired2x2(pb = delta * share, pc = delta * (1 - share),
                              npairs = text$pairs, sig.level = alpha, strict = TRUE)$power
  ))
})

rates <- list(
  list(events = 60, exposed_time = "8000", unexposed_time = "24000", rate_ratio = "2",
       alpha = "1/40"),
  list(events = 93, exposed_time = "8000", unexposed_time = "24000", rate_ratio = "2",
       alpha = "1/40"),
  list(events = 94, exposed_time = "8000", unexposed_time = "24000", rate_ratio = "2",
       alpha = "1/40"),
  list(events = 40, exposed_time = "1", unexposed_time = "1", rate_ratio = "3", alpha = "1/20"),
  list(events = 200, exposed_time = "3", unexposed_time = "7", rate_ratio = "1/2",
       alpha = "1/20")
)
rate_rows <- lapply(rates, function(text) {
  t1 <- value(text$exposed_time)
  t0 <- value(text$unexposed_time)
  theta <- value(text$rate_ratio)
  alpha <- value(text$alpha)
  share <- theta * t1 / (theta * t1 + t0)
  n <- text$events
  power <- 0
  for (x in 0:n) {
    p <- exactci::poisson.exact(c(x, n - x), c(t1, t0), tsmethod = "central")$p.value
    if (p <= alpha) power <- power + dbinom(x, n, share)
  }
  c(text, list(enumeration = power))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(exact2x2 = as.character(packageVersion("exact2x2")),
                  epiR = as.character(packageVersion("epiR")),
                  exactci = as.character(packageVersion("exactci"))),
  cases = rows,
  matched = matched_rows,
  rates = rate_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/observational_power_r.json")

sink("replication/comparison/observational_power_r.txt")
cat("Exact power of Fisher's test of no association, written to",
    "tests/fixtures/observational_power_r.json\n\n")
for (row in rows) {
  cat(sprintf("%-12s groups (%d, %d), p = (%s, %s), alpha %s:", row$design, row$first,
              row$second, row$p_first, row$p_second, row$alpha),
      sprintf("enumeration %.12f, exact2x2 %.8f, epiR %.4f\n", row$enumeration, row$exact2x2,
              row$epiR))
}
cat("\nMcNemar's test\n")
for (row in matched_rows) {
  cat(sprintf("%d pairs, discordant %s, odds ratio %s, alpha %s:", row$pairs, row$discordant,
              row$odds_ratio, row$alpha),
      sprintf("enumeration %.12f, exact2x2 %.8f\n", row$enumeration, row$exact2x2))
}
cat("\nThe rate test\n")
for (row in rate_rows) {
  cat(sprintf("%d events, person-time (%s, %s), rate ratio %s, alpha %s:", row$events,
              row$exposed_time, row$unexposed_time, row$rate_ratio, row$alpha),
      sprintf("enumeration %.12f\n", row$enumeration))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/observational_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
