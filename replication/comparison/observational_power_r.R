# Exact power of Fisher's test of no association for cohort and case-control studies,
# against R. Run from the repository root:
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
fixture <- list(
  r_version = R.version.string,
  packages = list(exact2x2 = as.character(packageVersion("exact2x2")),
                  epiR = as.character(packageVersion("epiR"))),
  cases = rows
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
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/observational_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
