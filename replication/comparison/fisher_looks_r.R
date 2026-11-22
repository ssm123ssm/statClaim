# Exact power of Fisher's test at two looks, by brute force in R: every table at the first
# look and every increment to the second, each tested with fisher.test.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/fisher_looks_r.R
# Needs jsonlite. It regenerates tests/fixtures/fisher_looks_r.json, which
# tests/test_fisher_looks.py compares with StatClaim offline, and writes fisher_looks_r.txt
# beside this file with the values and the R session.
#
# A path of counts stops at the first look whose fisher.test p-value is at most that look's
# level. The chance of stopping at each look is the sum of dbinom products over the paths
# that stop there. StatClaim carries the counts from look to look instead of listing paths;
# the two must agree to rounding.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
p_value <- function(x_c, n_c, x_t, n_t, alternative) {
  table <- matrix(c(x_t, x_c, n_t - x_t, n_c - x_c), nrow = 2)
  fisher.test(table, alternative = if (alternative == "greater") "greater" else "two.sided")$p.value
}
stopping <- function(case, p_c, p_t) {
  first <- case$looks[[1]]
  second <- case$looks[[2]]
  m_c <- second$n_control - first$n_control
  m_t <- second$n_treatment - first$n_treatment
  stop1 <- 0
  stop2 <- 0
  for (x_c in 0:first$n_control) {
    for (x_t in 0:first$n_treatment) {
      w <- dbinom(x_c, first$n_control, p_c) * dbinom(x_t, first$n_treatment, p_t)
      if (p_value(x_c, first$n_control, x_t, first$n_treatment, case$alternative) <=
          value(first$alpha)) {
        stop1 <- stop1 + w
        next
      }
      for (a in 0:m_c) {
        for (b in 0:m_t) {
          v <- w * dbinom(a, m_c, p_c) * dbinom(b, m_t, p_t)
          if (p_value(x_c + a, second$n_control, x_t + b, second$n_treatment, case$alternative) <=
              value(second$alpha)) stop2 <- stop2 + v
        }
      }
    }
  }
  c(stop1, stop2)
}
cases <- list(
  list(alternative = "two_sided", p_control = "3/10", p_treatment = "7/10",
       looks = list(list(n_control = 12, n_treatment = 12, alpha = "1/100"),
                    list(n_control = 24, n_treatment = 24, alpha = "1/25"))),
  list(alternative = "greater", p_control = "1/5", p_treatment = "3/5",
       looks = list(list(n_control = 8, n_treatment = 16, alpha = "1/50"),
                    list(n_control = 16, n_treatment = 32, alpha = "3/100")))
)
rows <- lapply(cases, function(case) {
  c(case, list(
    stopped = stopping(case, value(case$p_control), value(case$p_treatment)),
    stopped_null = stopping(case, value(case$p_control), value(case$p_control))
  ))
})

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/fisher_looks_r.json")

sink("replication/comparison/fisher_looks_r.txt")
cat("Fisher's test at two looks, by brute force, written to tests/fixtures/fisher_looks_r.json\n\n")
for (row in rows) {
  cat(sprintf("%s, rates (%s, %s): stopping %.12f, %.12f; under the null %.12f, %.12f\n",
              row$alternative, row$p_control, row$p_treatment, row$stopped[1], row$stopped[2],
              row$stopped_null[1], row$stopped_null[2]))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/fisher_looks_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
