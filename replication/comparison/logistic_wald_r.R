# Exact power of the Wald test of the treatment coefficient in a two-arm logistic
# regression, by enumerating every 2x2 table and fitting glm to each.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/logistic_wald_r.R
# Needs jsonlite. It regenerates tests/fixtures/logistic_wald_r.json, which
# tests/test_logistic_wald.py compares with StatClaim offline, and writes logistic_wald_r.txt
# beside this file with the values and the R session.
#
# For every table (control responders, treated responders) glm(binomial) gives the Wald
# p-value of the treatment coefficient, as summary(glm) reports it; power is the sum of
# dbinom(x_c) dbinom(x_t) over the tables it rejects. A table with an empty cell has no
# finite estimate; glm's huge standard error then keeps it from rejecting. StatClaim uses the
# closed form of the same statistic; the two must agree to rounding.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
wald_p <- function(x_c, x_t, n_c, n_t) {
  y <- cbind(c(x_c, x_t), c(n_c - x_c, n_t - x_t))
  arm <- c(0, 1)
  fit <- suppressWarnings(glm(y ~ arm, family = binomial))
  coefficients <- summary(fit)$coefficients
  if (nrow(coefficients) < 2) return(1)
  coefficients[2, 4]
}
power <- function(case) {
  n_c <- case$n_control
  n_t <- case$n_treatment
  alpha <- value(case$alpha)
  p_c <- value(case$p_control)
  p_t <- value(case$p_treatment)
  total <- 0
  for (x_c in 0:n_c) {
    for (x_t in 0:n_t) {
      p <- wald_p(x_c, x_t, n_c, n_t)
      if (case$side == "higher") {
        estimate <- if (x_c %in% c(0, n_c) || x_t %in% c(0, n_t)) 0 else
          log(x_t / (n_t - x_t)) - log(x_c / (n_c - x_c))
        rejects <- estimate > 0 && p / 2 <= alpha
      } else {
        rejects <- p <= alpha
      }
      if (rejects) total <- total + dbinom(x_c, n_c, p_c) * dbinom(x_t, n_t, p_t)
    }
  }
  total
}
cases <- list(
  list(n_control = 30, n_treatment = 30, alpha = "1/20", side = "both", p_control = "3/10", p_treatment = "1/2"),
  list(n_control = 30, n_treatment = 30, alpha = "1/20", side = "both", p_control = "3/10", p_treatment = "3/10"),
  list(n_control = 60, n_treatment = 40, alpha = "1/40", side = "higher", p_control = "1/5", p_treatment = "9/20"),
  list(n_control = 50, n_treatment = 50, alpha = "1/20", side = "both", p_control = "1/20", p_treatment = "1/5")
)
rows <- lapply(cases, function(case) c(case, list(power = power(case))))

fixture <- list(r_version = R.version.string, cases = rows)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/logistic_wald_r.json")

sink("replication/comparison/logistic_wald_r.txt")
cat("Exact power of the logistic Wald test by glm on every table, written to",
    "tests/fixtures/logistic_wald_r.json\n\n")
for (row in rows) {
  cat(sprintf("n (%d, %d), alpha %s (%s), rates (%s, %s): %.12f\n", row$n_control,
              row$n_treatment, row$alpha, row$side, row$p_control, row$p_treatment, row$power))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/logistic_wald_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
