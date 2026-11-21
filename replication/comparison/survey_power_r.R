# Power of the survey tests against R, through the design effect. Run from the repository
# root:
#   R_LIBS=path/to/library Rscript replication/comparison/survey_power_r.R
# Needs pwrss and jsonlite. It regenerates tests/fixtures/survey_power_r.json, which
# tests/test_survey_power.py compares with StatClaim offline, and writes survey_power_r.txt
# beside this file with the values and the R session.
#
# A complex sample of n with design effect deff has the power of a simple random sample of
# n / deff (Kish). So the participants a survey needs are deff times what pwrss gives for a
# simple random sample:
#   pwrss    power.z.logistic(method = "hsieh"), a binary exposure (two proportions) or a
#            normal one (an odds ratio per SD), not rounded
#   formula  the Wald test of a slope: pnorm(|slope| sd(x) sqrt(n / deff) / residual_sd - z)
suppressMessages({
  library(pwrss)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))

groups <- list(
  list(p_reference = "1/10", p_other = "3/25", share_other = "1/5", deff = "2", power = "4/5"),
  list(p_reference = "1/5", p_other = "1/4", share_other = "1/2", deff = "3/2", power = "9/10")
)
group_rows <- lapply(groups, function(case) {
  n <- power.z.logistic(base.prob = value(case$p_reference), prob = value(case$p_other),
                        power = value(case$power),
                        distribution = list(dist = "binomial", size = 1,
                                            prob = value(case$share_other)),
                        method = "hsieh", ceil.n = FALSE, verbose = 0)$n
  c(case, list(simple_random_n = n, survey_n = n * value(case$deff)))
})

trends <- list(
  list(odds_ratio = "6/5", baseline = "1/10", deff = "5/2", power = "4/5"),
  list(odds_ratio = "3/2", baseline = "1/5", deff = "4/5", power = "9/10")
)
trend_rows <- lapply(trends, function(case) {
  n <- power.z.logistic(base.prob = value(case$baseline), odds.ratio = value(case$odds_ratio),
                        power = value(case$power), method = "hsieh", ceil.n = FALSE,
                        verbose = 0)$n
  c(case, list(simple_random_n = n, survey_n = n * value(case$deff)))
})

slopes <- list(
  list(slope = "1/5", exposure_sd = "4", residual_sd = "15", deff = "3/2", n = 5000,
       alpha = "1/20"),
  list(slope = "-1/2", exposure_sd = "2", residual_sd = "10", deff = "2", n = 800,
       alpha = "1/100")
)
slope_rows <- lapply(slopes, function(case) {
  se <- value(case$residual_sd) / (value(case$exposure_sd) * sqrt(case$n / value(case$deff)))
  power <- pnorm(abs(value(case$slope)) / se - qnorm(1 - value(case$alpha) / 2))
  c(case, list(power = power))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(pwrss = as.character(packageVersion("pwrss"))),
  groups = group_rows,
  trends = trend_rows,
  slopes = slope_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/survey_power_r.json")

sink("replication/comparison/survey_power_r.txt")
cat("Power of the survey tests, written to tests/fixtures/survey_power_r.json\n\n")
for (row in group_rows) {
  cat(sprintf("p = (%s, %s), share exposed %s, deff %s, power %s: %.4f simple random, %.4f survey\n",
              row$p_reference, row$p_other, row$share_other, row$deff, row$power,
              row$simple_random_n, row$survey_n))
}
for (row in trend_rows) {
  cat(sprintf("OR per SD %s, baseline %s, deff %s, power %s: %.4f simple random, %.4f survey\n",
              row$odds_ratio, row$baseline, row$deff, row$power, row$simple_random_n,
              row$survey_n))
}
for (row in slope_rows) {
  cat(sprintf("slope %s, sd(x) %s, residual sd %s, deff %s, n %d, alpha %s: power %.12f\n",
              row$slope, row$exposure_sd, row$residual_sd, row$deff, row$n, row$alpha,
              row$power))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/survey_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
