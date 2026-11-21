# Precision of planned intervals against R. Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/precision_r.R
# Needs presize and jsonlite. It regenerates tests/fixtures/precision_r.json, which
# tests/test_precision.py compares with StatClaim offline, and writes precision_r.txt beside
# this file with the values and the R session.
#
# StatClaim's exact interval is Clopper-Pearson, rounded outward to a grid of 1/10,000; two
# groups combine their intervals, each at the smallest four-decimal level whose square is at
# least the requested level. The margin of error is half the width; a relative margin is half
# the width over the planning value, or for a ratio 1 - exp(-h) with h half the width of the
# log interval.
#   binom.test  each exact interval, for every count, and the assurance summed with dbinom
#   qbeta       the interval at an expected count that is not a whole number
#   presize     prec_prop (exact and Wald), prec_riskdiff (Wald), prec_riskratio (Katz) and
#               prec_or (Woolf): the normal intervals' widths
suppressMessages({
  library(presize)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))
grid <- function(bounds) c(floor(bounds[1] * 1e4) / 1e4, ceiling(bounds[2] * 1e4) / 1e4)
exact <- function(x, n, level) grid(as.numeric(binom.test(x, n, conf.level = level)$conf.int))
real_exact <- function(x, n, level) {
  tail <- (1 - level) / 2
  grid(c(if (x <= 0) 0 else qbeta(tail, x, n - x + 1),
         if (x >= n) 1 else qbeta(1 - tail, x + 1, n - x)))
}
arm_level <- function(level) {
  target <- level * 1e8
  root <- floor(sqrt(target))
  while (root^2 < target) root <- root + 1
  root / 1e4
}
odds <- function(p) p / (1 - p)

# A single proportion: the margin at the expected count, and the assurance.
singles <- list(
  list(p = "1/10", n = 400, level = "19/20", margin = "3/100"),
  list(p = "1/10", n = 417, level = "19/20", margin = "3/100"),
  list(p = "3/10", n = 89, level = "19/20", margin = "1/10"),
  list(p = "1/2", n = 1000, level = "99/100", margin = "103/2500")
)
single_rows <- lapply(singles, function(case) {
  p <- value(case$p)
  level <- value(case$level)
  d <- value(case$margin)
  expected <- real_exact(case$n * p, case$n, level)
  halves <- vapply(0:case$n, function(x) diff(exact(x, case$n, level)) / 2, numeric(1))
  row <- c(case, list(
    expected_margin = diff(expected) / 2,
    assurance = sum(dbinom(0:case$n, case$n, p)[halves <= d + 1e-12])
  ))
  if (abs(case$n * p - round(case$n * p)) < 1e-9) {
    row$presize_exact <- prec_prop(p = p, n = case$n, conf.level = level, method = "exact")$conf.width / 2
  }
  row
})

# Two groups: a trial's difference, a cohort's risk ratio and odds ratio. Each assurance is
# summed over every pair of counts.
pair_interval <- function(kind, x0, n0, x1, n1, level) {
  each <- arm_level(level)
  c0 <- exact(x0, n0, each)
  c1 <- exact(x1, n1, each)
  if (kind == "difference") return(c(c1[1] - c0[2], c1[2] - c0[1]))
  if (kind == "ratio") return(c(c1[1] / c0[2], if (c0[1] > 0) c1[2] / c0[1] else Inf))
  lower <- if (c0[2] >= 1) 0 else odds(c1[1]) / odds(c0[2])
  upper <- if (c0[1] > 0 && c1[2] < 1) odds(c1[2]) / odds(c0[1]) else Inf
  c(lower, upper)
}
margin_of <- function(kind, bounds, relative, value) {
  if (!is.finite(bounds[2])) return(Inf)
  if (!relative) return(diff(bounds) / 2)
  if (kind == "difference") return(diff(bounds) / (2 * abs(value)))
  if (bounds[1] <= 0) return(Inf)
  1 - exp(-(log(bounds[2]) - log(bounds[1])) / 2)
}
pairs <- list(
  list(kind = "difference", p0 = "3/10", p1 = "1/2", n0 = 150, n1 = 150, level = "19/20",
       relative = FALSE, margin = "9/50"),
  list(kind = "ratio", p0 = "1/10", p1 = "1/5", n0 = 300, n1 = 150, level = "19/20",
       relative = TRUE, margin = "11/20"),
  list(kind = "odds", p0 = "1/5", p1 = "1/3", n0 = 200, n1 = 100, level = "19/20",
       relative = TRUE, margin = "3/5"),
  list(kind = "ratio", p0 = "1/10", p1 = "1/5", n0 = 200, n1 = 100, level = "19/20",
       relative = FALSE, margin = "9/4")
)
pair_rows <- lapply(pairs, function(case) {
  p0 <- value(case$p0)
  p1 <- value(case$p1)
  level <- value(case$level)
  d <- value(case$margin)
  truth <- switch(case$kind, difference = p1 - p0, ratio = p1 / p0, odds = odds(p1) / odds(p0))
  w0 <- dbinom(0:case$n0, case$n0, p0)
  w1 <- dbinom(0:case$n1, case$n1, p1)
  total <- 0
  for (x0 in which(w0 > 1e-15) - 1) {
    for (x1 in which(w1 > 1e-15) - 1) {
      m <- margin_of(case$kind, pair_interval(case$kind, x0, case$n0, x1, case$n1, level),
                     case$relative, truth)
      if (m <= d + 1e-12) total <- total + w0[x0 + 1] * w1[x1 + 1]
    }
  }
  each <- arm_level(level)
  expected <- {
    c0 <- real_exact(case$n0 * p0, case$n0, each)
    c1 <- real_exact(case$n1 * p1, case$n1, each)
    switch(case$kind,
           difference = c(c1[1] - c0[2], c1[2] - c0[1]),
           ratio = c(c1[1] / c0[2], c1[2] / c0[1]),
           odds = c(odds(c1[1]) / odds(c0[2]), odds(c1[2]) / odds(c0[1])))
  }
  c(case, list(expected_margin = margin_of(case$kind, expected, case$relative, truth),
               assurance = total))
})

# A matched study's conditional odds ratio, and a rate ratio given the events.
matched <- list(pairs = 120, share = "1/4", odds_ratio = "2", level = "19/20", margin = "3/5")
matched_row <- local({
  share <- value(matched$share)
  psi <- value(matched$odds_ratio)
  level <- value(matched$level)
  total <- 0
  for (d in 0:matched$pairs) {
    wd <- dbinom(d, matched$pairs, share)
    if (wd < 1e-15 || d == 0) next
    for (x in 0:d) {
      b <- exact(x, d, level)
      bounds <- c(if (b[1] < 1) odds(b[1]) else Inf, if (b[2] < 1) odds(b[2]) else Inf)
      if (margin_of("odds", bounds, TRUE, psi) <= value(matched$margin) + 1e-12) {
        total <- total + wd * dbinom(x, d, psi / (1 + psi))
      }
    }
  }
  c(matched, list(assurance = total))
})
rates <- list(events = 60, rate_ratio = "2", exposed_time = "8000", unexposed_time = "24000",
              level = "19/20", margin = "9/20")
rate_row <- local({
  exposed <- value(rates$exposed_time) * value(rates$rate_ratio)
  share <- exposed / (exposed + value(rates$unexposed_time))
  scale <- value(rates$unexposed_time) / value(rates$exposed_time)
  level <- value(rates$level)
  total <- 0
  for (x in 0:rates$events) {
    b <- exact(x, rates$events, level)
    bounds <- c(if (b[1] < 1) odds(b[1]) * scale else Inf, if (b[2] < 1) odds(b[2]) * scale else Inf)
    if (margin_of("odds", bounds, TRUE, value(rates$rate_ratio)) <= value(rates$margin) + 1e-12) {
      total <- total + dbinom(x, rates$events, share)
    }
  }
  c(rates, list(assurance = total))
})

# Normal intervals: presize's widths, and Cochran's size with a design effect and a finite
# population.
normals <- list(
  list(kind = "proportion", p = "1/2", n = 385, level = "19/20",
       presize = prec_prop(p = 0.5, n = 385, method = "wald")$conf.width / 2),
  list(kind = "difference", p0 = "3/10", p1 = "1/2", n0 = 200, n1 = 200, level = "19/20",
       presize = prec_riskdiff(p1 = 0.5, p2 = 0.3, n1 = 200, r = 1, method = "wald")$conf.width / 2),
  list(kind = "ratio", p0 = "1/10", p1 = "1/5", n0 = 600, n1 = 300, level = "19/20",
       presize = prec_riskratio(p1 = 0.2, p2 = 0.1, n1 = 300, r = 2, method = "katz")$conf.width / 2),
  list(kind = "odds", p0 = "1/10", p1 = "1/5", n0 = 600, n1 = 300, level = "19/20",
       presize = prec_or(p1 = 0.2, p2 = 0.1, n1 = 300, r = 2, method = "woolf")$conf.width / 2)
)
cochran <- local({
  z <- qnorm(0.975)
  n0 <- z^2 * 0.25 / 0.03^2 * 2
  list(p = "1/2", deff = "2", population = 50000, margin = "3/100",
       n = ceiling(n0 / (1 + (n0 - 1) / 50000)))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(presize = as.character(packageVersion("presize"))),
  singles = single_rows,
  pairs = pair_rows,
  matched = matched_row,
  rates = rate_row,
  normals = normals,
  cochran = cochran
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/precision_r.json")

sink("replication/comparison/precision_r.txt")
cat("Precision of planned intervals, written to tests/fixtures/precision_r.json\n\n")
for (row in single_rows) {
  cat(sprintf("proportion %s, n %d, level %s, margin %s: expected margin %.6f, assurance %.12f",
              row$p, row$n, row$level, row$margin, row$expected_margin, row$assurance),
      if (is.null(row$presize_exact)) "\n" else sprintf(", presize exact %.6f\n", row$presize_exact),
      sep = "")
}
for (row in pair_rows) {
  cat(sprintf("%s, p = (%s, %s), groups (%d, %d), %s margin %s: expected %.6f, assurance %.12f\n",
              row$kind, row$p0, row$p1, row$n0, row$n1, if (row$relative) "relative" else "absolute",
              row$margin, row$expected_margin, row$assurance))
}
cat(sprintf("matched: %d pairs, discordant %s, odds ratio %s, relative margin %s: assurance %.12f\n",
            matched_row$pairs, matched_row$share, matched_row$odds_ratio, matched_row$margin,
            matched_row$assurance))
cat(sprintf("rate ratio: %d events, ratio %s, relative margin %s: assurance %.12f\n",
            rate_row$events, rate_row$rate_ratio, rate_row$margin, rate_row$assurance))
for (row in normals) cat(sprintf("normal %s: presize half width %.12f\n", row$kind, row$presize))
cat(sprintf("Cochran: p %s, deff %s, N %d, margin %s: n = %d\n", cochran$p, cochran$deff,
            cochran$population, cochran$margin, cochran$n))
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/precision_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
