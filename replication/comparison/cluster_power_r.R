# Power of the t-test on cluster summaries against R. Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/cluster_power_r.R
# Needs CRTSize and jsonlite. It regenerates tests/fixtures/cluster_power_r.json, which
# tests/test_cluster_power.py compares with StatClaim offline, and writes cluster_power_r.txt
# beside this file with the values and the R session.
#
# A cluster of m participants has a mean with variance sd^2 (1 + (m - 1) icc) / m, and a
# proportion with variance p (1 - p)(1 + (m - 1) icc) / m. The t-test compares cluster
# summaries with k_c + k_t - 2 degrees of freedom.
#   power.t.test  base R, for equal arms: n clusters per arm and the summary's standard
#                 deviation (for proportions, the root mean of the two arms' variances)
#   pt            the noncentral t directly, for unequal arms
#   CRTSize       n4means and n4props, the normal-approximation number of clusters per arm,
#                 for context: it does not use the t distribution
suppressMessages({
  library(CRTSize)
  library(jsonlite)
})

value <- function(text) eval(parse(text = text))
design_effect <- function(m, icc) 1 + (m - 1) * icc

# Two-sided power of the t-test on cluster summaries, ignoring the far tail as
# power.t.test does by default.
t_power <- function(k_c, k_t, shift, v_c, v_t, alpha) {
  df <- k_c + k_t - 2
  se <- sqrt(v_c / k_c + v_t / k_t)
  pt(qt(1 - alpha / 2, df), df, ncp = abs(shift) / se, lower.tail = FALSE)
}

mean_cases <- list(
  list(k_c = 6, k_t = 6, m = 20, delta = "5", sd = "10", icc = "1/20", alpha = "1/20"),
  list(k_c = 8, k_t = 8, m = 20, delta = "5", sd = "10", icc = "1/20", alpha = "1/20"),
  list(k_c = 4, k_t = 4, m = 50, delta = "3/2", sd = "2", icc = "1/10", alpha = "1/20"),
  list(k_c = 12, k_t = 12, m = 10, delta = "1/2", sd = "1", icc = "1/100", alpha = "1/100"),
  list(k_c = 10, k_t = 15, m = 30, delta = "4", sd = "12", icc = "3/100", alpha = "1/20"),
  list(k_c = 30, k_t = 30, m = 5, delta = "1", sd = "4", icc = "0", alpha = "1/20")
)
mean_rows <- lapply(mean_cases, function(case) {
  sd <- value(case$sd)
  v <- sd^2 * design_effect(case$m, value(case$icc)) / case$m
  delta <- value(case$delta)
  alpha <- value(case$alpha)
  row <- c(case, list(noncentral_t = t_power(case$k_c, case$k_t, delta, v, v, alpha)))
  if (case$k_c == case$k_t) {
    row$power_t_test <- power.t.test(n = case$k_c, delta = delta, sd = sqrt(v),
                                     sig.level = alpha)$power
  }
  row
})

proportion_cases <- list(
  list(k_c = 6, k_t = 6, m = 20, p_c = "3/10", p_t = "1/2", icc = "1/50", alpha = "1/20"),
  list(k_c = 10, k_t = 10, m = 50, p_c = "1/10", p_t = "1/5", icc = "1/20", alpha = "1/20"),
  list(k_c = 8, k_t = 12, m = 25, p_c = "2/5", p_t = "3/5", icc = "1/10", alpha = "1/20"),
  list(k_c = 20, k_t = 20, m = 100, p_c = "1/20", p_t = "1/10", icc = "1/100",
       alpha = "1/100")
)
proportion_rows <- lapply(proportion_cases, function(case) {
  p_c <- value(case$p_c)
  p_t <- value(case$p_t)
  effect <- design_effect(case$m, value(case$icc))
  v_c <- p_c * (1 - p_c) * effect / case$m
  v_t <- p_t * (1 - p_t) * effect / case$m
  alpha <- value(case$alpha)
  row <- c(case, list(noncentral_t = t_power(case$k_c, case$k_t, p_t - p_c, v_c, v_t, alpha)))
  if (case$k_c == case$k_t) {
    row$power_t_test <- power.t.test(n = case$k_c, delta = p_t - p_c, sd = sqrt((v_c + v_t) / 2),
                                     sig.level = alpha)$power
  }
  row
})

# The fewest clusters per arm, or participants per cluster, with power at least the target.
search_cases <- list(
  list(kind = "means", vary = "clusters", m = 20, delta = "5", sd = "10", icc = "1/20",
       alpha = "1/20", power = "4/5"),
  list(kind = "means", vary = "clusters", m = 10, delta = "3/10", sd = "1", icc = "1/50",
       alpha = "1/20", power = "9/10"),
  list(kind = "proportions", vary = "clusters", m = 30, p_c = "3/10", p_t = "1/2",
       icc = "1/50", alpha = "1/20", power = "4/5"),
  list(kind = "proportions", vary = "clusters", m = 50, p_c = "1/10", p_t = "3/20",
       icc = "1/20", alpha = "1/20", power = "4/5"),
  list(kind = "means", vary = "size", k = 6, delta = "5", sd = "10", icc = "1/20",
       alpha = "1/20", power = "4/5")
)
search_power <- function(case, k, m) {
  effect <- design_effect(m, value(case$icc))
  if (case$kind == "means") {
    v <- value(case$sd)^2 * effect / m
    return(power.t.test(n = k, delta = value(case$delta), sd = sqrt(v),
                        sig.level = value(case$alpha))$power)
  }
  p_c <- value(case$p_c)
  p_t <- value(case$p_t)
  v <- (p_c * (1 - p_c) + p_t * (1 - p_t)) / 2 * effect / m
  power.t.test(n = k, delta = p_t - p_c, sd = sqrt(v), sig.level = value(case$alpha))$power
}
search_rows <- lapply(search_cases, function(case) {
  target <- value(case$power)
  if (case$vary == "clusters") {
    k <- 4
    while (search_power(case, k, case$m) < target) k <- k + 1
    row <- c(case, list(clusters_per_arm = k, power_at = search_power(case, k, case$m)))
    crt <- if (case$kind == "means") {
      n4means(delta = value(case$delta), sigma = value(case$sd), m = case$m,
              ICC = value(case$icc), alpha = value(case$alpha), power = target)$n
    } else {
      n4props(pe = value(case$p_t), pc = value(case$p_c), m = case$m, ICC = value(case$icc),
              alpha = value(case$alpha), power = target)$n
    }
    row$crtsize <- crt
    return(row)
  }
  m <- 1
  while (search_power(case, case$k, m) < target) m <- m + 1
  c(case, list(cluster_size = m, power_at = search_power(case, case$k, m)))
})

fixture <- list(
  r_version = R.version.string,
  packages = list(CRTSize = as.character(packageVersion("CRTSize"))),
  means = mean_rows,
  proportions = proportion_rows,
  searches = search_rows
)
writeLines(toJSON(fixture, auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/cluster_power_r.json")

sink("replication/comparison/cluster_power_r.txt")
cat("Power of the t-test on cluster summaries, written to tests/fixtures/cluster_power_r.json\n\n")
cat("Cluster means\n")
for (row in mean_rows) {
  cat(sprintf("clusters (%d, %d) of %d, difference %s, sd %s, icc %s, alpha %s:", row$k_c,
              row$k_t, row$m, row$delta, row$sd, row$icc, row$alpha),
      sprintf(" noncentral t %.12f", row$noncentral_t),
      if (is.null(row$power_t_test)) "\n" else
        sprintf(", power.t.test %.12f\n", row$power_t_test), sep = "")
}
cat("\nCluster proportions\n")
for (row in proportion_rows) {
  cat(sprintf("clusters (%d, %d) of %d, p = (%s, %s), icc %s, alpha %s:", row$k_c, row$k_t,
              row$m, row$p_c, row$p_t, row$icc, row$alpha),
      sprintf(" noncentral t %.12f", row$noncentral_t),
      if (is.null(row$power_t_test)) "\n" else
        sprintf(", power.t.test %.12f\n", row$power_t_test), sep = "")
}
cat("\nSearches\n")
for (row in search_rows) {
  if (row$vary == "clusters") {
    cat(sprintf("%s, clusters of %d, icc %s, power %s: %d clusters per arm (power %.6f);",
                row$kind, row$m, row$icc, row$power, row$clusters_per_arm, row$power_at),
        sprintf("CRTSize %.3f\n", row$crtsize))
  } else {
    cat(sprintf("%s, %d clusters per arm, icc %s, power %s: %d per cluster (power %.6f)\n",
                row$kind, row$k, row$icc, row$power, row$cluster_size, row$power_at))
  }
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
output <- "replication/comparison/cluster_power_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
